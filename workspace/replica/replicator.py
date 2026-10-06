"""灾备复制器管理器 —— 复制循环 + 演练状态机 + 任期围栏。

截面原子性
==========
拉到的每个分段先在**投影副本**上完成“链校验 → 事件哈希 → 折叠 → 守恒”
全部检查，通过后才把边界与分段原文放进同一个 SQLite 事务提交，并原子
替换内存投影指针。任何时刻只读查询看到的投影都是某个完整确认边界，
绝不会出现“事件已进入、余额/租约/草案/命令结果只更新一半”。

重放幂等
========
已确认序号的分段重复到达 → 正文一致则忽略，正文不同则隔离；
确认边界在 SQLite 事务里推进，进程重启从最后确认边界继续。

演练状态机
==========
``POST /ops/drills`` 锁定当前截面进入 VALIDATING（复制立即冻结）→
全量验证（事件链、分段链、守恒、重放等价、命令结果、任期内无新分段）→
成功发 ISSUED 任期地址；同一演练再请求返回原结果；取消/到期 →
地址失效，复制自动恢复。
"""

from __future__ import annotations

import json
import threading
import time
import urllib.error
import urllib.request
import uuid
from typing import Any

from . import verifier
from .store import ReplicaStore, new_token

# 演练 / 复制异常原因码
PRIMARY_UNAVAILABLE = "PRIMARY_UNAVAILABLE"
LAG_OVER_LIMIT = "LAG_OVER_LIMIT"
STALE_EPOCH = "STALE_EPOCH"
ADVANCE_DURING_DRILL = "ADVANCE_DURING_DRILL"
VALIDATION_FAILED = "VALIDATION_FAILED"
LAG_EXCEEDED_AT_LOCK = "LAG_EXCEEDED_AT_LOCK"
NO_CONFIRMED_SURFACE = "NO_CONFIRMED_SURFACE"
ALREADY_ACTIVE_DRILL = "ALREADY_ACTIVE_DRILL"
REPLICATION_PAUSED = "REPLICATION_PAUSED"
TERM_EXPIRED = "TERM_EXPIRED"
PROCESS_RESTART = "PROCESS_RESTART"
BODY_CONFLICT = "BODY_CONFLICT"
OWNERSHIP_LOST = "OWNERSHIP_LOST"
WAIT_TIMEOUT = "WAIT_TIMEOUT"
WAIT_REQUEST_CONFLICT = "WAIT_REQUEST_CONFLICT"

# 水位等待：单次查询允许声明的最长等待（超出部分被截断并在响应中如实回显）
MAX_WAIT_MS = 120_000
# 等待循环周期性回读权威存储的最大间隔：接管实例在另一进程推进水位时，
# 本进程的等待者必须能跟随权威存储恢复，而不是睡死在自己的条件变量上
WAIT_RECHECK_SECONDS = 0.5


class ReplicatorError(Exception):
    status = 400

    def __init__(self, reason: str, message: str, status: int | None = None,
                 details: dict[str, Any] | None = None):
        super().__init__(message)
        self.reason = reason
        if status is not None:
            self.status = status
        self.details = details or {}


class Replicator:
    def __init__(
        self,
        store: ReplicaStore,
        primary_url: str,
        max_lag_segments: int = 5,
        poll_interval: float = 0.5,
        request_timeout: float = 5.0,
    ):
        self.store = store
        self.primary_url = primary_url.rstrip("/")
        self.max_lag_segments = max_lag_segments
        self.poll_interval = poll_interval
        self.request_timeout = request_timeout

        self._lock = threading.RLock()
        # 水位等待者条件变量：等待只阻塞各自的 HTTP 线程（wait 时释放锁），
        # 复制线程提交/重建后仅做 notify，绝不被等待者拖住。
        self._watermark_cond = threading.Condition(self._lock)
        self.epoch = self.store.get_epoch()
        self.segment_size = int(self.store.meta()["segment_size"])

        # 写入所有权围栏：失主（存储纪元已被接替实例提升）后永久置位。
        # 失主进程的在途提交/发布全部被拒，后台循环自行停摆。
        self._ownership_lost = False
        self.ownership_lost_at: float | None = None

        # 内存中的“最近完整确认截面”：启动时从持久化分段重放
        self.segments = self.store.load_segments()
        self.projection = verifier.replay_all(self.segments)
        self._published_digest = verifier.state_digest(self.projection)

        # 主站观测
        self.primary_tip_seq = 0
        self.primary_sealed_index = len(self.segments)
        self.primary_status_at: float | None = None
        self.last_pull_at: float | None = None
        self.last_error: str | None = None

        # 滞后隔离做状态化记录，避免同一轮落后反复刷审计
        self._lag_quarantined = False

        # 启动恢复：
        # - 验证中的演练因进程重启无法保证冻结语义 → 作废；
        # - 已发任期若截止时刻在停机期间到达 → 立即收口（不等 sweeper 首个
        #   tick，避免重启后仍有一段“已过期却冻结”的窗口）；
        # - 修复终态行/收口审计因崩溃留下的半截不一致。
        self._recover_drills_on_startup()

        self._stop = threading.Event()
        self.thread = threading.Thread(target=self._poll_loop, name="replica-poller", daemon=True)
        self.sweeper = threading.Thread(target=self._sweep_loop, name="drill-sweeper", daemon=True)

    # ------------------------------------------------------------------
    # 生命周期
    # ------------------------------------------------------------------

    def start(self) -> None:
        # 新进程接管：先提升纪元取得写入所有权，再从存储中的权威水位重建
        # 内存状态——顺序不能反：纪元一旦提升，任何旧纪元进程的迟到提交都会
        # 被存储层 CAS 拒绝，而本进程在权威水位重建完成前绝不发布内存结果。
        self.epoch = self.store.bump_epoch()
        self._rebuild_from_authoritative()
        # 停机期间已过截止时刻的等待请求：按当前权威水位立即收口为超时终态，
        # 重启后不存在“已过期却仍显示等待中”的窗口；同标识再请求返回该结果。
        self.sweep_expired_waits()
        self.store.audit("replicator_started", {
            "epoch": self.epoch,
            "confirmed_index": self.confirmed_index,
            "state_digest": self._published_digest,
        })
        self.thread.start()
        self.sweeper.start()

    def shutdown(self) -> None:
        self._stop.set()

    def _notify_watermark(self) -> None:
        """唤醒全部水位等待者（可在未持锁处调用；RLock 可重入）。"""
        with self._watermark_cond:
            self._watermark_cond.notify_all()

    def _rebuild_from_authoritative(self) -> None:
        """从存储中的权威水位完整重建内存状态。

        接替实例接管、或发现权威水位已被并行推进时，绝不允许“漏过别人刚
        提交的中间批次、继续发布后续批次内存结果”：丢弃全部在途内存状态，
        重新加载已确认分段并完整重放，使磁盘重算值与查询结果严格一致。
        """
        self.segments = self.store.load_segments()
        self.projection = verifier.replay_all(self.segments)
        self._published_digest = verifier.state_digest(self.projection)
        # 权威水位可能刚被并行实例推进：唤醒等待者按新水位重新判定
        self._notify_watermark()

    def _storage_epoch(self) -> int:
        return int(self.store.meta()["epoch"])

    def _demote_lost_owner(self, current_epoch: int, *, detail: str,
                           source: str = "poll") -> None:
        """失去写入所有权后的稳定退出：重建到权威水位 + 永久停摆。

        - 先把内存截面重建到存储权威水位（查询不再返回漏批的陈旧结果）；
        - 置失主标记并停止后台拉取/sweep，本进程不再产生任何在途写入；
        - 留下隔离记录与审计轨迹，页面/审计可见“被拒的旧实例”与接管纪元。
        重复调用幂等（只记录第一次失主）。
        """
        self._rebuild_from_authoritative()
        already_lost = self._ownership_lost
        self._ownership_lost = True
        if self.ownership_lost_at is None:
            self.ownership_lost_at = time.time()
        self._stop.set()
        self._notify_watermark()  # 失主后等待者改按权威存储水位重新判定
        if not already_lost:
            self.store.quarantine(
                OWNERSHIP_LOST, detail, source,
                epoch=self.epoch,
                envelope_digest_value=None,
            )
            self.store.audit("ownership_lost", {
                "lost_epoch": self.epoch,
                "current_epoch": current_epoch,
                "authoritative_index": self.confirmed_index,
                "state_digest": self._published_digest,
                "detail": detail,
            })
        self.last_error = f"{OWNERSHIP_LOST}: {detail}"

    def _recover_drills_on_startup(self) -> None:
        """进程启动时统一收口遗留演练（不依赖后台线程的首个 tick）。"""
        now = time.time()
        # 先修复终态行/收口审计因崩溃留下的半截不一致（幂等，只补不改终态），
        # 再决定哪些活动演练需要收口：避免把“审计已在、行残留 ISSUED”的
        # 镜像半截误当成新到期，落下第二条终态与审计。
        for drill in self.store.list_drills(limit=500):
            self.store.reconcile_drill_termination(drill["drill_id"])
        for drill in self.store.list_active_drills():
            if drill["state"] == "VALIDATING":
                # 验证中的演练无法在新进程内保证“验证窗口内截面定格”，作废
                self._finalize(
                    drill, "ABORTED", PROCESS_RESTART,
                    "进程重启：验证中的演练无法保证冻结语义，已作废",
                )
            elif (
                drill["state"] == "ISSUED"
                and drill["term_expires_at"]
                and now >= drill["term_expires_at"]
            ):
                # 截止时刻在停机期间已经到达：主动结束，旧凭证即刻稳定 410，
                # 复制立即从停下的位置继续（poller 不再被一条死演练冻结）
                self._expire_if_due(drill, now=now)

    # ------------------------------------------------------------------
    # 拉取循环
    # ------------------------------------------------------------------

    def _http_json(self, path: str) -> Any:
        url = f"{self.primary_url}{path}"
        with urllib.request.urlopen(url, timeout=self.request_timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def _poll_loop(self) -> None:
        while not self._stop.wait(self.poll_interval):
            try:
                self.poll_once()
            except Exception as exc:  # 拉取线程不能死
                with self._lock:
                    self.last_error = f"{type(exc).__name__}: {exc}"

    def _sweep_loop(self) -> None:
        while not self._stop.wait(0.5):
            try:
                self.sweep_due_terms()
            except Exception as exc:  # sweeper 线程任何异常都不能死
                with self._lock:
                    self.last_error = f"{type(exc).__name__}: {exc}"
            try:
                self.sweep_expired_waits()
            except Exception as exc:  # noqa: BLE001
                with self._lock:
                    self.last_error = f"{type(exc).__name__}: {exc}"

    def sweep_due_terms(self, now: float | None = None) -> list[str]:
        """主动收口所有截止时刻已到的 ISSUED 演练。

        即使调用方再也不请求任期地址，演练记录也会在这里自行收口、旧凭证
        转为稳定 410、后台复制从冻结点继续。返回本次实际收口的演练 id。
        """
        now = now if now is not None else time.time()
        expired: list[str] = []
        with self._lock:
            if self._ownership_lost:
                return expired  # 失主进程不再收口演练：交给持有当前纪元的实例
            for drill in self.store.list_active_drills():
                if (
                    drill["state"] == "ISSUED"
                    and drill["term_expires_at"]
                    and now >= drill["term_expires_at"]
                ):
                    if self._expire_if_due(drill, now=now):
                        expired.append(drill["drill_id"])
        return expired

    def _expire_if_due(self, drill: dict[str, Any], *, now: float) -> bool:
        """在锁内把一条已到期的 ISSUED 演练收口为 EXPIRED。

        收口前重新从权威行读取，确保定时结束与人工撤销/并发读取相撞时
        只能落下一次终态：原子条件更新输掉的一方不改状态、不写审计。
        """
        fresh = self.store.get_drill(drill["drill_id"])
        if fresh is None or fresh["state"] != "ISSUED":
            return False
        if not fresh["term_expires_at"] or now < fresh["term_expires_at"]:
            return False
        return self._finalize(
            fresh, "EXPIRED", TERM_EXPIRED,
            f"任期已于 {fresh['term_expires_at']} 到期",
        )

    def _finalize(self, drill: dict[str, Any], state: str,
                  reason: str, detail: str) -> bool:
        """唯一的演练终态落盘路径：原子条件更新 + 同一事务写一条审计。

        返回是否由本次调用完成收口。竞争失败（已被定时到期/人工撤销/另一
        进程收口）时返回 False，调用方按既有终态幂等返回。
        """
        report = drill.get("report") or {}
        report.setdefault("termination", {"reason": reason, "detail": detail,
                                          "at": time.time()})
        return self.store.finalize_drill_if_active(
            drill["drill_id"], state, reason, detail, report=report,
        )

    def poll_once(self) -> dict[str, Any] | None:
        """一轮拉取：看主站状态 → 滞后判定 → 拉下一分段。返回应用结果。"""
        with self._lock:
            if self._ownership_lost:
                return None  # 失主进程稳定退出，不再发起任何在途写入
            # 每次提交前先与存储中的权威纪元对账：已被接替实例接管则退出
            storage_epoch = self._storage_epoch()
            if storage_epoch != self.epoch:
                self._demote_lost_owner(
                    storage_epoch,
                    detail=(f"轮询前发现存储纪元 {storage_epoch} 已不是本实例"
                            f"持有的 {self.epoch}，旧实例停止在途工作"),
                )
                return None
            if self.store.meta()["paused"]:
                return None
            if self.store.active_drill() is not None:
                return None  # 演练冻结期间不复制

        status = self._fetch_primary_status()
        with self._lock:
            self.primary_tip_seq = status["tip_seq"]
            self.primary_sealed_index = status["sealed_index"]
            self.primary_status_at = time.time()
            if status["segment_size"] != self.segment_size:
                # 主站分段大小变了：不能再安全拼接，隔离并停止自动拉取
                self._quarantine(
                    verifier.SEGMENT_SIZE_MISMATCH,
                    f"主站分段大小 {status['segment_size']} 与本地 {self.segment_size} 不一致",
                    source="poll",
                )
                return None

            lag_segments = status["sealed_index"] - self.confirmed_index
            # 初始冷启动追赶（本地尚无确认分段）不做落后隔离：
            # “落后超限”针对的是稳态运行中复制被甩开，而不是首次建站。
            steady_state = self.confirmed_index > 0
            if steady_state and lag_segments > self.max_lag_segments:
                if not self._lag_quarantined:
                    self._lag_quarantined = True
                    self._quarantine(
                        LAG_OVER_LIMIT,
                        f"落后主站 {lag_segments} 个分段（{status['tip_seq'] - self.confirmed_seq} 事件）"
                        f"，超过限制 {self.max_lag_segments} 分段；已隔离，禁止继续暴露陈旧截面",
                        source="poll",
                    )
                return None
            self._lag_quarantined = False

            if status["sealed_index"] <= self.confirmed_index:
                return None  # 没有新的密封分段

            next_index = self.confirmed_index + 1
            env = self._fetch_segment(next_index)
            if env is None:
                self._quarantine(
                    verifier.SEGMENT_INDEX_MISMATCH,
                    f"主站报告已有 {status['sealed_index']} 段，但分段 {next_index} 取不到（缺失）",
                    source="poll", segment_index=next_index,
                )
                return None
            self.last_pull_at = time.time()
            result = self._ingest_locked(env, source="poll")
            return result

    def _fetch_primary_status(self) -> dict[str, Any]:
        try:
            return self._http_json("/replica/status")
        except (urllib.error.URLError, OSError, TimeoutError, json.JSONDecodeError) as exc:
            with self._lock:
                self.last_error = f"{PRIMARY_UNAVAILABLE}: {exc}"
            raise

    def _fetch_segment(self, index: int) -> dict[str, Any] | None:
        try:
            return self._http_json(f"/replica/segments/{index}")
        except urllib.error.HTTPError as exc:
            if exc.code == 404:
                return None
            with self._lock:
                self.last_error = f"{PRIMARY_UNAVAILABLE}: HTTP {exc.code}"
            raise

    # ------------------------------------------------------------------
    # 分段准入（核心）
    # ------------------------------------------------------------------

    def ingest(
        self,
        env: dict[str, Any],
        *,
        source: str,
        epoch: int | None = None,
    ) -> dict[str, Any]:
        """外部注入分段（测试/补拉）。走与轮询完全相同的准入路径。"""
        with self._lock:
            # 纪元以存储中的权威值为准（接替实例可能已经把纪元抬高）
            storage_epoch = self._storage_epoch()
            if epoch is not None and epoch != storage_epoch:
                self._quarantine(
                    STALE_EPOCH,
                    f"迟到写入来自旧纪元进程（收到 {epoch}，当前 {storage_epoch}），已拒绝",
                    source=source,
                    envelope_digest_value=env.get("digest") if isinstance(env, dict) else None,
                    epoch=epoch,
                )
                raise ReplicatorError(
                    STALE_EPOCH, "旧纪元进程的迟到更新被拒绝", status=410,
                    details={"received_epoch": epoch, "current_epoch": storage_epoch},
                )
            return self._ingest_locked(env, source=source)

    def _ingest_locked(self, env: Any, *, source: str) -> dict[str, Any]:
        # --- 结构 ---
        try:
            verifier.check_envelope(env)
        except verifier.VerifyError as ve:
            self._quarantine(ve.reason, ve.detail, source, getattr(env, "get", lambda *_: None)("segment_index"))
            raise ReplicatorError(ve.reason, ve.detail, status=422)

        index = env["segment_index"]
        digest = env["digest"]

        # 新批次（非重复）准入前先确认仍持有当前纪元。失主的在途提交必须
        # 稳定退出，绝不允许它推进内存投影——那正是“漏掉别人刚提交的中间
        # 批次、却继续发布后续批次内存结果”的缺陷根源。
        owner_epoch = self.epoch
        storage_epoch = self._storage_epoch()
        lost = self._ownership_lost or storage_epoch != owner_epoch

        # --- 重复批次：只能返回原结果（幂等优先于所有权判定）。
        #     失主重复重传别人已确认的批次不再被拒绝，但也不产生任何写入：
        #     内存落后于权威水位时先重建，保证返回的不是漏批截面。 ---
        existing = self.store.get_segment(index)
        if existing is not None:
            if existing["digest"] == digest:
                # 重复批次只能返回原结果：不产生任何写入，也不改变所有权状态。
                # 内存落后于权威水位时先重建，保证返回的不是漏批截面。
                if self.confirmed_index != len(self.segments):
                    self._rebuild_from_authoritative()
                return {
                    "outcome": "duplicate_ignored",
                    "segment_index": index,
                    "detail": "重复批次：分段正文与已确认分段一致，返回原结果",
                }
            # 同序号正文不同是数据分叉：失主也按隔离处理（不产生新写入）
            self._quarantine(
                BODY_CONFLICT,
                f"同序号 {index} 正文不同：已确认 {existing['digest'][:16]}…，"
                f"本次 {digest[:16]}…",
                source=source, segment_index=index, envelope_digest_value=digest,
            )
            raise ReplicatorError(
                BODY_CONFLICT, f"分段 {index} 同序号正文不同，已隔离", status=409,
                details={"segment_index": index,
                         "confirmed_digest": existing["digest"], "received_digest": digest},
            )

        if lost:
            self._demote_lost_owner(
                storage_epoch,
                detail=(f"分段提交被所有权围栏拒绝：存储纪元 {storage_epoch}"
                        f" ≠ 本实例纪元 {owner_epoch}，旧实例停止在途工作"),
                source=source,
            )
            raise ReplicatorError(
                OWNERSHIP_LOST,
                f"本实例已失去纪元 {owner_epoch} 的写入所有权"
                f"（当前纪元 {storage_epoch}），在途工作稳定退出",
                status=410,
                details={"lost_epoch": owner_epoch, "current_epoch": storage_epoch},
            )

        # --- 演练冻结期间收到“新”分段 ---
        drill = self.store.active_drill()
        if drill is not None:
            self._quarantine(
                ADVANCE_DURING_DRILL if drill["state"] == "VALIDATING" else "REPLICATION_FROZEN",
                f"演练 {drill['drill_id']}（{drill['state']}）冻结期间收到分段 {index}，已隔离",
                source=source, segment_index=index, envelope_digest_value=digest,
            )
            if drill["state"] == "VALIDATING":
                # 原子条件收口：若此刻 sweeper/取消/另一进程已抢先终态化，
                # 这里不会再落第二次终态与审计。
                self._finalize(
                    drill, "ABORTED", ADVANCE_DURING_DRILL,
                    f"验证尚未完成时分段 {index} 到达，锁定截面不再是受控截面",
                )
            raise ReplicatorError(
                ADVANCE_DURING_DRILL,
                "演练冻结期间不接受新分段", status=409,
                details={"drill_id": drill["drill_id"]},
            )

        # --- 序号必须正好是下一段（错序/缺失隔离）。权威水位以存储为准：
        #     内存可能落后于已被别的进程确认的批次，此时先重建再判缺口，
        #     异常缺口（仍缺中段）依旧阻挡前进。 ---
        if self.confirmed_index != len(self.segments):
            self._rebuild_from_authoritative()
        confirmed_index = self.confirmed_index
        expected_index = confirmed_index + 1
        if index != expected_index:
            reason = verifier.SEGMENT_INDEX_MISMATCH if index > expected_index else BODY_CONFLICT
            detail = (f"分段错序：期望 {expected_index}，收到 {index}，"
                      f"异常缺口未补齐前禁止前进"
                      if index > expected_index
                      else f"收到早于确认边界的旧分段 {index}（边界 {confirmed_index}）")
            self._quarantine(reason, detail, source, index, digest)
            raise ReplicatorError(reason, detail, status=409)

        # --- 本地自校验：大小/序号连续/前段摘要/信封摘要/事件链/折叠/守恒 ---
        # 先查自身：自身不一致（被篡改）按具体断裂原因隔离，而不是笼统的分叉。
        # 边界值此刻重新取自存储权威行，与随后的提交 CAS 使用同一前置条件。
        meta = self.store.meta()
        try:
            verifier.check_index_and_size(env, expected_index, self.segment_size)
            verifier.check_seq_contiguous(env, meta["confirmed_seq"])
            verifier.check_chain_link(env, meta["last_digest"])
            new_event_hash = verifier.check_event_hashes(env, meta["last_event_hash"])
        except verifier.VerifyError as ve:
            self._quarantine(ve.reason, ve.detail, source, index, digest, extra=ve.extra)
            raise ReplicatorError(ve.reason, ve.detail, status=422, details=ve.extra)

        # --- 再与主站当前权威摘要比对：本地自洽但与主站不同 → 同序号正文分叉 ---
        primary_digest = self._authoritative_digest(index)
        if primary_digest is not None and primary_digest != digest:
            self._quarantine(
                BODY_CONFLICT,
                f"分段 {index} 摘要与主站当前权威摘要不符："
                f"本地 {digest[:16]}…，主站 {primary_digest[:16]}…",
                source=source, segment_index=index, envelope_digest_value=digest,
            )
            raise ReplicatorError(
                BODY_CONFLICT,
                f"分段 {index} 与主站同序号正文不同（分叉），已隔离", status=409,
                details={"segment_index": index,
                         "primary_digest": primary_digest, "received_digest": digest},
            )

        # --- 语义校验：折叠进副本投影，检查守恒与回执 ---
        try:
            trial = verifier.clone_projection(self.projection)
            verifier.fold_segment(trial, env)
            verifier.audit_projection(trial)
            verifier.check_receipts_in_segment(env)
        except verifier.VerifyError as ve:
            self._quarantine(
                ve.reason, ve.detail, source, index, digest, extra=ve.extra
            )
            raise ReplicatorError(ve.reason, ve.detail, status=422, details=ve.extra)

        # --- 所有权围栏提交：存储层在同一事务内核对纪元与连续水位。
        #     即使校验全部做完后才与接替实例相撞，失主提交也会被稳定拒绝。 ---
        committed = self.store.commit_segment_if_owner(env, new_event_hash, owner_epoch)
        outcome = committed["outcome"]

        if outcome == self.store.COMMIT_OWNERSHIP_LOST:
            current_epoch = committed["current_epoch"]
            self._demote_lost_owner(
                current_epoch,
                detail=(f"分段 {index} 提交时发现纪元已被接替实例接管"
                        f"（{owner_epoch} → {current_epoch}），本实例在途工作退出"),
                source=source,
            )
            raise ReplicatorError(
                OWNERSHIP_LOST,
                f"提交时分段 {index} 的写入所有权已属于纪元 {current_epoch}",
                status=410,
                details={"lost_epoch": owner_epoch, "current_epoch": current_epoch},
            )

        if outcome == self.store.COMMIT_DUPLICATE:
            # 提交窗口内被并行进程抢先确认了同一批次（正文一致）：
            # 重复批次只返回原结果，并先重建到权威水位。
            self._rebuild_from_authoritative()
            return {
                "outcome": "duplicate_ignored",
                "segment_index": index,
                "detail": "重复批次：已由当前纪元确认且正文一致，返回原结果",
            }

        if outcome == self.store.COMMIT_BODY_CONFLICT:
            confirmed_digest = committed["confirmed_digest"]
            self._rebuild_from_authoritative()
            self._quarantine(
                BODY_CONFLICT,
                f"提交时同序号 {index} 已被确认且正文不同："
                f"已确认 {str(confirmed_digest)[:16]}…，本次 {digest[:16]}…",
                source=source, segment_index=index, envelope_digest_value=digest,
            )
            raise ReplicatorError(
                BODY_CONFLICT, f"分段 {index} 同序号正文不同，已隔离", status=409,
                details={"segment_index": index,
                         "confirmed_digest": confirmed_digest, "received_digest": digest},
            )

        if outcome == self.store.COMMIT_ADVANCED:
            # 提交前的瞬间别人补齐了缺口并把权威水位推过了本序号：
            # 先按权威水位重建（不漏批），再按既有结果/分叉/缺口分类。
            self._rebuild_from_authoritative()
            advanced_existing = self.store.get_segment(index)
            if advanced_existing is not None:
                if advanced_existing["digest"] == digest:
                    return {
                        "outcome": "duplicate_ignored",
                        "segment_index": index,
                        "detail": "重复批次：缺口已由当前纪元补齐且正文一致，返回原结果",
                    }
                self._quarantine(
                    BODY_CONFLICT,
                    f"权威水位推进后同序号 {index} 正文不同，已隔离",
                    source=source, segment_index=index, envelope_digest_value=digest,
                )
                raise ReplicatorError(
                    BODY_CONFLICT, f"分段 {index} 与权威水位同序号正文不同", status=409,
                    details={"segment_index": index,
                             "confirmed_digest": advanced_existing["digest"],
                             "received_digest": digest},
                )
            # 水位越过本序号却查不到本序号分段：链路异常，隔离阻挡前进
            self._quarantine(
                verifier.SEGMENT_INDEX_MISMATCH,
                f"权威水位已推进到 {committed['confirmed_index']} 但分段 {index} 缺失",
                source=source, segment_index=index, envelope_digest_value=digest,
            )
            raise ReplicatorError(
                verifier.SEGMENT_INDEX_MISMATCH,
                f"权威水位异常：分段 {index} 缺失", status=409,
            )

        # --- 发布前最后一次所有权确认：提交后、发布内存结果前若已失主，
        #     不发布本进程的在途内存结果，改为从权威水位重建。 ---
        final_epoch = self._storage_epoch()
        if final_epoch != owner_epoch:
            self._rebuild_from_authoritative()
            self._demote_lost_owner(
                final_epoch,
                detail=(f"分段 {index} 落盘后发布前纪元被接管"
                        f"（{owner_epoch} → {final_epoch}），放弃在途内存发布"),
                source=source,
            )
            raise ReplicatorError(
                OWNERSHIP_LOST,
                f"发布前已失去纪元 {owner_epoch} 的写入所有权", status=410,
                details={"lost_epoch": owner_epoch, "current_epoch": final_epoch},
            )

        # --- 提交与发布都确认仍持有当前纪元：原子替换内存投影 ---
        self.segments.append(env)
        self.projection = trial
        self._published_digest = verifier.state_digest(trial)
        self._notify_watermark()  # 连续水位前进：唤醒等待中的只读请求
        self.store.resolve_open_for_index(index, "健康分段已确认，此前隔离消除")
        self._lag_quarantined = False
        self.store.audit("segment_confirmed", {
            "segment_index": index,
            "seq_end": env["seq_end"],
            "digest": digest,
            "source": source,
            "epoch": owner_epoch,
            "state_digest": self._published_digest,
        })
        return {
            "outcome": "confirmed",
            "segment_index": index,
            "seq_end": env["seq_end"],
            "digest": digest,
            "epoch": owner_epoch,
            "state_digest": self._published_digest,
        }

    def _authoritative_digest(self, index: int) -> str | None:
        """查询主站当前该序号的权威分段摘要（网络失败不阻塞本地链校验）。"""
        try:
            status = self._http_json("/replica/status")
            for s in status.get("segments", []):
                if s["segment_index"] == index:
                    return s["digest"]
        except Exception:
            return None
        return None

    def _quarantine(
        self, reason: str, detail: str, source: str,
        segment_index: int | None = None,
        envelope_digest_value: str | None = None,
        epoch: int | None = None,
        extra: dict[str, Any] | None = None,
    ) -> int:
        qid = self.store.quarantine(
            reason, detail, source,
            segment_index=segment_index,
            envelope_digest_value=envelope_digest_value,
            epoch=epoch if epoch is not None else self.epoch,
        )
        self.store.audit("segment_quarantined", {
            "quarantine_id": qid, "reason": reason, "detail": detail,
            "source": source, "segment_index": segment_index, **(extra or {}),
        })
        self.last_error = f"{reason}: {detail}"
        return qid

    # ------------------------------------------------------------------
    # 只读查询（永远只暴露完整确认截面）
    # ------------------------------------------------------------------

    @property
    def confirmed_index(self) -> int:
        return int(self.store.meta()["confirmed_index"])

    @property
    def confirmed_seq(self) -> int:
        return int(self.store.meta()["confirmed_seq"])

    def _serve_authoritative_if_lost(self) -> None:
        """失主实例的读路径：每次从存储权威水位重建，查询永不滞后于磁盘。

        失主进程已停摆、不再是热路径；接管实例可能继续推进水位，因此读前
        总是丢弃本地在途内存、完整重放已确认分段，保证查询结果与磁盘重算
        值严格一致，而不是停在失主那一刻的旧快照。
        """
        if self._ownership_lost:
            self._rebuild_from_authoritative()

    def current_state(self) -> dict[str, Any]:
        with self._lock:
            self._serve_authoritative_if_lost()
            state = self.projection.to_state()
            state["server_time"] = None  # 灾备截面不带实时时钟，避免误读
            state["replica"] = {
                "confirmed_index": self.confirmed_index,
                "confirmed_seq": self.confirmed_seq,
                "state_digest": self._published_digest,
                "epoch": self.epoch,
                "authoritative_epoch": self._storage_epoch(),
                "ownership_lost": self._ownership_lost,
            }
            return state

    def commands_view(self, limit: int = 200) -> dict[str, Any]:
        with self._lock:
            self._serve_authoritative_if_lost()
            receipts: list[dict[str, Any]] = []
            for env in self.segments:
                receipts.extend(env.get("receipts", []))
            receipts.sort(key=lambda r: r["seq"], reverse=True)
            return {
                "confirmed_index": self.confirmed_index,
                "count": len(receipts),
                "commands": receipts[:limit],
            }

    def receipt(self, command_id: str) -> dict[str, Any] | None:
        with self._lock:
            self._serve_authoritative_if_lost()
            for env in reversed(self.segments):
                for r in env.get("receipts", []):
                    if r["command_id"] == command_id:
                        return r
        return None

    def plans_view(self) -> dict[str, Any]:
        with self._lock:
            self._serve_authoritative_if_lost()
            return {
                "confirmed_index": self.confirmed_index,
                "plans": [
                    {"id": pid, **pl}
                    for pid, pl in sorted(self.projection.plans.items())
                ],
            }

    # ------------------------------------------------------------------
    # 水位等待查询（最低连续水位 + 最长等待 + 请求标识幂等）
    # ------------------------------------------------------------------
    #
    # 只读调用方在状态 / 草案 / 命令结果查询上声明 min_watermark 与 wait_ms：
    # 当前权威连续水位未到时请求挂起，水位真正到达后返回**满足条件的同一
    # 原子截面**；超时返回当前权威水位与可再次请求的信息，绝不把较旧数据
    # 伪装成满足条件。等待期间发生接管 / 缺口隔离 / 暂停 / 重启时，等待者
    # 始终按**存储中的权威水位**重新判定（周期性回读 + 条件变量唤醒），
    # 只有连续水位真正达到要求才成功。request_id 是幂等键：等待参数以首次
    # 登记为准，终态结果落盘，同标识再请求返回原结果。

    def _authoritative_watermark(self) -> dict[str, Any]:
        """存储中的权威连续水位（等待判定的唯一依据，而非内存投影）。"""
        meta = self.store.meta()
        confirmed = int(meta["confirmed_index"])
        stored = sorted(self.store.segment_digests())
        return {
            "confirmed_index": confirmed,
            "confirmed_seq": int(meta["confirmed_seq"]),
            "contiguous": stored == list(range(1, confirmed + 1)),
            "paused": bool(meta["paused"]),
            "epoch": self.epoch,
            "authoritative_epoch": int(meta["epoch"]),
            "ownership_lost": self._ownership_lost,
        }

    @staticmethod
    def _wait_view_path(view: str, command_id: str | None) -> str:
        if view == "state":
            return "/api/state"
        if view == "plans":
            return "/api/plans"
        if view == "commands":
            return "/api/commands"
        return f"/api/commands/{command_id}"

    def _snapshot_for_view(self, view: str, command_id: str | None) -> dict[str, Any]:
        """在满足水位的锁内取同一原子截面（调用方必须持有 self._lock）。"""
        if view == "state":
            return self.current_state()
        if view == "plans":
            return self.plans_view()
        if view == "commands":
            return self.commands_view()
        receipt = self.receipt(command_id or "")
        if receipt is None:
            raise ReplicatorError(
                "NOT_FOUND", f"已确认截面内无此命令: {command_id}", status=404)
        return receipt

    def _wait_timeout_body(
        self, rec: dict[str, Any], wm: dict[str, Any], waited_ms: int,
    ) -> dict[str, Any]:
        """超时终态：只回权威水位与重试信息，绝不夹带较旧截面冒充满足条件。"""
        path = self._wait_view_path(rec["view"], rec.get("command_id"))
        query = (f"min_watermark={rec['min_watermark']}"
                 f"&wait_ms={rec['wait_ms']}&request_id={rec['request_id']}")
        return {
            "error": WAIT_TIMEOUT,
            "message": f"等待连续水位 {rec['min_watermark']} 超时：当前权威连续水位"
                       f" {wm['confirmed_index']}"
                       f"{'' if wm['contiguous'] else '（水位存在缺口）'}",
            "details": {
                "request_id": rec["request_id"],
                "view": rec["view"],
                "min_watermark": rec["min_watermark"],
                "wait_ms": rec["wait_ms"],
                "waited_ms": waited_ms,
                "authoritative_watermark": wm["confirmed_index"],
                "watermark_contiguous": wm["contiguous"],
                "paused": wm["paused"],
                "ownership_lost": wm["ownership_lost"],
                "idempotent_replay": False,
                "retry": {
                    "method": "GET",
                    "url": f"{path}?{query}",
                    "note": "同一 request_id 再请求返回本次原结果；"
                            "换用新 request_id 可从当前权威水位继续等待",
                },
            },
        }

    def wait_for_watermark(
        self,
        view: str,
        min_watermark: int,
        wait_ms: int,
        request_id: str | None = None,
        command_id: str | None = None,
    ) -> tuple[int, dict[str, Any]]:
        """按调用方声明的最低连续水位等待，返回 ``(HTTP 状态, 响应体)``。

        - 水位已满足：立即返回当前原子截面（``wait.satisfied``，不登记）；
        - 水位未到：挂起至水位到达或截止时刻，等待期间只阻塞本 HTTP 线程；
        - 超时：408 + 当前权威水位 + 重试信息（不返回任何截面数据）；
        - ``request_id`` 相同：返回首次登记/收口的原结果（幂等重放）。
        """
        if min_watermark < 0:
            raise ReplicatorError("BAD_WAIT_PARAMS",
                                  "min_watermark 必须是非负整数", status=400)
        if wait_ms < 0:
            raise ReplicatorError("BAD_WAIT_PARAMS",
                                  "wait_ms 必须是非负整数", status=400)
        clamped = min(wait_ms, MAX_WAIT_MS)
        started = time.time()

        # --- 幂等：同标识请求只认首次登记与首次终态 ---
        rec: dict[str, Any] | None = None
        if request_id is not None:
            existing = self.store.wait_get(request_id)
            if existing is not None:
                if (existing["view"] != view
                        or existing["min_watermark"] != min_watermark
                        or (existing.get("command_id") or None) != (command_id or None)):
                    raise ReplicatorError(
                        WAIT_REQUEST_CONFLICT,
                        f"请求标识 {request_id} 已用于另一组等待参数"
                        f"（{existing['view']} / 水位 {existing['min_watermark']}），"
                        "同一标识再请求只能返回原结果",
                        status=409,
                        details={"request_id": request_id,
                                 "first_view": existing["view"],
                                 "first_min_watermark": existing["min_watermark"]},
                    )
                if existing["outcome"] is not None:
                    # 已收口：直接返回原结果，绝不重新等待或重算
                    body = dict(existing["result"])
                    marker = body.get("wait") or body.get("details") or {}
                    marker["idempotent_replay"] = True
                    return int(existing["http_status"]), body
                rec = existing  # 待决请求：跟随首次登记的截止时刻继续等待
            else:
                rec, _ = self.store.wait_begin({
                    "request_id": request_id,
                    "view": view,
                    "command_id": command_id,
                    "min_watermark": min_watermark,
                    "wait_ms": clamped,
                    "deadline_at": started + clamped / 1000.0,
                    "created_at": started,
                })
                if (rec["view"] != view
                        or rec["min_watermark"] != min_watermark
                        or (rec.get("command_id") or None) != (command_id or None)):
                    # 并发登记撞键：以首次登记为准
                    raise ReplicatorError(
                        WAIT_REQUEST_CONFLICT,
                        f"请求标识 {request_id} 已用于另一组等待参数",
                        status=409,
                    )

        with self._watermark_cond:
            audited = False
            while True:
                wm = self._authoritative_watermark()
                if wm["contiguous"] and wm["confirmed_index"] >= min_watermark:
                    # 跟随权威存储：内存落后时先重建，再取同一原子截面
                    if len(self.segments) != wm["confirmed_index"]:
                        self._rebuild_from_authoritative()
                    try:
                        body = self._snapshot_for_view(view, command_id)
                        status = 200
                    except ReplicatorError as e:
                        if rec is None:
                            raise  # 未登记：按普通查询的错误语义返回
                        # 水位已真正到达：此刻的查询结果就是终态答案
                        # （如命令不存在的 404），作为本次等待的原结果收口
                        body = {"error": e.reason, "message": str(e),
                                "details": e.details}
                        status = e.status
                    body["wait"] = {
                        "request_id": rec["request_id"] if rec else request_id,
                        "min_watermark": min_watermark,
                        "satisfied": True,
                        "waited_ms": int((time.time() - started) * 1000),
                        "watermark": wm["confirmed_index"],
                        "watermark_contiguous": True,
                        "idempotent_replay": False,
                    }
                    if rec is None:
                        return status, body
                    return self._finalize_wait(rec, "satisfied", status, body,
                                               wm["confirmed_index"])
                # 水位未到：需要挂起的请求都登记一行（无标识则自动生成），
                # 让等待中的最低水位/剩余时间可观测、可跨重启恢复
                if rec is None:
                    request_id = "wait-" + uuid.uuid4().hex[:12]
                    rec, _ = self.store.wait_begin({
                        "request_id": request_id,
                        "view": view,
                        "command_id": command_id,
                        "min_watermark": min_watermark,
                        "wait_ms": clamped,
                        "deadline_at": started + clamped / 1000.0,
                        "created_at": started,
                    })
                if not audited:
                    self.store.audit("wait_started", {
                        "request_id": rec["request_id"], "view": view,
                        "min_watermark": min_watermark, "wait_ms": clamped,
                        "deadline_at": rec["deadline_at"],
                    })
                    audited = True
                remaining = rec["deadline_at"] - time.time()
                if remaining <= 0:
                    waited_ms = int((time.time() - started) * 1000)
                    body = self._wait_timeout_body(rec, wm, waited_ms)
                    return self._finalize_wait(rec, "timeout", 408, body,
                                               wm["confirmed_index"])
                # 周期性回读权威存储：接管实例在另一进程推进水位时，
                # 本进程等待者靠这个节拍跟随恢复（notify 只是加速器）
                self._watermark_cond.wait(
                    timeout=min(remaining, WAIT_RECHECK_SECONDS))

    def _finalize_wait(
        self, rec: dict[str, Any], outcome: str, http_status: int,
        body: dict[str, Any], watermark: int,
    ) -> tuple[int, dict[str, Any]]:
        """收口等待请求：唯一赢家落盘，输家返回已落盘的原结果。"""
        if self.store.wait_finish_if_pending(
                rec["request_id"], outcome, http_status, body, watermark):
            self.store.audit("wait_finished", {
                "request_id": rec["request_id"], "view": rec["view"],
                "outcome": outcome, "min_watermark": rec["min_watermark"],
                "watermark_at_finish": watermark,
            })
            return http_status, body
        stored = self.store.wait_get(rec["request_id"])
        return int(stored["http_status"]), dict(stored["result"])

    def sweep_expired_waits(self, now: float | None = None) -> list[str]:
        """主动收口截止时刻已到的待决等待请求（不等调用方再请求）。

        与演练到期收口同理：即使调用方再也不来，等待记录也会自行收口；
        收口时连续水位若已真正达到要求则按满足收口（跟随权威存储恢复），
        否则按当前权威水位收口为超时终态；同标识再请求返回该原结果。
        """
        now = now if now is not None else time.time()
        expired: list[str] = []
        with self._watermark_cond:
            for rec in self.store.list_pending_waits():
                if rec["deadline_at"] > now:
                    continue
                wm = self._authoritative_watermark()
                if wm["contiguous"] and wm["confirmed_index"] >= rec["min_watermark"]:
                    if len(self.segments) != wm["confirmed_index"]:
                        self._rebuild_from_authoritative()
                    try:
                        body = self._snapshot_for_view(
                            rec["view"], rec.get("command_id"))
                        status = 200
                    except ReplicatorError as e:
                        # 水位已真正到达：查询结果（如 404）就是终态答案
                        body = {"error": e.reason, "message": str(e),
                                "details": e.details}
                        status = e.status
                    body["wait"] = {
                        "request_id": rec["request_id"],
                        "min_watermark": rec["min_watermark"],
                        "satisfied": True,
                        "waited_ms": int((now - rec["created_at"]) * 1000),
                        "watermark": wm["confirmed_index"],
                        "watermark_contiguous": True,
                        "idempotent_replay": False,
                    }
                    if self.store.wait_finish_if_pending(
                            rec["request_id"], "satisfied", status, body,
                            wm["confirmed_index"], now=now):
                        self.store.audit("wait_finished", {
                            "request_id": rec["request_id"],
                            "view": rec["view"], "outcome": "satisfied",
                            "min_watermark": rec["min_watermark"],
                            "watermark_at_finish": wm["confirmed_index"],
                            "swept": True,
                        })
                        expired.append(rec["request_id"])
                    continue
                waited_ms = int((now - rec["created_at"]) * 1000)
                body = self._wait_timeout_body(rec, wm, waited_ms)
                if self.store.wait_finish_if_pending(
                        rec["request_id"], "timeout", 408, body,
                        wm["confirmed_index"], now=now):
                    self.store.audit("wait_finished", {
                        "request_id": rec["request_id"], "view": rec["view"],
                        "outcome": "timeout",
                        "min_watermark": rec["min_watermark"],
                        "watermark_at_finish": wm["confirmed_index"],
                        "swept": True,
                    })
                    expired.append(rec["request_id"])
        return expired

    def list_waits(self) -> dict[str, Any]:
        """运维面视图：等待中的最低水位/剩余时间 + 最近终态结果。"""
        now = time.time()
        waits = self.store.list_waits()
        for w in waits:
            w["remaining_ms"] = (
                max(0, int((w["deadline_at"] - now) * 1000))
                if w["outcome"] is None else 0
            )
        return {
            "pending_count": sum(1 for w in waits if w["outcome"] is None),
            "waits": waits,
        }

    # ------------------------------------------------------------------
    # 受控切换演练
    # ------------------------------------------------------------------

    def create_drill(
        self,
        drill_id: str | None,
        *,
        max_lag_segments: int | None = None,
        term_seconds: float = 300.0,
        validation_delay_ms: int = 0,
    ) -> dict[str, Any]:
        with self._lock:
            if self._ownership_lost or self._storage_epoch() != self.epoch:
                raise ReplicatorError(
                    OWNERSHIP_LOST,
                    "本实例已失去写入所有权，受控切换演练由当前纪元实例发起",
                    status=410,
                    details={"lost_epoch": self.epoch,
                             "current_epoch": self._storage_epoch()},
                )
            # 同一演练再次请求 → 返回原结果（幂等）
            if drill_id:
                existing = self.store.get_drill(drill_id)
                if existing is not None:
                    existing["idempotent_replay"] = True
                    return existing

            active = self.store.active_drill()
            if active is not None:
                raise ReplicatorError(
                    ALREADY_ACTIVE_DRILL,
                    f"已有进行中的演练 {active['drill_id']}（{active['state']}），"
                    "请先取消或等待其到期",
                    status=409,
                )
            if self.store.meta()["paused"]:
                raise ReplicatorError(
                    REPLICATION_PAUSED,
                    "复制当前处于人工暂停状态，不能创建演练",
                    status=409,
                )

            max_lag = (
                max_lag_segments if max_lag_segments is not None
                else self.max_lag_segments
            )

            # 锁定前先看主站：落后过多则拒绝（不能对陈旧截面做切换）
            try:
                status = self._http_json("/replica/status")
            except Exception as exc:
                raise ReplicatorError(
                    PRIMARY_UNAVAILABLE,
                    f"锁定截面时无法读取主站状态: {exc}", status=503,
                )
            lag = status["sealed_index"] - self.confirmed_index
            if lag > max_lag:
                self.store.audit("drill_rejected", {
                    "reason": LAG_EXCEEDED_AT_LOCK,
                    "lag_segments": lag, "max_lag_segments": max_lag,
                })
                raise ReplicatorError(
                    LAG_EXCEEDED_AT_LOCK,
                    f"当前落后主站 {lag} 个分段，超过演练允许的 {max_lag}；"
                    "拒绝以陈旧截面切换",
                    status=409,
                    details={"lag_segments": lag, "max_lag_segments": max_lag},
                )

            drill_id = drill_id or f"DR-{uuid.uuid4().hex[:12]}"
            now = time.time()
            locked = {
                "drill_id": drill_id,
                "state": "VALIDATING",
                "locked_index": self.confirmed_index,
                "locked_digest": self.store.meta()["last_digest"],
                "locked_event_hash": self.store.meta()["last_event_hash"],
                "term_token": None,
                "term_expires_at": None,
                "max_lag_segments": max_lag,
                "report": {},
                "created_at": now,
                "updated_at": now,
                "finished_at": None,
                "fail_reason": None,
            }
            # 先持久化 VALIDATING：此刻起复制立即冻结（_ingest_locked 可见）
            self.store.upsert_drill(locked)
            self.store.audit("drill_created", {
                "drill_id": drill_id,
                "locked_index": locked["locked_index"],
                "sealed_index_at_lock": status["sealed_index"],
                "lag_segments": lag,
            })

            if validation_delay_ms:
                # 确定性注入：验证窗口内主站若继续写入，将稳定触发
                # ADVANCE_DURING_DRILL（用于演练演示，默认 0）
                time.sleep(validation_delay_ms / 1000.0)

            return self._validate_drill_locked(locked, status["sealed_index"], term_seconds)

    def _validate_drill_locked(
        self, drill: dict[str, Any], sealed_index_at_lock: int, term_seconds: float
    ) -> dict[str, Any]:
        """对锁定截面做全量验证。任何失败 → ABORTED（截面不受污染）。"""
        checks: list[dict[str, Any]] = []
        try:
            # 1) 从磁盘上的已确认分段完整重放（不使用线上投影）
            stored = self.store.load_segments()
            rebuilt = verifier.replay_all(stored)

            # 2) 分段链与事件链统计
            total_events = sum(len(s["events"]) for s in stored)
            checks.append({
                "name": "segment_hash_chain",
                "ok": True,
                "detail": f"{len(stored)} 个分段的 prev_digest/digest 链完整"
                          f"（{total_events} 条事件的 event_hash 链同时重算通过）",
            })

            # 3) 守恒审计（非负/全局守恒/层级/租约）
            audit = verifier.audit_projection(rebuilt)
            checks.extend(audit["checks"])

            # 4) 重放等价：磁盘重放摘要 == 当前线上确认投影摘要
            replay_digest = verifier.state_digest(rebuilt)
            replay_ok = replay_digest == self._published_digest
            checks.append({
                "name": "replay_equivalence",
                "ok": replay_ok,
                "detail": f"磁盘重放摘要 {replay_digest[:16]}… 与确认截面一致"
                if replay_ok else "磁盘重放与确认投影摘要不一致",
                "digest": replay_digest,
            })

            # 5) 命令结果（回执完整性 + 结果与事件推导一致）
            receipt_check = verifier.full_receipt_check(stored)
            checks.append(receipt_check)

            if not all(c["ok"] for c in checks):
                raise verifier.VerifyError(
                    VALIDATION_FAILED,
                    "存在未通过的验证项",
                    {"failed": [c["name"] for c in checks if not c["ok"]]},
                )

            # 6) 验证期间主站不得又密封出新分段（截面必须定格在锁定点）
            end_status = self._http_json("/replica/status")
            if end_status["sealed_index"] != sealed_index_at_lock:
                raise verifier.VerifyError(
                    ADVANCE_DURING_DRILL,
                    f"验证期间主站又密封了新分段"
                    f"（{sealed_index_at_lock} → {end_status['sealed_index']}）",
                    {"sealed_at_lock": sealed_index_at_lock,
                     "sealed_at_verify": end_status["sealed_index"]},
                )

        except verifier.VerifyError as ve:
            drill["report"] = self._build_report(drill, checks, ok=False, fail_reason=ve.reason)
            self._finalize(drill, "ABORTED", ve.reason, ve.detail)
            raise ReplicatorError(
                ve.reason, f"演练 {drill['drill_id']} 验证失败：{ve.detail}",
                status=409, details={"report": drill["report"]},
            )
        except ReplicatorError:
            raise
        except Exception as exc:
            drill["report"] = self._build_report(drill, checks, ok=False, fail_reason=PRIMARY_UNAVAILABLE)
            self._finalize(drill, "ABORTED", PRIMARY_UNAVAILABLE, str(exc))
            raise ReplicatorError(PRIMARY_UNAVAILABLE, str(exc), status=503)

        # --- 全部通过：发放带任期的只读查询地址 ---
        now = time.time()
        token = new_token()
        term_expires_at = now + term_seconds
        frozen_state = rebuilt.to_state()
        frozen_state["server_time"] = None
        report = self._build_report(drill, checks, ok=True, extra={
            "term_token": token,
            "term_expires_at": term_expires_at,
            "frozen_digest": replay_digest,
            "surface": {
                "global_capacity": audit["global_capacity"],
                "total_available": audit["total_available"],
                "total_consumed": audit["total_consumed"],
                "node_count": len(rebuilt.nodes),
                "lease_count": len(rebuilt.leases),
                "plan_count": len(rebuilt.plans),
                "command_count": receipt_check["checked_commands"],
                "surface_state": frozen_state,
                "commands": self._commands_upto(drill['locked_index']),
            },
        })
        # 受保护推进：只有行仍 VALIDATING 才能 ISSUED。若此刻已被别的路径
        # 终态化（并发收口/另一进程启动作废），放弃发放并返回权威终态。
        if not self.store.issue_drill_if_validating(
            drill["drill_id"], token, term_expires_at, report, now=now
        ):
            final = self.store.get_drill(drill["drill_id"])
            raise ReplicatorError(
                final["fail_reason"] or VALIDATION_FAILED,
                f"演练 {drill['drill_id']} 在验证完成前已被收口（{final['state']}）",
                status=409, details={"report": final.get("report")},
            )
        drill.update({
            "state": "ISSUED",
            "term_token": token,
            "term_expires_at": term_expires_at,
            "updated_at": now,
            "report": report,
        })
        self.store.audit("drill_issued", {
            "drill_id": drill["drill_id"],
            "locked_index": drill["locked_index"],
            "term_token": token,
            "term_expires_at": term_expires_at,
        })
        return drill

    def _commands_upto(self, index: int) -> list[dict[str, Any]]:
        out: list[dict[str, Any]] = []
        for env in self.segments[:index]:
            out.extend(env.get("receipts", []))
        out.sort(key=lambda r: r["seq"])
        return out

    def _build_report(
        self, drill: dict[str, Any], checks: list[dict[str, Any]], *,
        ok: bool, fail_reason: str | None = None, extra: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        report = {
            "drill_id": drill["drill_id"],
            "ok": ok,
            "validated_at": time.time(),
            "locked_index": drill["locked_index"],
            "locked_digest": drill["locked_digest"],
            "checks": [{k: v for k, v in c.items() if k != "surface"} for c in checks],
            "all_passed": ok,
        }
        if fail_reason:
            report["fail_reason"] = fail_reason
        if extra:
            report.update(extra)
        return report

    def cancel_drill(self, drill_id: str) -> dict[str, Any]:
        with self._lock:
            drill = self.store.get_drill(drill_id)
            if drill is None:
                raise ReplicatorError("NOT_FOUND", f"演练不存在: {drill_id}", status=404)
            if drill["state"] in ("CANCELLED", "ABORTED", "EXPIRED"):
                drill["idempotent_replay"] = True
                return drill
            self._finalize(drill, "CANCELLED", "CANCELLED", "操作员取消演练")
            # 若恰与定时到期相撞并由对方胜出，这里返回权威终态，
            # 绝不把 EXPIRED 覆盖成 CANCELLED 或再写一条审计。
            final = self.store.get_drill(drill_id)
            final["idempotent_replay"] = final["state"] != "CANCELLED"
            return final

    def get_drill(self, drill_id: str) -> dict[str, Any]:
        d = self.store.get_drill(drill_id)
        if d is None:
            raise ReplicatorError("NOT_FOUND", f"演练不存在: {drill_id}", status=404)
        return d

    def list_drills(self) -> list[dict[str, Any]]:
        return self.store.list_drills()

    def serve_term(self, token: str) -> dict[str, Any]:
        """带任期的只读查询：仅 ISSUED 且未到期的地址可用。

        读取路径本身不落终态（保证“并发读取相撞”不会制造额外终态/审计）；
        若读到一条已过截止时刻却尚未被 sweeper 收口的任期，则触发一次
        原子条件收口，收口者同样只有一个。
        """
        with self._lock:
            drill = self.store.drill_by_token(token)
            if drill is None or drill["state"] != "ISSUED":
                raise ReplicatorError(TERM_EXPIRED, "任期地址无效（演练不存在/已取消/已到期）",
                                      status=410)
            now = time.time()
            if drill["term_expires_at"] and now >= drill["term_expires_at"]:
                self._expire_if_due(drill, now=now)
                raise ReplicatorError(TERM_EXPIRED, "任期地址已到期", status=410)
            surface = dict(drill["report"].get("surface", {}))
            # 兼容旧版本持久化报告：冻结投影旧键名为 state
            frozen = surface.pop("surface_state", surface.pop("state", {}))
            return {
                **surface,
                "drill_id": drill["drill_id"],
                "state": drill["state"],
                "locked_index": drill["locked_index"],
                "frozen_digest": drill["report"].get("frozen_digest"),
                "term_expires_at": drill["term_expires_at"],
                "seconds_remaining": max(0, int(drill["term_expires_at"] - time.time())),
                "surface_state": frozen,
            }
    # ------------------------------------------------------------------
    # 运维操作 / 状态
    # ------------------------------------------------------------------

    def set_paused(self, paused: bool) -> dict[str, Any]:
        with self._lock:
            if self._ownership_lost:
                raise ReplicatorError(
                    OWNERSHIP_LOST,
                    "本实例已失去写入所有权，暂停/恢复操作由当前纪元实例负责",
                    status=410,
                    details={"lost_epoch": self.epoch,
                             "current_epoch": self._storage_epoch()},
                )
            self.store.set_paused(paused)
            self.store.audit("replication_paused" if paused else "replication_resumed",
                             {"paused": paused, "epoch": self.epoch})
            return {"paused": paused, "epoch": self.epoch}

    def status(self) -> dict[str, Any]:
        with self._lock:
            meta = self.store.meta()
            storage_epoch = int(meta["epoch"])
            lag_events = max(0, self.primary_tip_seq - meta["confirmed_seq"])
            lag_segments = max(0, self.primary_sealed_index - meta["confirmed_index"])
            drill = self.store.active_drill()
            open_q = self.store.list_quarantined()
            # 连续水位：已确认分段序号必须恰好为 1..confirmed_index 无缺口
            stored_indexes = sorted(self.store.segment_digests())
            watermark_contiguous = stored_indexes == list(range(1, meta["confirmed_index"] + 1))
            epoch_bounds = self.store.segment_epochs()
            takeover_epochs = sorted({e for e in epoch_bounds.values() if e is not None})
            pending_waits = self.store.list_pending_waits()
            now = time.time()
            return {
                "replication": {
                    "running": not self._stop.is_set(),
                    "paused": bool(meta["paused"]),
                    "epoch": self.epoch,
                    "authoritative_epoch": storage_epoch,
                    "ownership_lost": self._ownership_lost,
                    "ownership_lost_at": self.ownership_lost_at,
                    "takeover_epochs": takeover_epochs,
                    "segment_epochs": epoch_bounds,
                    "watermark_contiguous": watermark_contiguous,
                    "segment_size": self.segment_size,
                    "confirmed_index": meta["confirmed_index"],
                    "confirmed_seq": meta["confirmed_seq"],
                    "last_digest": meta["last_digest"],
                    "state_digest": self._published_digest,
                    "primary_url": self.primary_url,
                    "primary_tip_seq": self.primary_tip_seq,
                    "primary_sealed_index": self.primary_sealed_index,
                    "primary_status_at": self.primary_status_at,
                    "last_pull_at": self.last_pull_at,
                    "lag_events": lag_events,
                    "lag_segments": lag_segments,
                    "max_lag_segments": self.max_lag_segments,
                    "lag_over_limit": lag_segments > self.max_lag_segments,
                    "frozen_by_drill": drill["drill_id"] if drill else None,
                    "last_error": self.last_error,
                },
                "drill": {
                    "active": drill["drill_id"] if drill else None,
                    "state": drill["state"] if drill else None,
                },
                "waits": {
                    "pending_count": len(pending_waits),
                    "pending": [
                        {"request_id": w["request_id"], "view": w["view"],
                         "min_watermark": w["min_watermark"],
                         "remaining_ms": max(0, int((w["deadline_at"] - now) * 1000))}
                        for w in pending_waits
                    ],
                },
                "quarantine": {
                    "open_count": len(open_q),
                    "open": open_q,
                },
            }

    def full_audit(self) -> dict[str, Any]:
        """离线/在线通用的全量一致性审计。"""
        with self._lock:
            stored = self.store.load_segments()
            checks: list[dict[str, Any]] = []
            rebuilt = verifier.replay_all(stored)
            total_events = sum(len(s["events"]) for s in stored)
            checks.append({
                "name": "segment_hash_chain",
                "ok": True,
                "detail": f"{len(stored)} 个分段 / {total_events} 条事件的双链完整",
            })
            checks.extend(verifier.audit_projection(rebuilt)["checks"])
            digest = verifier.state_digest(rebuilt)
            checks.append({
                "name": "replay_equivalence",
                "ok": digest == self._published_digest,
                "detail": "磁盘重放与线上确认截面一致"
                if digest == self._published_digest else "磁盘重放与线上截面不一致",
            })
            checks.append(verifier.full_receipt_check(stored))
            return {
                "ok": all(c["ok"] for c in checks),
                "checked_at": time.time(),
                "confirmed_index": self.confirmed_index,
                "confirmed_seq": self.confirmed_seq,
                "state_digest": digest,
                "checks": checks,
            }
