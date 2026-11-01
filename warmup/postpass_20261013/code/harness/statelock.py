"""fcntl lock around a workspace's state.json read-modify-write (driver v2, docs/cc_driver_v2.md §4, 2026-10-12): the v2 tool scripts
(LRA_CHECK_V2=1) and the Claude Code driver's end-of-session ledger write take it, so two tool calls Claude runs in parallel, or a tool and
the ledger, never lose each other's attempts, best or spend. A separate lock file (<ws>/.state.lock): state.json itself is rewritten whole.
Bounded wait (2026-10-11: every wait needs a timeout): after `timeout` seconds the caller gets TimeoutError."""
from __future__ import annotations

import contextlib, fcntl, time
from pathlib import Path


@contextlib.contextmanager
def state_lock(ws_root, timeout: float = 1700.0, poll: float = 0.2):
    with open(Path(ws_root) / ".state.lock", "a") as fh:
        t0 = time.time()
        while True:
            try:
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB); break
            except BlockingIOError:
                if time.time() - t0 > timeout:
                    raise TimeoutError(f"state.json lock busy for {timeout:.0f} s")
                time.sleep(poll)
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)
