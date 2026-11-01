"""Extract of harness/hx_heldout.py at the commit named in POSTPASS.md: only `_kill_marked`, the one function the transfer lane
calls (transfer.kill_own). The ladder itself is not part of this post-pass bundle."""
import os, signal


def _kill_marked(marker: str) -> int:
    """SIGKILL every process whose environment carries marker (the post-pass's compiles run in sessions of their own: scorer/memgate.py)."""
    n, mk = 0, marker.encode()
    for d in os.listdir("/proc") if os.path.isdir("/proc") else []:
        if d.isdigit() and int(d) != os.getpid():
            try:
                with open(f"/proc/{d}/environ", "rb") as f:
                    if mk in f.read().split(b"\0"):
                        os.kill(int(d), signal.SIGKILL); n += 1
            except (OSError, ProcessLookupError):
                pass
    return n
