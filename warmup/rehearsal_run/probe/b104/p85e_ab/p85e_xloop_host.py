#!/usr/bin/env python3
"""ON the A100 box (p85e, 2026-10-31 ~22:00 UTC; operator go ~21:45 UTC "Yes, until 11:30 (Recommended)"): a small scheduler BESIDE the live
p85b driver (no driver restart, no vLLM restart, no harness/scorer/llm edit). Plan wf_5a596588-311 ranks 1-3 with every checker fix.

  phase 1  hot write-back (no sessions needed): every WB_S the official-verified Z=100 bests in WB_FILES (jsonl {name, proof, score, tokens,
           heartbeats, L, H, Z, source}; the GB10 unit lra-p85e-wbpush keeps /workspace/p85c/squeeze_best.jsonl current) are merged into the
           driver's /workspace/out-p85b/work/<row>/state.json (+ best.lean), atomically (tmp + os.replace), only when better by >= WB_MARGIN
           (0.02: official meter vs box meter); state.json.before-p85e is written once per row before the first write. agent.py's
           Workspace.save() keeps the higher on-disk best, so an in-flight session never undoes it (a lost race heals on the next re-apply).
  continue CONT=1: a row the driver can NEVER schedule again (its own accounting: op.sessions_used over agent_sessions.jsonl + the run dirs
           p85b-sNN-k*, >= --max-sessions; or its last line parked; or the driver's agent stage is over) and with no driver agent.py for
           GRACE_S gets more sessions on the SAME work root; run ids p85b-cNN-kK (the driver's resume glob p85b-sNN-k* never sees them).
  twins    TWINS=04,05,06,07,09: a second lineage per row in /workspace/p85e/twin/work, seeded once from the main row dir (best, attempts,
           ledger; notes.md header only unless TWIN_NOTES=copy), run ids p85b-tNN-kK; every tick the higher best is merged both ways
           (main <-> twin, margin TWIN_MARGIN), so a twin session always starts from max(main best, twin best) and the pick sees twin gains.
Sessions: exactly the driver's command builder (op.session_cmd from RUN_CMD, --work-root swapped for twins, never --fresh), its environment
(op.base_env) and its process supervision (op.run_session: SIGTERM/SIGKILL at the deadline + reap of left-behind Lean processes).
Capacity: running agent.py sessions (every agent.py on the box that is not SIGSTOPped and not ours) + ours <= cap; cap = MAX_EARLY (14) until
MAX_SWITCH_EPOCH (2026-10-31 23:30 UTC), then MAX_LATE (16 = vLLM --max-num-seqs); MAX_TOTAL overrides both (0 = write-back only). No start
while vLLM KV >= KV_HIGH or requests are waiting, while the driver is down (restart in progress), or within 180 s of a driver start.
Deadline: XDEADLINE_EPOCH (2026-11-01 11:30 UTC); a session starts only if its row's p75 session length (min 900 s) fits before it; each
session is also bounded by SESSION_MAX_S. Babysit: every BABYSIT_S each running external session is checked (turns, tokens, checks ok/fail,
TOOL ERROR / Traceback / start-proof / connect lines); trouble stops the session and disables that lineage; 3 disabled -> no new sessions.
Single instance: flock /workspace/p85e/xloop.lock + /workspace/p85e/xloop.pid. Files: xloop.log, ext_sessions.jsonl, babysit.jsonl, logs/.
Stop: touch /workspace/p85e/STOP (no new session; running ones finish or hit the deadline); also STOP_NOW = stop running ones now (SIGTERM,
bests kept). Relaunch only via p85e_ctl.sh relaunch (STOP, bounded wait for the pid, rm STOP, start).
DRY=1: print the candidate list against the live driver and exit (no lock, no writes).

v3 (2026-11-01 ~00:00 UTC; operator 2026-10-31 ~23:40 UTC "Keep A100 do warm-up climbing until the board is reset on Nov 1"):
  END_AT   the external deadline is read from /workspace/p85e/END_AT at every loop pass (first token = epoch seconds, or an ISO time
           "YYYY-MM-DDTHH:MM[:SS]Z"); missing file = XDEADLINE_EPOCH (default = the cap); always clamped to END_CAP_EPOCH (2026-11-02 00:00
           UTC, the stop rule's hard cap); an unparsable file keeps the last good value. The GB10 moves it without a restart
           (p85e_ctl.sh set-end). A session starts only if its row's p75 length fits before END_AT, and every running session is stopped
           (SIGTERM, then SIGKILL; bests are banked) as soon as END_AT has passed, also when END_AT is moved earlier.
  POST=1   post-driver mode: rows at or above SKIP_ABOVE (the Putnams >= 94) are deprioritized (priority x LOW_MULT, 0.1) instead of
           skipped; once the driver's agent stage is over (and after the driver exits) every row qualifies for a continuation on its own
           best (op.session_cmd, same endpoint), twins as before; a babysit-disabled lineage is re-enabled after DISABLE_TTL_S (7200 s), and
           3 disabled lineages pause new sessions for 1 h instead of until a relaunch.
  busy     lineages are also read from the process table (any agent.py with run id <tag>-cNN-k* / <tag>-tNN-k*, e.g. the sessions a
           draining predecessor still runs): never two sessions on one lineage.
  handover the single-instance lock is /workspace/p85e/xloop.main.lock, held only during the main loop: on STOP / END_AT the
           instance releases it and drains its running sessions, so p85e_ctl.sh handover starts the successor at once (the predecessor's
           sessions keep running, are counted against the cap and their lineages stay busy).

v3.2-ab (2026-11-01 ~04:30 UTC, b104 box A/B; opt-in AB=1, see probe/b104/p85e_ab/make_ab.py in lean-refactor branch b104-turncap).
v3.1 (2026-11-01 ~00:40 UTC; review: KV 0.94-0.99 + preemptions 0 -> 21 at 16 sessions = vLLM max-num-seqs, 150-270 tok/s instead of
440-550): admission is paced, not only gated. At most ONE start per tick; >= START_GAP_S (120) between starts (also after an instance
start); no start while vllm:num_preemptions_total rose within PREEMPT_WIN_S (300) or while the preemption history does not cover that
window yet (fresh instance, or a vLLM counter reset). SHED=1: when KV reached SHED_KV (0.95), stayed >= SHED_KV - 0.05 for SHED_HOLD_S (600),
is >= SHED_KV again and the preemptions rose in that window, the youngest running session of THIS instance is stopped (SIGTERM; its best is banked; its lineage is NOT disabled), at most one per SHED_GAP_S
(900). Recommended env (launch.env): MAX_TOTAL=14 KV_HIGH=0.75 SESSION_MAX_S=5400. A tick that raises is logged and skipped (the main
loop survives).
"""
import calendar, collections, fcntl, hashlib, json, os, re, shlex, shutil, statistics, subprocess, sys, threading, time, traceback
from pathlib import Path

W = Path(os.environ.get("P85E_W") or "/workspace"); LRA = W / "lra"; OUT = W / "out-p85b"; RUN_DIR = W / "lra-run-p85b"; X = W / "p85e"
MAIN = OUT / "work"; TWIN = X / "twin" / "work"
GATES = ("DRY", "CONT", "TWINS", "MAX_TOTAL", "MAX_EARLY", "MAX_LATE", "MAX_SWITCH_EPOCH", "XDEADLINE_EPOCH", "WB_FILES", "WB_MARGIN",
         "TWIN_MARGIN", "SKIP_ABOVE", "SESSION_MAX_S", "TWIN_NOTES", "KV_HIGH", "POST", "LOW_MULT", "END_CAP_EPOCH", "DISABLE_TTL_S",
         "P85E_W", "START_GAP_S", "PREEMPT_WIN_S", "SHED", "SHED_KV", "SHED_HOLD_S", "SHED_GAP_S",
         "AB", "AB_ROWS", "AB_PAIRS", "AB_BUDGET_S", "AB_END_EPOCH", "AB_AGENT", "AB_AGENT_MD5", "AB_FLAGS", "AB_TARGET", "AB_MIN_CHAIN_S")
E = os.environ.get
DRY = E("DRY", "0") == "1"
CONT = E("CONT", "0") == "1"
TWINS = [r for r in E("TWINS", "").split(",") if r.strip()]
MAX_TOTAL = int(E("MAX_TOTAL")) if E("MAX_TOTAL", "") != "" else None
MAX_EARLY, MAX_LATE = int(E("MAX_EARLY", "14")), int(E("MAX_LATE", "16"))
MAX_SWITCH = float(E("MAX_SWITCH_EPOCH") or 1793489400)          # 2026-10-31 23:30 UTC
END_CAP = float(E("END_CAP_EPOCH") or 1793577600)               # 2026-11-02 00:00 UTC: the stop rule's hard cap
END_DEFAULT = min(float(E("XDEADLINE_EPOCH") or END_CAP), END_CAP)  # without an END_AT file
POST = E("POST", "0") == "1"
LOW_MULT = float(E("LOW_MULT", "0.1"))
DISABLE_TTL_S = float(E("DISABLE_TTL_S", "7200" if POST else "0"))   # 0 = a disabled lineage stays disabled until a relaunch
PAUSE3_S = 3600
WB_FILES = [Path(p) for p in E("WB_FILES", "/workspace/p85c/squeeze_best.jsonl").split(",") if p]
WB_MARGIN, TWIN_MARGIN = float(E("WB_MARGIN", "0.02")), float(E("TWIN_MARGIN", "0.005"))
SKIP_ABOVE = float(E("SKIP_ABOVE", "94"))
SESSION_MAX_S = float(E("SESSION_MAX_S", "10800"))
TWIN_NOTES = E("TWIN_NOTES", "header")
KV_HIGH = float(E("KV_HIGH", "0.85"))
START_GAP_S = float(E("START_GAP_S", "120"))          # v3.1: >= this between two starts (also after the instance start)
PREEMPT_WIN_S = float(E("PREEMPT_WIN_S", "300"))      # v3.1: no start while num_preemptions_total rose within this window
SHED = E("SHED", "1") == "1"                          # v3.1: shed the youngest own session on a sustained KV saturation
SHED_KV, SHED_HOLD_S, SHED_GAP_S = float(E("SHED_KV", "0.95")), float(E("SHED_HOLD_S", "600")), float(E("SHED_GAP_S", "900"))
GRACE_S, WB_S, TICK_S, BABYSIT_S, DRIVER_WARM_S = 90, 300, 20, 300, 180
# b104 box A/B (v3.2-ab, 2026-11-01): see probe/b104/p85e_ab/make_ab.py
AB = E("AB", "0") == "1"
AB_ROWS = [int(r) for r in E("AB_ROWS", "").split(",") if r.strip()]
AB_PAIRS = int(E("AB_PAIRS", "3"))
AB_BUDGET_S = float(E("AB_BUDGET_S", "2400"))
AB_END = float(E("AB_END_EPOCH") or 0)
AB_AGENT = E("AB_AGENT", "/workspace/b104/lra/harness/agent.py")
AB_AGENT_MD5 = E("AB_AGENT_MD5", "")
AB_FLAGS = E("AB_FLAGS", "--late-turn-cap 6000 --late-turn-from 4 --no-trunc-escalation").split()
AB_TARGET = int(E("AB_TARGET", "8"))
AB_MIN_CHAIN_S = float(E("AB_MIN_CHAIN_S", "300"))
ROOM_FLAT_K, ROOM_FLAT_MULT, ROOM_FLAT_EPS = 3, 0.3, 0.005

sys.path.insert(0, str(LRA)); os.chdir(LRA)
from harness import open_package as op  # noqa: E402

argv = shlex.split((RUN_DIR / "RUN_CMD").read_text())
a = op.build_parser().parse_args(argv[argv.index("harness/open_package.py") + 1:])
if a.started_at is None:
    a.started_at = json.loads((OUT / "clock.json").read_text())["started_at"]
clock = op.Clock(a.started_at, a.job_seconds, a.end_seconds, a.export_margin, norm_seconds=(a.normalize_seconds if a.normalize else 0.0))
names, rows, hbs = op.load_rows(a.rows, a.heartbeats)
ALL_IDX = {n: i for i, n in enumerate(names)}   # the driver's row index (run ids p85b-sNN) = the position in the full rows file
if a.problems:
    names = [n for n in names if n in set(a.problems)]
ENV = {k: v for k, v in op.base_env(a).items() if k not in GATES}
TAG = a.tag
LOG = X / "xloop.log"
END_FILE = X / "END_AT"
_wlock = threading.Lock()   # serializes this process's own state.json writes (main thread + session threads)
AB_ROOT = X / "ab"; AB_ARM = {"a": AB_ROOT / "A" / "work", "b": AB_ROOT / "B" / "work"}
AB_STOP = AB_ROOT / "STOP"; AB_PAIRS_J = AB_ROOT / "ab_pairs.jsonl"; AB_SESS_J = AB_ROOT / "ab_sessions.jsonl"


def root_of(kind: str) -> Path:
    return {"t": TWIN, "a": AB_ARM["a"], "b": AB_ARM["b"]}.get(kind, MAIN)


def log(m: str) -> None:
    line = f"[{time.strftime('%m-%d %H:%M:%S', time.gmtime())}] {m}"
    if DRY:
        print(line, flush=True); return
    with LOG.open("a") as fh:
        fh.write(line + "\n")


def hm(t: float) -> str:
    return time.strftime("%m-%d %H:%M:%S", time.gmtime(t)) if t != float("inf") else "never"


def parse_end(txt: str) -> float | None:
    """First token = epoch seconds; else the whole text as an ISO / 'YYYY-MM-DD HH:MM UTC' time; None when unparsable."""
    s = txt.strip()
    if not s:
        return None
    tok = s.split()[0]
    if re.fullmatch(r"\d{9,11}(\.\d+)?", tok):
        return float(tok)
    for fmt in ("%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%MZ", "%Y-%m-%d %H:%M:%S UTC", "%Y-%m-%d %H:%M UTC"):
        try:
            return float(calendar.timegm(time.strptime(s, fmt)))
        except ValueError:
            continue
    return None


END = END_DEFAULT
_end_note = "default"
_end_bad = None


def read_end() -> float:
    """The external deadline (module global END), re-read from END_FILE; logged when it changes."""
    global END, _end_note, _end_bad
    try:
        txt = END_FILE.read_text()
    except FileNotFoundError:
        v, note = END_DEFAULT, "no END_AT file: default"
    except OSError:
        return END
    else:
        v = parse_end(txt)
        if v is None:
            if _end_bad != txt:
                _end_bad = txt; log(f"END_AT file unparsable ({txt.strip()[:60]!r}): keeping {hm(END)} UTC")
            return END
        note = "END_AT file"
    clamped = v > END_CAP
    v = min(v, END_CAP)
    if v != END or note != _end_note:
        log(f"END_AT {hm(END)} -> {hm(v)} UTC ({note}{'; clamped to the cap ' + hm(END_CAP) if clamped else ''})")
        END, _end_note = v, note
    return END


def jappend(p: Path, rec: dict) -> None:
    with p.open("a") as fh:
        fh.write(json.dumps(rec, ensure_ascii=False) + "\n")


def read_state(st: Path) -> dict:
    try:
        return json.loads(st.read_text())
    except (OSError, ValueError):
        return {}


def best_of(st: Path) -> dict:
    return read_state(st).get("best") or {}


def score_of(st: Path) -> float:
    try:
        return float(best_of(st).get("score") or 0)
    except (TypeError, ValueError):
        return 0.0


FIELDS = ("score", "proof", "tokens", "heartbeats", "L", "H", "Z", "compat")
_backed = set()


def merge_best(st: Path, src: dict, margin: float, backup: bool) -> tuple:
    """Write src as st's best when src.score > best + margin; atomic replace + best.lean. Returns (old, new) or None. A torn read of a file an
    agent is writing is skipped (next tick retries)."""
    if not src.get("proof") or src.get("score") is None or not st.exists():
        return None
    with _wlock:
        try:
            raw = st.read_text(); s = json.loads(raw)
        except (OSError, ValueError):
            return None
        b = s.get("best") or {}
        old = float(b.get("score") or 0)
        if float(src["score"]) <= old + margin:
            return None
        if backup and st not in _backed:
            bk = st.with_name("state.json.before-p85e")
            if not bk.exists():
                bk.write_text(raw)
            _backed.add(st)
        nb = {k: src[k] for k in FIELDS if k in src and src[k] is not None}
        for k in FIELDS[2:]:
            nb.setdefault(k, b.get(k))   # as p85d: fields the source lacks (compat) kept from the old best
        nb["score"] = float(src["score"])
        s["best"] = nb
        tmp = st.with_name("state.json.p85e-tmp")
        tmp.write_text(json.dumps(s, ensure_ascii=False, indent=1)); os.replace(tmp, st)
        btmp = st.with_name("best.lean.p85e-tmp")
        btmp.write_text(nb["proof"].rstrip() + "\n"); os.replace(btmp, st.parent / "best.lean")
        return (old, nb["score"])


try:
    from scorer.tokenize import split_declaration
    from scorer.forbidden import check_forbidden
except Exception:  # noqa: BLE001
    split_declaration = check_forbidden = None


def proof_ok(name: str, proof: str) -> str | None:
    if not proof or not proof.strip():
        return "empty"
    if split_declaration is not None and split_declaration(proof.rstrip(), rows[name]["statement"]) is None:
        return "does not start with the exact statement + :="
    if check_forbidden is not None:
        f = check_forbidden(proof)
        if f is not None:
            return f"forbidden: {f}"
    return None


_wb_skip = set()


def live_writeback() -> None:
    for f in WB_FILES:
        if not f.exists():
            continue
        for l in f.read_text(errors="replace").splitlines():
            try:
                e = json.loads(l)
            except ValueError:
                continue
            n = e.get("name")
            if n not in rows or n not in names or float(e.get("Z") or 0) < 100 or not e.get("proof"):
                continue
            why = proof_ok(n, e["proof"])
            if why:
                if (n, why) not in _wb_skip:
                    _wb_skip.add((n, why)); log(f"write-back skipped {n[:40]}: {why}")
                continue
            r = merge_best(MAIN / op.safe(n) / "state.json", e, WB_MARGIN, backup=True)
            if r:
                log(f"live write-back {n[:48]} {r[0]:.3f}->{r[1]:.3f} {e.get('source') or f.name}")


def twin_sync() -> None:
    for i, n in enumerate(names):
        if f"{i:02d}" not in TWINS:
            continue
        ts, ms = TWIN / op.safe(n) / "state.json", MAIN / op.safe(n) / "state.json"
        if not ts.exists():
            continue
        r = merge_best(ts, best_of(ms), TWIN_MARGIN, backup=False)
        if r:
            log(f"twin merge {n[:40]} main->twin {r[0]:.3f}->{r[1]:.3f}")
        r = merge_best(ms, best_of(ts), TWIN_MARGIN, backup=True)
        if r:
            log(f"twin merge {n[:40]} twin->main {r[0]:.3f}->{r[1]:.3f}")


# ------------------------------------------------------------------------------------------------------------------------- box readings
def procs() -> list:
    """[(pid, stat, etimes, args)] of the box's processes (ps in this script, never pgrep -f over ssh)."""
    out = subprocess.run(["ps", "-ww", "-eo", "pid=,stat=,etimes=,args="], capture_output=True, text=True).stdout
    res = []
    for l in out.splitlines():
        p = l.split(None, 3)
        if len(p) == 4 and p[0].isdigit():
            res.append((int(p[0]), p[1], int(p[2]) if p[2].isdigit() else 0, p[3]))
    return res


RID = re.compile(r"harness/agent\.py .*--run-id (\S+)")


def agent_procs(ps: list) -> list:
    """[(pid, stopped, run_id)] of every agent.py session on the box."""
    res = []
    for pid, stat, _, args in ps:
        m = RID.search(args)
        if m and ("python" in args.split()[0] or args.startswith("harness/agent.py")):
            res.append((pid, stat.startswith("T"), m.group(1)))
    return res


def driver_proc(ps: list):
    for pid, _, et, args in ps:
        if "harness/open_package.py run " in args and f"--tag {TAG} " in args and f"--out {OUT} " in args + " ":
            return pid, et
    return None


def driver_accounting() -> dict:
    """Per row, the driver's own numbers: used (op.sessions_used, exactly as agent_stage's resume), parked, gains, finished seconds."""
    lines = op.read_jsonl_records(OUT / "agent_sessions.jsonl")
    acc = {n: {"ks": [], "parked": False, "gains": [], "secs": []} for n in names}
    for l in lines:
        n = l.get("problem")
        if n not in acc:
            continue
        acc[n]["ks"].append(int(l.get("k") or 0)); acc[n]["gains"].append(op.session_gain(l))
        acc[n]["parked"] = bool(l.get("parked"))
        if l.get("rc") == 0 and l.get("seconds"):
            acc[n]["secs"].append(float(l["seconds"]))
    idx = ALL_IDX
    for n in names:
        cut = []
        if (MAIN / op.safe(n)).exists():
            for d in op.RUNS.glob(f"{TAG}-s{idx[n]:02d}-k*"):
                m = re.fullmatch(rf"{re.escape(TAG)}-s{idx[n]:02d}-k(\d+)", d.name)
                if m and int(m.group(1)) not in acc[n]["ks"]:
                    cut.append(int(m.group(1)))
        acc[n]["used"] = op.sessions_used(acc[n]["ks"], cut)
        acc[n]["cut"] = sorted(cut)
    return acc


_mprev: dict = {}
_phist: collections.deque = collections.deque()   # v3.1: (t, vllm:num_preemptions_total) samples


def preempt_rise(now: float, win: float) -> tuple:
    """(rise of num_preemptions_total over the last `win` s, span of the history in s). The base is the newest sample at or before now - win
    (else the oldest sample: a short history, see span)."""
    if not _phist:
        return 0.0, 0.0
    base = _phist[0]
    for s in _phist:
        if s[0] <= now - win:
            base = s
        else:
            break
    return _phist[-1][1] - base[1], _phist[-1][0] - _phist[0][0]


def vllm_metrics() -> dict | None:
    """running / waiting / kv / gen tok/s from vLLM's /metrics (the key is read from its file into a header, never logged)."""
    try:
        import requests
        key = Path(a.api_key_file).read_text().strip() if a.api_key_file else ""
        url = re.sub(r"/v1/?$", "", a.base_url) + "/metrics"
        r = requests.get(url, headers={"Authorization": f"Bearer {key}"} if key else {}, timeout=10)
        r.raise_for_status()
        v: dict = {}
        for l in r.text.splitlines():
            m = re.match(r"^vllm:(num_requests_running|num_requests_waiting|kv_cache_usage_perc|generation_tokens_total|num_preemptions_total)\{[^}]*\} (\S+)", l)
            if m:
                v[m.group(1)] = v.get(m.group(1), 0.0) + float(m.group(2))
        t = time.time(); g = v.get("generation_tokens_total")
        pr = v.get("num_preemptions_total")
        if pr is not None:
            if _phist and pr < _phist[-1][1]:
                _phist.clear()   # vLLM counter reset (restart): the history starts again (starts wait until it spans 60 s)
            _phist.append((t, pr))
            while _phist and t - _phist[0][0] > PREEMPT_WIN_S + SHED_HOLD_S + 120:
                _phist.popleft()
        if g is not None and _mprev.get("t") and t - _mprev["t"] >= 30:
            v["gen_tok_s"] = (g - _mprev["g"]) / (t - _mprev["t"])
            _mprev.update(t=t, g=g, rate=v["gen_tok_s"])
        elif g is not None and not _mprev.get("t"):
            _mprev.update(t=t, g=g)
        if "gen_tok_s" not in v and "rate" in _mprev:
            v["gen_tok_s"] = _mprev["rate"]
        return v
    except Exception as e:  # noqa: BLE001
        return {"error": f"{type(e).__name__}"}


# ------------------------------------------------------------------------------------------------------------------------- sessions
ext: dict = {}            # (kind, i) -> {"thread", "run_id", "t0", "flag", "first"}
kcount: dict = {}
disabled: dict = {}       # (kind, i) -> {"why", "t"}
paused_until = 0.0
started_once: set = set()
EXT_J = X / "ext_sessions.jsonl"; BAB_J = X / "babysit.jsonl"


def ext_history() -> dict:
    """(kind, i) -> [gains] of finished external sessions (this and earlier p85e instances)."""
    h: dict = {}
    for r in op.read_jsonl_records(EXT_J):
        h.setdefault((r.get("kind"), r.get("row")), []).append(float(r.get("gain") or 0))
    return h


def ext_secs() -> dict:
    s: dict = {}
    for r in op.read_jsonl_records(EXT_J):
        if r.get("rc") == 0 and r.get("seconds"):
            s.setdefault(r.get("row"), []).append(float(r["seconds"]))
    return s


def next_k(kind: str, i: int) -> int:
    pre = f"{TAG}-{kind}{i:02d}-k"
    ks = [int(d.name[len(pre):]) for d in op.RUNS.glob(pre + "*") if d.name[len(pre):].isdigit()]
    return max(ks + [kcount.get((kind, i), 0)]) + 1


def seed_twin(n: str) -> None:
    tdir = TWIN / op.safe(n)
    if tdir.exists():
        return
    tmp = TWIN / (op.safe(n) + ".p85e-seed")
    shutil.rmtree(tmp, ignore_errors=True)
    shutil.copytree(MAIN / op.safe(n), tmp, ignore=shutil.ignore_patterns("LRAScratch", "*.p85e-tmp", "state.json.before-*"))
    if TWIN_NOTES != "copy":
        (tmp / "notes.md").write_text("# Notes (yours to keep; persisted across runs)\n")
    os.replace(tmp, tdir)
    log(f"twin seeded {n[:48]} from the main row dir (best {score_of(tdir / 'state.json'):.3f}; notes {TWIN_NOTES})")


def session(kind: str, i: int, k: int, flag: threading.Event) -> None:
    n = names[i]; run_id = f"{TAG}-{kind}{i:02d}-k{k}"
    mst = MAIN / op.safe(n) / "state.json"
    try:
        if kind == "t":
            seed_twin(n)
            twin_sync()
        own = (TWIN if kind == "t" else MAIN) / op.safe(n) / "state.json"
        if not own.exists():
            log(f"{run_id}: no state.json at {own}: NOT started (never --fresh)"); return
        b0_main, b0_own = score_of(mst), score_of(own)
        cmd = op.session_cmd(a, n, run_id, fresh=False)
        if kind == "t":
            cmd[cmd.index("--work-root") + 1] = str(TWIN)
        assert "--fresh" not in cmd
        t0 = time.time(); dl = min(END, t0 + SESSION_MAX_S)
        log(f"{run_id} starts ({'twin' if kind == 't' else 'continuation'}; own best {b0_own:.3f}, main {b0_main:.3f}; stop by "
            f"{time.strftime('%H:%M', time.gmtime(dl))})")
        # stopped at dl, at a flag (babysit / STOP_NOW), or as soon as END_AT has passed (END is re-read by the main loop: moving it earlier
        # stops the running sessions too)
        rc = op.run_session(cmd, ENV, X / "logs" / f"{run_id}.log", dl,
                            now=lambda: float("inf") if (flag.is_set() or time.time() >= END) else time.time())
        if kind == "t":
            twin_sync()
        b1_main, b1_own = score_of(mst), score_of(own)
        rec = {"kind": kind, "row": i, "problem": n, "k": k, "run_id": run_id, "rc": rc, "seconds": round(time.time() - t0, 1),
               "out_tokens": op.session_out_tokens(op.RUNS / run_id), "tool_errors": op.session_tool_errors(op.RUNS / run_id),
               "own_before": b0_own, "own_after": b1_own, "gain": round(b1_own - b0_own, 4), "main_before": b0_main, "main_after": b1_main,
               "stopped": flag.is_set(), "end_cut": time.time() >= END, "t_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        jappend(EXT_J, rec)
        log(f"{run_id} done rc {rc} in {rec['seconds']:.0f} s: own {b0_own:.3f}->{b1_own:.3f}, main {b0_main:.3f}->{b1_main:.3f}, "
            f"out_tok {rec['out_tokens']}, tool errors {rec['tool_errors'] or 0}{' (stopped)' if flag.is_set() else ''}"
            f"{' (END_AT)' if rec['end_cut'] else ''}")
    except Exception as e:  # noqa: BLE001
        log(f"{run_id}: session thread raised {type(e).__name__}: {e}")


def is_disabled(key, now: float) -> bool:
    d = disabled.get(key)
    if not d:
        return False
    if DISABLE_TTL_S > 0 and now - d["t"] >= DISABLE_TTL_S:
        disabled.pop(key, None)
        log(f"lineage {key[0]}{key[1]:02d} re-enabled after {DISABLE_TTL_S / 3600:.1f} h (disabled for: {d['why']})")
        return False
    return True


def stop_session(key, why: str, disable: bool) -> None:
    if key[0] in "ab":
        ab_stop_pair(key[1], f"babysit: {why}"); return
    j = ext.get(key)
    if j:
        j["flag"].set()
    if disable:
        disabled[key] = {"why": why, "t": time.time()}
    log(f"CRITICAL babysit: {j['run_id'] if j else key}: {why}: session stopped{'; lineage disabled' if disable else ''}")


CONN = re.compile(r"turn \d+: (?!no-thinking|budget reclaim|junk).*(connect|refused|timed out|rate.?limit|\b429\b|\b5\d\d\b|server error|transport)", re.I)


def babysit() -> None:
    global paused_until
    for key, j in list(ext.items()):
        if not j["thread"].is_alive():
            continue
        rid = j["run_id"]; el = time.time() - j["t0"]
        try:
            txt = (X / "logs" / f"{rid}.log").read_text(errors="replace")
        except OSError:
            txt = ""
        terr = len(re.findall(r"TOOL ERROR (\w+): (\w+)", txt)); tb = len(re.findall(r"^Traceback", txt, re.M))
        sp = "start proof does not compile" in txt; conn = sum(1 for l in txt.splitlines() if CONN.search(l))
        turns, otok = 0, 0
        try:
            for l in (op.RUNS / rid / "turns.jsonl").read_text().splitlines():
                turns += 1; otok += int((json.loads(l) or {}).get("out_tok") or 0)
        except (OSError, ValueError):
            pass
        own = root_of(key[0]) / op.safe(names[key[1]]) / "state.json"
        att = [x for x in (read_state(own).get("attempts") or []) if x.get("run_id") == rid]
        ok = sum(1 for x in att if x.get("ok"))
        rec = {"t": time.strftime("%H:%M:%S", time.gmtime()), "run_id": rid, "first": j["first"], "min": round(el / 60, 1), "turns": turns,
               "out_tok": otok, "tok_s": round(otok / el, 1) if el > 0 else None, "checks_ok": ok, "checks_fail": len(att) - ok,
               "tool_errors": terr, "tracebacks": tb, "start_proof_fail": sp, "conn_lines": conn}
        jappend(BAB_J, rec)
        log(f"babysit {rid}{' (first)' if j['first'] else ''}: {rec['min']} min, {turns} turns, {otok} out tok ({rec['tok_s']} tok/s), "
            f"checks ok {ok} fail {len(att) - ok}, tool errors {terr}, tracebacks {tb}, conn {conn}")
        if tb or sp:
            stop_session(key, "Traceback" if tb else "start proof does not compile", True)
        elif terr >= 3:
            stop_session(key, f"tool-error storm ({terr})", True)
        elif turns == 0 and el > 25 * 60:
            stop_session(key, "no turn in 25 min", True)
        elif conn >= 5:
            paused_until = time.time() + 900; log(f"CRITICAL babysit: {rid}: {conn} connect/server-error lines: no new external session for 15 min")
    now = time.time(); act = [k for k in list(disabled) if is_disabled(k, now)]
    if len(act) >= 3 and paused_until < now + 60:
        paused_until = now + PAUSE3_S if POST else float("inf")
        log(f"CRITICAL babysit: {len(act)} lineages disabled ({ {f'{k[0]}{k[1]:02d}': disabled[k]['why'] for k in act} }): NO new external "
            f"sessions {'for 1 h' if POST else '(relaunch to reset)'}")


def cap_now(now: float) -> int:
    if MAX_TOTAL is not None:
        return MAX_TOTAL
    return MAX_EARLY if now < MAX_SWITCH else MAX_LATE


def room(best: float, k: int, gains: list) -> float:
    p = (100.0 - best) / (1 + k)
    if len(gains) >= ROOM_FLAT_K and all(g <= ROOM_FLAT_EPS for g in gains[-ROOM_FLAT_K:]):
        p *= ROOM_FLAT_MULT
    return p


last_seen = {i: (0.0 if DRY else time.time()) for i in range(len(names))}   # live: no continuation in the first GRACE_S (unknown history)
_said: dict = {}


def say_every(key: str, m: str, s: float = 600) -> None:
    if time.time() - _said.get(key, 0) >= s:
        _said[key] = time.time(); log(m)


def plan(now: float, ps: list, vm: dict | None) -> tuple:
    """(candidates sorted by priority, info). A candidate: (prio, kind, i, best, need_s, why)."""
    ap_ = agent_procs(ps); mine = {j["run_id"] for j in ext.values() if j["thread"].is_alive()}
    busy = set()   # lineages with an agent.py that is not ours (a draining predecessor's session): never a second session on them
    for _, _, rid in ap_:
        m = re.fullmatch(rf"{re.escape(TAG)}-([ct])(\d\d)-k\d+", rid)
        if m and rid not in mine:
            busy.add((m.group(1), int(m.group(2))))
    run_ = lambda kind, i: (kind, i) in ext or (kind, i) in busy
    drv_rows = {}
    for pid, stopped, rid in ap_:
        m = re.fullmatch(rf"{re.escape(TAG)}-s(\d\d)-k\d+", rid)
        if m:
            drv_rows[int(m.group(1))] = (pid, stopped, rid); last_seen[int(m.group(1))] = now
    others = sum(1 for _, stopped, rid in ap_ if not stopped and rid not in mine)
    total = others + sum(1 for j in ext.values() if j["thread"].is_alive())
    acc = driver_accounting(); hist = ext_history(); esec = ext_secs()
    dp = driver_proc(ps)
    stage_over = (OUT / "agent_stage.json").exists() or (OUT / "summary.json").exists() or now >= clock.agent_deadline - a.min_session_seconds
    info = {"total": total, "driver_sessions": len(drv_rows), "other_agents": others - len(drv_rows), "ours": len(mine), "cap": cap_now(now),
            "driver": (dp[0] if dp else None), "driver_up_s": (dp[1] if dp else None), "stage_over": stage_over, "vllm": vm,
            "busy": sorted(f"{k}{i:02d}" for k, i in busy), "end": END}
    cands = []
    for i, n in enumerate(names):
        mb = score_of(MAIN / op.safe(n) / "state.json"); tb = score_of(TWIN / op.safe(n) / "state.json")
        best = max(mb, tb)
        secs = sorted(acc[n]["secs"] + esec.get(i, []))
        need = max(900.0, min(7200.0, secs[int(0.75 * (len(secs) - 1))] if secs else 3600.0))
        row = {"i": i, "name": n, "main": mb, "twin": tb or None, "used": acc[n]["used"], "max": a.max_sessions, "parked": acc[n]["parked"],
               "driver_running": i in drv_rows, "need_s": round(need), "running": [k for k in "ct" if run_(k, i)]}
        info.setdefault("rows", []).append(row)
        low = best >= SKIP_ABOVE
        if low and not POST:
            row["skip"] = f">= {SKIP_ABOVE}"; continue
        if END - now < need:
            row["skip"] = "deadline"; continue
        if not (MAIN / op.safe(n) / "state.json").exists():
            row["skip"] = "no state.json (never --fresh)"; continue
        mult, tag_ = (LOW_MULT, f"; low: >= {SKIP_ABOVE}") if low else (1.0, "")
        capped = acc[n]["used"] >= a.max_sessions or acc[n]["parked"] or stage_over
        if CONT and not run_("c", i) and not is_disabled(("c", i), now):
            if i in drv_rows or now - last_seen[i] <= GRACE_S:
                row["cont"] = "driver session (or within grace)"
            elif not capped:
                row["cont"] = f"driver still schedules it ({acc[n]['used']}/{a.max_sessions})"
            else:
                g = acc[n]["gains"] + hist.get(("c", i), [])
                p = room(mb, len(hist.get(("c", i), [])), g) * (0.5 if run_("t", i) else 1.0) * mult
                row["cont"] = round(p, 2); cands.append((p, "c", i, mb, need, ("capped" if not stage_over else "agent stage over") + tag_))
        if f"{i:02d}" in TWINS and not run_("t", i) and not is_disabled(("t", i), now):
            p = room(best, len(hist.get(("t", i), [])), hist.get(("t", i), [])) * (0.5 if (run_("c", i) or i in drv_rows) else 1.0) * mult
            row["twin_prio"] = round(p, 2); cands.append((p, "t", i, best, need, "twin" + tag_))
    cands.sort(key=lambda c: -c[0])
    return cands, info


last_start = 0.0 if DRY else time.time()   # v3.1: an instance start counts as a start (START_GAP_S after a handover too)
last_shed = 0.0
kv_high_since = None


def shed_check(now: float, vm: dict | None) -> None:
    """v3.1: KV >= SHED_KV for SHED_HOLD_S with the preemptions rising in that window -> stop the youngest running session of this instance
    (best banked; lineage not disabled); at most one per SHED_GAP_S."""
    global kv_high_since, last_shed
    if not vm or "error" in vm:
        return
    kv = vm.get("kv_cache_usage_perc", 0)
    if kv_high_since is None:
        if kv >= SHED_KV:
            kv_high_since = now
        return
    if kv < SHED_KV - 0.05:   # a real drop ends the saturated period; short dips to 0.90-0.95 do not
        kv_high_since = None; return
    if kv < SHED_KV or not SHED or now - kv_high_since < SHED_HOLD_S or now - last_shed < SHED_GAP_S:
        return
    rise, span = preempt_rise(now, now - kv_high_since)
    if rise <= 0 or span < SHED_HOLD_S - 60:
        return
    live = [(j["t0"], key) for key, j in ext.items() if j["thread"].is_alive() and not j["flag"].is_set()]
    if not live:
        say_every("shednone", f"vLLM KV {kv:.2f} >= {SHED_KV} for {(now - kv_high_since) / 60:.0f} min, preemptions +{rise:.0f}: no own "
                              f"session to shed (driver / predecessor sessions only)", 900); return
    t0, key = max(live)
    if key[0] in "ab":
        last_shed = now
        log(f"CRITICAL shed: vLLM KV {kv:.2f} >= {SHED_KV} for {(now - kv_high_since) / 60:.0f} min with preemptions +{rise:.0f}: the youngest "
            f"own session is A/B {ext[key]['run_id']}: its pair stops and row {key[1]:02d} is dropped")
        ab_stop_pair(key[1], "shed (KV saturation)"); return
    j = ext[key]; j["flag"].set(); last_shed = now
    log(f"CRITICAL shed: vLLM KV {kv:.2f} >= {SHED_KV} for {(now - kv_high_since) / 60:.0f} min with preemptions +{rise:.0f}: stopping the "
        f"youngest own session {j['run_id']} (up {(now - t0) / 60:.0f} min; best banked; lineage stays enabled)")


def tick(now: float) -> None:
    global last_start
    ps = procs(); vm = vllm_metrics()
    shed_check(now, vm)
    cands, info = plan(now, ps, vm)
    free = info["cap"] - info["total"]
    abwant = ab_want_pair(now)
    if free <= 0 or not (cands or abwant):
        return
    if now < paused_until:
        say_every("paused", f"paused until {hm(paused_until)}: no new session"); return
    if info["driver"] is None and not info["stage_over"]:
        say_every("drvdown", "driver not alive and its agent stage not over (restart in progress?): no new session"); return
    if info["driver"] is not None and (info["driver_up_s"] or 0) < DRIVER_WARM_S:
        say_every("drvwarm", f"driver up only {info['driver_up_s']} s: waiting {DRIVER_WARM_S} s before any new session"); return
    if not vm or "error" in vm:
        say_every("vm", f"vLLM metrics unreadable ({vm}): no new session"); return
    if vm.get("kv_cache_usage_perc", 0) >= KV_HIGH or vm.get("num_requests_waiting", 0) > 0:
        say_every("kv", f"vLLM KV {vm.get('kv_cache_usage_perc', 0):.2f} waiting {vm.get('num_requests_waiting', 0):.0f}: no new session", 300); return
    if now - last_start < START_GAP_S:
        return
    rise, span = preempt_rise(now, PREEMPT_WIN_S)
    if span < PREEMPT_WIN_S - 2 * TICK_S:
        say_every("pspan", f"preemption history only {span:.0f} s of {PREEMPT_WIN_S:.0f}: no new session yet", 300); return
    if rise > 0:
        say_every("preempt", f"vLLM preemptions +{rise:.0f} within {PREEMPT_WIN_S:.0f} s: no new session", 300); return
    if abwant:
        if free >= 2:
            if ab_start_pair(now, info, vm):
                last_start = now
            return
        else:
            say_every("abres", f"A/B: a pair is due, {free} free slot(s) of {info['cap']}: slots reserved for the pair (no c/t start)", 600)
            return
    for p, kind, i, best, need, why in cands:
        if (kind, i) in ext or now >= END:
            continue
        k = next_k(kind, i); kcount[(kind, i)] = k
        flag = threading.Event()
        t = threading.Thread(target=session, args=(kind, i, k, flag), daemon=False, name=f"{kind}{i:02d}")
        first = (kind, i) not in started_once; started_once.add((kind, i))
        ext[(kind, i)] = {"thread": t, "run_id": f"{TAG}-{kind}{i:02d}-k{k}", "t0": time.time(), "flag": flag, "first": first}
        log(f"start {kind}{i:02d}-k{k} prio {p:.2f} ({why}; best {best:.3f}, need {need:.0f} s; total {info['total']} -> "
            f"{info['total'] + 1} of cap {info['cap']}; kv {vm.get('kv_cache_usage_perc', 0):.2f}; END_AT {hm(END)})")
        info["total"] += 1; last_start = now
        t.start()
        break   # v3.1: at most one start per tick


# ------------------------------------------------------------------------------------------------------------------------- b104 A/B
ab_pairs: dict = {}        # row -> {"t0", "t_end", "s0", "name", "dropped", "done", "flags": {kind: Event}}
ab_started: set = set()    # rows with a pair start record (this or an earlier instance): never seeded twice
ab_fin = {"a": 0, "b": 0}  # finished arm sessions of this instance
ab_off_why = None
ab_said_done = False


def md5_of(p: str) -> str:
    try:
        return hashlib.md5(Path(p).read_bytes()).hexdigest()
    except OSError:
        return "missing"


def ab_init() -> None:
    global ab_off_why
    if not AB:
        return
    if not DRY:
        AB_ROOT.mkdir(parents=True, exist_ok=True)
    for r in op.read_jsonl_records(AB_PAIRS_J):
        if r.get("event") == "start":
            ab_started.add(int(r["row"]))
    m = md5_of(AB_AGENT)
    if AB_END <= 0 or not AB_ROWS:
        ab_off_why = "AB_END_EPOCH / AB_ROWS not set"
    elif not AB_AGENT_MD5 or m != AB_AGENT_MD5:
        ab_off_why = f"overlay agent md5 {m} != AB_AGENT_MD5 {AB_AGENT_MD5 or '-'}"
    elif any(r < 0 or r >= len(names) for r in AB_ROWS):
        ab_off_why = f"AB_ROWS out of range: {AB_ROWS}"


def ab_running(i: int) -> bool:
    return any((k, i) in ext and ext[(k, i)]["thread"].is_alive() for k in "ab")


def ab_next_row():
    for i in AB_ROWS:
        if i not in ab_started and i not in ab_pairs:
            return i
    return None


def ab_window(now: float) -> bool:
    return AB and ab_off_why is None and now < AB_END and not AB_STOP.exists()


def ab_want_pair(now: float) -> bool:
    if not ab_window(now):
        return False
    if min(ab_fin.values()) >= AB_TARGET:
        return False
    if sum(1 for i in ab_pairs if ab_running(i)) >= AB_PAIRS:
        return False
    if now + AB_BUDGET_S > min(AB_END, END):
        return False
    return ab_next_row() is not None


def ab_stop_pair(i: int, why: str) -> None:
    p = ab_pairs.get(i)
    if not p:
        return
    for f in p["flags"].values():
        f.set()
    if not p.get("dropped"):
        p["dropped"] = why
        jappend(AB_PAIRS_J, {"event": "drop", "row": i, "problem": p["name"], "why": why, "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())})
        log(f"CRITICAL A/B: pair row {i:02d} stopped and dropped from both arms: {why}")


def _sha(p: Path) -> str:
    try:
        return hashlib.sha256(p.read_bytes()).hexdigest()[:16]
    except OSError:
        return "missing"


def ab_seed(i: int):
    """One snapshot of the main row dir, copied into both arms (byte-identical). Returns (s0 best, sha A, sha B) or None (row dropped)."""
    n = names[i]; sd = op.safe(n)
    snap = AB_ROOT / "snap" / sd
    if snap.exists() or (AB_ARM["a"] / sd).exists() or (AB_ARM["b"] / sd).exists():
        log(f"A/B: row {i:02d} already has an arm or snapshot dir (an earlier pair): skipped"); return None
    snap.parent.mkdir(parents=True, exist_ok=True)
    ign = shutil.ignore_patterns("LRAScratch", "*.p85e-tmp", "state.json.before-*", "state.json.tmp*", "*.tmp")
    with _wlock:   # no own write-back into the main row while copying
        shutil.copytree(MAIN / sd, snap, ignore=ign)
    for k in "ab":
        AB_ARM[k].mkdir(parents=True, exist_ok=True)
        tmp = AB_ARM[k] / (sd + ".ab-seed")
        shutil.rmtree(tmp, ignore_errors=True)
        shutil.copytree(snap, tmp)
        os.replace(tmp, AB_ARM[k] / sd)
    sa, sb = _sha(AB_ARM["a"] / sd / "state.json"), _sha(AB_ARM["b"] / sd / "state.json")
    if sa != sb or sa == "missing":
        log(f"CRITICAL A/B: row {i:02d} arm seeds differ ({sa} vs {sb}): row dropped"); return None
    return score_of(snap / "state.json"), sa, sb


def ab_start_pair(now: float, info: dict, vm: dict) -> bool:
    global ab_off_why
    m = md5_of(AB_AGENT)
    if m != AB_AGENT_MD5:
        ab_off_why = f"overlay agent md5 changed: {m}"; log(f"CRITICAL A/B off: {ab_off_why}"); return False
    i = ab_next_row()
    if i is None:
        return False
    ab_started.add(i)
    seed = ab_seed(i)
    if seed is None:
        jappend(AB_PAIRS_J, {"event": "start", "row": i, "problem": names[i], "seeded": False}); return False
    s0, sa, sb = seed
    t0 = time.time(); t_end = min(t0 + AB_BUDGET_S, AB_END)
    p = {"t0": t0, "t_end": t_end, "s0": s0, "name": names[i], "dropped": None, "done": False,
         "flags": {"a": threading.Event(), "b": threading.Event()}}
    ab_pairs[i] = p
    jappend(AB_PAIRS_J, {"event": "start", "row": i, "problem": names[i], "seeded": True, "s0": s0, "sha_a": sa, "sha_b": sb,
                         "t0": round(t0, 1), "t_end": round(t_end, 1), "budget_s": AB_BUDGET_S, "agent_md5": m, "flags_b": AB_FLAGS,
                         "kv": vm.get("kv_cache_usage_perc"), "total_before": info["total"],
                         "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t0))})
    for k in "ab":
        kk = next_k(k, i); kcount[(k, i)] = kk
        th = threading.Thread(target=ab_arm, args=(k, i, p), daemon=False, name=f"{k}{i:02d}")
        ext[(k, i)] = {"thread": th, "run_id": f"{TAG}-{k}{i:02d}-k{kk}", "t0": time.time(), "flag": p["flags"][k], "first": True}
        th.start()
    info["total"] += 2
    log(f"A/B pair start row {i:02d} {names[i][:44]} (s0 {s0:.3f}, seed sha {sa}; budget {AB_BUDGET_S:.0f} s -> stop by "
        f"{time.strftime('%H:%M:%S', time.gmtime(t_end))}; total {info['total'] - 2} -> {info['total']} of cap {info['cap']}; kv "
        f"{vm.get('kv_cache_usage_perc', 0):.2f}; finished arm sessions A {ab_fin['a']} B {ab_fin['b']})")
    return True


def ab_arm(kind: str, i: int, p: dict) -> None:
    """One arm of a pair: sessions chained on the arm's own lineage until the pair's t_end (or a stop)."""
    n = names[i]; root = AB_ARM[kind]; own = root / op.safe(n) / "state.json"; mst = MAIN / op.safe(n) / "state.json"
    flag = p["flags"][kind]; faults = 0; first = True
    try:
        while not flag.is_set() and time.time() < END:
            left = p["t_end"] - time.time()
            if left <= (1 if first else AB_MIN_CHAIN_S):
                break
            k = next_k(kind, i) if not first else kcount[(kind, i)]
            kcount[(kind, i)] = k
            run_id = f"{TAG}-{kind}{i:02d}-k{k}"
            j = ext.get((kind, i))
            if j is not None:
                j["run_id"] = run_id; j["t0"] = time.time(); j["first"] = first
            cmd = op.session_cmd(a, n, run_id, fresh=False)
            assert cmd[1] == "harness/agent.py" and "--fresh" not in cmd
            cmd[1] = AB_AGENT
            cmd[cmd.index("--work-root") + 1] = str(root)
            if kind == "b":
                cmd += AB_FLAGS
            b0 = score_of(own); t0 = time.time()
            log(f"{run_id} starts (A/B arm {kind.upper()}; own best {b0:.3f}, s0 {p['s0']:.3f}; stop by "
                f"{time.strftime('%H:%M:%S', time.gmtime(p['t_end']))})")
            rc = op.run_session(cmd, ENV, X / "logs" / f"{run_id}.log", p["t_end"],
                                now=lambda: float("inf") if (flag.is_set() or time.time() >= END) else time.time())
            b1 = score_of(own); sec = time.time() - t0
            otok = op.session_out_tokens(op.RUNS / run_id)
            rec = {"arm": kind.upper(), "kind": kind, "row": i, "problem": n, "k": k, "run_id": run_id, "rc": rc, "seconds": round(sec, 1),
                   "out_tokens": otok, "tool_errors": op.session_tool_errors(op.RUNS / run_id), "own_before": b0, "own_after": b1,
                   "gain": round(b1 - b0, 4), "s0": p["s0"], "stopped": flag.is_set(), "budget_cut": rc is None and not flag.is_set(),
                   "end_cut": time.time() >= END, "t_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
            jappend(AB_SESS_J, rec)
            ab_fin[kind] += 1; first = False
            r = merge_best(mst, best_of(own), WB_MARGIN, backup=True)
            log(f"{run_id} done rc {rc} in {sec:.0f} s: own {b0:.3f}->{b1:.3f} (s0 {p['s0']:.3f}), out_tok {otok}"
                f"{'; arm->main ' + format(r[0], '.3f') + '->' + format(r[1], '.3f') if r else ''}{' (stopped)' if flag.is_set() else ''}")
            if rc is None:
                break
            if rc != 0 and otok == 0 and not flag.is_set():
                faults += 1
                if faults >= 2:
                    ab_stop_pair(i, f"arm {kind.upper()}: two failed sessions in a row (rc {rc}, 0 output tokens)"); break
                time.sleep(30)
            else:
                faults = 0
    except Exception as e:  # noqa: BLE001
        log(f"A/B arm {kind}{i:02d}: thread raised {type(e).__name__}: {e}")
        ab_stop_pair(i, f"arm {kind.upper()} thread raised {type(e).__name__}")


def ab_housekeep(now: float) -> None:
    """Finished pairs (both arm threads ended): readout + one-way write-back; harm stop; STOP file; the end of the window (logged once)."""
    global ab_off_why, ab_said_done
    if not AB:
        return
    if AB_STOP.exists() and ab_off_why is None:
        ab_off_why = "ab/STOP file"
        for i in list(ab_pairs):
            if ab_running(i):
                ab_stop_pair(i, "ab/STOP file")
        log("A/B off: ab/STOP file present (running pairs stopped, bests banked)")
    for i, p in list(ab_pairs.items()):
        if p["done"] or ab_running(i):
            continue
        p["done"] = True
        n = names[i]; ba = score_of(AB_ARM["a"] / op.safe(n) / "state.json"); bb = score_of(AB_ARM["b"] / op.safe(n) / "state.json")
        rec = {"event": "done", "row": i, "problem": n, "s0": p["s0"], "best_a": ba, "best_b": bb, "gain_a": round(ba - p["s0"], 4),
               "gain_b": round(bb - p["s0"], 4), "d_b_minus_a": round(bb - ba, 4), "dropped": p["dropped"], "wall_s": round(now - p["t0"], 1),
               "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        jappend(AB_PAIRS_J, rec)
        for k in "ab":
            r = merge_best(MAIN / op.safe(n) / "state.json", best_of(AB_ARM[k] / op.safe(n) / "state.json"), WB_MARGIN, backup=True)
            if r:
                log(f"A/B write-back row {i:02d} arm {k.upper()} -> main {r[0]:.3f}->{r[1]:.3f}")
        log(f"A/B pair done row {i:02d} {n[:44]}: s0 {p['s0']:.3f}, A {ba:.3f} ({ba - p['s0']:+.3f}), B {bb:.3f} ({bb - p['s0']:+.3f}), "
            f"B-A {bb - ba:+.3f}{' DROPPED: ' + p['dropped'] if p['dropped'] else ''}")
        fin = [q for q in ab_pairs.values() if q["done"] and not q["dropped"]]
        if ab_off_why is None and len(fin) >= max(4, (len(AB_ROWS) + 1) // 2):
            worse = 0
            for q in fin:
                qa = score_of(AB_ARM["a"] / op.safe(q["name"]) / "state.json"); qb = score_of(AB_ARM["b"] / op.safe(q["name"]) / "state.json")
                worse += 1 if qb < qa - 1.0 else 0
            if worse >= 0.75 * len(fin):
                ab_off_why = f"harm stop: B worse than A by > 1 on {worse}/{len(fin)} finished rows"
                for jj in list(ab_pairs):
                    if ab_running(jj):
                        ab_stop_pair(jj, ab_off_why)
                log(f"CRITICAL A/B off: {ab_off_why}")
    over = not ab_window(now) or min(ab_fin.values()) >= AB_TARGET or (ab_next_row() is None)
    if over and not ab_said_done and not any(ab_running(i) for i in ab_pairs) and ab_pairs:
        ab_said_done = True
        log(f"A/B window over ({ab_off_why or ('AB_END' if now >= AB_END else 'target / rows done')}): {len(ab_pairs)} pairs, finished arm "
            f"sessions A {ab_fin['a']} B {ab_fin['b']}; this instance continues as v3.1 (c/t) until p85e_ctl.sh handover reverts it")


def dry() -> int:
    now = time.time(); ps = procs(); vm = vllm_metrics(); read_end()
    cands, info = plan(now, ps, vm)
    print(f"p85e v3.1 DRY tick {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime(now))}: CONT={int(CONT)} TWINS={','.join(TWINS) or '-'} "
          f"cap {info['cap']} (early {MAX_EARLY} until {time.strftime('%H:%M', time.gmtime(MAX_SWITCH))}, late {MAX_LATE}); running agent "
          f"sessions {info['total']} (driver {info['driver_sessions']}, other {info['other_agents']}, ours {info['ours']}; busy lineages "
          f"{','.join(info['busy']) or '-'}); POST={int(POST)} (low x{LOW_MULT} at >= {SKIP_ABOVE}); driver pid "
          f"{info['driver']} up {info['driver_up_s']} s; agent stage over {info['stage_over']}; END_AT "
          f"{hm(END)} UTC ({_end_note}; cap {hm(END_CAP)}); vLLM {json.dumps({k: round(v, 3) for k, v in (vm or {}).items() if isinstance(v, float)})}")
    print(f"{'row':>3} {'name':44} {'main':>7} {'twin':>7} {'used':>5} {'drv':>3} {'need':>5}  continuation / twin")
    for r in info["rows"]:
        print(f"{r['i']:>3} {r['name'][:44]:44} {r['main']:7.3f} {(r['twin'] or 0):7.3f} {r['used']:>2}/{r['max']:<2} "
              f"{'yes' if r['driver_running'] else '-':>3} {r['need_s']:>5}  {('[' + '+'.join(r['running']) + ' running] ') if r['running'] else ''}"
              f"{r.get('skip') or ''}{'cont=' + str(r['cont']) if 'cont' in r else ''}"
              f"{'  twin=' + str(r['twin_prio']) if 'twin_prio' in r else ''}")
    free = max(0, info["cap"] - info["total"])
    print(f"v3.1 pacing: one start per tick, >= {START_GAP_S:.0f} s apart, none while preemptions rose within {PREEMPT_WIN_S:.0f} s "
          f"(a live instance needs that window of history first); KV_HIGH {KV_HIGH}; shed {'on' if SHED else 'off'} (KV >= {SHED_KV} for "
          f"{SHED_HOLD_S:.0f} s with preemptions rising -> the youngest own session, <= 1 per {SHED_GAP_S:.0f} s); SESSION_MAX_S {SESSION_MAX_S:.0f}")
    if AB:
        ab_init()
        print(f"A/B {'ON' if ab_off_why is None else 'OFF (' + ab_off_why + ')'}: rows {','.join(f'{r:02d}' for r in AB_ROWS)} (already "
              f"started {sorted(ab_started) or '-'}); pairs <= {AB_PAIRS}; budget {AB_BUDGET_S:.0f} s per row and arm; end "
              f"{hm(AB_END)} UTC; target {AB_TARGET} finished sessions per arm; agent {AB_AGENT} md5 {md5_of(AB_AGENT)} (want "
              f"{AB_AGENT_MD5 or '-'}); arm B flags {' '.join(AB_FLAGS)}; next row {ab_next_row()}; a pair wanted now: {ab_want_pair(now)}")
        for r in AB_ROWS:
            print(f"  A/B row {r:02d} {names[r][:50]:50} main {score_of(MAIN / op.safe(names[r]) / 'state.json'):.3f}")
    print(f"candidates (priority order; {free} free slot(s) now -> the first one would start once the gates allow):")
    for p, kind, i, best, need, why in cands:
        print(f"  {kind}{i:02d} {names[i][:50]:50} prio {p:6.2f}  best {best:.3f}  {why}")
    return 0


def main() -> int:
    if DRY:
        return dry()
    X.mkdir(parents=True, exist_ok=True); (X / "logs").mkdir(exist_ok=True); TWIN.mkdir(parents=True, exist_ok=True)
    lk = open(X / "xloop.main.lock", "w")   # v3: held only during the main loop (released before the drain: handover)
    try:
        fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print(f"p85e: another main loop holds {X}/xloop.main.lock: exit", file=sys.stderr); return 3
    (X / "xloop.pid").write_text(f"{os.getpid()}\n")
    read_end()
    ab_init()
    if AB:
        log(f"p85e v3.2-ab A/B {'ON' if ab_off_why is None else 'OFF (' + ab_off_why + ')'}: rows {','.join(f'{r:02d}' for r in AB_ROWS)}; "
            f"pairs <= {AB_PAIRS}; budget {AB_BUDGET_S:.0f} s per row and arm; end {hm(AB_END)} UTC; target {AB_TARGET}/arm; agent "
            f"{AB_AGENT} md5 {md5_of(AB_AGENT)}; arm B {' '.join(AB_FLAGS)}")
    log(f"p85e xloop v3.1 up pid {os.getpid()}: POST={int(POST)} CONT={int(CONT)} TWINS={','.join(TWINS) or '-'} cap "
        f"{MAX_TOTAL if MAX_TOTAL is not None else f'{MAX_EARLY}->{MAX_LATE} at ' + time.strftime('%H:%M', time.gmtime(MAX_SWITCH))} "
        f"SKIP_ABOVE {SKIP_ABOVE}{f' (low x{LOW_MULT})' if POST else ' (skipped)'} WB_MARGIN {WB_MARGIN} END_AT {hm(END)} UTC ({_end_note}; cap "
        f"{hm(END_CAP)}) disable TTL {DISABLE_TTL_S:.0f} s; driver agent deadline "
        f"{time.strftime('%m-%d %H:%M', time.gmtime(clock.agent_deadline))}; max_sessions {a.max_sessions}; KV_HIGH {KV_HIGH}; SESSION_MAX_S "
        f"{SESSION_MAX_S:.0f}; pacing 1/tick, gap {START_GAP_S:.0f} s, preempt window {PREEMPT_WIN_S:.0f} s; shed {'on' if SHED else 'off'} "
        f"(KV >= {SHED_KV} for {SHED_HOLD_S:.0f} s, gap {SHED_GAP_S:.0f} s)")
    last_wb = last_bs = last_vm = 0.0
    try:
        while not (X / "STOP").exists() and time.time() < read_end():
            now = time.time()
            if now - last_wb >= WB_S:
                live_writeback(); last_wb = now
            twin_sync()
            for key in [kk for kk, j in ext.items() if not j["thread"].is_alive()]:
                ext.pop(key)
            try:
                ab_housekeep(now)
            except Exception as e:  # noqa: BLE001
                say_every("aberr", f"CRITICAL A/B housekeeping raised {type(e).__name__}: {str(e)[:160]}", 300)
            if (MAX_TOTAL is None or MAX_TOTAL > 0) and (CONT or TWINS or AB):
                try:
                    tick(now)
                except Exception as e:  # noqa: BLE001   v3.1: a raising tick is logged and skipped; the main loop survives
                    tbl = traceback.format_exc().strip().splitlines()
                    say_every("tickerr", f"CRITICAL tick raised {type(e).__name__}: {str(e)[:120]}: skipped "
                                         f"({tbl[-2].strip()[:160] if len(tbl) >= 2 else '?'})", 300)
            if now - last_bs >= BABYSIT_S:
                babysit(); last_bs = now
            if now - last_vm >= BABYSIT_S:
                vm = vllm_metrics() or {}
                ps = procs(); ap_ = agent_procs(ps)
                if "error" not in vm:
                    run = vm.get("num_requests_running", 0)
                    log(f"vllm: running {run:.0f} waiting {vm.get('num_requests_waiting', 0):.0f} kv {vm.get('kv_cache_usage_perc', 0):.2f} gen "
                        f"{vm.get('gen_tok_s', 0):.0f} tok/s ({(vm.get('gen_tok_s', 0) / run) if run else 0:.1f}/stream) preempt "
                        f"{vm.get('num_preemptions_total', 0):.0f}; agent.py {len(ap_)} (ours {sum(1 for j in ext.values() if j['thread'].is_alive())})")
                    if vm.get("kv_cache_usage_perc", 0) >= 0.9:
                        log("CRITICAL vllm KV >= 0.90: no new external session until it drops (admission gate KV_HIGH)")
                last_vm = now
            if (X / "STOP_NOW").exists():
                break
            time.sleep(TICK_S)
        why = "STOP" if (X / "STOP").exists() else ("STOP_NOW" if (X / "STOP_NOW").exists() else f"END_AT {hm(END)}")
        log(f"p85e xloop: no new sessions ({why}); waiting for {sum(1 for j in ext.values() if j['thread'].is_alive())} running")
        lk.close()   # the main-loop lock: a successor (p85e_ctl.sh handover) may start now; this instance only drains
        hard = time.time() + SESSION_MAX_S + 300
        while any(j["thread"].is_alive() for j in ext.values()) and time.time() < hard:
            read_end()   # END_AT moved earlier stops the draining sessions too
            if (X / "STOP_NOW").exists():
                for j in ext.values():
                    j["flag"].set()
            twin_sync()
            for key in [kk for kk, j in ext.items() if not j["thread"].is_alive()]:
                ext.pop(key)
            try:
                ab_housekeep(time.time())
            except Exception as e:  # noqa: BLE001
                say_every("aberr", f"CRITICAL A/B housekeeping raised {type(e).__name__}: {str(e)[:160]}", 300)
            if time.time() - last_bs >= BABYSIT_S:
                babysit(); last_bs = time.time()
            time.sleep(10)
        twin_sync()
        try:
            ab_housekeep(time.time())
        except Exception:  # noqa: BLE001
            pass
        log("p85e xloop exits")
    finally:
        try:
            if (X / "xloop.pid").read_text().strip() == str(os.getpid()):
                (X / "xloop.pid").unlink()
        except OSError:
            pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
