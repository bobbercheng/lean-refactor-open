#!/usr/bin/env python3
"""Lean fixtures of the finer sorry check (harness/finer_sorry.py), run on demand on a machine with the library environments.

Each fixture (fixtures/F*.lean, its expectation in its `-- expect:` line) is compiled in each environment, as a plain file and, where
the library has `module` files, as a `module` file, with the guard's own Lean program appended (the names `mainT` and `LRAFix.mainT`,
as the guard prints the plain and the namespace-qualified name). The program's output is read with the guard's own parser and checked
against the expectation; then each fixture is decided against F2 (one lemma of the file proved by sorry) as the reference proof, with
the guard's own rule (finer_sorry.decide). Nothing is written into the environments: the files go to --out, outside them, and are
compiled with `lake env lean` from the environment's folder.

    python3 tests/finer_lean/run_fixtures.py --envs /path/to/envs [--only mathlib-v4.26.0,...] [--fixtures F1,F5] [--variants plain]
                                            [--jobs 2] [--timeout 900] [--wrap "systemd-run --user --scope ... --"] [--json OUT]
exit 0: every check passed; 1: some check failed; 2: nothing ran."""
from __future__ import annotations

import argparse, json, os, re, shlex, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import finer_sorry as F  # noqa: E402

NAMES = ["mainT", "LRAFix.mainT"]
# per environment: the plain file's header, the `module` file's (where the library is built as modules), and an imported constant
# of the library that rests on sorry (F8; none known in the others)
ENVS = {
    "mathlib-v4.26.0": {"plain": "import Mathlib"},
    "mathlib-v4.27.0": {"plain": "import Mathlib"},
    "arklib-v4.29.0": {"plain": "import ArkLib.Data.Fin.Basic", "imported": "Fin.sumCases", "imported_term": "Fin.sumCases.{0}"},   # before v4.30: the program walks imports; .{0}: its motive is a Sort
    "strata-v4.29.1": {"plain": "import Strata.Languages.Laurel.ResolutionProps",
                       "module": "module\n\npublic import Strata.Languages.Laurel.ResolutionProps\n\npublic section"},
    "cslib-v4.31.0": {"plain": "import Cslib", "module": "module\n\npublic import Cslib\n\npublic section"},
    "arklib-v4.31.0": {"plain": "import ArkLib.Commitments.Functional.Hachi.Sumcheck.Rounds",
                       "imported": "ArkLib.Lattices.Ajtai.InnerOuter.roundExtractor"},
    "physlib-v4.32.0": {"plain": "import Physlib.QFT.PerturbationTheory.WickContraction.Perm",
                        "module": "module\n\npublic import Physlib.QFT.PerturbationTheory.WickContraction.Perm\n\npublic section",
                        "imported": "WickContraction.Perm.isFull_of_isFull"},
    "cslib-v4.33.0-rc2": {"plain": "import Cslib", "module": "module\n\npublic import Cslib\n\npublic section"},
    "leanpool-v4.35.0-rc3": {"plain": "import LeanPool", "module": "module\n\npublic import LeanPool\n\npublic section"},
}
DECIDE_AGAINST = "F2"   # the reference proof of the decision column
WANT_DECISION = {"F1": True, "F2": True, "F3": False, "F4": False, "F5": False, "F6": False, "F7": True, "F8": False, "F9": False, "F10": False,
                 "F11": False, "F12": True, "F13": True, "F14": True}
SORRY_MSG = re.compile(r"\bdeclaration uses\b.*\bsorry", re.DOTALL)


def fixtures(only=None) -> dict:
    out = {}
    for p in sorted(HERE.glob("fixtures/F*.lean"), key=lambda p: int(re.match(r"F(\d+)", p.name).group(1))):
        fid = p.name.split("_")[0]
        if only and fid not in only:
            continue
        text = p.read_text()
        m = re.search(r"^-- expect: (\{.*\})$", text, re.M)
        out[fid] = {"path": p, "text": text, "expect": json.loads(m.group(1))}
    return out


def build(fx: dict, header: str, imported: str | None, nonce: str, lean_import: bool = False) -> tuple[str, int, int, int]:
    """(file text, the program's first line, D's first line, the proof text's first line: the line after the fixture's `-- proof`
    line, as the guard passes the first line after the library file's prefix). `lean_import`: with Lean's command elaborator
    imported, as the guard's finer_reading retries when the program did not run (finer_sorry.with_lean_import)."""
    body = fx["text"].replace("@HEADER@", header).replace("@IMPORTED@", imported or "")
    head = (F.with_lean_import(body) if lean_import else body).rstrip() + "\n\n"
    first = head.count("\n") + 1
    lines = head.splitlines()
    dline = next(i + 1 for i, l in enumerate(lines) if re.search(r"\b(theorem|def) mainT(?![\w.])", l))
    pline = next(i + 2 for i, l in enumerate(lines) if l.strip() == "-- proof")
    return head + F.program(NAMES, nonce, pline), first, dline, pline


def run_one(env_dir: Path, path: Path, wrap: list, timeout: int) -> tuple[list, float, str]:
    elan = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan") / "bin"
    env = dict(os.environ, PATH=f"{elan}:{os.environ.get('PATH', '')}")
    t0 = time.time()
    try:
        p = subprocess.run(wrap + ["lake", "env", "lean", "--json", str(path)], cwd=env_dir, env=env, capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return [], time.time() - t0, "timeout"
    msgs = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                msgs.append(json.loads(line))
            except ValueError:
                pass
    return msgs, time.time() - t0, ("" if p.returncode == 0 else f"lean exit {p.returncode}: {p.stderr[-300:]}")


def check(fid: str, fx: dict, parsed: dict, msgs: list, dline: int, first: int, imported: str | None, variant: str, ver: str) -> list:
    """The failed checks ([] = pass)."""
    exp = dict(fx["expect"])
    if variant == "module" and ver < "v4.30":   # the program refuses: imported bodies are not loaded there
        return [] if "error" in parsed and "module file before v4.30" in parsed["error"] else [f"expected the program to refuse: {parsed}"]
    if "error" in parsed:
        return [f"no reading: {parsed['error']}"]
    if variant == "module":   # a `where` auxiliary is private in a `module` file: the program names it so
        for k in ("sources", "own"):
            if k in exp:
                exp[k] = [s + F.PRIVATE_TAG if s in exp.get("private_in_module", []) else s for s in exp[k]]
    ms = parsed["markers"]
    bad = []
    if sorted(m["q"] for m in ms) != sorted(NAMES):
        bad.append(f"markers for {[m['q'] for m in ms]}, want one per name {NAMES} (unresolved: {parsed['end']['unresolved']})")
    if len({m["decl"] for m in ms}) != 1:
        bad.append(f"the names resolved to {sorted({m['decl'] for m in ms})}")
    srcs = sorted(set().union(*(m["sources"] for m in ms)))
    own = sorted(set().union(*(m["own"] for m in ms)))
    want = [s.replace("@IMPORTED@", imported or "") for s in exp.get("sources", srcs)]
    if "sources" in exp and srcs != sorted(want):
        bad.append(f"sources {srcs}, want {sorted(want)}")
    if "own" in exp and own != sorted(exp["own"]):
        bad.append(f"own {own}, want {sorted(exp['own'])}")
    if "own_prefix" in exp and (not own or not all(o == exp["own_prefix"] or o.startswith(exp["own_prefix"] + ".") for o in own)
                                or set(srcs) - set(own)):
        bad.append(f"own {own} (sources {srcs}): want every source OWN under {exp['own_prefix']}")
    if "local" in exp and sorted(set().union(*(m["local"] for m in ms))) != sorted(exp["local"]):
        bad.append(f"local {sorted(set().union(*(m['local'] for m in ms)))}, want {exp['local']}")
    if "decl" in exp and {m["decl"] for m in ms} != {exp["decl"]}:
        bad.append(f"decl {sorted({m['decl'] for m in ms})}, want {exp['decl']}")
    ax = "sorryAx" in set().union(*(m["axioms"] for m in ms))
    if "sorryAx" in exp and ax != exp["sorryAx"]:
        bad.append(f"sorryAx among the axioms: {ax}, want {exp['sorryAx']}")
    msg = any(SORRY_MSG.search(str(m.get("data", ""))) and dline <= ((m.get("pos") or {}).get("line") or 0) < first for m in msgs)
    if "sorry_message" in exp and msg != exp["sorry_message"]:
        bad.append(f"Lean's sorry message on D: {msg}, want {exp['sorry_message']}")
    errs = [m for m in msgs if m.get("severity") == "error"]
    if errs:
        bad.append(f"errors: {[str(e.get('data'))[:120] for e in errs[:2]]}")
    return bad


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--envs", default=str(ROOT / "envs"), help="the folder of the library environments (default: the package's envs/)")
    ap.add_argument("--only", default="", help="environments, comma-separated (default: every one listed in ENVS that exists)")
    ap.add_argument("--fixtures", default="", help="fixtures, comma-separated (F1,F5,...)")
    ap.add_argument("--variants", default="plain,module")
    ap.add_argument("--jobs", type=int, default=2, help="compiles at once (default 2)")
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--wrap", default="", help="a command prefix for each compile (e.g. a memory-capped systemd-run scope)")
    ap.add_argument("--out", default="", help="folder for the compiled files (default: a new temp folder)")
    ap.add_argument("--json", default="", help="write the results here")
    a = ap.parse_args(argv)
    envs_dir = Path(a.envs)
    names = [n for n in (a.only.split(",") if a.only else ENVS) if n]
    fxs = fixtures(set(a.fixtures.split(",")) if a.fixtures else None)
    out = Path(a.out or tempfile.mkdtemp(prefix="lra-finer-fixtures-"))
    out.mkdir(parents=True, exist_ok=True)
    wrap = shlex.split(a.wrap)
    jobs = []
    for en in names:
        cfg, ed = ENVS.get(en), envs_dir / en
        if cfg is None or not (ed / "lean-toolchain").exists():
            print(f"skip {en}: {'not configured' if cfg is None else 'no environment at ' + str(ed)}")
            continue
        for var in a.variants.split(","):
            if var not in cfg:
                continue
            for fid, fx in fxs.items():
                if fid == "F8" and not cfg.get("imported"):
                    continue
                jobs.append((en, var, fid))
    if not jobs:
        print("nothing to run")
        return 2
    results, lock = [], threading.Lock()

    def compile_fixture(en, var, fid, lean_import):
        cfg = ENVS[en]
        nonce = F.new_nonce()
        text, first, dline, pline = build(fxs[fid], cfg[var], cfg.get("imported_term") or cfg.get("imported"), nonce, lean_import)
        path = out / f"{en}__{var}__{fid}{'__import' if lean_import else ''}.lean"
        path.write_text(text)
        msgs, secs, err = run_one(envs_dir / en, path, wrap, a.timeout)
        parsed = F.parse(msgs, first, nonce, pline) if not err or msgs else {"error": err}
        prog_errs = [m for m in msgs if m.get("severity") == "error" and ((m.get("pos") or {}).get("line") or 0) >= first]
        return msgs, secs, err, parsed, first, dline, prog_errs

    def go(j):
        en, var, fid = j
        msgs, secs, err, parsed, first, dline, prog_errs = compile_fixture(en, var, fid, False)
        lean_import = False
        if "error" in parsed and prog_errs:   # the guard's finer_reading retries once with Lean's command elaborator imported
            first_try = (str(prog_errs[0].get("data"))[:100], round(secs, 1))
            msgs, secs2, err, parsed, first, dline, prog_errs = compile_fixture(en, var, fid, True)
            secs, lean_import = secs + secs2, first_try
        cfg = ENVS[en]
        fails = check(fid, fxs[fid], parsed, msgs, dline, first, cfg.get("imported"), var, en.split("-", 1)[1])
        ms = parsed.get("markers") or []
        r = {"env": en, "variant": var, "fixture": fid, "ok": not fails, "fails": fails, "wall_s": round(secs, 1),
             "program_ms": (parsed.get("end") or {}).get("ms"), "decl": sorted({m["decl"] for m in ms}),
             "sources": sorted(set().union(*(m["sources"] for m in ms))) if ms else None,
             "own": sorted(set().union(*(m["own"] for m in ms))) if ms else None, "error": parsed.get("error"),
             "n_local": max((m.get("n_local", 0) for m in ms), default=None), "n_frontier": max((m.get("n_frontier", 0) for m in ms), default=None),
             "walked": (parsed.get("end") or {}).get("walked"), "stored": (parsed.get("end") or {}).get("stored"),
             "lean_import": lean_import, "lean_exit": err[:200],
             "reading": {"markers": ms, "end": parsed.get("end")} if ms else {"error": parsed.get("error")}}
        with lock:
            results.append(r)
            print(f"{en:22} {var:6} {fid:4} {'PASS' if r['ok'] else 'FAIL'} {r['wall_s']:7.1f} s program {r['program_ms']} ms "
                  f"sources={r['sources']} own={r['own']}" + (" (with the Lean import)" if lean_import else "")
                  + (f" {fails}" if fails else ""), flush=True)
    with ThreadPoolExecutor(max_workers=max(1, a.jobs)) as ex:
        list(ex.map(go, jobs))
    # the rule on real readings: each fixture as the proof, F2 as the reference proof, per environment and variant; and each fixture
    # against itself (as its own reference): OK exactly when it has no OWN source (F11: a library lemma `mainT.aux` is not OWN)
    by = {(r["env"], r["variant"], r["fixture"]): r for r in results}
    dec_fail = 0
    for (en, var, fid), r in sorted(by.items()):
        if "error" in r["reading"]:
            continue
        sok, swhy, _ = F.decide(r["reading"], r["reading"])
        r["decision_self"] = "OK" if sok else "BAD"
        if sok != (not r["own"]):
            dec_fail += 1
            r["ok"] = False
            r["fails"].append(f"decision against itself: {'OK' if sok else 'BAD'} with OWN {r['own']} ({swhy})")
        ref = by.get((en, var, DECIDE_AGAINST))
        if ref is None or "error" in ref["reading"]:
            continue
        ok, why, _ = F.decide(r["reading"], ref["reading"])
        r["decision_vs_F2"] = "OK" if ok else "BAD"
        r["decision_why"] = why
        if fid in WANT_DECISION and ok != WANT_DECISION[fid]:
            dec_fail += 1
            r["ok"] = False
            r["fails"].append(f"decision vs {DECIDE_AGAINST}: {'OK' if ok else 'BAD'}, want {'OK' if WANT_DECISION[fid] else 'BAD'} ({why})")
    n_ok = sum(r["ok"] for r in results)
    print(f"\n{n_ok} of {len(results)} fixture compiles pass (decisions checked against {DECIDE_AGAINST}; {dec_fail} wrong)")
    for r in sorted(results, key=lambda r: (r["env"], r["variant"], int(r["fixture"][1:]))):
        print(f"  {r['env']:22} {r['variant']:6} {r['fixture']:4} {'PASS' if r['ok'] else 'FAIL'} wall {r['wall_s']:6.1f} s, program "
              f"{r['program_ms']} ms, vs F2 {r.get('decision_vs_F2', '-')}: sources {r['sources']} own {r['own']}"
              + (" [with the Lean import]" if r["lean_import"] else "")
              + (f" error {r['error']}" if r["error"] else "") + ("" if r["ok"] else f"  FAILED: {r['fails']}"))
    if a.json:
        Path(a.json).write_text(json.dumps(results, indent=1))
    return 0 if n_ok == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
