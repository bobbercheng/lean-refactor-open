import json, subprocess, os, sys
d = json.load(open(sys.argv[1]))
for name, e in d.items():
    want = e.get("commit") if isinstance(e, dict) else None
    p = f"envs/{name}"
    if not os.path.isdir(p):
        print(f"{name:24s} want {str(want)[:9]}  MISSING"); continue
    have = subprocess.run(["git", "-c", "safe.directory=*", "-C", p, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    ok = bool(want) and have.startswith(want[:9])
    print(f"{name:24s} want {str(want)[:9]} have {have[:9]} {'OK' if ok else '<-- MISMATCH'}")
