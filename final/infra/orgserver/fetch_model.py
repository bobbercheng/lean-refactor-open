#!/usr/bin/env python3
"""The pinned checkpoint into a Hugging Face cache, and its check (2026-10-31; README.md, setup.sh step "model").





"""
from __future__ import annotations

import argparse, json, os, sys, time
from pathlib import Path

REPO = "wtdcode/GLM-5.3-Flash-AWQ-W4A16"
REV = "abd7b07719111f137e1de8a0c1b7e01c11b74d1a"
NEED = ("config.json", "generation_config.json", "tokenizer.json", "tokenizer_config.json", "chat_template.jinja")                                                                        


def snapshot_dir(hf_home: Path, repo: str, rev: str) -> Path:
    return Path(hf_home) / "hub" / ("models--" + repo.replace("/", "--")) / "snapshots" / rev


def verify(hf_home: Path, repo: str = REPO, rev: str = REV) -> tuple[bool, str]:
    d = snapshot_dir(hf_home, repo, rev)
    if not d.is_dir():
        return False, f"no snapshot {d}"
    miss = [n for n in NEED if not (d / n).is_file()]
    idx = d / "model.safetensors.index.json"
    shards: list[str] = []
    if idx.is_file():
        try:
            shards = sorted(set(json.loads(idx.read_text())["weight_map"].values()))
        except (ValueError, KeyError) as e:
            return False, f"unreadable {idx.name}: {e}"
    elif (d / "model.safetensors").is_file():
        shards = ["model.safetensors"]
    else:
        miss.append("model.safetensors.index.json")
    size = 0
    for s in shards:
        p = d / s
        if not p.is_file() or p.stat().st_size == 0:
            miss.append(s)
        else:
            size += p.stat().st_size
    if miss:
        return False, f"{d}: {len(miss)} file(s) missing or empty, e.g. {miss[:3]}"
    return True, f"{d}: {len(shards)} shard(s), {size / 1e9:.1f} GB"


def download(hf_home: Path, repo: str, rev: str, retries: int) -> None:
    os.environ["HF_HOME"] = str(hf_home)
    os.environ.pop("HF_HUB_OFFLINE", None)
    try:
        import hf_transfer              
        os.environ.setdefault("HF_HUB_ENABLE_HF_TRANSFER", "1")
    except ImportError:
        os.environ.pop("HF_HUB_ENABLE_HF_TRANSFER", None)
    from huggingface_hub import snapshot_download
    for k in range(1, retries + 1):
        try:
            p = snapshot_download(repo_id=repo, revision=rev, max_workers=16)
            print(f"download done: {p}", flush=True)
            return
        except Exception as e:                                                                      
            print(f"download attempt {k}/{retries} failed: {type(e).__name__}: {e}", flush=True)
            if k == retries:
                raise
            time.sleep(30 * k)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--hf-home", required=True)
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--rev", default=REV)
    ap.add_argument("--verify-only", action="store_true")
    ap.add_argument("--retries", type=int, default=3)
    ap.add_argument("--print-path", action="store_true", help="on success print only the snapshot directory (messages to stderr)")
    a = ap.parse_args(argv)
    hf = Path(a.hf_home)
    say = (lambda m: print(m, file=sys.stderr)) if a.print_path else print
    if not a.verify_only:
        ok, msg = verify(hf, a.repo, a.rev)
        if ok:
            say(f"model already complete: {msg}")
            if a.print_path:
                print(os.path.abspath(snapshot_dir(hf, a.repo, a.rev)))                                                         
            return 0
        download(hf, a.repo, a.rev, a.retries)
    ok, msg = verify(hf, a.repo, a.rev)
    say(f"model {'ok' if ok else 'INCOMPLETE'}: {msg}")
    if ok and a.print_path:
        print(os.path.abspath(snapshot_dir(hf, a.repo, a.rev)))                                                         
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
