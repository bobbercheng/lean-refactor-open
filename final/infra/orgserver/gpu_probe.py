#!/usr/bin/env python3
"""What the vLLM server will see, run INSIDE the image by run.sh / setup.sh (lib.sh lra_gpu_check; 2026-11-01). Standard library only.



"""
from __future__ import annotations

import importlib.util, os, re, shutil, subprocess, sys

TP = 4                                                               


def load_nvml():
    try:
        spec = importlib.util.find_spec("vllm")                                                          
        for d in (spec.submodule_search_locations or []) if spec else []:
            p = os.path.join(d, "third_party", "pynvml.py")
            if os.path.isfile(p):
                s = importlib.util.spec_from_file_location("_lra_pynvml", p)
                m = importlib.util.module_from_spec(s)
                s.loader.exec_module(m)
                return m, "vllm.third_party.pynvml"
    except Exception:                
        pass
    try:
        import pynvml                 
        return pynvml, "pynvml"
    except Exception:                
        return None, None


def visible(n: int) -> list[int]:
    cvd = os.environ.get("CUDA_VISIBLE_DEVICES")
    if cvd is not None and re.fullmatch(r"\s*\d+\s*(,\s*\d+\s*)*", cvd):
        return [int(x) for x in cvd.split(",") if int(x) < n]
    return list(range(n))


def by_nvml() -> int | None:
    m, src = load_nvml()
    if m is None:
        return None
    try:
        m.nvmlInit()
        ids = visible(m.nvmlDeviceGetCount())
        hs = {i: m.nvmlDeviceGetHandleByIndex(i) for i in ids}
        lines = []                                                                                                                     
        for i in ids:                                                                                                   
            name = m.nvmlDeviceGetName(hs[i])
            lines.append(f"GPU {i}: {name.decode() if isinstance(name, bytes) else name}")
        first = ids[:TP]
        full = len(first) > 1 and all(m.nvmlDeviceGetP2PStatus(hs[a], hs[b], m.NVML_P2P_CAPS_INDEX_NVLINK) == m.NVML_P2P_STATUS_OK
                                      for k, a in enumerate(first) for b in first[k + 1:])
        lines.append(f"NVLINK {int(full)} (NVML P2P NVLink status of GPUs {first}, {src})")
        print("\n".join(lines))
        return 0 if ids else 1
    except Exception as e:                
        print(f"NVML: {type(e).__name__}: {e}", file=sys.stderr)
        return None


def by_smi() -> int:
    path = os.environ.get("PATH", "") + ":/opt/udiImage/bin:/opt/udiImage/modules/gpu/bin:/usr/local/nvidia/bin:/usr/bin:/bin"
    smi = shutil.which("nvidia-smi", path=path)
    if not smi:
        print("no NVML library and no nvidia-smi in this environment", file=sys.stderr)
        return 1
    try:
        lst = subprocess.run([smi, "-L"], capture_output=True, text=True, timeout=120).stdout
        topo = subprocess.run([smi, "topo", "-m"], capture_output=True, text=True, timeout=120).stdout
    except (OSError, subprocess.SubprocessError) as e:
        print(f"nvidia-smi: {e}", file=sys.stderr)
        return 1
    gpus = [l for l in lst.splitlines() if re.match(r"GPU \d+:", l)]
    keep = set(visible(len(gpus)))
    for l in gpus:
        if int(l.split()[1].rstrip(":")) in keep:
            print(re.sub(r" \(UUID.*", "", l))
    print(f"NVLINK {int(bool(re.search(r'(?m)^GPU\d.*\bNV\d+', topo)))} (nvidia-smi topo -m)")
    return 0 if keep else 1


def main() -> int:
    rc = by_nvml()
    return by_smi() if rc is None else rc


if __name__ == "__main__":
    raise SystemExit(main())
