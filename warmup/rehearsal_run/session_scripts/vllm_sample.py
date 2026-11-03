"""Samples vLLM /metrics through the bridge every 15 s for 10 min: running/waiting, KV usage, generation and prompt token rates,
finished reasons; then histogram means (TTFT, inter-token latency, e2e, prefill, decode, queue) from the deltas."""
import re, time, urllib.request, pathlib, json
K = pathlib.Path.home().joinpath(".config/vexorium/vllm_api_key").read_text().strip()
def get():
    t = urllib.request.urlopen(urllib.request.Request("http://127.0.0.1:8000/metrics", headers={"Authorization": f"Bearer {K}"}), timeout=30).read().decode()
    d = {}
    for l in t.splitlines():
        if l.startswith("vllm:"):
            m = re.match(r"(vllm:[a-z_:]+)(\{[^}]*\})?\s+([-0-9.e+]+)", l)
            if m: d[m.group(1) + (m.group(2) or "")] = float(m.group(3))
    return d
def g(d, name, extra=""):
    return sum(v for k, v in d.items() if k.startswith(name + "{") and extra in k)
s0 = get(); t0 = time.time(); runs, kv = [], []
for _ in range(40):
    time.sleep(15); s = get(); runs.append(g(s, "vllm:num_requests_running")); kv.append(g(s, "vllm:kv_cache_usage_perc"))
s1, dt = s, time.time() - t0
gen = (g(s1, "vllm:generation_tokens_total") - g(s0, "vllm:generation_tokens_total")) / dt
pr = (g(s1, "vllm:prompt_tokens_total") - g(s0, "vllm:prompt_tokens_total")) / dt
hit = (g(s1, "vllm:prefix_cache_hits_total") - g(s0, "vllm:prefix_cache_hits_total")) / max(1, g(s1, "vllm:prefix_cache_queries_total") - g(s0, "vllm:prefix_cache_queries_total"))
fin = {r: g(s1, "vllm:request_success_total", f'finished_reason="{r}"') - g(s0, "vllm:request_success_total", f'finished_reason="{r}"') for r in ("stop", "length")}
out = {"window_s": round(dt), "gen_tok_s": round(gen, 1), "prompt_tok_s": round(pr, 1), "prefix_hit": round(hit, 3), "running_mean": round(sum(runs) / len(runs), 2),
       "running_min_max": [min(runs), max(runs)], "kv_mean": round(sum(kv) / len(kv), 3), "kv_max": round(max(kv), 3), "finished": fin,
       "per_stream_gen_tok_s": round(gen / max(0.1, sum(runs) / len(runs)), 1)}
for h in ("time_to_first_token_seconds", "inter_token_latency_seconds", "time_per_output_token_seconds", "e2e_request_latency_seconds",
          "request_queue_time_seconds", "request_prefill_time_seconds", "request_decode_time_seconds", "request_generation_tokens", "request_prompt_tokens"):
    ds, dc = g(s1, f"vllm:{h}_sum") - g(s0, f"vllm:{h}_sum"), g(s1, f"vllm:{h}_count") - g(s0, f"vllm:{h}_count")
    if dc > 0: out[h + "_mean"] = round(ds / dc, 4)
print(json.dumps(out, indent=1))
