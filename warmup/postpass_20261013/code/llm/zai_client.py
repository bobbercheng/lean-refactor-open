"""Thin client for GLM models on z.ai's Anthropic-compatible endpoint.
Dev-only: outputs are NOT eligible for the Track 2 bank (see config/models.yaml)."""
from __future__ import annotations

import os, time
from pathlib import Path
from dataclasses import dataclass

import anthropic

BASE_URL = "https://api.z.ai/api/anthropic"


def _key() -> str:
    p = Path(os.environ.get("ZAI_KEY_FILE", "~/.config/vexorium/glm_api_key")).expanduser()
    return p.read_text().strip()


@dataclass
class Completion:
    text: str
    thinking_chars: int
    input_tokens: int
    output_tokens: int
    stop_reason: str
    seconds: float


def complete(prompt: str, *, model: str = "glm-5.3-flash", system: str | None = None,
             max_tokens: int = 32768, temperature: float = 1.0, top_p: float = 0.95,
             reasoning_effort: str | None = None, retries: int = 6) -> Completion:
    client = anthropic.Anthropic(api_key=_key(), base_url=BASE_URL, timeout=3600, max_retries=0)
    kw: dict = dict(model=model, max_tokens=max_tokens, temperature=temperature, top_p=top_p,
                    messages=[{"role": "user", "content": prompt}])
    if system:
        kw["system"] = system
    if reasoning_effort:
        kw["extra_body"] = {"reasoning_effort": reasoning_effort}
    last = None
    for attempt in range(retries):
        t0 = time.time()
        try:
            with client.messages.stream(**kw) as s:
                msg = s.get_final_message()
            text = "".join(b.text for b in msg.content if getattr(b, "type", "") == "text")
            think = sum(len(getattr(b, "thinking", "") or "") for b in msg.content if getattr(b, "type", "") == "thinking")
            return Completion(text, think, msg.usage.input_tokens, msg.usage.output_tokens,
                              str(msg.stop_reason), time.time() - t0)
        except anthropic.RateLimitError as e:
            last = e
            time.sleep(min(20 * (2 ** attempt), 300))  # 20, 40, 80, 160, 300 s
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(5 * (attempt + 1))
    raise RuntimeError(f"z.ai request failed after {retries} attempts: {last}")
