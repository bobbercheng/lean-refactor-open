"""OpenAI-chat-compatible client path for harness/agent.py (self-hosted vLLM / SGLang, or OpenRouter's /chat/completions).

The agent keeps its conversation in the Anthropic Messages shape (content blocks: text / thinking / tool_use / tool_result).
This module converts that shape to OpenAI chat messages + function tools, makes one non-streaming request, and returns an
object that quacks like the subset of `anthropic.types.Message` the agent uses: `.content` (blocks with .type/.text/.name/
.input/.id/.thinking and .model_dump()), `.stop_reason` (end_turn | tool_use | max_tokens) and `.usage` (input/output tokens).

Reasoning: vLLM/SGLang with `--reasoning-parser glm45` return the model's thinking in `message.reasoning_content`
(OpenRouter: `message.reasoning`); it is kept as a `thinking` block and sent back inside the content as <think>...</think> so the chat template
renders the real reasoning for earlier turns instead of an empty <think></think>.
"""
from __future__ import annotations

import json
import re
import time
import uuid
from dataclasses import dataclass, field
from typing import Any

import requests


@dataclass
class Block:
    type: str
    text: str | None = None
    thinking: str | None = None
    name: str | None = None
    input: dict | None = None
    id: str | None = None

    def model_dump(self, exclude_none: bool = True) -> dict:
        d = {"type": self.type, "text": self.text, "thinking": self.thinking, "name": self.name, "input": self.input, "id": self.id}
        return {k: v for k, v in d.items() if v is not None} if exclude_none else d


@dataclass
class Usage:
    input_tokens: int = 0
    output_tokens: int = 0


@dataclass
class Message:
    content: list = field(default_factory=list)
    stop_reason: str = "end_turn"
    usage: Usage = field(default_factory=Usage)
    provider: str | None = None
    raw_finish_reason: str | None = None


class OpenAIChatError(Exception):
    def __init__(self, status: int, body: str):
        super().__init__(f"Error code: {status} - {body[:300]}")
        self.status_code = status


def tools_to_openai(tools: list[dict]) -> list[dict]:
    return [{"type": "function", "function": {"name": t["name"], "description": t.get("description", ""), "parameters": t.get("input_schema", {"type": "object"})}} for t in tools]


def messages_to_openai(system: str, msgs: list[dict]) -> list[dict]:
    out: list[dict] = [{"role": "system", "content": system}]
    for m in msgs:
        role, content = m["role"], m["content"]
        if isinstance(content, str):
            out.append({"role": role, "content": content}); continue
        if role == "assistant":
            text = "".join(b.get("text", "") for b in content if b.get("type") == "text")
            # Pass earlier thinking back as <think>...</think> inside the content: GLM's chat template splits it out as
            # reasoning_content, and renders an empty <think></think> when none is given — after a few such turns the
            # model stops thinking (A100 POC: 36% of turns with ~240 chars vs 65% / ~3.9k chars via the Anthropic path).
            think = "".join(b.get("thinking", "") for b in content if b.get("type") == "thinking")
            if think:
                text = f"<think>{think}</think>" + text
            calls = [{"id": b["id"], "type": "function", "function": {"name": b["name"], "arguments": json.dumps(b.get("input") or {}, ensure_ascii=False)}}
                     for b in content if b.get("type") == "tool_use"]
            msg: dict[str, Any] = {"role": "assistant", "content": text or None}
            if calls:
                msg["tool_calls"] = calls
            out.append(msg)
        else:  # user: tool results and/or plain text blocks
            for b in content:
                if b.get("type") == "tool_result":
                    c = b.get("content")
                    if isinstance(c, list):
                        c = "".join(x.get("text", "") for x in c)
                    out.append({"role": "tool", "tool_call_id": b["tool_use_id"], "content": c if isinstance(c, str) else json.dumps(c)})
                elif b.get("type") == "text":
                    out.append({"role": "user", "content": b.get("text", "")})
    return out


_GLM_CALL = re.compile(r"<tool_call>\s*([^<\s]+)\s*(.*?)</tool_call>", re.S)
_GLM_ARG = re.compile(r"<arg_key>(.*?)</arg_key>\s*<arg_value>(.*?)</arg_value>", re.S)


def parse_glm_tool_calls(text: str) -> tuple[str, list[Block]]:
    """GLM-5.x tool-call markup (chat template): <tool_call>name<arg_key>k</arg_key><arg_value>v</arg_value>…</tool_call>; string values are
    raw, other types JSON. Used for budget-forced continuations, where vLLM's reasoning parser labels the whole output as reasoning (no
    </think> in the output) and its tool parser therefore never sees the calls (2026-10-08). Returns (text outside the calls, tool_use blocks)."""
    blocks: list[Block] = []
    for m in _GLM_CALL.finditer(text or ""):
        args: dict[str, Any] = {}
        for k, v in _GLM_ARG.findall(m.group(2)):
            v = v.strip("\n")
            if v[:1] in "[{" or v in ("true", "false", "null") or re.fullmatch(r"-?\d+(\.\d+)?", v or "x"):
                try:
                    args[k.strip()] = json.loads(v); continue
                except json.JSONDecodeError:
                    pass
            args[k.strip()] = v
        blocks.append(Block(type="tool_use", name=m.group(1).strip(), input=args, id=f"call_{uuid.uuid4().hex[:12]}"))
    return _GLM_CALL.sub("", text or "").strip(), blocks


def create(*, base_url: str, api_key: str, model: str, max_tokens: int, system: str, tools: list[dict], messages: list[dict],
           extra_body: dict | None = None, timeout=(30, 3600)) -> Message:   # 2026-10-08: 900 s cut non-streamed high-effort answers on a saturated A100 (13-55% retried, biased to short outputs)   # (connect, read) — read = max silence while a generation is awaited; a 24k-token turn at ~44 tok/s is ~9 min
    body: dict[str, Any] = {"model": model, "max_tokens": max_tokens, "messages": messages_to_openai(system, messages),
                            "stream": False}
    if tools:   # vLLM rejects an empty tools array with HTTP 400 (2026-10-07: the LR eval's tool-less calls all failed)
        body.update(tools=tools_to_openai(tools), tool_choice="auto")
    if extra_body:
        body.update(extra_body)
    url = base_url.rstrip("/") + "/chat/completions"
    r = requests.post(url, headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}, json=body, timeout=timeout)
    if r.status_code == 400 and "maximum context length" in r.text:
        # Window guard (A100 POC 2026-10-06: escalated 18-24k caps on 107k+ prompts overflowed a 131k window and the harness
        # retried the same 400 twenty times): shrink max_tokens to what fits and retry once, immediately.
        m_ = re.search(r"maximum context length is (\d+) tokens.*?contains at least (\d+) input tokens", r.text, re.S)
        if m_:
            fit = int(m_.group(1)) - int(m_.group(2)) - 256
            if fit >= 512:
                body["max_tokens"] = fit
                r = requests.post(url, headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}, json=body, timeout=timeout)
    if r.status_code != 200:
        raise OpenAIChatError(r.status_code, r.text)
    j = r.json()
    if "error" in j and not j.get("choices"):
        raise OpenAIChatError(int((j["error"] or {}).get("code") or 500), json.dumps(j["error"])[:300])
    ch = j["choices"][0]; msg = ch.get("message") or {}
    blocks: list[Block] = []
    think = msg.get("reasoning_content") or msg.get("reasoning")
    if think:
        blocks.append(Block(type="thinking", thinking=think))
    if msg.get("content"):
        blocks.append(Block(type="text", text=msg["content"]))
    for tc in msg.get("tool_calls") or []:
        fn = tc.get("function") or {}
        try:
            args = json.loads(fn.get("arguments") or "{}")
        except json.JSONDecodeError:
            args = {"_raw_arguments": fn.get("arguments")}
        blocks.append(Block(type="tool_use", name=fn.get("name"), input=args if isinstance(args, dict) else {"value": args},
                            id=tc.get("id") or f"call_{uuid.uuid4().hex[:12]}"))
    fr = ch.get("finish_reason")
    stop = "max_tokens" if fr == "length" else ("tool_use" if (fr == "tool_calls" or any(b.type == "tool_use" for b in blocks)) else "end_turn")
    u = j.get("usage") or {}
    return Message(content=blocks, stop_reason=stop, usage=Usage(int(u.get("prompt_tokens") or 0), int(u.get("completion_tokens") or 0)),
                   provider=j.get("provider"), raw_finish_reason=fr)


if __name__ == "__main__":  # smoke test against OpenRouter's OpenAI endpoint: python3 llm/openai_compat.py
    import os, pathlib
    key = pathlib.Path("~/.config/vexorium/openrouter_api_key").expanduser().read_text().strip()
    t0 = time.time()
    m = create(base_url="https://openrouter.ai/api/v1", api_key=key, model="z-ai/glm-5.3-flash", max_tokens=200, system="You are terse.",
               tools=[{"name": "echo", "description": "echo a string", "input_schema": {"type": "object", "properties": {"s": {"type": "string"}}, "required": ["s"]}}],
               messages=[{"role": "user", "content": "Call the echo tool with s='ready'."}],
               extra_body={"reasoning": {"effort": "low"}, "provider": {"quantizations": ["nvfp4"], "allow_fallbacks": False}})
    print(m.stop_reason, m.provider, m.usage, [b.model_dump() for b in m.content], f"{time.time()-t0:.1f}s")
