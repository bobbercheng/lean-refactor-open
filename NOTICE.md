# Notices

Our own code, notes and run records in this repository are licensed under the PolyForm Noncommercial License 1.0.0
(see [`LICENSE`](LICENSE)): free for study, research and other noncommercial use. Commercial use needs a separate license:
contact b.cheng@vexorium.net.

The following material was not written by us. It keeps its own terms, and the license above does not cover it.

| Material | Where | Terms |
|---|---|---|
| Lean source files of upstream libraries (ArkLib, Strata, cslib, PhysLean), copied as problem context | `**/context.lean`, the per-problem state folders and run trajectories | the upstream projects' licenses; the copied files keep their copyright headers (Apache 2.0 where stated) |
| Competition problems, seed proofs, reference proofs and heartbeat data (incl. PutnamBench statements) | `**/data/benchmark_*.jsonl`, problem statements and seed proofs in run records | the competition organizers' and the original sources' terms |
| Model outputs (GLM-5.3-Flash, AWQ W4A16) | run trajectories, logs and the per-problem state | recorded as produced; the model's license terms apply |
| The model checkpoint and the serving image | referenced by name and revision in `warmup/README.md` and `warmup/infra/vast/`; not included | their publishers' terms |

## Edits for public release (2026-10-28)

The history of this repository was rewritten once before it was made public. Every commit keeps its date and content, except:

- home-directory paths read `/home/user` (also in logs and trajectories), and the user name in `ls -l` output reads `user`;
- one shell result in a trajectory (`warmup/probe/runs/fresh-a100-p5/`, interleaved row) listed the home directory of the machine
  that ran the driver; that listing is replaced by a note, and the JSON line stays valid;
- vast.ai instance and machine ids read `<instance>` and `<machine>`;
- the three A100 operation diaries (`warmup/docs/a100_poc_log.md`, `warmup/docs/a100_80_babysit.md`,
  `warmup/accounting/a100_poc.md`: rentals, bids, credit and host details) were deleted; `warmup/` still cites them as sources, and
  we keep them in our private development repository;
- internal notes were removed from comments, docstrings, help texts, log messages and docs; the code's behaviour is unchanged
  (same syntax tree apart from help-text strings and log messages);
- the provenance paragraphs of `README.md` and `warmup/README.md` were made more precise about how the harness was developed;
- model-facing prompts and recorded trajectories are unchanged apart from the items above.
