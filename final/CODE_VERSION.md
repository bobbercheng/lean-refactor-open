# Code version (open track)

| | |
|---|---|
| package in this folder | commit `2dcf255fd9aaf5dbc426ec7a13a38ee1b4168b47` (branch `open-clean`), release export of 2026-11-02 (99 files, export leak scan: pass, 0 hits) |
| code of our official run 2 | commit `748d964cd4704dfee32314db18f0a093d4c21e18` (exact export: tag `open-run2-exact-748d964c`) |
| difference | `f0225b2d` removes switched-off code only; `2dcf255f` corrects README text (11 workers, context cap and stagger on by default) and one help string |

## Removed in `f0225b2d` (every item was off under our run command)
- The opt-in style step: `--style-rw*`, the `style` command, `harness/style_rw_open.py`, its example file, `probe/open_style/replay.py`.
- The opening-message dialect card: `--dialect-card`, agent.py `--open-card`, `harness/open_card_dialect.md`. (The model-free dialect
  PASS of the end stage, `--dialect`, is active and stays.)
- The blind start: `--blind-start` in the driver and agent.py, `harness/blind_facts.py`.
- The THINK LONGER nudge: agent.py `--think-prompt`.
- `method_flags.json` now records only `end_pipe_writeback`; an output directory of the earlier code still resumes.

## Why the run is the same
Checked against `748d964c` with the official run's arguments: the parsed options (apart from the removed ones, all off or default), the
session commands and environment, the run clock at 1,728 points, the driver's stage calls and files, the export on a fixture that
exercises every fallback, and agent.py sessions against a scripted model (every request body byte-identical: system prompt sha16
`bbfdbae9756a2915`, tool list `67ceb7f48a3cc48e`, same opening messages, same trajectories and workspace state). Two independent reviews
found no change that can act under the run command. The release smoke from the export tree (the $0 dry run with a fake model) passed.
