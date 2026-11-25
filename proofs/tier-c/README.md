# The tier C proof file

Labels: (M) measured, (C) computed.

[`proofs.jsonl`](proofs.jsonl) holds our proofs of the 60 final problems as our report's tier C counts them
([report](https://openreview.net/forum?id=cvXHNZWtn8)): one JSON object per
line, with the fields `name` and `proof`. Its sha256 is

```
391c880ae869678d84a93f222324807d8417f6eb66b2b7e29055dbafb4219f0a
```

the same hash the report's pins table prints. The release `open-camready-20261124` holds the same file as an asset,
byte-identical (asset `vexorium-open-tier-c-proofs-20261124.jsonl`). Added on 2026-11-24.

## What it is

The file of our report's tier C: the submitted file `sub43` with four problems' proofs taken from a separate chain of post-step
passes. It was prepared but never uploaded, so the Arena never graded it.

It is not our final upload. `sub43` is the upload, and its proof file is not in this repository
([`RESULTS.md`](../../RESULTS.md), section "Final result").

## Measured

- Stored mean on our meter: 81.4367 (M).
- One fresh read of all 60 proofs (2026-11-24): 81.4217, all 60 rows read, with 16 listed items on 13 rows, the same as for tier
  B's input (M). See [`RESULTS.md`](../../RESULTS.md), section "The tier C file, re-checked".
- The axiom guard of tag `open-camready-20261124` (`final/harness/axiom_guard.py`; this version's differs from it only in names
  and comments), run on a copy that held these 60 proofs byte for byte (with each row's stored score added): exit code 0, 60 of 60 pass, no proof changed (M). Its first read, the second
  after the machine started from a deallocated state (the first was of another file), left 11 rows not read (398 s, 21 compile
  timeouts; exit code 3, every row kept).
  See [`RESULTS.md`](../../RESULTS.md), section "The axiom guard on the measured outputs".
- The word `sorry` does not occur in the file (C).

## How it was made, and what that means

The proofs start from the competition's seed proofs and were edited by the open model in our official run 3, by the model-free
end stage and by our post-step; one row (`FTheory.SU5.ChargeSpectrum.containsPhenoCompletionsOfMinimallyAllows_viableCompletions`) is the seed
proof unchanged. Four problems' proofs come from a separate chain of post-step passes. The post-step's ops
were written after the final problems were released, most of them after study of closed-model proofs of those problems; see
[`DISCLOSURES.md`](../../DISCLOSURES.md), section "Provenance". The number this file gives is therefore in sample and not free of
that work; the result that does not depend on the post-step is the job's export.

No published command rebuilds this exact file: the records of the chain that made those four problems' proofs are not in
this repository.

## Terms

The proofs start from the competition's seed proofs (the upstream libraries' proofs) and include the model's edits; see
[`NOTICE.md`](../../NOTICE.md) for the terms of each.
