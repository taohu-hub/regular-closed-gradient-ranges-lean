# Local verification record

Status: **all local checks passed**, including from a fresh Git checkout, on 2026-11-01.

The release uses Lean 4.35.0 and canonical Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Verification runs locally on Ubuntu 24.04 x86_64 with bubblewrap sandboxing and NanoDa enabled.

The tested command was `bash scripts/verify.sh`. The fresh checkout initially contained no `.lake` directory: dependencies were materialized at the pinned revisions, the canonical Mathlib cache was obtained, and every project module was compiled anew. The script exited with code 0 and left the checkout's tracked files unchanged.

| Check | Result |
| --- | --- |
| Source layout and statement identity | Passed; 21 Lean module sources |
| Production proof holes and custom axioms | None |
| Official pinned Palomar metadata validator | Accepted |
| Full `lake build`, including `Audit` | Passed; 9,071 build jobs |
| Challenge/Solution Comparator | `Your solution is okay!` |
| NanoDa independent replay | Accepted |
| Lean kernel replay | Accepted |
| Advisory con-ron replay | Accepted; 55,583 declarations, `--verified`, two workers |
| Independent AI source review | No unresolved finding; see [review](../docs/REVIEW.md) |

The exported theorem's complete axiom set is:

```text
[propext, Classical.choice, Quot.sound]
```

The Challenge has exactly one deliberate statement-only proof hole. It is not imported by the production proof. No production theorem or definition has an admitted proof.

The unchanged official metadata validator and advisory checker policy were taken from PalomarSubmission commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. The con-ron update was authenticated by both its release archive and binary SHA-256; its exact provenance and verdict are in [con-ron.json](con-ron.json). This advisory check supplements the mandatory Lean and NanoDa checks.

The final 30 proof, configuration and verifier files match the tested fresh checkout byte for byte. Their individual SHA-256 values are in [source-hashes.json](source-hashes.json). Documentation and status records were finalized after the checks; the final metadata was validated again. The SHA-256 of the sorted Lean-source hash listing is `04084baa50fb4b6bab188b7a30ff9deddcf5a00c5019f709c61a9b04e4420c63` (each entry is the file SHA-256, two spaces, its relative path and LF, sorted by relative path).

See [report.json](report.json) and [kernel-verdicts.txt](kernel-verdicts.txt) for compact machine-readable evidence and output excerpts. Running the documented script regenerates detailed logs under the ignored `verification/local/` directory.

This is local verification, rather than a Palomar registration or Palomar-hosted execution-profile report. The private repository is intended for later submission after its owner elects to make it public. No independent human peer review or registry acceptance is claimed.
