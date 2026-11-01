# Regular closed gradient ranges

**Author: Tao Hu**

A Lean 4 formalization of Theorem 1.1 of [*Regular closed gradient ranges and asymptotic gradient values*, arXiv:2609.05951v1](https://arxiv.org/abs/2609.05951v1).

## Mathematical statement

For every integer $n\geq 1$ and every nonzero, compactly supported $C^1$ function $f:\mathbb{R}^n\to\mathbb{R}$, the gradient range is regular closed:

$$\{\nabla f(x):x\in\mathbb{R}^n\}=\overline{\mathrm{int}\{\nabla f(x):x\in\mathbb{R}^n\}}.$$

The formal statement uses Mathlib's Euclidean space, gradient, compact support, interior and closure. Its hypotheses are precisely dimension at least one, continuous differentiability, nonzeroness and compact support. It assumes no symplectic rigidity result or analytic existence theorem.

## Formalization

Codex prepared this formalization from the paper's original informal proof and the existing Lean development. Earlier Aristotle-assisted proof components are retained with their full proofs and checked again locally. The gradient-graph argument uses a proved finite-dimensional variational argument for zero-section rigidity. The complete proof dependencies for Theorem 1.1 are included here.

- [Challenge.lean](Challenge.lean) states the result using only canonical Mathlib notions.
- [Solution.lean](Solution.lean) proves exactly the same statement.
- [GradientRanges/Theorem11.lean](GradientRanges/Theorem11.lean) assembles the mathematical proof.
- [Audit.lean](Audit.lean) rejects every transitive axiom except `propext`, `Quot.sound` and `Classical.choice`.
- [comparator.json](comparator.json) selects `PalomarGradientRanges.theorem_1_1` for statement comparison and independent NanoDa replay.

The Challenge contains the one deliberate proof hole required for statement/proof comparison. Production proofs and definitions must contain no proof holes or custom axioms. Theorems 1.2 and 1.4 and Corollary 1.3 are outside this repository's advertised scope.

## Local verification

The project pins Lean **4.35.0** and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (the canonical `v4.35.0` release). The complete dependency graph is fixed by `lake-manifest.json`.

On Linux x86_64, install `elan`, `git`, `curl`, a C/C++ toolchain, `zstd`, Python 3.11 or 3.12 with `venv` support, and `bubblewrap`. The metadata check installs a hash-pinned PyYAML dependency in its own ignored virtual environment and runs the unchanged official Palomar metadata validator at the recorded commit. Its dependency hashes include the official PyPI Python 3.12 Linux wheel for Ubuntu 24.04. On Windows, use a checkout in the Linux filesystem inside WSL2. Run from the repository root:

```sh
elan toolchain install "$(cat lean-toolchain)"
bash scripts/verify.sh
```

The script checks the source layout and metadata, obtains the matching Mathlib cache, builds the project and axiom audit, and runs the sandboxed Comparator with NanoDa enabled. It also attempts the advisory con-ron replay using Palomar's pinned checker update, downloading its authenticated Lean release archive on first use (up to 700 MiB). An advisory decline is recorded separately from proof acceptance. A nonzero script exit means verification failed. Detailed logs are written under the ignored `verification/local/` directory.

Verification is performed locally on Ubuntu 24.04 x86_64. This repository does not require GitHub Actions. The full proof passed compilation, the axiom audit, statement comparison and independent kernel replay. The exact results and fresh-checkout evidence are recorded in [verification/RESULTS.md](verification/RESULTS.md).

## Provenance, review and scope

The mathematical source is Tao Hu's arXiv manuscript, specifically Theorem 1.1 and its proof in Section 3. No manuscript TeX source is included. See [formalization.yaml](formalization.yaml) for authorship, automation, provenance and review disclosures, and [docs/STATEMENT-AUDIT.md](docs/STATEMENT-AUDIT.md) for the source-to-statement correspondence.

### Errata and deviations

Theorem 1.1 has no statement correction, extra hypothesis or weakened conclusion. The proof supplies the zero-section rigidity ingredient through its included finite-dimensional variational proof. This proof-route difference is recorded in [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).

This repository is being prepared for later Palomar submission. A private repository cannot be registered while it remains private. No Palomar registration or editorial acceptance is claimed.

## License and acknowledgements

Code is distributed under [Apache-2.0](LICENSE). Lean and Mathlib provide the underlying proof infrastructure. Development guidance was consulted from [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills). See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
