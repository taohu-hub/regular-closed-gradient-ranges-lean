# Source-to-statement correspondence

Source: Tao Hu, *Regular closed gradient ranges and asymptotic gradient values*, [arXiv:2609.05951v1](https://arxiv.org/abs/2609.05951v1), Section 1, definition of a bump and Theorem 1.1; Section 3, proof of Theorem 1.1.

The paper defines a bump as a nonzero function with compact support. It states the regular-closed gradient-range conclusion for every dimension at least one and every continuously differentiable bump.

The exact compared export is `PalomarGradientRanges.theorem_1_1` in `Challenge.lean` and `Solution.lean`.

| Lean binder | Classification | Source correspondence |
| --- | --- | --- |
| `n : ℕ` | SOURCE | The finite Euclidean dimension. |
| `hn : 1 ≤ n` | SOURCE | The source explicitly assumes dimension at least one. |
| `f : EuclideanSpace ℝ (Fin n) → ℝ` | SOURCE | The source function on real Euclidean n-space. |
| `hf : ContDiff ℝ 1 f` | SOURCE | The source's continuously differentiable hypothesis. |
| `hne : f ≠ 0` | SOURCE | Nonzeroness in the source definition of a bump. |
| `hsupp : HasCompactSupport f` | SOURCE | Compact support in the same definition. |

Counts: SOURCE 6, STANDING 0, TYPING 0, RULED 0, EXCESS 0. There are no additional implicit or instance binders in the compared declaration.

The conclusion is `Set.range (gradient f) = closure (interior (Set.range (gradient f)))`. Both sides use canonical Mathlib objects. The Euclidean carrier uses the usual inner product, rather than the supremum norm on a coordinate function type. Mathlib's gradient is the Riesz representation of the Fréchet derivative; the C1 hypothesis ensures differentiability throughout the source domain.

The compared type contains no project-defined predicate, abstract gradient, rigidity premise, analytic existence assumption, or result bundle. Its only project-owned name is the theorem name itself. The proof must supply all auxiliary results.

The Challenge's deliberate proof hole records the statement to be compared. It is never imported by the production proof. `Solution.lean` imports the full included proof and must pass the axiom audit, Comparator statement check, Lean kernel check and independent NanoDa replay.

Status: this correspondence received independent AI source review. The unchanged compared declaration passed the axiom audit, Comparator statement comparison, Lean kernel check and independent NanoDa replay, including in a fresh Git checkout. See [verification/RESULTS.md](../verification/RESULTS.md) for the evidence and scope.
