module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Support

/-- Theorem 1.1 of arXiv:2609.05951: the gradient range of a nonzero,
compactly supported C¹ function on Euclidean n-space is regular closed. -/
public theorem PalomarGradientRanges.theorem_1_1
    (n : ℕ) (hn : 1 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hne : f ≠ 0) (hsupp : HasCompactSupport f) :
    Set.range (gradient f) = closure (interior (Set.range (gradient f))) := by
  sorry
