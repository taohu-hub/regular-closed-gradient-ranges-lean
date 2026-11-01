module
public import GradientRanges.Asymptotic
public import GradientRanges.Projection
public import GradientRanges.Graph

@[expose] public section

open Set Metric Filter Topology
open scoped ContDiff

namespace GradRange
variable {n : ℕ}

theorem snd_image_gradGraph (f : E n → ℝ) : Prod.snd '' gradGraph f = gradRange f := by
  ext p
  simp [gradGraph, gradRange]

/-- Key step of Theorem 1.2: a gradient value which is not an asymptotic value lies in
`closure (int G_f)`. -/
theorem mem_closure_interior_of_not_mem_asymptoticValues (f : E n → ℝ) (hf : ContDiff ℝ 1 f)
    (p₀ : E n) (hp : p₀ ∈ gradRange f) (hpA : p₀ ∉ asymptoticValues f) :
    p₀ ∈ closure (interior (gradRange f)) := by
  obtain ⟨r, hr, R, hR, hfar⟩ := exists_away_of_not_mem_asymptoticValues f p₀ hpA
  rw [← snd_image_gradGraph]
  refine lemma_2_2 (gradGraph f) (isClosed_gradGraph f hf)
    (fun U hU hUb hUΓ => lemma_3_1 f hf U hU hUb hUΓ) p₀ (by rwa [snd_image_gradGraph]) r hr ?_
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_gradGraph f hf).inter (isClosed_closedBall.preimage continuous_snd)
  · apply (Metric.isBounded_closedBall (x := ((0 : E n), p₀)) (r := max R r)).subset
    rintro z ⟨⟨x, rfl⟩, hz⟩
    simp only [mem_preimage, mem_closedBall] at hz
    have hx : ‖x‖ < R := by
      by_contra h
      push_neg at h
      exact absurd hz (not_le.mpr (hfar x h))
    rw [mem_closedBall, Prod.dist_eq]
    simp only [dist_zero_right]
    exact max_le (le_max_of_le_left hx.le) (le_max_of_le_right hz)

/-- **Theorem 1.1.** For a `C¹` bump `f` on `ℝⁿ`, `G_f = closure (int G_f)`. -/
theorem theorem_1_1 (f : E n → ℝ) (hf : ContDiff ℝ 1 f) (hne : f ≠ 0)
    (hsupp : HasCompactSupport f) :
    gradRange f = closure (interior (gradRange f)) := by
  have hc := isCompact_gradRange_bump f hf hsupp
  apply le_antisymm
  · intro p hp
    by_cases hpA : p ∈ asymptoticValues f
    · have h0 : p = 0 := asymptoticValues_bump_subset f hsupp hpA
      subst h0
      exact subset_closure (zero_mem_interior_gradRange_bump f hf hne hsupp)
    · exact mem_closure_interior_of_not_mem_asymptoticValues f hf p hp hpA
  · calc closure (interior (gradRange f)) ⊆ closure (gradRange f) :=
          closure_mono interior_subset
      _ = gradRange f := hc.isClosed.closure_eq


end GradRange
