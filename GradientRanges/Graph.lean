module

public import GradientRanges.C0Invariance
public import GradientRanges.ZeroSectionRigid
public import GradientRanges.Flow
public import GradientRanges.Shear
public import GradientRanges.Mollify

@[expose] public section

/-!
# Lemma 3.1: rigidity of gradient graphs
-/

open Set Metric Filter Topology
open scoped ContDiff

namespace GradRange

variable {n : ℕ}

/-- The shear `ψ_f(x,p) = (x, p + ∇f(x))` as a homeomorphism. -/
noncomputable def shear (f : E n → ℝ) (hf : ContDiff ℝ 1 f) : P n ≃ₜ P n where
  toFun z := (z.1, z.2 + gradient f z.1)
  invFun z := (z.1, z.2 - gradient f z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    have := continuous_gradient_of_contDiff f hf
    fun_prop
  continuous_invFun := by
    have := continuous_gradient_of_contDiff f hf
    fun_prop

/-- For `f ∈ C¹`, `ψ_f` is a symplectic homeomorphism. -/
theorem shear_isSymplecticHomeomorph (f : E n → ℝ) (hf : ContDiff ℝ 1 f) :
    IsSymplecticHomeomorph (shear f hf) := by
  obtain ⟨g, hgs, hconv⟩ := exists_smooth_gradient_approx f hf
  refine ⟨fun k => shearMap (g k), fun k => isSymplecticDiffeo_shearMap (g k) (hgs k), ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hconv ⊢
  intro S hS
  have hT := hconv _ (hS.image continuous_fst)
  rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
  intro ε hε
  filter_upwards [hT ε hε] with k hk
  intro z hz
  have := hk z.1 ⟨z, hz, rfl⟩
  simp only [shear, shearMap, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Prod.dist_eq,
    dist_self, dist_add_left]
  rw [max_eq_right dist_nonneg]
  exact this

/-- The gradient graph of a `C¹` function is closed. -/
theorem isClosed_gradGraph (f : E n → ℝ) (hf : ContDiff ℝ 1 f) : IsClosed (gradGraph f) := by
  have hc := continuous_gradient_of_contDiff f hf
  have : gradGraph f = {z : P n | z.2 = gradient f z.1} := by
    ext z
    simp only [gradGraph, mem_range, mem_setOf_eq]
    constructor
    · rintro ⟨x, rfl⟩; rfl
    · intro h; exact ⟨z.1, by rw [← h]⟩
  rw [this]
  exact isClosed_eq continuous_snd (hc.comp continuous_fst)

theorem shear_image_zeroSection (f : E n → ℝ) (hf : ContDiff ℝ 1 f) :
    shear f hf '' zeroSection n = gradGraph f := by
  ext z
  simp only [mem_image, zeroSection, mem_setOf_eq, gradGraph, mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.1, ?_⟩
    simp [shear, hw]
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), rfl, by simp [shear]⟩

/-- **Lemma 3.1.** For `f ∈ C¹(ℝⁿ)` and every bounded open `U ⊆ ℝ²ⁿ` meeting `Γ_f`,
`e(U, Γ_f) > 0`.

The boundedness hypothesis is kept as in the paper; the proof gives the conclusion for every
open `U` meeting `Γ_f`, so the hypothesis is not needed. The proof combines the rigidity of the
zero section (`ZSV.zeroSection_rigid_variational`, proved by the discrete action functional, without Floer
theory) with Usher's `C⁰`-invariance (`isDisplacementRigid_image`, proved in `C0Invariance.lean`). -/
theorem lemma_3_1 (f : E n → ℝ) (hf : ContDiff ℝ 1 f) (U : Set (P n)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUΓ : (U ∩ gradGraph f).Nonempty) :
    displacementEnergy U (gradGraph f) ≠ 0 := by
  have hZ : IsClosed (zeroSection n) := isClosed_eq continuous_snd continuous_const
  have h := isDisplacementRigid_image (zeroSection n) hZ ZSV.zeroSection_rigid_variational (shear f hf)
    (shear_isSymplecticHomeomorph f hf)
  rw [shear_image_zeroSection f hf] at h
  exact h U hU hUΓ

end GradRange
