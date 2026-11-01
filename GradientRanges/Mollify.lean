module

public import GradientRanges.Defs

@[expose] public section

/-!
# Smooth approximation of a `C¹` function in the `C¹` topology on compact sets

Mollifications `f_ν` of a cut-off of `f` are smooth and `∇f_ν → ∇f` locally uniformly.
-/

open Set Metric Filter Topology MeasureTheory
open scoped ContDiff

namespace GradRange

variable {n : ℕ}

theorem exists_smooth_gradient_approx (f : E n → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ g : ℕ → E n → ℝ, (∀ k, ContDiff ℝ ∞ (g k)) ∧
      TendstoLocallyUniformly (fun k => gradient (g k)) (gradient f) atTop := by
  let χ : ℕ → ContDiffBump (0 : E n) := fun k => ⟨(k:ℝ) + 1, (k:ℝ) + 2, by positivity, by linarith⟩
  let φ : ℕ → ContDiffBump (0 : E n) := fun k =>
    ⟨1 / (2 * ((k:ℝ) + 1)), 1 / ((k:ℝ) + 1), by positivity, by
      apply one_div_lt_one_div_of_lt (by positivity); linarith⟩
  let ft : ℕ → E n → ℝ := fun k x => χ k x * f x
  let g : ℕ → E n → ℝ := fun k =>
    convolution ((φ k).normed volume) (ft k) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hftc : ∀ k, ContDiff ℝ 1 (ft k) := fun k => ((χ k).contDiff).mul hf
  have hftcs : ∀ k, HasCompactSupport (ft k) := fun k => (χ k).hasCompactSupport.mul_right
  have hgs : ∀ k, ContDiff ℝ ∞ (g k) := by
    intro k
    exact (φ k).hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _
      (φ k).contDiff_normed ((hftc k).continuous.locallyIntegrable)
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  -- derivative of the mollification
  have hgd : ∀ k x, fderiv ℝ (g k) x =
      convolution ((φ k).normed volume) (fderiv ℝ (ft k)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro k x
    have h := (hftcs k).hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      ((φ k).integrable_normed (μ := volume)).locallyIntegrable (hftc k) x
    rw [h.fderiv]
    simp only [convolution]
    congr 1
  -- on large balls, `fderiv (ft k) = fderiv f`
  have hft_eq : ∀ (k : ℕ) (y : E n), ‖y‖ < (k:ℝ) + 1 → fderiv ℝ (ft k) y = fderiv ℝ f y := by
    intro k y hy
    apply Filter.EventuallyEq.fderiv_eq
    have : (χ k : E n → ℝ) =ᶠ[𝓝 y] 1 :=
      (χ k).eventuallyEq_one_of_mem_ball (by rw [mem_ball, dist_zero_right]; exact hy)
    filter_upwards [this] with z hz
    simp only [ft, hz, Pi.one_apply, one_mul]
  refine ⟨g, hgs, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huc := (isCompact_closedBall (0 : E n) (|R| + 1)).uniformContinuousOn_of_continuous
    hD.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδD⟩ := huc (ε / 2) (by positivity)
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max (|R| + 1) (1 / δ))
  filter_upwards [eventually_ge_atTop k₀] with k hk
  intro x hx
  have hxR : ‖x‖ ≤ |R| := by
    have := hR hx
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_abs_self R]
  have hk' : (max (|R| + 1) (1 / δ)) < (k:ℝ) + 1 := by
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hrOut : (φ k).rOut < δ := by
    show 1 / ((k:ℝ) + 1) < δ
    rw [div_lt_iff₀ (by positivity)]
    have := lt_of_le_of_lt (le_max_right _ _) hk'
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hrOut1 : (φ k).rOut ≤ 1 := by
    show 1 / ((k:ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]; linarith
  have hbound := (φ k).dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := ε / 2)
    (g := fderiv ℝ (ft k)) ((hftc k).continuous_fderiv (by norm_num)).aestronglyMeasurable (by
      intro y hy
      rw [mem_ball] at hy
      have hyx : ‖y‖ < |R| + 1 + 0 := by
        have := norm_le_norm_add_norm_sub' y x
        rw [← dist_eq_norm] at this
        linarith
      rw [hft_eq k y (by linarith [le_max_left (|R| + 1) (1 / δ)]),
        hft_eq k x (by linarith [le_max_left (|R| + 1) (1 / δ)])]
      apply le_of_lt
      apply hδD y (by rw [mem_closedBall, dist_zero_right]; linarith)
        x (by rw [mem_closedBall, dist_zero_right]; linarith)
      linarith)
  rw [← hgd, hft_eq k x (by linarith [le_max_left (|R| + 1) (1 / δ)])] at hbound
  have hiso : dist (gradient f x) (gradient (g k) x) = dist (fderiv ℝ f x) (fderiv ℝ (g k) x) := by
    simp only [gradient]
    exact (InnerProductSpace.toDual ℝ (E n)).symm.dist_map _ _
  rw [hiso, dist_comm]
  linarith

end GradRange
