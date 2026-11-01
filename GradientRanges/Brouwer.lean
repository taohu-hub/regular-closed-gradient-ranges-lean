module
import all Mathlib.Basic.Real.Basic

public import Mathlib
public meta import ProofAudit

@[expose] public section

/-!
# Brouwer's fixed point theorem and a linking lemma

Mathlib (at the pinned commit) does not contain Brouwer's fixed point theorem. We prove it
for closed balls of finite-dimensional real inner product spaces by the analytic argument:

* a `C¹` map `r` defined near the closed unit ball, equal to the identity on the sphere and
  taking values in the sphere, cannot exist (`no_smooth_retraction`): for small `τ` the map
  `x ↦ x + τ (r x - x)` is a diffeomorphism of the open ball, so by the change of variables
  formula `∫_B det(1 + τ (Dr - 1)) = vol B`; this is a polynomial identity in `τ`, so it also
  holds for `τ = 1`, where `det Dr = 0` because `r` takes values in the sphere;
* a continuous self-map of the closed ball without fixed points is mollified and turned into
  such a retraction (`brouwer_euclidean`).

The consequence used later is the linking lemma `exists_zero_of_boundary_close`: a continuous
map `g` of the closed ball of radius `R` with `‖g θ - θ‖ < R` on the boundary sphere has a
zero.
-/

open Set Metric MeasureTheory Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace GradRange.Brouwer

variable {d : ℕ}

local notation "Y" => EuclideanSpace ℝ (Fin d)

/-- `τ ↦ det (1 + τ B)` is a polynomial of degree at most `d`. -/
theorem exists_det_poly (B : Y →L[ℝ] Y) :
    ∃ p : ℝ[X], p.natDegree ≤ d ∧ ∀ τ : ℝ, p.eval τ = (1 + τ • B).det := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let M := LinearMap.toMatrix b b (B : _ →ₗ[ℝ] _)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin d) (Fin d) ℝ).map C), ?_, ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · intro τ
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    have h1 : Polynomial.eval τ
        (Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin d) (Fin d) ℝ).map C))
        = Matrix.det ((Polynomial.evalRingHom τ).mapMatrix
          ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin d) (Fin d) ℝ).map C)) := by
      rw [← RingHom.map_det]; rfl
    rw [h1]
    congr 1
    have h2 : LinearMap.toMatrix b b
        ((1 + τ • B : Y →L[ℝ] Y) : _ →ₗ[ℝ] _) = 1 + τ • M := by
      rw [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul, map_add, map_smul,
        ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id, LinearMap.toMatrix_id]
    rw [h2]
    ext i j
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]; ring

/-- If `∫_s det(1 + τ B x) dx = c` for all small `τ > 0`, then also for `τ = 1`. -/
theorem integral_det_eq_of_small (B : Y → (Y →L[ℝ] Y)) (s : Set Y)
    (hint : ∀ τ : ℝ, IntegrableOn (fun x => (1 + τ • B x).det) s)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (c : ℝ)
    (hc : ∀ τ ∈ Ioc 0 t₀, ∫ x in s, (1 + τ • B x).det = c) :
    ∫ x in s, (1 + B x).det = c := by
  classical
  let v : Fin (d+1) → ℝ := fun i => t₀ * ((i:ℝ) + 1) / ((d:ℝ) + 1)
  have hd1 : (0:ℝ) < (d:ℝ) + 1 := by positivity
  have hv_inj : Set.InjOn v (Finset.univ : Finset (Fin (d+1))) := by
    intro i _ j _ h
    simp only [v] at h
    rw [div_left_inj' hd1.ne', mul_right_inj' ht₀.ne'] at h
    exact Fin.ext (by exact_mod_cast (add_right_cancel h))
  have hv_mem : ∀ i, v i ∈ Ioc 0 t₀ := by
    intro i
    refine ⟨by positivity, ?_⟩
    simp only [v]
    rw [div_le_iff₀ hd1]
    have : ((i:ℕ):ℝ) + 1 ≤ (d:ℝ) + 1 := by
      have := i.isLt; exact_mod_cast (by omega : (i:ℕ) + 1 ≤ d + 1)
    nlinarith
  choose p hpdeg hpeval using fun x => exists_det_poly (B x)
  have key : ∀ x, (1 + B x).det =
      ∑ i, (Lagrange.basis Finset.univ v i).eval 1 * (1 + v i • B x).det := by
    intro x
    have hdeg : (p x).degree < (Finset.univ : Finset (Fin (d+1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact (Polynomial.degree_le_natDegree).trans_lt
        (by exact_mod_cast Nat.lt_succ_of_le (hpdeg x))
    have h := congrArg (Polynomial.eval 1) (Lagrange.eq_interpolate hv_inj hdeg)
    rw [Lagrange.interpolate_apply, eval_finset_sum] at h
    have h1 : (1 + B x).det = (p x).eval 1 := by rw [hpeval, one_smul]
    rw [h1, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_mul, eval_C, hpeval, mul_comm]
  simp_rw [key]
  rw [integral_finset_sum _ (fun i _ => (hint (v i)).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hc _ (hv_mem i)])]
  rw [← Finset.sum_mul, ← eval_finset_sum, Lagrange.sum_basis hv_inj Finset.univ_nonempty,
    eval_one, one_mul]

/-- If `‖r‖ = 1` near `x`, then `det (Dr x) = 0`. -/
theorem det_fderiv_eq_zero_of_norm_one (r : Y → Y) (x : Y) (hU : ∀ᶠ y in 𝓝 x, ‖r y‖ = 1)
    (hd : DifferentiableAt ℝ r x) : (fderiv ℝ r x).det = 0 := by
  have horth : ∀ v : Y, inner ℝ (r x) (fderiv ℝ r x v) = 0 := by
    intro v
    have h1 : HasDerivAt (fun τ : ℝ => r (x + τ • v)) (fderiv ℝ r x v) 0 := by
      have hl : HasDerivAt (fun τ : ℝ => x + τ • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
      have hd' : HasFDerivAt r (fderiv ℝ r x) (x + (0:ℝ) • v) := by simpa using hd.hasFDerivAt
      exact hd'.comp_hasDerivAt (0:ℝ) hl
    have h2 := h1.norm_sq
    have h3 : HasDerivAt (fun τ : ℝ => ‖r (x + τ • v)‖ ^ 2) 0 0 := by
      apply (hasDerivAt_const (0:ℝ) (1:ℝ)).congr_of_eventuallyEq
      have hc : Tendsto (fun τ : ℝ => x + τ • v) (𝓝 0) (𝓝 x) := by
        have : Continuous (fun τ : ℝ => x + τ • v) := by fun_prop
        simpa using this.tendsto 0
      filter_upwards [hc.eventually hU] with τ hτ
      simp [hτ]
    have := h2.unique h3
    simp at this
    simpa using this
  by_contra hdet
  have hu : IsUnit (fderiv ℝ r x : Y →ₗ[ℝ] Y) := by
    rw [LinearMap.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.2 hdet
  obtain ⟨v, hv⟩ := ((Module.End.isUnit_iff _).1 hu).2 (r x)
  have := horth v
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv, real_inner_self_eq_norm_sq] at this
  have h1 : ‖r x‖ = 1 := hU.self_of_nhds
  rw [h1] at this; norm_num at this

/-- A small perturbation of the identity has nonzero determinant. -/
theorem det_ne_zero_of_norm_lt (A : Y →L[ℝ] Y) (hA : ‖A‖ < 1) : (1 + A).det ≠ 0 := by
  have hinj : Function.Injective ((1 + A : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply] at hv
    have h1 : v = -A v := eq_neg_of_add_eq_zero_left hv
    have h2 : ‖v‖ ≤ ‖A‖ * ‖v‖ := by
      calc ‖v‖ = ‖A v‖ := by conv_lhs => rw [h1]
                             rw [norm_neg]
        _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    by_contra hv0
    have : 0 < ‖v‖ := norm_pos_iff.2 hv0
    nlinarith
  have hu : IsUnit ((1 + A : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) :=
    (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  rw [LinearMap.isUnit_iff_isUnit_det] at hu
  exact hu.ne_zero

/-- No `C¹` retraction of the closed unit ball onto its boundary sphere. -/
theorem no_smooth_retraction (O : Set Y) (hO : IsOpen O) (hB : closedBall (0:Y) 1 ⊆ O)
    (r : Y → Y) (hr : ContDiffOn ℝ 1 r O) (hS : ∀ x : Y, ‖x‖ = 1 → r x = x)
    (hn : ∀ x ∈ closedBall (0:Y) 1, ‖r x‖ = 1) : False := by
  have hdiff : DifferentiableOn ℝ r O := hr.differentiableOn one_ne_zero
  have hdiffAt : ∀ x ∈ O, DifferentiableAt ℝ r x :=
    fun x hx => (hdiff x hx).differentiableAt (hO.mem_nhds hx)
  have hcont' : ContinuousOn (fderiv ℝ r) O := hr.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ closedBall (0:Y) 1, ‖fderiv ℝ r x‖ ≤ M :=
    (isCompact_closedBall 0 1).exists_bound_of_continuousOn (hcont'.mono hB)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  have hlip : ∀ x ∈ closedBall (0:Y) 1, ∀ y ∈ closedBall (0:Y) 1,
      ‖r y - r x‖ ≤ M * ‖y - x‖ :=
    fun x hx y hy => (convex_closedBall 0 1).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hdiffAt z (hB hz)) hM hx hy
  set t₀ : ℝ := 1 / (2 * (M + 1)) with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  have ht₀M : t₀ * (M + 1) = 1 / 2 := by rw [ht₀def]; field_simp
  set B : Y → (Y →L[ℝ] Y) := fun x => fderiv ℝ r x - 1 with hBdef
  have hBn : ∀ x ∈ closedBall (0:Y) 1, ‖B x‖ ≤ M + 1 := fun x hx =>
    (norm_sub_le _ _).trans (add_le_add (hM x hx) ContinuousLinearMap.norm_id_le)
  have hsmallnorm : ∀ x ∈ closedBall (0:Y) 1, ∀ σ ∈ Icc 0 t₀, ‖σ • B x‖ < 1 := by
    intro x hx σ hσ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
    calc σ * ‖B x‖ ≤ t₀ * (M + 1) := mul_le_mul hσ.2 (hBn x hx) (norm_nonneg _) ht₀.le
      _ < 1 := by rw [ht₀M]; norm_num
  have hdet_pos : ∀ x ∈ closedBall (0:Y) 1, ∀ τ ∈ Icc 0 t₀, 0 < (1 + τ • B x).det := by
    intro x hx τ hτ
    by_contra hneg
    push_neg at hneg
    have hc : ContinuousOn (fun σ : ℝ => (1 + σ • B x).det) (Icc 0 τ) :=
      (ContinuousLinearMap.continuous_det.comp
        (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    have hiv := intermediate_value_Icc' hτ.1 hc
    have h0 : (0:ℝ) ∈ Icc ((1 + τ • B x).det) ((1 + (0:ℝ) • B x).det) := by
      refine ⟨hneg, ?_⟩
      have : (1 + (0:ℝ) • B x) = 1 := by ext; simp
      rw [this, ContinuousLinearMap.det, ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id,
        LinearMap.det_id]
      norm_num
    obtain ⟨σ, hσ, hσ0⟩ := hiv h0
    exact det_ne_zero_of_norm_lt _ (hsmallnorm x hx σ ⟨hσ.1, hσ.2.trans hτ.2⟩) hσ0
  have hsmall : ∀ τ ∈ Ioc 0 t₀, ∫ x in ball (0:Y) 1, (1 + τ • B x).det =
      volume.real (ball (0:Y) 1) := by
    intro τ hτ
    have hτ1 : τ ≤ 1 := by nlinarith [hτ.2, ht₀M]
    set F : Y → Y := fun x => x + τ • (r x - x) with hFdef
    have hFcd : ContDiffOn ℝ 1 F O := contDiffOn_id.add ((hr.sub contDiffOn_id).const_smul τ)
    have hF' : ∀ x ∈ O, HasFDerivAt F (1 + τ • B x) x := by
      intro x hx
      have := (hasFDerivAt_id x).add
        (((hdiffAt x hx).hasFDerivAt.sub (hasFDerivAt_id x)).const_smul τ)
      convert this using 1
      ext y
      simp only [F, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, id_eq]
    have hFc : ContinuousOn F (closedBall 0 1) := fun x hx =>
      (hF' x (hB hx)).continuousAt.continuousWithinAt
    have hsph : ∀ x : Y, ‖x‖ = 1 → F x = x := by
      intro x hx; simp [hFdef, hS x hx]
    have hmaps : ∀ x ∈ closedBall (0:Y) 1, F x ∈ closedBall (0:Y) 1 := by
      intro x hx
      have hx' : ‖x‖ ≤ 1 := by simpa using hx
      have hr1 := hn x hx
      rw [mem_closedBall, dist_zero_right]
      have : F x = (1 - τ) • x + τ • r x := by
        simp only [hFdef, smul_sub, sub_smul, one_smul]; abel
      rw [this]
      calc ‖(1 - τ) • x + τ • r x‖ ≤ (1 - τ) * ‖x‖ + τ * ‖r x‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), abs_of_nonneg hτ.1.le]
        _ ≤ 1 := by
          rw [hr1]; nlinarith [mul_nonneg (sub_nonneg.2 hτ1) (sub_nonneg.2 hx')]
    have hinj : InjOn F (closedBall 0 1) := by
      intro x hx y hy hxy
      by_contra hne
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have h1 : F x - F y = (1 - τ) • (x - y) + τ • (r x - r y) := by
        simp only [hFdef, smul_sub, sub_smul, one_smul]; abel
      have h2 : ‖F x - F y‖ ≥ (1 - τ) * ‖x - y‖ - τ * (M * ‖x - y‖) := by
        rw [h1]
        have := norm_sub_norm_le ((1 - τ) • (x - y)) (-(τ • (r x - r y)))
        rw [sub_neg_eq_add, norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hτ.1.le] at this
        have hl := hlip y hy x hx
        nlinarith [hτ.1]
      rw [hxy, sub_self, norm_zero] at h2
      have hτM : τ * (M + 1) ≤ 1 / 2 := by
        rw [← ht₀M]; exact mul_le_mul_of_nonneg_right hτ.2 (by linarith)
      have h3 : 0 < (1 - τ * (M + 1)) * ‖x - y‖ := mul_pos (by linarith) hpos
      have h4 : (1 - τ) * ‖x - y‖ - τ * (M * ‖x - y‖) = (1 - τ * (M + 1)) * ‖x - y‖ := by ring
      linarith
    have hFopen : IsOpen (F '' ball 0 1) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hxO : x ∈ O := hB (ball_subset_closedBall hx)
      have hs := (hFcd.contDiffAt (hO.mem_nhds hxO)).hasStrictFDerivAt one_ne_zero
      rw [(hF' x hxO).fderiv] at hs
      have hdet := (hdet_pos x (ball_subset_closedBall hx) τ ⟨hτ.1.le, hτ.2⟩).ne'
      have hsurj : LinearMap.range ((1 + τ • B x : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) = ⊤ := by
        have hu : IsUnit ((1 + τ • B x : Y →L[ℝ] Y) : Y →ₗ[ℝ] Y) := by
          rw [LinearMap.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.2 hdet
        exact LinearMap.range_eq_top.2 ((Module.End.isUnit_iff _).1 hu).2
      rw [← hs.map_nhds_eq_of_surj hsurj]
      exact image_mem_map (isOpen_ball.mem_nhds hx)
    have himg : F '' ball 0 1 = ball 0 1 := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := hmaps x (ball_subset_closedBall hx)
        rw [mem_ball, dist_zero_right]
        rw [mem_closedBall, dist_zero_right] at h1
        rcases h1.lt_or_eq with h | h
        · exact h
        · exfalso
          have := hinj (hmaps x (ball_subset_closedBall hx)) (ball_subset_closedBall hx)
            (hsph _ h)
          rw [mem_ball, dist_zero_right] at hx
          rw [this] at h; linarith
      · have hcl : IsClosed (F '' closedBall 0 1) :=
          ((isCompact_closedBall 0 1).image_of_continuousOn hFc).isClosed
        refine (isPreconnected_ball (x := (0:Y)) (r := 1)).subset_left_of_subset_union hFopen
          hcl.isOpen_compl ?_ ?_ ?_
        · rw [Set.disjoint_left]
          rintro _ ⟨x, hx, rfl⟩ h
          exact h ⟨x, ball_subset_closedBall hx, rfl⟩
        · intro y hy
          by_cases h : y ∈ F '' closedBall 0 1
          · obtain ⟨x, hx, rfl⟩ := h
            left
            rw [mem_closedBall, dist_zero_right] at hx
            rcases hx.lt_or_eq with h' | h'
            · exact ⟨x, by rwa [mem_ball, dist_zero_right], rfl⟩
            · rw [hsph x h', mem_ball, dist_zero_right, h'] at hy
              exact absurd hy (lt_irrefl _)
          · right; exact h
        · refine ⟨F 0, ?_, 0, mem_ball_self one_pos, rfl⟩
          rw [mem_ball, dist_zero_right]
          simp only [hFdef, sub_zero, zero_add, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hτ.1.le]
          rw [hn 0 (by simp)]
          have : t₀ < 1 := by nlinarith
          linarith [hτ.2]
    have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
      (fun x hx => (hF' x (hB (ball_subset_closedBall hx))).hasFDerivWithinAt)
      (hinj.mono ball_subset_closedBall) (fun _ => (1:ℝ))
    rw [himg, setIntegral_const, smul_eq_mul, mul_one] at hcv
    rw [hcv]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    simp only [smul_eq_mul, mul_one]
    exact (abs_of_pos (hdet_pos x (ball_subset_closedBall hx) τ ⟨hτ.1.le, hτ.2⟩)).symm
  have hint : ∀ τ : ℝ, IntegrableOn (fun x => (1 + τ • B x).det) (ball (0:Y) 1) := by
    intro τ
    have hBc : ContinuousOn B (closedBall (0:Y) 1) := by
      simpa only [B, Pi.sub_def] using (hcont'.mono hB).sub continuousOn_const
    have hscaled : ContinuousOn (fun x => τ • B x) (closedBall (0:Y) 1) := by
      simpa only [Pi.smul_def] using hBc.const_smul τ
    have : ContinuousOn (fun x => (1 + τ • B x).det) (closedBall (0:Y) 1) :=
      ContinuousLinearMap.continuous_det.comp_continuousOn
        (continuousOn_const.add hscaled)
    exact (this.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  have h1 := integral_det_eq_of_small B _ hint t₀ ht₀ _ hsmall
  have h2 : ∫ x in ball (0:Y) 1, (1 + B x).det = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [show (1 + B x) = fderiv ℝ r x from add_sub_cancel _ _]
    apply det_fderiv_eq_zero_of_norm_one r x _ (hdiffAt x (hB (ball_subset_closedBall hx)))
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hn y (ball_subset_closedBall hy)
  have hpos : 0 < volume.real (ball (0:Y) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

/-- A `C¹` self-map of a neighbourhood of the closed ball with values in the open ball and no
fixed point on the closed ball cannot exist: it would give a `C¹` retraction onto the sphere. -/
theorem no_smooth_fixedPointFree (g : Y → Y) (hg : ContDiff ℝ 1 g)
    (hlt : ∀ x ∈ closedBall (0:Y) 1, ‖g x‖ < 1) (hne : ∀ x ∈ closedBall (0:Y) 1, g x ≠ x) :
    False := by
  set w : Y → Y := fun x => x - g x with hw
  set a : Y → ℝ := fun x => inner ℝ x (w x) with ha
  set D : Y → ℝ := fun x => a x ^ 2 + ‖w x‖ ^ 2 * (1 - ‖x‖ ^ 2) with hD
  set lam : Y → ℝ := fun x => (-a x + Real.sqrt (D x)) / ‖w x‖ ^ 2 with hlam
  set r : Y → Y := fun x => x + lam x • w x with hr
  have hwc : ContDiff ℝ 1 w := contDiff_id.sub hg
  have hac : ContDiff ℝ 1 a := contDiff_id.inner ℝ hwc
  have hWc : ContDiff ℝ 1 (fun x => ‖w x‖ ^ 2) := (contDiff_norm_sq ℝ).comp hwc
  have hDc : ContDiff ℝ 1 D :=
    (hac.pow 2).add (hWc.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))
  set O : Set Y := {x | 0 < D x} ∩ {x | ‖w x‖ ^ 2 ≠ 0} with hO
  have hOopen : IsOpen O := (isOpen_lt continuous_const hDc.continuous).inter
    (isOpen_ne_fun hWc.continuous continuous_const)
  have hapos : ∀ x : Y, ‖x‖ = 1 → 0 < a x := by
    intro x hx
    have hx' : x ∈ closedBall (0:Y) 1 := by simp [hx]
    have h1 : a x = 1 - inner ℝ x (g x) := by
      simp only [ha, hw, inner_sub_right, real_inner_self_eq_norm_sq, hx]; ring
    have h2 : inner ℝ x (g x) ≤ ‖g x‖ := by
      have := real_inner_le_norm x (g x); rw [hx, one_mul] at this; exact this
    have := hlt x hx'
    linarith
  have hBO : closedBall (0:Y) 1 ⊆ O := by
    intro x hx
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    have hw0 : ‖w x‖ ^ 2 ≠ 0 := by
      have : w x ≠ 0 := sub_ne_zero.2 (hne x hx).symm
      positivity
    refine ⟨?_, hw0⟩
    show 0 < a x ^ 2 + ‖w x‖ ^ 2 * (1 - ‖x‖ ^ 2)
    rcases hx'.lt_or_eq with h | h
    · have : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have : 0 < ‖w x‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hw0)
      positivity
    · have := hapos x h
      rw [h]; nlinarith
  have hrc : ContDiffOn ℝ 1 r O := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hs : ContDiffAt ℝ 1 (fun x => Real.sqrt (D x)) x :=
      hDc.contDiffAt.sqrt hx.1.ne'
    have hl : ContDiffAt ℝ 1 lam x :=
      ((hac.contDiffAt.neg).add hs).div hWc.contDiffAt hx.2
    exact contDiffAt_id.add (hl.smul hwc.contDiffAt)
  have hnorm : ∀ x ∈ O, ‖r x‖ = 1 := by
    intro x hx
    have hsq : Real.sqrt (D x) ^ 2 = D x := Real.sq_sqrt hx.1.le
    have hlW : lam x * ‖w x‖ ^ 2 = -a x + Real.sqrt (D x) := by
      simp only [hlam]; rw [div_mul_cancel₀ _ hx.2]
    have h1 : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * ‖w x‖ ^ 2 := by
      simp only [hr, ha]
      rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have h2 : ‖r x‖ ^ 2 = 1 := by
      rw [h1]
      have : (‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * ‖w x‖ ^ 2) * ‖w x‖ ^ 2 = ‖w x‖ ^ 2 := by
        have e : (‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * ‖w x‖ ^ 2) * ‖w x‖ ^ 2
            = ‖x‖ ^ 2 * ‖w x‖ ^ 2 + 2 * a x * (lam x * ‖w x‖ ^ 2)
              + (lam x * ‖w x‖ ^ 2) ^ 2 := by ring
        rw [e, hlW]
        have hD' : D x = a x ^ 2 + ‖w x‖ ^ 2 * (1 - ‖x‖ ^ 2) := rfl
        nlinarith [hsq, hD']
      exact mul_right_cancel₀ hx.2 (by rw [this, one_mul])
    have := norm_nonneg (r x)
    nlinarith [h2]
  have hsph : ∀ x : Y, ‖x‖ = 1 → r x = x := by
    intro x hx
    have hax := hapos x hx
    have hDx : D x = a x ^ 2 := by simp only [hD, hx]; ring
    have : lam x = 0 := by
      simp only [hlam, hDx, Real.sqrt_sq hax.le]; ring
    simp [hr, this]
  exact no_smooth_retraction O hOopen hBO r hrc hsph (fun x hx => hnorm x (hBO hx))

/-- Brouwer's fixed point theorem for the closed unit ball of `ℝᵈ`. -/
theorem brouwer_euclidean (f : Y → Y) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0:Y) 1, f x = x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall (0:Y) 1).exists_isMinOn
    ⟨0, mem_closedBall_self zero_le_one⟩ ((hf.sub continuousOn_id).norm)
  set δ : ℝ := min ‖f x₀ - x₀‖ 1 with hδ
  have hδ0 : 0 < δ := lt_min (norm_pos_iff.2 (sub_ne_zero.2 (hcon x₀ hx₀))) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hdisp : ∀ x ∈ closedBall (0:Y) 1, δ ≤ ‖f x - x‖ := fun x hx =>
    (min_le_left _ _).trans (hmin hx)
  -- radial retraction onto the closed ball
  set π : Y → Y := fun x => (max 1 ‖x‖)⁻¹ • x with hπ
  have hπc : Continuous π := by
    have hc : Continuous (fun x : Y => (max (1 : ℝ) ‖x‖)⁻¹) :=
      (continuous_const.max continuous_norm).inv₀ (fun x => by positivity)
    exact continuous_smul.comp (hc.prodMk continuous_id)
  have hπB : ∀ x, π x ∈ closedBall (0:Y) 1 := by
    intro x
    rw [mem_closedBall, dist_zero_right, hπ, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]; exact le_max_right _ _
  have hπid : ∀ x ∈ closedBall (0:Y) 1, π x = x := by
    intro x hx
    have : ‖x‖ ≤ 1 := by simpa using hx
    simp [hπ, max_eq_left this]
  set f₁ : Y → Y := fun x => (1 - δ / 2) • f (π x) with hf₁
  have hf₁c : Continuous f₁ := by
    simpa only [f₁, Pi.smul_def, Function.comp_def] using
      (hf.comp_continuous hπc hπB).const_smul (1 - δ / 2)
  -- mollification
  have huc := (isCompact_closedBall (0:Y) 2).uniformContinuousOn_of_continuous hf₁c.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ρ, hρ, hρf⟩ := huc (δ / 4) (by positivity)
  set ρ' := min ρ 1 with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ one_pos
  let φ : ContDiffBump (0:Y) := ⟨ρ' / 2, ρ', by positivity, by linarith⟩
  set g : Y → Y := convolution (φ.normed volume) f₁ (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hg
  have hgc : ContDiff ℝ 1 g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf₁c.locallyIntegrable
  have hclose : ∀ x ∈ closedBall (0:Y) 1, dist (g x) (f₁ x) ≤ δ / 4 := by
    intro x hx
    apply φ.dist_normed_convolution_le hf₁c.aestronglyMeasurable
    intro y hy
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    have hy' : dist y x < ρ' := hy
    apply le_of_lt
    apply hρf y _ x (by rw [mem_closedBall, dist_zero_right]; linarith)
      (lt_of_lt_of_le hy' (min_le_left _ _))
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' y x
    rw [dist_eq_norm] at hy'
    linarith [min_le_right ρ 1]
  apply no_smooth_fixedPointFree g hgc
  · intro x hx
    have h1 := hclose x hx
    have h2 : ‖f₁ x‖ ≤ 1 - δ / 2 := by
      simp only [hf₁, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < 1 - δ / 2)]
      have := hmaps (hπB x)
      rw [mem_closedBall, dist_zero_right] at this
      nlinarith
    have := norm_le_norm_add_norm_sub' (g x) (f₁ x)
    rw [← dist_eq_norm] at this
    linarith
  · intro x hx heq
    have h1 := hclose x hx
    have h2 : ‖f x - f₁ x‖ ≤ δ / 2 := by
      simp only [hf₁, hπid x hx]
      rw [show f x - (1 - δ / 2) • f x = (δ / 2) • f x by rw [sub_smul, one_smul]; abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := hmaps hx
      rw [mem_closedBall, dist_zero_right] at this
      nlinarith
    have h3 := hdisp x hx
    rw [heq] at h1
    have : ‖f x - x‖ ≤ ‖f x - f₁ x‖ + ‖f₁ x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [dist_comm, dist_eq_norm] at h1
    linarith

/-- Brouwer's fixed point theorem for closed balls of finite-dimensional real inner product
spaces. -/
theorem brouwer {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (R : ℝ) (hR : 0 < R) (f : V → V)
    (hf : ContinuousOn f (closedBall 0 R)) (hmaps : MapsTo f (closedBall 0 R) (closedBall 0 R)) :
    ∃ x ∈ closedBall (0:V) R, f x = x := by
  let e := (stdOrthonormalBasis ℝ V).repr
  set f' : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    fun y => R⁻¹ • e (f (e.symm (R • y))) with hf'
  have hin : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) 1,
      e.symm (R • y) ∈ closedBall (0:V) R := by
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy ⊢
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  have hc : ContinuousOn f' (closedBall 0 1) := by
    have hc := e.continuous.comp_continuousOn
      (hf.comp (e.symm.continuous.comp (continuous_const_smul R)).continuousOn hin)
    simpa only [f', Pi.smul_def, Function.comp_def] using hc.const_smul R⁻¹
  have hm : MapsTo f' (closedBall 0 1) (closedBall 0 1) := by
    intro y hy
    have := hmaps (hin y hy)
    rw [mem_closedBall, dist_zero_right] at this ⊢
    rw [hf', norm_smul, LinearIsometryEquiv.norm_map, norm_inv, Real.norm_eq_abs, abs_of_pos hR,
      inv_mul_le_iff₀ hR, mul_one]
    exact this
  obtain ⟨y, hy, hfy⟩ := brouwer_euclidean f' hc hm
  refine ⟨e.symm (R • y), hin y hy, ?_⟩
  have h1 : e (f (e.symm (R • y))) = R • y := by
    have := congrArg (fun z => R • z) hfy
    simp only [hf', smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at this
    exact this
  have := congrArg e.symm h1
  rw [LinearIsometryEquiv.symm_apply_apply] at this
  exact this

/-- **Linking lemma.** A continuous map of the closed ball of radius `R` which moves every
point of the boundary sphere by less than `R` has a zero. -/
theorem exists_zero_of_boundary_close {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (R : ℝ) (hR : 0 < R) (g : V → V)
    (hg : ContinuousOn g (closedBall 0 R)) (hb : ∀ θ : V, ‖θ‖ = R → ‖g θ - θ‖ < R) :
    ∃ θ ∈ closedBall (0:V) R, g θ = 0 := by
  by_contra hcon
  push_neg at hcon
  set f : V → V := fun θ => (-(R / ‖g θ‖)) • g θ with hf
  have hgn : ∀ θ ∈ closedBall (0:V) R, 0 < ‖g θ‖ := fun θ hθ => norm_pos_iff.2 (hcon θ hθ)
  have hfc : ContinuousOn f (closedBall 0 R) := by
    apply ContinuousOn.smul _ hg
    exact (continuousOn_const.div hg.norm (fun θ hθ => (hgn θ hθ).ne')).neg
  have hfn : ∀ θ ∈ closedBall (0:V) R, ‖f θ‖ = R := by
    intro θ hθ
    rw [hf, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (div_pos hR (hgn θ hθ)),
      div_mul_cancel₀ _ (hgn θ hθ).ne']
  have hm : MapsTo f (closedBall 0 R) (closedBall 0 R) := by
    intro θ hθ
    rw [mem_closedBall, dist_zero_right, hfn θ hθ]
  obtain ⟨θ, hθ, hfθ⟩ := brouwer R hR f hfc hm
  have hnθ : ‖θ‖ = R := by rw [← hfθ, hfn θ hθ]
  have h1 : g θ - θ = (1 + R / ‖g θ‖) • g θ := by
    rw [show g θ - θ = g θ - f θ by rw [hfθ]]
    simp only [hf, add_smul, one_smul, neg_smul, sub_neg_eq_add]
  have h2 : ‖g θ - θ‖ = ‖g θ‖ + R := by
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by have := hgn θ hθ; positivity),
      add_mul, one_mul, div_mul_cancel₀ _ (hgn θ hθ).ne']
  have := hb θ hnθ
  rw [h2] at this
  linarith [hgn θ hθ]

end GradRange.Brouwer

assert_standard_axioms GradRange.Brouwer.no_smooth_retraction GradRange.Brouwer.brouwer_euclidean
  GradRange.Brouwer.brouwer GradRange.Brouwer.exists_zero_of_boundary_close
