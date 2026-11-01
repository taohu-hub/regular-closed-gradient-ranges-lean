module

public import GradientRanges.Defs

@[expose] public section

/-!
# Elementary facts on gradient ranges and asymptotic values
-/

open Set Metric Filter Topology

namespace GradRange

variable {n : ℕ}

/-- Sequence characterisation: `p ∈ A_∞(f)` iff `∇f(x_k) → p` for some `|x_k| → ∞`. -/
theorem mem_asymptoticValues_iff (f : E n → ℝ) (p : E n) :
    p ∈ asymptoticValues f ↔ ∃ x : ℕ → E n,
      Tendsto (fun k => ‖x k‖) atTop atTop ∧ Tendsto (fun k => gradient f (x k)) atTop (𝓝 p) := by
  constructor
  · intro hp
    simp only [asymptoticValues, mem_iInter] at hp
    have : ∀ k : ℕ, ∃ x : E n, (k : ℝ) + 1 ≤ ‖x‖ ∧ dist (gradient f x) p < 1 / ((k : ℝ) + 1) := by
      intro k
      have h := hp ((k : ℝ) + 1) (by positivity)
      rw [Metric.mem_closure_iff] at h
      obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := h (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨x, hx, by rwa [dist_comm]⟩
    choose x hx1 hx2 using this
    refine ⟨x, ?_, ?_⟩
    · refine tendsto_atTop_mono (fun k => le_trans (by linarith) (hx1 k)) ?_
      exact tendsto_natCast_atTop_atTop
    · rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun k => dist_nonneg) (fun k => (hx2 k).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨x, hx, hgx⟩
    simp only [asymptoticValues, mem_iInter]
    intro R _
    apply mem_closure_of_tendsto hgx
    filter_upwards [hx.eventually_ge_atTop R] with k hk
    exact ⟨x k, hk, rfl⟩

/-- `A_∞(f)` is closed. -/
theorem isClosed_asymptoticValues (f : E n → ℝ) : IsClosed (asymptoticValues f) :=
  isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closure

/-- `A_∞(f) ⊆ closure G_f`. -/
theorem asymptoticValues_subset_closure (f : E n → ℝ) :
    asymptoticValues f ⊆ closure (gradRange f) := by
  intro p hp
  simp only [asymptoticValues, mem_iInter] at hp
  exact closure_mono (image_subset_range _ _) (hp 1 one_pos)

/-- If `p ∉ A_∞(f)` there are `r, R > 0` with `|∇f(x) - p| > r` for `|x| ≥ R`. -/
theorem exists_away_of_not_mem_asymptoticValues (f : E n → ℝ) (p : E n)
    (hp : p ∉ asymptoticValues f) :
    ∃ r > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → r < dist (gradient f x) p := by
  simp only [asymptoticValues, mem_iInter, not_forall] at hp
  obtain ⟨R, hR, hpR⟩ := hp
  rw [Metric.mem_closure_iff] at hpR
  push_neg at hpR
  obtain ⟨r, hr, hfar⟩ := hpR
  refine ⟨r / 2, by positivity, R, hR, fun x hx => ?_⟩
  have := hfar _ ⟨x, hx, rfl⟩
  rw [dist_comm] at this
  linarith

/-- Outside the support of `f`, `∇f = 0`. -/
theorem gradient_eq_zero_of_notMem_tsupport (f : E n → ℝ) (x : E n) (hx : x ∉ tsupport f) :
    gradient f x = 0 := by
  have : fderiv ℝ f x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ (f := f) h)
  simp [gradient, this]

/-- A compactly supported function has vanishing gradient outside some ball. -/
theorem exists_gradient_eq_zero_of_hasCompactSupport (f : E n → ℝ) (hsupp : HasCompactSupport f) :
    ∃ R > 0, ∀ x : E n, R ≤ ‖x‖ → gradient f x = 0 := by
  obtain ⟨R₀, hR₀⟩ := hsupp.isBounded.subset_closedBall 0
  refine ⟨max R₀ 0 + 1, by positivity, fun x hx => ?_⟩
  apply gradient_eq_zero_of_notMem_tsupport
  intro hxs
  have := hR₀ hxs
  rw [mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R₀ 0]

/-- For a compactly supported `f`, `A_∞(f) ⊆ {0}`. -/
theorem asymptoticValues_bump_subset (f : E n → ℝ) (hsupp : HasCompactSupport f) :
    asymptoticValues f ⊆ {0} := by
  obtain ⟨R, hR, hz⟩ := exists_gradient_eq_zero_of_hasCompactSupport f hsupp
  intro p hp
  simp only [asymptoticValues, mem_iInter] at hp
  have hsub : gradient f '' {x | R ≤ ‖x‖} ⊆ {0} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hz x hx
  exact closure_minimal hsub isClosed_singleton (hp R hR)

/-- For a bump, `A_∞(f) = {0}` (`n ≥ 1`). -/
theorem asymptoticValues_bump (hn : 1 ≤ n) (f : E n → ℝ) (hsupp : HasCompactSupport f) :
    asymptoticValues f = {0} := by
  refine subset_antisymm (asymptoticValues_bump_subset f hsupp) ?_
  rw [singleton_subset_iff]
  obtain ⟨R₀, hR₀, hz⟩ := exists_gradient_eq_zero_of_hasCompactSupport f hsupp
  haveI : Nontrivial (E n) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  simp only [asymptoticValues, mem_iInter]
  intro R hR
  obtain ⟨x, hx⟩ := exists_norm_eq (E n) (c := max R R₀) (by positivity)
  apply subset_closure
  exact ⟨x, by rw [mem_setOf_eq, hx]; exact le_max_left _ _,
    hz x (by rw [hx]; exact le_max_right _ _)⟩

/-- For a `C¹` bump, `G_f` is compact. -/
theorem isCompact_gradRange_bump (f : E n → ℝ) (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) : IsCompact (gradRange f) := by
  have h1 : HasCompactSupport (gradient f) := by
    have := (hsupp.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (E n)).symm) (by simp)
    exact this
  exact h1.isCompact_range (continuous_gradient_of_contDiff f hf)

/-- The maximum argument: if `g` is a `C¹` function with compact support and `g(x⋆) > 0`,
then a ball about `0` lies in `G_g`. -/
theorem zero_mem_interior_gradRange_of_pos (g : E n → ℝ) (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) (xs : E n) (hxs : 0 < g xs) :
    (0 : E n) ∈ interior (gradRange g) := by
  obtain ⟨R₀, hR₀⟩ := hsupp.isBounded.subset_closedBall 0
  set R := max R₀ ‖xs‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hzero : ∀ x : E n, ‖x‖ = R → g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have := hR₀ hxt
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R₀ ‖xs‖]
  set δ := g xs / (2 * R) with hδ
  have hδpos : 0 < δ := by positivity
  rw [mem_interior]
  refine ⟨ball 0 δ, ?_, isOpen_ball, mem_ball_self hδpos⟩
  intro q hq
  rw [mem_ball, dist_zero_right] at hq
  set h : E n → ℝ := fun x => g x - innerSL ℝ q x with hh
  have hcont : Continuous h := by
    have := hg.continuous
    fun_prop
  obtain ⟨xm, hxm, hmax⟩ := (isCompact_closedBall (0 : E n) R).exists_isMaxOn
    ⟨xs, by rw [mem_closedBall, dist_zero_right]; linarith [le_max_right R₀ ‖xs‖]⟩
    hcont.continuousOn
  have hqR : ∀ x : E n, ‖x‖ ≤ R → |innerSL ℝ q x| ≤ ‖q‖ * R := by
    intro x hx
    rw [innerSL_apply_apply]
    calc |inner ℝ q x| ≤ ‖q‖ * ‖x‖ := abs_real_inner_le_norm q x
      _ ≤ ‖q‖ * R := by gcongr
  have hqR' : ‖q‖ * R < g xs / 2 := by
    calc ‖q‖ * R < δ * R := by gcongr
      _ = g xs / 2 := by rw [hδ]; field_simp
  have hxmR : ‖xm‖ < R := by
    rw [mem_closedBall, dist_zero_right] at hxm
    rcases hxm.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hle := hmax (show xs ∈ closedBall 0 R by
        rw [mem_closedBall, dist_zero_right]; linarith [le_max_right R₀ ‖xs‖])
      simp only [hh, mem_setOf_eq] at hle
      rw [hzero xm h1] at hle
      have a1 := hqR xm h1.le
      have a2 := hqR xs (by linarith [le_max_right R₀ ‖xs‖])
      have a3 := abs_le.mp a1
      have a4 := abs_le.mp a2
      linarith
  have hloc : IsLocalMax h xm := by
    apply hmax.isLocalMax
    apply closedBall_mem_nhds_of_mem
    rwa [mem_ball, dist_zero_right]
  have hder := hloc.fderiv_eq_zero
  have hfd : HasFDerivAt h (fderiv ℝ g xm - innerSL ℝ q) xm :=
    (hgd xm).hasFDerivAt.sub (innerSL ℝ q).hasFDerivAt
  rw [hfd.fderiv, sub_eq_zero] at hder
  refine ⟨xm, ?_⟩
  simp only [gradient, hder]
  apply (InnerProductSpace.toDual ℝ (E n)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]; ext v; simp

/-- For a `C¹` bump, `0 ∈ int G_f`. -/
theorem zero_mem_interior_gradRange_bump (f : E n → ℝ) (hf : ContDiff ℝ 1 f) (hne : f ≠ 0)
    (hsupp : HasCompactSupport f) : (0 : E n) ∈ interior (gradRange f) := by
  obtain ⟨xs, hxs⟩ : ∃ xs, f xs ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  rcases hxs.lt_or_gt with hneg | hpos
  · have h := zero_mem_interior_gradRange_of_pos (-f) hf.neg hsupp.neg xs (by simp; linarith)
    have hG : gradRange (-f) = (Homeomorph.neg (E n)) ⁻¹' gradRange f := by
      ext p
      simp only [gradRange, mem_range, mem_preimage, Homeomorph.coe_neg]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        simp [gradient, fderiv_neg]
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        simp [gradient, fderiv_neg] at hx ⊢
        rw [hx, neg_neg]
    rw [hG, ← (Homeomorph.neg (E n)).preimage_interior] at h
    simpa using h
  · exact zero_mem_interior_gradRange_of_pos f hf hsupp xs hpos

/-- If `∇f(x) → p∞` at infinity, then `A_∞(f) = {p∞}` (`n ≥ 1`). -/
theorem asymptoticValues_of_tendsto (hn : 1 ≤ n) (f : E n → ℝ) (p : E n)
    (h : Tendsto (gradient f) (cocompact (E n)) (𝓝 p)) :
    asymptoticValues f = {p} := by
  apply subset_antisymm
  · intro q hq
    obtain ⟨x, hx, hgx⟩ := (mem_asymptoticValues_iff f q).mp hq
    have hx' : Tendsto x atTop (cocompact (E n)) := by
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      exact hx
    exact tendsto_nhds_unique hgx (h.comp hx')
  · rw [singleton_subset_iff, mem_asymptoticValues_iff]
    haveI : Nontrivial (E n) := by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      infer_instance
    obtain ⟨u, hu⟩ := exists_norm_eq (E n) (c := 1) zero_le_one
    refine ⟨fun k => (k : ℝ) • u, ?_, ?_⟩
    · simp only [norm_smul, hu, mul_one, Real.norm_natCast]
      exact tendsto_natCast_atTop_atTop
    · apply h.comp
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      simp only [norm_smul, hu, mul_one, Real.norm_natCast]
      exact tendsto_natCast_atTop_atTop

end GradRange
