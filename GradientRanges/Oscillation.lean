module
import all Mathlib.Basic.Real.Basic

public import GradientRanges.Defs

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2.1: small oscillating periodic functions with large gradient on a nowhere dense set

Instead of mollifying a sum of triangular waves, we use an explicit smoothed triangular wave
`triWave c` (the primitive of a smoothed square wave). Its derivative is exactly `±1` wherever
`|sin(π s)| ≥ c`, which plays the role of the distance-to-breakpoints condition of the paper.
-/

open Set Real Metric Filter Topology
open scoped ContDiff

namespace GradRange

/-! ## A one-dimensional smoothed triangle wave -/

/-- Smooth odd step `Φ`, equal to `±1` outside `(-1,1)`. -/
noncomputable def oddStep (x : ℝ) : ℝ := smoothTransition x - smoothTransition (-x)

theorem contDiff_oddStep : ContDiff ℝ ∞ oddStep := by
  have h : ContDiff ℝ ∞ smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  exact h.sub (h.comp contDiff_neg)

theorem oddStep_neg (x : ℝ) : oddStep (-x) = -oddStep x := by
  simp [oddStep]

theorem abs_oddStep_le (x : ℝ) : |oddStep x| ≤ 1 := by
  have := smoothTransition.nonneg x; have := smoothTransition.le_one x
  have := smoothTransition.nonneg (-x); have := smoothTransition.le_one (-x)
  rw [oddStep, abs_le]; constructor <;> linarith

theorem abs_oddStep_of_one_le_abs (x : ℝ) (hx : 1 ≤ |x|) : |oddStep x| = 1 := by
  rcases le_abs'.mp hx with h | h
  · rw [oddStep, smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.one_of_one_le (by linarith)]; norm_num
  · rw [oddStep, smoothTransition.one_of_one_le h,
      smoothTransition.zero_of_nonpos (by linarith)]; norm_num

/-- Smoothed square wave with threshold `c`: `±1` wherever `|sin(π s)| ≥ c`. -/
noncomputable def sqWave (c s : ℝ) : ℝ := oddStep (sin (π * s) / c)

theorem contDiff_sqWave (c : ℝ) : ContDiff ℝ ∞ (sqWave c) := by
  unfold sqWave
  apply contDiff_oddStep.comp
  exact ((contDiff_const.mul contDiff_id).sin).div_const c

theorem sqWave_add_one (c s : ℝ) : sqWave c (s + 1) = -sqWave c s := by
  simp only [sqWave]
  rw [mul_add, mul_one, sin_add_pi, neg_div, oddStep_neg]

theorem continuous_sqWave (c : ℝ) : Continuous (sqWave c) := (contDiff_sqWave c).continuous

/-- Smoothed triangle wave `t ↦ ∫₀ᵗ sqWave c`. -/
noncomputable def triWave (c t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, sqWave c s

theorem hasDerivAt_triWave (c t : ℝ) : HasDerivAt (triWave c) (sqWave c t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_sqWave c).intervalIntegrable _ _)
    ((continuous_sqWave c).stronglyMeasurableAtFilter _ _) (continuous_sqWave c).continuousAt

theorem contDiff_triWave (c : ℝ) : ContDiff ℝ ∞ (triWave c) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_triWave c t).differentiableAt, ?_⟩
  have : deriv (triWave c) = sqWave c := funext fun t => (hasDerivAt_triWave c t).deriv
  rw [this]; exact contDiff_sqWave c

theorem triWave_periodic (c : ℝ) : Function.Periodic (triWave c) 2 := by
  intro t
  simp only [triWave]
  have hi : ∀ a b : ℝ, IntervalIntegrable (sqWave c) MeasureTheory.volume a b :=
    fun a b => (continuous_sqWave c).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t (t+2)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi t (t+1)) (hi (t+1) (t+2))]
  have : ∫ s in (t+1)..(t+2), sqWave c s = - ∫ s in t..(t+1), sqWave c s := by
    rw [show t + 2 = (t + 1) + 1 by ring, ← intervalIntegral.integral_comp_add_right]
    simp only [sqWave_add_one, intervalIntegral.integral_neg]
  rw [this]; ring

theorem abs_triWave_le (c t : ℝ) : |triWave c t| ≤ 2 := by
  obtain ⟨t', ht', heq⟩ := (triWave_periodic c).exists_mem_Ico₀ (by norm_num : (0:ℝ) < 2) t
  rw [heq, triWave, ← Real.norm_eq_abs]
  calc ‖∫ s in (0:ℝ)..t', sqWave c s‖ ≤ 1 * |t' - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s _
        rw [Real.norm_eq_abs]; exact abs_oddStep_le _
    _ ≤ 2 := by rw [sub_zero, abs_of_nonneg ht'.1]; linarith [ht'.2]

/-! ## The oscillating function on `ℝⁿ` -/

variable {n : ℕ}

/-- `H(p) = λ δ ∑ⱼ triWave c ((pⱼ - aⱼ)/δ)`. -/
noncomputable def oscFun (lam δ c : ℝ) (a : E n) (p : E n) : ℝ :=
  lam * δ * ∑ j, triWave c ((p j - a j) / δ)

theorem contDiff_oscFun (lam δ c : ℝ) (a : E n) : ContDiff ℝ ∞ (oscFun lam δ c a) := by
  unfold oscFun
  apply contDiff_const.mul
  apply ContDiff.sum
  intro j _
  apply (contDiff_triWave c).comp
  apply ContDiff.div_const
  apply ContDiff.sub _ contDiff_const
  exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

theorem oscFun_periodic (lam δ c : ℝ) (a : E n) (hδ : δ ≠ 0) (j : Fin n) (p : E n) :
    oscFun lam δ c a (p + EuclideanSpace.single j (2 * δ)) = oscFun lam δ c a p := by
  unfold oscFun
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j
  · subst hk
    simp only [PiLp.add_apply, PiLp.single_apply, if_true]
    rw [show (p k + 2 * δ - a k) / δ = (p k - a k) / δ + 2 by field_simp; ring]
    exact triWave_periodic c _
  · simp [PiLp.single_apply, hk]

theorem abs_oscFun_le (lam δ c : ℝ) (a : E n) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (p : E n) :
    |oscFun lam δ c a p| ≤ lam * δ * 2 * n := by
  unfold oscFun
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc (lam * δ)]
  gcongr
  calc |∑ j, triWave c ((p j - a j) / δ)| ≤ ∑ j, |triWave c ((p j - a j) / δ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (2:ℝ) := Finset.sum_le_sum fun j _ => abs_triWave_le c _
    _ = 2 * n := by simp [mul_comm]

theorem fderiv_oscFun_single (lam δ c : ℝ) (a : E n) (hδ : δ ≠ 0) (p : E n) (j : Fin n) :
    fderiv ℝ (oscFun lam δ c a) p (EuclideanSpace.single j 1) =
      lam * sqWave c ((p j - a j) / δ) := by
  have hd : DifferentiableAt ℝ (oscFun lam δ c a) p :=
    ((contDiff_oscFun lam δ c a).differentiable (by simp)) p
  have hline : HasDerivAt (fun t : ℝ => p + t • EuclideanSpace.single j (1:ℝ))
      (EuclideanSpace.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (EuclideanSpace.single j (1:ℝ))).const_add p
  have hd' : HasFDerivAt (oscFun lam δ c a) (fderiv ℝ (oscFun lam δ c a) p)
      (p + (0:ℝ) • EuclideanSpace.single j (1:ℝ)) := by simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0:ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => oscFun lam δ c a (p + t • EuclideanSpace.single j 1))
      (lam * sqWave c ((p j - a j) / δ)) 0 := by
    unfold oscFun
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
        (fun t : ℝ => triWave c (((p + t • EuclideanSpace.single j (1:ℝ)) k - a k) / δ))
        (if k = j then sqWave c ((p j - a j) / δ) * (1 / δ) else 0) 0 := by
      intro k _
      by_cases hk : k = j
      · subst hk
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, if_true,
          smul_eq_mul, mul_one]
        have hlin : HasDerivAt (fun t : ℝ => (p k + t - a k) / δ) (1 / δ) 0 := by
          have := ((hasDerivAt_id (0:ℝ)).const_add (p k)).sub_const (a k) |>.div_const δ
          simpa using this
        have := (hasDerivAt_triWave c ((p k + 0 - a k) / δ)).comp (0:ℝ) hlin
        simpa only [Function.comp_def, add_zero, one_div] using this
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hk, if_false,
          smul_eq_mul, mul_zero, add_zero]
        exact hasDerivAt_const _ _
    have hs := (HasDerivAt.fun_sum hterm).const_mul (lam * δ)
    convert hs using 1
    rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
    field_simp
  have := h1.unique h2
  simpa using this

theorem norm_gradient_ge_of_fderiv (H : E n → ℝ) (p : E n) (j : Fin n) :
    |fderiv ℝ H p (EuclideanSpace.single j 1)| ≤ ‖gradient H p‖ := by
  have h : fderiv ℝ H p (EuclideanSpace.single j 1) =
      inner ℝ (gradient H p) (EuclideanSpace.single j (1:ℝ)) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [h]
  calc |inner ℝ (gradient H p) (EuclideanSpace.single j (1:ℝ))|
      ≤ ‖gradient H p‖ * ‖EuclideanSpace.single j (1:ℝ)‖ := abs_real_inner_le_norm _ _
    _ = ‖gradient H p‖ := by simp

/-- Choice of a translated lattice `a + δℤⁿ` disjoint from `K` (Baire category). -/
theorem exists_lattice_avoiding (K : Set (E n)) (hK : IsClosed K) (hKi : interior K = ∅)
    (δ : ℝ) : ∃ a : E n, ∀ m : Fin n → ℤ, a + δ • intVec m ∉ K := by
  set T : (Fin n → ℤ) → Set (E n) := fun m => ((fun a => a + δ • intVec m) ⁻¹' K)ᶜ with hT
  have hopen : ∀ m, IsOpen (T m) := fun m =>
    (hK.preimage (continuous_id.add continuous_const)).isOpen_compl
  have hdense : ∀ m, Dense (T m) := by
    intro m
    rw [hT, ← interior_eq_empty_iff_dense_compl]
    have := (Homeomorph.addRight (δ • intVec m)).preimage_interior K
    simp only [Homeomorph.coe_addRight] at this
    rw [← this, hKi, preimage_empty]
  obtain ⟨a, ha⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  refine ⟨a, fun m hm => ?_⟩
  rw [mem_iInter] at ha
  exact ha m hm

/-- **Lemma 2.1.** Let `K ⊆ ℝⁿ` be compact with empty interior. For every `ε, D > 0` there is
a smooth `H : ℝⁿ → ℝ`, periodic in each coordinate, with `‖H‖_∞ < ε` (a uniform bound
`|H| ≤ c` with `c < ε`) and `|∇H(p)| > D` for `p ∈ K`. -/
theorem lemma_2_1 (K : Set (E n)) (hK : IsCompact K) (hKi : interior K = ∅)
    (ε D : ℝ) (hε : 0 < ε) (hD : 0 < D) :
    ∃ H : E n → ℝ, ContDiff ℝ ∞ H ∧
      (∃ T > 0, ∀ (j : Fin n) (p : E n), H (p + EuclideanSpace.single j T) = H p) ∧
      (∃ c < ε, ∀ p, |H p| ≤ c) ∧
      ∀ p ∈ K, D < ‖gradient H p‖ := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨fun _ => 0, contDiff_const, ⟨1, one_pos, fun _ _ => rfl⟩, ⟨0, hε, fun _ => by simp⟩,
      ?_⟩
    simp [hKe]
  set lam : ℝ := D + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  set δ : ℝ := ε / (4 * (n + 1) * lam) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨a, ha⟩ := exists_lattice_avoiding K hK.isClosed hKi δ
  set w : E n → ℝ := fun p => ∑ j, sin (π * ((p j - a j) / δ)) ^ 2 with hw
  have hwc : Continuous w := by
    simp only [hw]
    fun_prop
  have hwpos : ∀ p ∈ K, 0 < w p := by
    intro p hp
    by_contra hle
    push_neg at hle
    have hzero : w p = 0 := le_antisymm hle (Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [hw, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at hzero
    have hint : ∀ j, ∃ m : ℤ, (m : ℝ) * π = π * ((p j - a j) / δ) := by
      intro j
      exact Real.sin_eq_zero_iff.mp (pow_eq_zero_iff (two_ne_zero) |>.mp
        (hzero j (Finset.mem_univ _)))
    choose m hm using hint
    apply ha m
    convert hp using 1
    ext j
    have := hm j
    have hπ : π ≠ 0 := Real.pi_ne_zero
    have : (m j : ℝ) = (p j - a j) / δ := by
      have h2 : π * (m j : ℝ) = π * ((p j - a j) / δ) := by rw [mul_comm]; exact this
      exact mul_left_cancel₀ hπ h2
    simp only [PiLp.add_apply, PiLp.smul_apply, intVec, smul_eq_mul]
    rw [this]; field_simp; ring
  obtain ⟨p₀, hp₀K, hmin⟩ := hK.exists_isMinOn hKne hwc.continuousOn
  set w₀ := w p₀ with hw₀
  have hw₀pos : 0 < w₀ := hwpos p₀ hp₀K
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      simp [hw₀, hw] at hw₀pos
    · exact_mod_cast h
  set c : ℝ := w₀ / n with hc
  have hc0 : 0 < c := by positivity
  refine ⟨oscFun lam δ c a, contDiff_oscFun lam δ c a,
    ⟨2 * δ, by positivity, fun j p => oscFun_periodic lam δ c a hδ0.ne' j p⟩,
    ⟨lam * δ * 2 * n, ?_, abs_oscFun_le lam δ c a hlam0.le hδ0.le⟩, ?_⟩
  · rw [hδ]
    field_simp
    nlinarith
  · intro p hp
    -- a good coordinate
    obtain ⟨j, hj⟩ : ∃ j, c ≤ sin (π * ((p j - a j) / δ)) ^ 2 := by
      by_contra hcon
      push_neg at hcon
      have hlt : w p < ∑ _j : Fin n, c := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by exact_mod_cast hn⟩⟩
        · exact fun j _ => hcon j
      have : ∑ _j : Fin n, c = w₀ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
        field_simp
      have := hmin hp
      simp only [mem_setOf_eq] at this
      linarith
    have hsin : c ≤ |sin (π * ((p j - a j) / δ))| := by
      have h1 := abs_sin_le_one (π * ((p j - a j) / δ))
      have h2 : sin (π * ((p j - a j) / δ)) ^ 2 ≤ |sin (π * ((p j - a j) / δ))| := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (sin (π * ((p j - a j) / δ)))]
      linarith
    have hsq : |sqWave c ((p j - a j) / δ)| = 1 := by
      apply abs_oddStep_of_one_le_abs
      rw [abs_div, abs_of_pos hc0, le_div_iff₀ hc0, one_mul]
      exact hsin
    have := norm_gradient_ge_of_fderiv (oscFun lam δ c a) p j
    rw [fderiv_oscFun_single lam δ c a hδ0.ne' p j, abs_mul, hsq, abs_of_pos hlam0,
      mul_one] at this
    linarith

end GradRange
