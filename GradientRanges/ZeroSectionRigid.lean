module
import all Mathlib.Basic.Real.Basic

public import GradientRanges.ZeroSectionVariational

@[expose] public section

/-!
# Displacement rigidity of the zero section, by the discrete action functional

This file completes the finite-dimensional variational proof that the zero section of `ℝ²ⁿ`
is displacement rigid (`zeroSection_rigid_variational`); see the module docstring of
`GradientRanges.ZeroSectionVariational` for the outline.
-/

open Set Metric Filter Topology
open scoped ContDiff

noncomputable section

namespace GradRange.ZSV

open GradRange.DAction

variable {n : ℕ}

local instance {m : ℕ} : ContinuousSMul ℝ (VS n m) :=
  IsBoundedSMul.continuousSMul

/-! ## Elementary facts -/

theorem filter_le_eq_Ico (N j : ℕ) :
    (Finset.range N).filter (fun k => j ≤ k) = Finset.Ico j N := by
  ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

theorem tk_mem {N k : ℕ} (hk : k < N) : tk N k ∈ Icc (0:ℝ) 1 := by
  have hN : (0:ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hk' : (k:ℝ) + 1 ≤ N := by exact_mod_cast hk
  refine ⟨by unfold tk; positivity, ?_⟩
  unfold tk; rw [div_le_one hN]; exact hk'

theorem slice_contDiff (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (t : ℝ) :
    ContDiff ℝ ∞ (F t) :=
  hF.1.comp (contDiff_const.prodMk contDiff_id)

theorem slice_hasCompactSupport (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) : HasCompactSupport (F t) := by
  obtain ⟨K, hK, hKz⟩ := hF.2
  exact HasCompactSupport.intro hK (fun z hz => hKz t ht z hz)

theorem norm_gradient_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V → ℝ) (x : V) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

/-! ## The bump function -/

/-- A bump `g = ε β(x) χ(p)` adapted to the point `xs` and the radius `r`. -/
structure Bump (xs : E n) (r : ℝ) where
  g : P n → ℝ
  ε : ℝ
  hε : 0 < ε
  hε1 : ε ≤ 1
  smooth : ContDiff ℝ 2 g
  supp : HasCompactSupport g
  nonneg : ∀ q, 0 ≤ g q
  le_eps : ∀ q, g q ≤ ε
  center : ∀ p : E n, ‖p‖ ≤ 1 → g (xs, p) = ε
  near : ∀ q, g q ≠ 0 → q.1 ∈ closedBall xs (r / 4)
  gradP_le : ∀ q, ‖gradP g q‖ ≤ r / 4
  gradX_le : ∀ q, ‖gradX g q‖ ≤ r / 4

theorem exists_bump (xs : E n) (r : ℝ) (hr : 0 < r) : Nonempty (Bump xs r) := by
  let β : ContDiffBump xs := ⟨r / 8, r / 4, by positivity, by linarith⟩
  let χ : ContDiffBump (0 : E n) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨Mβ, -, hMβ0, -, hMβ, -⟩ := fderiv_bounds_of_hasCompactSupport (β : E n → ℝ)
    β.contDiff β.hasCompactSupport
  obtain ⟨Mχ, -, hMχ0, -, hMχ, -⟩ := fderiv_bounds_of_hasCompactSupport (χ : E n → ℝ)
    χ.contDiff χ.hasCompactSupport
  set ε := min 1 (min (r / (4 * (Mβ + 1))) (r / (4 * (Mχ + 1)))) with hεdef
  have hε : 0 < ε := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεβ : ε * Mβ ≤ r / 4 := by
    have h1 : ε ≤ r / (4 * (Mβ + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hεχ : ε * Mχ ≤ r / 4 := by
    have h1 : ε ≤ r / (4 * (Mχ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hβd : Differentiable ℝ (β : E n → ℝ) := (β.contDiff (n := 1)).differentiable one_ne_zero
  have hχd : Differentiable ℝ (χ : E n → ℝ) := (χ.contDiff (n := 1)).differentiable one_ne_zero
  refine ⟨{
    g := fun q => ε * (β q.1 * χ q.2)
    ε := ε
    hε := hε
    hε1 := hε1
    smooth := contDiff_const.mul ((β.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd))
    supp := ?_
    nonneg := fun q => mul_nonneg hε.le (mul_nonneg β.nonneg χ.nonneg)
    le_eps := fun q => by
      have : β q.1 * χ q.2 ≤ 1 :=
        mul_le_one₀ β.le_one χ.nonneg χ.le_one
      nlinarith
    center := fun p hp => by
      show ε * (β xs * χ p) = ε
      rw [β.one_of_mem_closedBall (mem_closedBall_self (by positivity)),
        χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hp)]
      ring
    near := fun q hq => by
      by_contra hc
      apply hq
      show ε * (β q.1 * χ q.2) = 0
      rw [β.zero_of_le_dist (le_of_lt (not_le.1 hc)), zero_mul, mul_zero]
    gradP_le := fun q => by
      rw [gradP, norm_gradient_eq]
      have e : (fun p => ε * (β (q.1, p).1 * χ (q.1, p).2)) = fun p => (ε * β q.1) * χ p := by
        funext p; ring
      rw [e, fderiv_const_mul (hχd _), norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hε.le β.nonneg)]
      have h1 : ε * β q.1 ≤ ε := by nlinarith [β.le_one (x := q.1), β.nonneg (x := q.1)]
      have h2 := hMχ q.2
      have h3 : 0 ≤ ‖fderiv ℝ (χ : E n → ℝ) q.2‖ := norm_nonneg _
      nlinarith [mul_nonneg hε.le (β.nonneg (x := q.1))]
    gradX_le := fun q => by
      rw [gradX, norm_gradient_eq]
      have e : (fun x => ε * (β (x, q.2).1 * χ (x, q.2).2)) = fun x => (ε * χ q.2) * β x := by
        funext x; ring
      rw [e, fderiv_const_mul (hβd _), norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hε.le χ.nonneg)]
      have h1 : ε * χ q.2 ≤ ε := by nlinarith [χ.le_one (x := q.2), χ.nonneg (x := q.2)]
      have h2 := hMβ q.1
      have h3 : 0 ≤ ‖fderiv ℝ (β : E n → ℝ) q.1‖ := norm_nonneg _
      nlinarith [mul_nonneg hε.le (χ.nonneg (x := q.2))] }⟩
  refine HasCompactSupport.intro ((isCompact_closedBall xs (r / 4)).prod
    (isCompact_closedBall (0 : E n) 2)) fun q hq => ?_
  show ε * (β q.1 * χ q.2) = 0
  rw [mem_prod, not_and_or] at hq
  rcases hq with hq | hq
  · rw [β.zero_of_le_dist (le_of_lt (not_le.1 hq)), zero_mul, mul_zero]
  · rw [χ.zero_of_le_dist (le_of_lt (not_le.1 hq)), mul_zero, mul_zero]

/-! ## Bounds for the Hamiltonian part -/

theorem Hpart_le (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) (z : VS n (N + 1)) :
    Hpart F N z ≤ ∑ k ∈ Finset.range N, (1 / (N:ℝ)) * ⨆ q, F (tk N k) q := by
  obtain ⟨Bd, hBd⟩ := hamiltonian_bounded F hF
  unfold Hpart
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := tk_mem (Finset.mem_range.1 hk)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_ciSup ⟨Bd, by rintro _ ⟨q, rfl⟩; exact (le_abs_self _).trans (hBd _ hk' q)⟩ _

theorem le_Hpart (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) (z : VS n (N + 1)) :
    ∑ k ∈ Finset.range N, (1 / (N:ℝ)) * ⨅ q, F (tk N k) q ≤ Hpart F N z := by
  obtain ⟨Bd, hBd⟩ := hamiltonian_bounded F hF
  unfold Hpart
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := tk_mem (Finset.mem_range.1 hk)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ciInf_le ⟨-Bd, by rintro _ ⟨q, rfl⟩; exact neg_le_of_abs_le (hBd _ hk' q)⟩ _

/-! ## Regularity of the action -/

theorem hasFDerivAt_W0 (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) (g : P n → ℝ)
    (z : VS n (N + 1)) : HasFDerivAt (W0 F N) (Wd F N g 0 z) z := by
  have hFd : ∀ t, Differentiable ℝ (F t) := fun t =>
    (slice_contDiff F hF t).differentiable (by simp)
  have := hasFDerivAt_W F N hFd (fun _ => 0) (differentiable_const _) 0 z
  have e : Wd F N g 0 z = Wd F N (fun _ => 0) 0 z := by simp [Wd]
  rw [e]
  convert this using 2 with y
  ring

theorem slice_bounds (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) :
    ∃ Bk Lk : ℕ → ℝ, ∀ k < N, 0 ≤ Bk k ∧ 0 ≤ Lk k ∧
      (∀ q, ‖fderiv ℝ (F (tk N k)) q‖ ≤ Bk k) ∧
      ∀ q q', ‖fderiv ℝ (F (tk N k)) q - fderiv ℝ (F (tk N k)) q'‖ ≤ Lk k * ‖q - q'‖ := by
  have h : ∀ k, ∃ B L : ℝ, k < N → (0 ≤ B ∧ 0 ≤ L ∧
      (∀ q, ‖fderiv ℝ (F (tk N k)) q‖ ≤ B) ∧
      ∀ q q', ‖fderiv ℝ (F (tk N k)) q - fderiv ℝ (F (tk N k)) q'‖ ≤ L * ‖q - q'‖) := by
    intro k
    by_cases hk : k < N
    · obtain ⟨B, L, h1, h2, h3, h4⟩ := fderiv_bounds_of_hasCompactSupport (F (tk N k))
        ((slice_contDiff F hF _).of_le (WithTop.coe_le_coe.2 le_top)) (slice_hasCompactSupport F hF _ (tk_mem hk))
      exact ⟨B, L, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose Bk Lk hBL using h
  exact ⟨Bk, Lk, fun k hk => hBL k hk⟩

theorem continuous_Qd {m : ℕ} : Continuous (Qd : VS n m → (VS n m →L[ℝ] ℝ)) := by
  apply LipschitzWith.continuous (K := Real.toNNReal (2 * m))
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), ← fderiv_Qf, ← fderiv_Qf]
  exact fderiv_Qf_lip z z'

theorem W0_lip (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) :
    ∃ L, 0 ≤ L ∧ ∀ z z' : VS n (N + 1),
      ‖fderiv ℝ (W0 F N) z - fderiv ℝ (W0 F N) z'‖ ≤ L * ‖z - z'‖ := by
  obtain ⟨Bk, Lk, hk⟩ := slice_bounds F hF N
  refine ⟨2 * ((N + 1 : ℕ) : ℝ) + ∑ k ∈ Finset.range N, (1 / (N:ℝ)) *
      (Lk k * ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖ * ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖),
      ?_, ?_⟩
  · apply add_nonneg (by positivity)
    refine Finset.sum_nonneg fun k hk' => ?_
    have := (hk k (Finset.mem_range.1 hk')).2.1
    positivity
  · intro z z'
    rw [(hasFDerivAt_W0 F hF N (fun _ => 0) z).fderiv, (hasFDerivAt_W0 F hF N (fun _ => 0) z').fderiv]
    have e : Wd F N (fun _ => 0) 0 z - Wd F N (fun _ => 0) 0 z' = (Qd z - Qd z') -
        ∑ k ∈ Finset.range N, (1 / (N:ℝ)) • ((fderiv ℝ (F (tk N k)) (Ll (k + 1) z) -
          fderiv ℝ (F (tk N k)) (Ll (k + 1) z')).comp (Ll (k + 1))) := by
      simp only [Wd, zero_smul, sub_zero, ContinuousLinearMap.sub_comp, smul_sub,
        Finset.sum_sub_distrib]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖Qd z - Qd z'‖ ≤ 2 * ((N + 1 : ℕ) : ℝ) * ‖z - z'‖ := by
      rw [← fderiv_Qf, ← fderiv_Qf]; exact fderiv_Qf_lip z z'
    have h2 : ‖∑ k ∈ Finset.range N, (1 / (N:ℝ)) • ((fderiv ℝ (F (tk N k)) (Ll (k + 1) z) -
          fderiv ℝ (F (tk N k)) (Ll (k + 1) z')).comp
            (Ll (k + 1) : VS n (N + 1) →L[ℝ] P n))‖ ≤
        ∑ k ∈ Finset.range N, (1 / (N:ℝ)) *
          (Lk k * ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖ *
            ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖) * ‖z - z'‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk' => ?_)
      obtain ⟨-, hL0, -, hLip⟩ := hk k (Finset.mem_range.1 hk')
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h3 := hLip (Ll (k + 1) z) (Ll (k + 1) z')
      rw [← map_sub] at h3
      have h4 := (Ll (k + 1) : VS n (N + 1) →L[ℝ] P n).le_opNorm (z - z')
      calc _ ≤ Lk k * ‖Ll (k + 1) (z - z')‖ * ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖ :=
            mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ ≤ Lk k * (‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖ * ‖z - z'‖) *
            ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖ := by gcongr
        _ = _ := by ring
    rw [add_mul, Finset.sum_mul]; linarith

theorem continuous_Wd (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) (g : P n → ℝ)
    (hg : ContDiff ℝ 2 g) :
    Continuous (fun p : ℝ × VS n (N + 1) => Wd F N g p.1 p.2) := by
  unfold Wd
  apply Continuous.sub
  · apply Continuous.sub (continuous_Qd.comp continuous_snd)
    apply continuous_finset_sum
    intro k _
    simpa only [Pi.smul_def, Function.comp_def] using
      ((((slice_contDiff F hF _).continuous_fderiv (by simp)).comp
        ((Ll (k + 1)).continuous.comp continuous_snd)).clm_comp continuous_const).const_smul
          (1 / (N : ℝ))
  · exact continuous_fst.smul (((hg.continuous_fderiv (by norm_num)).comp
      ((Ll 0).continuous.comp continuous_snd)).clm_comp continuous_const)

theorem Wd_sub_Qd_le (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (N : ℕ) (g : P n → ℝ)
    (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z v : VS n (N + 1),
      |Wd F N g s z v - Qd z v| ≤ M * ‖v‖ := by
  obtain ⟨Bk, Lk, hk⟩ := slice_bounds F hF N
  obtain ⟨Bg, -, hBg0, -, hBg, -⟩ := fderiv_bounds_of_hasCompactSupport g hg hgs
  refine ⟨∑ k ∈ Finset.range N, (1 / (N:ℝ)) *
      (Bk k * ‖(Ll (k + 1) : VS n (N + 1) →L[ℝ] P n)‖) +
      Bg * ‖(Ll 0 : VS n (N + 1) →L[ℝ] P n)‖, ?_, ?_⟩
  · apply add_nonneg _ (by positivity)
    refine Finset.sum_nonneg fun k hk' => ?_
    have := (hk k (Finset.mem_range.1 hk')).1
    positivity
  · intro s hs z v
    rw [Wd_apply]
    have e : Qd z v - ∑ k ∈ Finset.range N,
        (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z) (Ll (k + 1) v) -
        s * fderiv ℝ g (Ll 0 z) (Ll 0 v) - Qd z v = -(∑ k ∈ Finset.range N,
        (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z) (Ll (k + 1) v) +
        s * fderiv ℝ g (Ll 0 z) (Ll 0 v)) := by ring
    rw [e, abs_neg]
    refine (abs_add_le _ _).trans ?_
    rw [add_mul, Finset.sum_mul]
    have hop : ∀ (T : P n →L[ℝ] ℝ) (L' : VS n (N + 1) →L[ℝ] P n) (b : ℝ), ‖T‖ ≤ b →
        |T (L' v)| ≤ b * ‖L'‖ * ‖v‖ := by
      intro T L' b hb
      rw [← Real.norm_eq_abs]
      refine (T.le_opNorm _).trans ?_
      calc ‖T‖ * ‖L' v‖ ≤ b * (‖L'‖ * ‖v‖) :=
            mul_le_mul hb (L'.le_opNorm v) (norm_nonneg _) ((norm_nonneg _).trans hb)
        _ = _ := by ring
    apply add_le_add
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk' => ?_)
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / N), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hop _ _ _ ((hk k (Finset.mem_range.1 hk')).2.2.1 _))
        (by positivity)
    · rw [abs_mul, abs_of_nonneg hs.1]
      have := hop _ (Ll 0) _ (hBg (Ll 0 z))
      have h0 : 0 ≤ |fderiv ℝ g (Ll 0 z) (Ll 0 v)| := abs_nonneg _
      calc s * |fderiv ℝ g (Ll 0 z) (Ll 0 v)| ≤ 1 * |fderiv ℝ g (Ll 0 z) (Ll 0 v)| :=
            mul_le_mul_of_nonneg_right hs.2 h0
        _ ≤ _ := by rw [one_mul]; exact this

/-! ## Critical points and the gradient lower bound -/

theorem no_crit (xs : E n) (r : ℝ) (hr : 0 < r) (B : Bump xs r) (F : ℝ → P n → ℝ)
    (hF : IsHamiltonian F) (φ : ℝ → P n → P n) (hφ : IsHamFlow F φ)
    (hd : Disjoint (φ 1 '' closedBall ((xs, 0) : P n) r) (zeroSection n)) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N, N₀ ≤ N → ∀ s ∈ Icc (0:ℝ) 1, ∀ z : VS n (N + 1),
      xl z ∈ closedBall xs (r / 4) → Wd F N B.g s z ≠ 0 := by
  set K := φ 1 '' closedBall ((xs, 0) : P n) r with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).image (continuous_hamFlow_one F hF φ hφ)
  have hZc : IsClosed (zeroSection n) := isClosed_eq continuous_snd continuous_const
  obtain ⟨δ, hδ, hδK⟩ := hKc.exists_thickening_subset_open hZc.isOpen_compl
    (fun a ha hz => Set.disjoint_left.1 hd ha hz)
  have hgap : ∀ a ∈ K, ∀ b ∈ zeroSection n, δ ≤ dist b a := by
    intro a ha b hb
    by_contra hcon
    push_neg at hcon
    exact hδK (Metric.mem_thickening_iff.2 ⟨a, ha, hcon⟩) hb
  obtain ⟨N₀, hN₀, hclose⟩ := discrete_orbit_close F hF φ hφ (δ / 2) (by positivity)
  refine ⟨N₀, hN₀, fun N hN s hs z hxl hz => ?_⟩
  have hFd : ∀ t, Differentiable ℝ (F t) := fun t =>
    (slice_contDiff F hF t).differentiable (by simp)
  have hgd : Differentiable ℝ B.g := B.smooth.differentiable (by norm_num)
  obtain ⟨h0, hstep, hp, hsum⟩ := crit_equations F N hFd B.g hgd s z hz
  have hp' : ∀ j ≤ N, pl j z = ∑ k ∈ Finset.Ico j N,
      (1 / (N:ℝ)) • gradX (F (tk N k)) (Ll (k + 1) z) := fun j hj => by
    rw [hp j hj, filter_le_eq_Ico]
  have hXs : ∀ j, Xl (j + 1) z = Xl j z + Dl j z := fun j => by
    rw [Xl_apply, Xl_apply, Finset.sum_range_succ, add_assoc]
  set y : ℕ → P n := fun k => (Xl (k + 1) z, pl k z) with hy
  have hrec : ∀ k < N, y (k + 1) = y k + (1 / (N:ℝ)) •
      hamVF F (((k:ℝ) + 1) / N) ((y k).1, (y (k + 1)).2) := by
    intro k hk
    have hL : ((y k).1, (y (k + 1)).2) = Ll (k + 1) z := rfl
    rw [hL]
    refine Prod.ext ?_ ?_
    · show Xl (k + 1 + 1) z = Xl (k + 1) z + (1 / (N:ℝ)) • gradP (F (((k:ℝ) + 1) / N)) _
      rw [hXs, hstep k hk]; rfl
    · show pl (k + 1) z = pl k z + (1 / (N:ℝ)) • -gradX (F (((k:ℝ) + 1) / N)) _
      rw [hp' k hk.le, hp' (k + 1) hk, Finset.sum_eq_sum_Ico_succ_bot hk, smul_neg]
      simp only [tk]; abel
  have hyN : y N ∈ zeroSection n := by
    show pl N z = 0
    rw [hp' N le_rfl, Finset.Ico_self, Finset.sum_empty]
  have hy0 : y 0 ∈ closedBall ((xs, 0) : P n) r := by
    have hD : ‖Dl 0 z‖ ≤ r / 4 := by
      rw [h0, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      have := B.gradP_le (Ll 0 z)
      have : 0 ≤ ‖gradP B.g (Ll 0 z)‖ := norm_nonneg _
      nlinarith [hs.2]
    have hP : ‖pl 0 z‖ ≤ r / 4 := by
      have e : pl 0 z = -(s • gradX B.g (Ll 0 z)) := by
        rw [hp' 0 (Nat.zero_le _), ← Finset.range_eq_Ico]
        exact eq_neg_of_add_eq_zero_left hsum
      rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      have := B.gradX_le (Ll 0 z)
      have : 0 ≤ ‖gradX B.g (Ll 0 z)‖ := norm_nonneg _
      nlinarith [hs.2]
    have hX := mem_closedBall_iff_norm.1 hxl
    rw [mem_closedBall, Prod.dist_eq]
    apply max_le
    · show dist (Xl (0 + 1) z) xs ≤ r
      rw [hXs, dist_eq_norm, Xl_apply, Finset.sum_range_zero, add_zero]
      have : xl z + Dl 0 z - xs = (xl z - xs) + Dl 0 z := by abel
      rw [this]
      have := norm_add_le (xl z - xs) (Dl 0 z)
      linarith
    · show dist (pl 0 z) 0 ≤ r
      rw [dist_zero_right]; linarith
  have h1 := hclose N hN y hrec
  have h2 := hgap (φ 1 (y 0)) ⟨y 0, hy0, rfl⟩ (y N) hyN
  rw [dist_eq_norm] at h2
  linarith

theorem grad_lower (xs : E n) (r : ℝ) (B : Bump xs r) (F : ℝ → P n → ℝ)
    (hF : IsHamiltonian F) (N : ℕ)
    (hN : ∀ s ∈ Icc (0:ℝ) 1, ∀ z : VS n (N + 1),
      xl z ∈ closedBall xs (r / 4) → Wd F N B.g s z ≠ 0) :
    ∃ η > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ z : VS n (N + 1), B.g (Ll 0 z) ≠ 0 →
      η ≤ ‖Wd F N B.g s z‖ := by
  obtain ⟨M, hM0, hM⟩ := Wd_sub_Qd_le F hF N B.g B.smooth B.supp
  set R0 := (‖xs‖ + r / 4) + (M + 1) with hR0
  set S : Set (ℝ × VS n (N + 1)) :=
    Icc (0:ℝ) 1 ×ˢ (closedBall 0 R0 ∩ xl ⁻¹' closedBall xs (r / 4)) with hS
  have hSc : IsCompact S := isCompact_Icc.prod
    ((isCompact_closedBall _ _).inter_right (isClosed_closedBall.preimage xl.continuous))
  -- a positive lower bound on the compact part
  obtain ⟨η₁, hη₁, hη₁S⟩ : ∃ η₁ > 0, ∀ p ∈ S, η₁ ≤ ‖Wd F N B.g p.1 p.2‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by rw [he] at hp; exact absurd hp (notMem_empty _)⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hSc.exists_isMinOn hne
        ((continuous_Wd F hF N B.g B.smooth).norm.continuousOn)
      refine ⟨‖Wd F N B.g p₀.1 p₀.2‖, ?_, fun p hp => hmin hp⟩
      exact norm_pos_iff.2 (hN p₀.1 hp₀.1 p₀.2 hp₀.2.2)
  refine ⟨min η₁ 1, lt_min hη₁ one_pos, fun s hs z hz => ?_⟩
  have hxl : xl z ∈ closedBall xs (r / 4) := by
    have := B.near _ hz
    rwa [Ll_apply, Xl_apply, Finset.sum_range_zero, add_zero] at this
  by_cases hzR : ‖z‖ ≤ R0
  · exact (min_le_left _ _).trans (hη₁S (s, z) ⟨hs, mem_closedBall_zero_iff.2 hzR, hxl⟩)
  · push_neg at hzR
    refine (min_le_right _ _).trans ?_
    have ha : ‖xl z‖ ≤ ‖xs‖ + r / 4 := by
      have h1 := mem_closedBall_iff_norm.1 hxl
      have h2 := norm_le_insert' (xl z) xs
      linarith
    have hsq := norm_sq_eq_xl_swapv z
    have hsw : M + 1 < ‖swapv z‖ := by
      by_contra hcon
      push_neg at hcon
      have h0 : 0 ≤ ‖xl z‖ := norm_nonneg _
      have h0' : 0 ≤ ‖swapv z‖ := norm_nonneg _
      have : ‖z‖ ^ 2 ≤ R0 ^ 2 := by
        rw [hsq, hR0]; nlinarith
      have := (pow_le_pow_iff_left₀ (norm_nonneg z) (by linarith : (0:ℝ) ≤ R0)
        two_ne_zero).1 this
      linarith
    have h1 := hM s hs z (swapv z)
    rw [Qd_swapv] at h1
    have h2 : Wd F N B.g s z (swapv z) ≤ ‖Wd F N B.g s z‖ * ‖swapv z‖ :=
      (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ (Wd F N B.g s z).le_opNorm _)
    have h3 : ‖swapv z‖ ^ 2 - M * ‖swapv z‖ ≤ ‖Wd F N B.g s z‖ * ‖swapv z‖ := by
      have := (abs_le.1 h1).1
      linarith
    have hpos : 0 < ‖swapv z‖ := by linarith
    by_contra hcon
    push_neg at hcon
    have : ‖Wd F N B.g s z‖ * ‖swapv z‖ < 1 * ‖swapv z‖ :=
      mul_lt_mul_of_pos_right hcon hpos
    nlinarith

/-! ## The quantitative estimate -/

/-- **Energy–capacity inequality for the zero section.** If the time-one map of `F` displaces
the closed ball of radius `r` around `(xs, 0)` from the zero section, then the Hofer length of
`F` is at least `ε/4`, where `ε > 0` depends only on the bump (i.e. on `xs` and `r`). -/
theorem hoferLength_ge_of_displaces (xs : E n) (r : ℝ) (hr : 0 < r) (B : Bump xs r)
    (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (φ : ℝ → P n → P n) (hφ : IsHamFlow F φ)
    (hd : Disjoint (φ 1 '' closedBall ((xs, 0) : P n) r) (zeroSection n)) :
    B.ε / 4 ≤ hoferLength F := by
  have hε := B.hε
  obtain ⟨N₁, hN₁, hcrit⟩ := no_crit xs r hr B F hF φ hφ hd
  obtain ⟨N₂, hN₂, hriem⟩ := riemann_osc_le F hF (B.ε / 4) (by positivity)
  set N := max N₁ N₂ with hNdef
  have hN : 0 < N := lt_of_lt_of_le hN₁ (le_max_left _ _)
  obtain ⟨η, hη, hgrad⟩ := grad_lower xs r B F hF N (hcrit N (le_max_left _ _))
  -- the perturbation `c = -g ∘ L₀`
  set c : VS n (N + 1) → ℝ := fun z => (fun q => -B.g q) (Ll 0 z) with hc
  have hgd : Differentiable ℝ B.g := B.smooth.differentiable (by norm_num)
  have hngd : Differentiable ℝ (fun q => -B.g q) := hgd.neg
  obtain ⟨Bc, Lc, -, hLc0, hBc, hLc⟩ := fderiv_bounds_of_hasCompactSupport (fun q => -B.g q)
    B.smooth.neg B.supp.neg
  have hcb := (comp_clm_bounds (fun q => -B.g q) hngd (Ll 0 : VS n (N + 1) →L[ℝ] P n) Bc Lc hBc hLc hLc0)
  obtain ⟨LW, hLW0, hLW⟩ := W0_lip F hF N
  have hW0d : Differentiable ℝ (W0 F N) := fun z =>
    (hasFDerivAt_W0 F hF N B.g z).differentiableAt
  have hcd : Differentiable ℝ c := hngd.comp (Ll 0).differentiable
  set L := max LW (Lc * ‖(Ll 0 : VS n (N + 1) →L[ℝ] P n)‖ * ‖(Ll 0 : VS n (N + 1) →L[ℝ] P n)‖)
  have hFd : ∀ t, Differentiable ℝ (F t) := fun t =>
    (slice_contDiff F hF t).differentiable (by simp)
  obtain ⟨G, hGc, hGmove, hGW⟩ := Deformation.exists_deformation (W0 F N) c hW0d hcd L
    (hLW0.trans (le_max_left _ _))
    (fun x y => (hLW x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    (fun x y => (hcb.2 x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
    B.ε (fun x => by
      simp only [hc, abs_neg]
      rw [abs_of_nonneg (B.nonneg _)]; exact B.le_eps _)
    η hη
    (fun s hs x hx => by
      have hder : HasFDerivAt (fun y => W0 F N y + s * c y) (Wd F N B.g s x) x := by
        have := hasFDerivAt_W F N hFd B.g hgd s x
        convert this using 2 with y
        simp only [hc]; ring
      rw [norm_gradient_eq, hder.fderiv]
      apply hgrad s hs x
      intro h0; apply hx; simp only [hc, h0, neg_zero])
    (B.ε / 2) (by positivity)
  -- Brouwer on the negative disc
  set R := B.ε / η + 1 with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨θ, -, hθ⟩ := Brouwer.exists_zero_of_boundary_close R hR0
    (fun θ : YS n (N + 1) => proj2 (G (DAction.iota xs θ)))
    (continuous_proj2.comp (hGc.comp (continuous_iota xs))).continuousOn
    (fun θ _ => by
      have e : proj2 (G (DAction.iota xs θ)) - θ =
          proj2 (G (DAction.iota xs θ) - DAction.iota xs θ) := by
        rw [← proj2_sub, proj2_iota]
      rw [e]
      refine lt_of_le_of_lt ((norm_proj2_le _).trans (hGmove _)) ?_
      rw [hR]; linarith)
  set z := G (DAction.iota xs θ)
  -- lower bound for `W₀` on `{proj2 = 0}`
  have hlow : -(∑ k ∈ Finset.range N, (1 / (N:ℝ)) * ⨆ q, F (tk N k) q) ≤ W0 F N z := by
    have h1 := Qf_nonneg_of_proj2_eq_zero z hθ
    have h2 := Hpart_le F hF N z
    unfold W0; linarith
  -- upper bound on the negative disc
  have hup : W0 F N (DAction.iota xs θ) + c (DAction.iota xs θ) ≤
      -B.ε - ∑ k ∈ Finset.range N, (1 / (N:ℝ)) * ⨅ q, F (tk N k) q := by
    have h2 := le_Hpart F hF N (DAction.iota xs θ)
    have hL0 : Ll 0 (DAction.iota xs θ) = (xs, -θ ⟨0, Nat.succ_pos N⟩) := by
      rw [Ll_apply, Xl_apply, Finset.sum_range_zero, add_zero, xl_iota,
        pl_iota xs θ 0 (Nat.succ_pos N)]
    have hq : -‖θ‖ ^ 2 - B.g (xs, -θ ⟨0, Nat.succ_pos N⟩) ≤ -B.ε := by
      by_cases h1 : ‖θ ⟨0, Nat.succ_pos N⟩‖ ≤ 1
      · rw [B.center _ (by rwa [norm_neg])]
        nlinarith [norm_nonneg θ]
      · push_neg at h1
        have h3 : ‖θ ⟨0, Nat.succ_pos N⟩‖ ≤ ‖θ‖ := PiLp.norm_apply_le θ _
        have h4 := B.nonneg (xs, -θ ⟨0, Nat.succ_pos N⟩)
        have h5 := B.hε1
        nlinarith
    simp only [hc, W0, Qf_iota, hL0]
    linarith
  have hG := hGW (DAction.iota xs θ)
  have hgap : B.ε / 2 ≤ (1 / (N:ℝ)) * ∑ k ∈ Finset.range N, oscSlice F (((k:ℝ) + 1) / N) := by
    have e : (1 / (N:ℝ)) * ∑ k ∈ Finset.range N, oscSlice F (((k:ℝ) + 1) / N) =
        (∑ k ∈ Finset.range N, (1 / (N:ℝ)) * ⨆ q, F (tk N k) q) -
        ∑ k ∈ Finset.range N, (1 / (N:ℝ)) * ⨅ q, F (tk N k) q := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [oscSlice, tk]; ring
    rw [e]; linarith
  have := hriem N (le_max_right _ _)
  linarith

/-- **Rigidity of the zero section** `ℝⁿ × {0} ⊆ ℝ²ⁿ`, proved by the discrete action
functional (no Floer theory). -/
theorem zeroSection_rigid_variational : IsDisplacementRigid (zeroSection n) := by
  rintro W hW ⟨z₀, hz₀W, hz₀Z⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW z₀ hz₀W
  have hr2 : 0 < r / 2 := by positivity
  have hsub : closedBall z₀ (r / 2) ⊆ closure W :=
    (closedBall_subset_ball (by linarith)).trans (hrW.trans subset_closure)
  have hz : z₀ = ((z₀.1, 0) : P n) := by
    simp only [zeroSection, mem_setOf_eq] at hz₀Z; ext <;> simp [hz₀Z]
  obtain ⟨B⟩ := exists_bump z₀.1 (r / 2) hr2
  have hpos : 0 < B.ε / 4 := by have := B.hε; positivity
  have key : ENNReal.ofReal (B.ε / 4) ≤ displacementEnergy W (zeroSection n) := by
    apply le_sInf
    rintro e ⟨F, φ, hF, hφ, hd, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    apply hoferLength_ge_of_displaces z₀.1 (r / 2) hr2 B F hF φ hφ
    rw [← hz]
    exact hd.mono_left (image_mono hsub)
  intro h0
  rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at key
  linarith

end GradRange.ZSV

assert_standard_axioms GradRange.ZSV.exists_bump GradRange.ZSV.no_crit GradRange.ZSV.grad_lower
  GradRange.ZSV.hoferLength_ge_of_displaces GradRange.ZSV.zeroSection_rigid_variational
