module

public import GradientRanges.Defs
public meta import ProofAudit

@[expose] public section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

/-!
# The finite-dimensional space of broken trajectories

A broken trajectory with `m` steps is recorded by a point `z` of
`VS n m = ℓ²(Option (Fin m ⊕ Fin m); ℝⁿ)`:

* `xl z = z none` is the initial position `x₀`;
* `Dl i z = z (some (inl i))` is the `i`-th position increment `Δᵢ`;
* `pl i z = z (some (inr i))` is the `i`-th momentum `pᵢ`.

The positions are `Xl j z = x₀ + Δ₀ + ⋯ + Δ_{j-1}` and `Ll j z = (Xl j z, pl j z)`.
The quadratic part of the discrete action is `Qf z = ∑ᵢ ⟪pᵢ, Δᵢ⟫`.
This file collects the linear algebra and the regularity estimates needed for the discrete
action functional.
-/

open Set Metric

noncomputable section

namespace GradRange.DAction

variable {n m : ℕ}

/-- Index set of the coordinates of a broken trajectory. -/
abbrev Idx (m : ℕ) := Option (Fin m ⊕ Fin m)

/-- The space of broken trajectories. -/
abbrev VS (n m : ℕ) := PiLp 2 (fun _ : Idx m => E n)

/-- The fibre space `ℓ²(Fin m; ℝⁿ)` (the negative directions of `Qf`). -/
abbrev YS (n m : ℕ) := PiLp 2 (fun _ : Fin m => E n)

/-- Initial position. -/
def xl : VS n m →L[ℝ] E n := PiLp.proj 2 (fun _ : Idx m => E n) none

/-- Position increments (zero for out-of-range indices). -/
def Dl (i : ℕ) : VS n m →L[ℝ] E n :=
  if h : i < m then PiLp.proj 2 (fun _ : Idx m => E n) (some (Sum.inl ⟨i, h⟩)) else 0

/-- Momenta (zero for out-of-range indices). -/
def pl (i : ℕ) : VS n m →L[ℝ] E n :=
  if h : i < m then PiLp.proj 2 (fun _ : Idx m => E n) (some (Sum.inr ⟨i, h⟩)) else 0

/-- Positions `x₀ + Δ₀ + ⋯ + Δ_{j-1}`. -/
def Xl (j : ℕ) : VS n m →L[ℝ] E n := xl + ∑ i ∈ Finset.range j, Dl i

/-- The phase-space point `(Xⱼ, pⱼ)`. -/
def Ll (j : ℕ) : VS n m →L[ℝ] P n := (Xl j).prod (pl j)

/-- Quadratic part of the discrete action. -/
def Qf (z : VS n m) : ℝ := ∑ i ∈ Finset.range m, inner ℝ (pl i z) (Dl i z)

theorem xl_apply (z : VS n m) : xl z = z none := rfl

theorem Dl_apply (i : ℕ) (z : VS n m) :
    Dl i z = if h : i < m then z (some (Sum.inl ⟨i, h⟩)) else 0 := by
  unfold Dl; split_ifs <;> rfl

theorem pl_apply (i : ℕ) (z : VS n m) :
    pl i z = if h : i < m then z (some (Sum.inr ⟨i, h⟩)) else 0 := by
  unfold pl; split_ifs <;> rfl

theorem Xl_apply (j : ℕ) (z : VS n m) : Xl j z = xl z + ∑ i ∈ Finset.range j, Dl i z := by
  simp [Xl, ContinuousLinearMap.sum_apply]

theorem Ll_apply (j : ℕ) (z : VS n m) : Ll j z = (Xl j z, pl j z) := rfl

theorem norm_coord_le (z : VS n m) (o : Idx m) : ‖z o‖ ≤ ‖z‖ := PiLp.norm_apply_le z o

theorem norm_Dl_le (i : ℕ) (z : VS n m) : ‖Dl i z‖ ≤ ‖z‖ := by
  rw [Dl_apply]; split_ifs
  · exact norm_coord_le _ _
  · simp

theorem norm_pl_le (i : ℕ) (z : VS n m) : ‖pl i z‖ ≤ ‖z‖ := by
  rw [pl_apply]; split_ifs
  · exact norm_coord_le _ _
  · simp

theorem norm_sq_VS (z : VS n m) :
    ‖z‖ ^ 2 = ‖xl z‖ ^ 2 + ∑ i : Fin m, (‖z (some (Sum.inl i))‖ ^ 2 + ‖z (some (Sum.inr i))‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

/-! ## The swap vector `(0, p, Δ)` -/

/-- The vector exchanging increments and momenta. -/
def swapv (z : VS n m) : VS n m :=
  WithLp.toLp 2 (fun o => match o with
    | none => 0
    | some (Sum.inl i) => z (some (Sum.inr i))
    | some (Sum.inr i) => z (some (Sum.inl i)))

theorem Dl_swapv (i : ℕ) (z : VS n m) : Dl i (swapv z) = pl i z := by
  rw [Dl_apply, pl_apply]; split_ifs <;> rfl

theorem pl_swapv (i : ℕ) (z : VS n m) : pl i (swapv z) = Dl i z := by
  rw [Dl_apply, pl_apply]; split_ifs <;> rfl

theorem norm_sq_swapv (z : VS n m) :
    ‖swapv z‖ ^ 2 = ∑ i : Fin m, (‖z (some (Sum.inl i))‖ ^ 2 + ‖z (some (Sum.inr i))‖ ^ 2) := by
  rw [norm_sq_VS]
  simp only [xl_apply, swapv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem norm_sq_eq_xl_swapv (z : VS n m) : ‖z‖ ^ 2 = ‖xl z‖ ^ 2 + ‖swapv z‖ ^ 2 := by
  rw [norm_sq_VS, norm_sq_swapv]

theorem sum_range_eq_sum_fin (f : ℕ → ℝ) : ∑ i ∈ Finset.range m, f i = ∑ i : Fin m, f i :=
  (Fin.sum_univ_eq_sum_range f m).symm

theorem sum_norm_sq_eq_norm_sq_swapv (z : VS n m) :
    ∑ i ∈ Finset.range m, (‖pl i z‖ ^ 2 + ‖Dl i z‖ ^ 2) = ‖swapv z‖ ^ 2 := by
  rw [norm_sq_swapv, sum_range_eq_sum_fin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pl_apply, Dl_apply, dif_pos i.isLt, dif_pos i.isLt, add_comm]

/-! ## The quadratic form -/

/-- The derivative of `Qf`. -/
def Qd (z : VS n m) : VS n m →L[ℝ] ℝ :=
  ∑ i ∈ Finset.range m, (fderivInnerCLM ℝ (pl i z, Dl i z)).comp ((pl i).prod (Dl i))

theorem Qd_apply (z v : VS n m) :
    Qd z v = ∑ i ∈ Finset.range m, (inner ℝ (pl i z) (Dl i v) + inner ℝ (pl i v) (Dl i z)) := by
  simp [Qd, ContinuousLinearMap.sum_apply, fderivInnerCLM_apply]

theorem hasFDerivAt_Qf (z : VS n m) : HasFDerivAt Qf (Qd z) z := by
  unfold Qf Qd
  apply HasFDerivAt.fun_sum
  intro i _
  exact (pl i).hasFDerivAt.inner ℝ (Dl i).hasFDerivAt

theorem differentiable_Qf : Differentiable ℝ (Qf : VS n m → ℝ) :=
  fun z => (hasFDerivAt_Qf z).differentiableAt

theorem fderiv_Qf (z : VS n m) : fderiv ℝ (Qf : VS n m → ℝ) z = Qd z := by
  letI : ContinuousSMul ℝ (VS n m) := IsBoundedSMul.continuousSMul
  exact (hasFDerivAt_Qf z).fderiv

theorem fderiv_Qf_lip (z z' : VS n m) :
    ‖fderiv ℝ (Qf : VS n m → ℝ) z - fderiv ℝ (Qf : VS n m → ℝ) z'‖ ≤ (2 * m) * ‖z - z'‖ := by
  rw [fderiv_Qf, fderiv_Qf]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [ContinuousLinearMap.sub_apply, Qd_apply, Qd_apply, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have key : ∀ i ∈ Finset.range m,
      ‖inner ℝ (pl i z) (Dl i v) + inner ℝ (pl i v) (Dl i z) -
        (inner ℝ (pl i z') (Dl i v) + inner ℝ (pl i v) (Dl i z'))‖ ≤ 2 * (‖z - z'‖ * ‖v‖) := by
    intro i _
    have e : inner ℝ (pl i z) (Dl i v) + inner ℝ (pl i v) (Dl i z) -
        (inner ℝ (pl i z') (Dl i v) + inner ℝ (pl i v) (Dl i z')) =
        inner ℝ (pl i (z - z')) (Dl i v) + inner ℝ (pl i v) (Dl i (z - z')) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := (abs_real_inner_le_norm (pl i (z - z')) (Dl i v)).trans
      (mul_le_mul (norm_pl_le i _) (norm_Dl_le i v) (norm_nonneg _) (norm_nonneg _))
    have h2 := (abs_real_inner_le_norm (pl i v) (Dl i (z - z'))).trans
      (mul_le_mul (norm_pl_le i v) (norm_Dl_le i _) (norm_nonneg _) (norm_nonneg _))
    linarith
  refine (Finset.sum_le_sum key).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith [norm_nonneg (z - z'), norm_nonneg v]

theorem Qd_swapv (z : VS n m) : Qd z (swapv z) = ‖swapv z‖ ^ 2 := by
  rw [Qd_apply, ← sum_norm_sq_eq_norm_sq_swapv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Dl_swapv, pl_swapv, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-! ## The linking data: the negative disc and its projection -/

/-- The negative disc through the base point `x`: `Δ = b`, `p = -b`. -/
def iota (x : E n) (b : YS n m) : VS n m :=
  WithLp.toLp 2 (fun o => match o with
    | none => x
    | some (Sum.inl i) => b i
    | some (Sum.inr i) => -b i)

/-- Projection onto the negative directions along `{Δ = p}`. -/
def proj2 (z : VS n m) : YS n m :=
  WithLp.toLp 2 (fun i => (1 / 2 : ℝ) • (z (some (Sum.inl i)) - z (some (Sum.inr i))))

theorem proj2_iota (x : E n) (b : YS n m) : proj2 (iota x b) = b := by
  apply PiLp.ext; intro i
  simp only [proj2, iota, sub_neg_eq_add]
  show (1 / 2 : ℝ) • (b i + b i) = b i
  rw [← two_smul ℝ (b i), smul_smul]; norm_num

theorem proj2_sub (z z' : VS n m) : proj2 z - proj2 z' = proj2 (z - z') := by
  apply PiLp.ext; intro i
  simp only [proj2, PiLp.sub_apply]
  show (1 / 2 : ℝ) • (z (some (Sum.inl i)) - z (some (Sum.inr i))) -
    (1 / 2 : ℝ) • (z' (some (Sum.inl i)) - z' (some (Sum.inr i))) =
    (1 / 2 : ℝ) • ((z - z') (some (Sum.inl i)) - (z - z') (some (Sum.inr i)))
  simp only [PiLp.sub_apply, ← smul_sub]; congr 1; abel

theorem norm_proj2_le (z : VS n m) : ‖proj2 z‖ ≤ ‖z‖ := by
  have h : ‖proj2 z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, norm_sq_VS]
    have h0 : 0 ≤ ‖xl z‖ ^ 2 := by positivity
    have : ∑ i : Fin m, ‖(proj2 z) i‖ ^ 2 ≤
        ∑ i : Fin m, (‖z (some (Sum.inl i))‖ ^ 2 + ‖z (some (Sum.inr i))‖ ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      show ‖(1 / 2 : ℝ) • (z (some (Sum.inl i)) - z (some (Sum.inr i)))‖ ^ 2 ≤ _
      rw [norm_smul, mul_pow]
      have := norm_sub_le (z (some (Sum.inl i))) (z (some (Sum.inr i)))
      have h1 : ‖z (some (Sum.inl i)) - z (some (Sum.inr i))‖ ^ 2 ≤
          (‖z (some (Sum.inl i))‖ + ‖z (some (Sum.inr i))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) this 2
      norm_num
      nlinarith [sq_nonneg (‖z (some (Sum.inl i))‖ - ‖z (some (Sum.inr i))‖)]
    linarith
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 h

theorem continuous_proj2 : Continuous (proj2 : VS n m → YS n m) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [dist_eq_norm, dist_eq_norm, proj2_sub, NNReal.coe_one, one_mul]
  exact norm_proj2_le _

theorem continuous_iota (x : E n) : Continuous (iota x : YS n m → VS n m) := by
  unfold iota
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro o
  rcases o with _ | (i | i)
  · exact continuous_const
  · exact PiLp.continuous_apply 2 _ i
  · exact (PiLp.continuous_apply 2 _ i).neg

theorem xl_iota (x : E n) (b : YS n m) : xl (iota x b) = x := rfl

theorem pl_iota (x : E n) (b : YS n m) (i : ℕ) (hi : i < m) :
    pl i (iota x b) = -b ⟨i, hi⟩ := by
  rw [pl_apply, dif_pos hi]; rfl

theorem Qf_iota (x : E n) (b : YS n m) : Qf (iota x b) = -‖b‖ ^ 2 := by
  rw [Qf, sum_range_eq_sum_fin, PiLp.norm_sq_eq_of_L2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pl_apply, Dl_apply, dif_pos i.isLt, dif_pos i.isLt]
  show inner ℝ (-b i) (b i) = -‖b i‖ ^ 2
  rw [inner_neg_left, real_inner_self_eq_norm_sq]

theorem Qf_nonneg_of_proj2_eq_zero (z : VS n m) (hz : proj2 z = 0) : 0 ≤ Qf z := by
  rw [Qf, sum_range_eq_sum_fin]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [pl_apply, Dl_apply, dif_pos i.isLt, dif_pos i.isLt]
  have h := congrArg (fun y : YS n m => y i) hz
  simp only [proj2] at h
  change (1 / 2 : ℝ) • (z (some (Sum.inl i)) - z (some (Sum.inr i))) = 0 at h
  rw [smul_eq_zero] at h
  rcases h with h | h
  · norm_num at h
  · rw [sub_eq_zero] at h
    rw [← h, real_inner_self_eq_norm_sq]; positivity

/-! ## Regularity of compositions -/

/-- A `C²` compactly supported function has bounded, Lipschitz derivative. -/
theorem fderiv_bounds_of_hasCompactSupport {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (g : V → ℝ) (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ B) ∧
      ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ L * ‖x - y‖ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hs1 : HasCompactSupport (fderiv ℝ g) := hs.fderiv (𝕜 := ℝ)
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) := hs1.fderiv (𝕜 := ℝ)
  obtain ⟨B, hB⟩ := h1.continuous.bounded_above_of_compact_support hs1
  obtain ⟨L, hL⟩ := (h1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hs2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨B, L, hB0, hL0, hB, fun x y => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (h1.differentiable (by norm_num)) z) (fun z _ => hL z) (mem_univ y) (mem_univ x)
  exact this

/-- Derivative of a composition with a continuous linear map. -/
theorem fderiv_comp_clm {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V → ℝ) (hg : Differentiable ℝ g)
    (L : X →L[ℝ] V) (z : X) : fderiv ℝ (fun z => g (L z)) z = (fderiv ℝ g (L z)).comp L :=
  ((hg (L z)).hasFDerivAt.comp z L.hasFDerivAt).fderiv

theorem comp_clm_bounds {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V → ℝ) (hg : Differentiable ℝ g)
    (L : X →L[ℝ] V) (B Lg : ℝ) (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B)
    (hLg : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ Lg * ‖x - y‖) (hLg0 : 0 ≤ Lg) :
    (∀ z, ‖fderiv ℝ (fun z => g (L z)) z‖ ≤ B * ‖L‖) ∧
    ∀ z z', ‖fderiv ℝ (fun z => g (L z)) z - fderiv ℝ (fun z => g (L z)) z'‖ ≤
      (Lg * ‖L‖ * ‖L‖) * ‖z - z'‖ := by
  refine ⟨fun z => ?_, fun z z' => ?_⟩
  · rw [fderiv_comp_clm g hg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
  · rw [fderiv_comp_clm g hg, fderiv_comp_clm g hg, ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hLg (L z) (L z')
    rw [← map_sub] at h1
    have h2 := L.le_opNorm (z - z')
    calc ‖fderiv ℝ g (L z) - fderiv ℝ g (L z')‖ * ‖L‖ ≤ (Lg * (‖L‖ * ‖z - z'‖)) * ‖L‖ :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hLg0))
            (norm_nonneg _)
      _ = (Lg * ‖L‖ * ‖L‖) * ‖z - z'‖ := by ring

end GradRange.DAction

assert_standard_axioms GradRange.DAction.fderiv_Qf_lip GradRange.DAction.Qf_nonneg_of_proj2_eq_zero
  GradRange.DAction.fderiv_bounds_of_hasCompactSupport
