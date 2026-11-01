module

public import Mathlib
public meta import ProofAudit

@[expose] public section

/-!
# A deformation lemma for a one-parameter family of functions

Let `W_s = W₀ + s c` (`0 ≤ s ≤ 1`) on a real inner product space, with Lipschitz derivatives,
`|c| ≤ A`, and suppose that `‖∇W_s‖ ≥ η > 0` wherever `c ≠ 0`. Then for every `ε > 0` there is
a continuous map `G` moving points by at most `A / η` with `W₀ ∘ G ≤ W₁ + ε`.

`G` is a composition of `M` explicit small gradient steps; each step trades the change of
parameter `1/M` against a decrease of `W` along `∇W_s`, up to an error `O(1/M²)`.
This replaces the flow `∂ₛψ = -(∂ₛW)∇W/|∇W|²` and needs no ODE theory.
-/

open Set Metric

noncomputable section

namespace GradRange.Deformation

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Second-order upper bound for a function with `K`-Lipschitz derivative. -/
theorem le_add_fderiv_add_sq (f : X → ℝ) (hf : Differentiable ℝ f) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ K * ‖x - y‖) (x v : X) :
    f (x + v) ≤ f x + fderiv ℝ f x v + K * ‖v‖ ^ 2 := by
  set g : X → ℝ := fun y => f y - fderiv ℝ f x y with hg
  have hgd : ∀ y, HasFDerivAt g (fderiv ℝ f y - fderiv ℝ f x) y := fun y =>
    (hf y).hasFDerivAt.sub (fderiv ℝ f x).hasFDerivAt
  have hbound : ∀ y ∈ segment ℝ x (x + v), ‖fderiv ℝ g y‖ ≤ K * ‖v‖ := by
    intro y hy
    rw [(hgd y).fderiv]
    refine (hK y x).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rw [segment_eq_image'] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have := (convex_segment x (x + v)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (hgd y).differentiableAt) hbound (left_mem_segment ℝ x (x + v))
    (right_mem_segment ℝ x (x + v))
  simp only [hg, add_sub_cancel_left, map_add] at this
  have h2 := le_abs_self (f (x + v) - (fderiv ℝ f x x + fderiv ℝ f x v) - (f x - fderiv ℝ f x x))
  rw [Real.norm_eq_abs] at this
  nlinarith

variable [CompleteSpace X]

theorem fderiv_apply_eq_inner_gradient (f : X → ℝ) (x v : X) :
    fderiv ℝ f x v = inner ℝ (gradient f x) v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

/-- One gradient step. -/
theorem step_estimate (W : X → ℝ) (hW : Differentiable ℝ W) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ x y, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ K * ‖x - y‖)
    (c : X → ℝ) (A η τ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hA : ∀ x, |c x| ≤ A)
    (hgrad : ∀ x, c x ≠ 0 → η ≤ ‖gradient W x‖) (x : X) :
    ‖(τ * c x / max (‖gradient W x‖ ^ 2) (η ^ 2)) • gradient W x‖ ≤ τ * A / η ∧
    W (x + (τ * c x / max (‖gradient W x‖ ^ 2) (η ^ 2)) • gradient W x) ≤
      W x + τ * c x + K * (τ * A / η) ^ 2 := by
  set g := gradient W x with hg
  set m := max (‖g‖ ^ 2) (η ^ 2) with hm
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have ham : ‖g‖ * η ≤ m := by
    rcases le_total η ‖g‖ with h | h
    · exact le_trans (by nlinarith [norm_nonneg g]) (le_max_left _ _)
    · exact le_trans (by nlinarith [norm_nonneg g]) (le_max_right _ _)
  have hnv : ‖(τ * c x / m) • g‖ ≤ τ * A / η := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hτ, abs_of_pos hm0,
      div_mul_eq_mul_div, div_le_div_iff₀ hm0 hη]
    have h1 := hA x
    have h2 : 0 ≤ |c x| := abs_nonneg _
    calc τ * |c x| * ‖g‖ * η = τ * |c x| * (‖g‖ * η) := by ring
      _ ≤ τ * A * m := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hτ) ham (by positivity)
          (mul_nonneg hτ (h2.trans h1))
  refine ⟨hnv, ?_⟩
  have hT := le_add_fderiv_add_sq W hW K hK0 hK x ((τ * c x / m) • g)
  have hD : fderiv ℝ W x ((τ * c x / m) • g) = τ * c x := by
    rw [fderiv_apply_eq_inner_gradient, ← hg, inner_smul_right, real_inner_self_eq_norm_sq]
    by_cases hc : c x = 0
    · simp [hc]
    · have h1 := hgrad x hc
      rw [← hg] at h1
      have : m = ‖g‖ ^ 2 := max_eq_left (by nlinarith)
      rw [this]
      field_simp
      have : ‖g‖ ≠ 0 := by linarith
      field_simp
  rw [hD] at hT
  have hsq : ‖(τ * c x / m) • g‖ ^ 2 ≤ (τ * A / η) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnv 2
  nlinarith

/-- **Deformation lemma.** -/
theorem exists_deformation (W₀ c : X → ℝ) (hW₀ : Differentiable ℝ W₀) (hc : Differentiable ℝ c)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hlipW : ∀ x y, ‖fderiv ℝ W₀ x - fderiv ℝ W₀ y‖ ≤ L * ‖x - y‖)
    (hlipc : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ L * ‖x - y‖)
    (A : ℝ) (hA : ∀ x, |c x| ≤ A) (η : ℝ) (hη : 0 < η)
    (hgrad : ∀ s ∈ Icc (0:ℝ) 1, ∀ x, c x ≠ 0 → η ≤ ‖gradient (fun y => W₀ y + s * c y) x‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ G : X → X, Continuous G ∧ (∀ x, ‖G x - x‖ ≤ A / η) ∧
      ∀ x, W₀ (G x) ≤ W₀ x + c x + ε := by
  set W : ℝ → X → ℝ := fun s y => W₀ y + s * c y with hW
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hWd : ∀ s, Differentiable ℝ (W s) := fun s => hW₀.add (hc.const_mul s)
  have hWf : ∀ s y, fderiv ℝ (W s) y = fderiv ℝ W₀ y + s • fderiv ℝ c y := by
    intro s y
    exact ((hW₀ y).hasFDerivAt.add ((hc y).hasFDerivAt.const_mul s)).fderiv
  have hWlip : ∀ s ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖fderiv ℝ (W s) x - fderiv ℝ (W s) y‖ ≤ (2 * L) * ‖x - y‖ := by
    intro s hs x y
    rw [hWf, hWf]
    have : fderiv ℝ W₀ x + s • fderiv ℝ c x - (fderiv ℝ W₀ y + s • fderiv ℝ c y)
        = (fderiv ℝ W₀ x - fderiv ℝ W₀ y) + s • (fderiv ℝ c x - fderiv ℝ c y) := by
      rw [smul_sub]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have h1 := hlipW x y
    have h2 := hlipc x y
    have h3 : s * ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ 1 * (L * ‖x - y‖) :=
      mul_le_mul hs.2 h2 (norm_nonneg _) zero_le_one
    nlinarith
  have hgc : ∀ s ∈ Icc (0:ℝ) 1, Continuous (gradient (W s)) := by
    intro s hs
    have : Continuous (fderiv ℝ (W s)) := by
      have hl : LipschitzWith (2 * L).toNNReal (fderiv ℝ (W s)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
        exact hWlip s hs x y
      exact hl.continuous
    exact (InnerProductSpace.toDual ℝ X).symm.continuous.comp this
  -- number of steps
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (2 * L * A ^ 2 / (η ^ 2 * ε))
  set M : ℕ := M₀ + 1 with hM
  have hMpos : (0:ℝ) < M := by positivity
  set τ : ℝ := 1 / M with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hτM : (M:ℝ) * τ = 1 := by rw [hτ]; field_simp
  set E : ℝ := 2 * L * (τ * A / η) ^ 2 with hE
  set step : ℝ → X → X := fun s x =>
    x + (τ * c x / max (‖gradient (W s) x‖ ^ 2) (η ^ 2)) • gradient (W s) x with hstep
  have hstepc : ∀ s ∈ Icc (0:ℝ) 1, Continuous (step s) := by
    intro s hs
    apply continuous_id.add
    apply Continuous.smul _ (hgc s hs)
    apply Continuous.div (continuous_const.mul hc.continuous)
      (((hgc s hs).norm.pow 2).max continuous_const)
    intro x
    exact (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'
  have key : ∀ k : ℕ, k ≤ M → ∃ G : X → X, Continuous G ∧
      (∀ x, ‖G x - x‖ ≤ k * (τ * A / η)) ∧ ∀ x, W (1 - k * τ) (G x) ≤ W 1 x + k * E := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨id, continuous_id, fun x => by simp, fun x => by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨G, hG, hGd, hGW⟩ := ih (Nat.le_of_succ_le hk)
      set s : ℝ := 1 - (k + 1 : ℕ) * τ with hs
      have hsI : s ∈ Icc (0:ℝ) 1 := by
        have : ((k + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hk
        constructor
        · rw [hs]; nlinarith
        · rw [hs]; have : (0:ℝ) ≤ ((k+1 : ℕ) : ℝ) * τ := by positivity
          linarith
      refine ⟨step s ∘ G, (hstepc s hsI).comp hG, fun x => ?_, fun x => ?_⟩
      · have h1 := (step_estimate (W s) (hWd s) (2 * L) (by positivity) (hWlip s hsI) c A η τ hη
          hτ0 hA (hgrad s hsI) (G x)).1
        have h2 := hGd x
        simp only [Function.comp_apply, hstep]
        calc ‖G x + (τ * c (G x) / max (‖gradient (W s) (G x)‖ ^ 2) (η ^ 2)) •
              gradient (W s) (G x) - x‖
            ≤ ‖(τ * c (G x) / max (‖gradient (W s) (G x)‖ ^ 2) (η ^ 2)) •
              gradient (W s) (G x)‖ + ‖G x - x‖ := by
              rw [show G x + (τ * c (G x) / max (‖gradient (W s) (G x)‖ ^ 2) (η ^ 2)) •
                gradient (W s) (G x) - x = (τ * c (G x) / max (‖gradient (W s) (G x)‖ ^ 2)
                (η ^ 2)) • gradient (W s) (G x) + (G x - x) by abel]
              exact norm_add_le _ _
          _ ≤ τ * A / η + k * (τ * A / η) := add_le_add h1 h2
          _ = ((k + 1 : ℕ) : ℝ) * (τ * A / η) := by push_cast; ring
      · have h1 := (step_estimate (W s) (hWd s) (2 * L) (by positivity) (hWlip s hsI) c A η τ hη
          hτ0 hA (hgrad s hsI) (G x)).2
        have h2 := hGW x
        simp only [Function.comp_apply, hstep]
        have h3 : W s (G x) + τ * c (G x) = W (1 - k * τ) (G x) := by
          simp only [hW, hs]; push_cast; ring
        calc W s (G x + (τ * c (G x) / max (‖gradient (W s) (G x)‖ ^ 2) (η ^ 2)) •
              gradient (W s) (G x)) ≤ W s (G x) + τ * c (G x) + E := h1
          _ ≤ W 1 x + k * E + E := by rw [h3]; linarith
          _ = W 1 x + ((k + 1 : ℕ) : ℝ) * E := by push_cast; ring
  obtain ⟨G, hG, hGd, hGW⟩ := key M le_rfl
  refine ⟨G, hG, fun x => ?_, fun x => ?_⟩
  · have := hGd x
    rwa [show (M:ℝ) * (τ * A / η) = A / η by
      rw [show (M:ℝ) * (τ * A / η) = (M * τ) * A / η by ring, hτM, one_mul]] at this
  · have := hGW x
    rw [hτM, sub_self] at this
    simp only [hW, zero_mul, add_zero, one_mul] at this
    have hME : (M:ℝ) * E < ε := by
      have : (M:ℝ) * E = 2 * L * A ^ 2 / (η ^ 2 * M) := by
        rw [hE, hτ]; field_simp
      rw [this, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hM₀
      have : (M₀ : ℝ) < M := by rw [hM]; push_cast; linarith
      nlinarith [mul_pos (pow_pos hη 2) hε]
    linarith

end GradRange.Deformation

assert_standard_axioms GradRange.Deformation.exists_deformation
