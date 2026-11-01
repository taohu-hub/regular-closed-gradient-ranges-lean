module
import all Mathlib.Basic.Real.Basic

public import GradientRanges.DiscreteAction
public import GradientRanges.DiscreteEuler
public import GradientRanges.Deformation
public import GradientRanges.Brouwer
public import GradientRanges.C0Invariance
public meta import ProofAudit

@[expose] public section

/-!
# Rigidity of the zero section by a finite-dimensional variational argument

This file and `GradientRanges/ZeroSectionRigid.lean` prove, without Floer theory, that the zero section `Z = ℝⁿ × {0}` of `ℝ²ⁿ` is
displacement rigid (`zeroSection_rigid_variational`). The quantitative statement is
`hoferLength_ge_of_displaces`: if the time-one map of a compactly supported Hamiltonian `F`
moves the closed ball of radius `r` around a point of `Z` off `Z`, then `𝓛(F) ≥ a(r) > 0`.

The proof uses the discrete action functional of broken trajectories (Chaperon's method of
broken geodesics, with the implicit symplectic Euler scheme, whose generating functions are
explicit):

`W_s(z) = ∑ᵢ ⟪pᵢ, Δᵢ⟫ - (1/N) ∑_{k<N} F((k+1)/N, X_{k+1}, p_{k+1}) - s·ε β(x₀) χ(p₀)`.

* Critical points of `W_s` are discrete chords from `Z` to `Z` (`crit_equations`); by the
  convergence of the scheme (`discrete_orbit_close`) none of them starts near the displaced
  ball, so `‖∇W_s‖ ≥ η > 0` where the bump term is active (`grad_lower`, in `ZeroSectionRigid.lean`).
* The deformation lemma (`Deformation.exists_deformation`) gives `G` with
  `W₀ ∘ G ≤ W₁ + ε/2` moving points a bounded distance.
* The negative disc `ι` through the centre of the bump satisfies `W₁ ∘ ι ≤ -ε - R⁻`, while by
  Brouwer's theorem (`Brouwer.exists_zero_of_boundary_close`) the deformed disc `G ∘ ι` meets
  `{Δ = p}`, where `W₀ ≥ -R⁺`. Hence `R⁺ - R⁻ ≥ ε/2`, and `R⁺ - R⁻` is a Riemann sum of the
  Hofer length (`riemann_osc_le`).
-/

open Set Metric Filter Topology

noncomputable section

namespace GradRange.ZSV

open GradRange.DAction

variable {n : ℕ}

/-! ## Coordinate vectors -/

/-- The vector with a single nonzero coordinate `w` at index `o`. -/
def ev {m : ℕ} (o : Idx m) (w : E n) : VS n m := WithLp.toLp 2 (Pi.single o w)

theorem ev_apply {m : ℕ} (o o' : Idx m) (w : E n) :
    (ev o w) o' = if o' = o then w else 0 := by
  simp [ev, Pi.single_apply]

theorem xl_ev {m : ℕ} (o : Idx m) (w : E n) : xl (ev o w) = if o = none then w else 0 := by
  rw [xl_apply, ev_apply]; simp [eq_comm]

theorem Dl_ev {m : ℕ} (i : ℕ) (o : Idx m) (w : E n) :
    Dl i (ev o w) = if ∃ h : i < m, o = some (Sum.inl ⟨i, h⟩) then w else 0 := by
  rw [Dl_apply]
  by_cases hi : i < m
  · rw [dif_pos hi, ev_apply]
    by_cases ho : o = some (Sum.inl ⟨i, hi⟩)
    · rw [if_pos ho.symm, if_pos ⟨hi, ho⟩]
    · rw [if_neg (Ne.symm ho), if_neg]; rintro ⟨_, h⟩; exact ho h
  · rw [dif_neg hi, if_neg]; rintro ⟨h, _⟩; exact hi h

theorem pl_ev {m : ℕ} (i : ℕ) (o : Idx m) (w : E n) :
    pl i (ev o w) = if ∃ h : i < m, o = some (Sum.inr ⟨i, h⟩) then w else 0 := by
  rw [pl_apply]
  by_cases hi : i < m
  · rw [dif_pos hi, ev_apply]
    by_cases ho : o = some (Sum.inr ⟨i, hi⟩)
    · rw [if_pos ho.symm, if_pos ⟨hi, ho⟩]
    · rw [if_neg (Ne.symm ho), if_neg]; rintro ⟨_, h⟩; exact ho h
  · rw [dif_neg hi, if_neg]; rintro ⟨h, _⟩; exact hi h

/-! ## Partial gradients as derivatives -/

theorem fderiv_apply_inl (H : P n → ℝ) (q : P n) (hH : DifferentiableAt ℝ H q) (w : E n) :
    fderiv ℝ H q (w, 0) = inner ℝ (gradX H q) w := by
  have h1 : HasFDerivAt (fun x => H (x, q.2))
      ((fderiv ℝ H q).comp (ContinuousLinearMap.inl ℝ (E n) (E n))) q.1 := by
    have := hH.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
    simpa only [Function.comp_def] using this
  rw [gradX, ← Deformation.fderiv_apply_eq_inner_gradient, h1.fderiv]
  rfl

theorem fderiv_apply_inr (H : P n → ℝ) (q : P n) (hH : DifferentiableAt ℝ H q) (w : E n) :
    fderiv ℝ H q (0, w) = inner ℝ (gradP H q) w := by
  have h1 : HasFDerivAt (fun p => H (q.1, p))
      ((fderiv ℝ H q).comp (ContinuousLinearMap.inr ℝ (E n) (E n))) q.2 := by
    have := hH.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
    simpa only [Function.comp_def] using this
  rw [gradP, ← Deformation.fderiv_apply_eq_inner_gradient, h1.fderiv]
  rfl

section evLemmas

variable {m : ℕ}

theorem Dl_ev_none (i : ℕ) (w : E n) : Dl i (ev (none : Idx m) w) = 0 := by
  rw [Dl_ev, if_neg]; rintro ⟨_, h⟩; cases h

theorem pl_ev_none (i : ℕ) (w : E n) : pl i (ev (none : Idx m) w) = 0 := by
  rw [pl_ev, if_neg]; rintro ⟨_, h⟩; cases h

theorem Xl_ev_none (i : ℕ) (w : E n) : Xl i (ev (none : Idx m) w) = w := by
  rw [Xl_apply, xl_ev, if_pos rfl]; simp [Dl_ev_none]

theorem Dl_ev_inl (i j : ℕ) (hj : j < m) (w : E n) :
    Dl i (ev (some (Sum.inl ⟨j, hj⟩) : Idx m) w) = if i = j then w else 0 := by
  rw [Dl_ev]
  by_cases hij : i = j
  · subst hij; rw [if_pos ⟨hj, rfl⟩, if_pos rfl]
  · rw [if_neg, if_neg hij]
    rintro ⟨h, he⟩
    simp only [Option.some.injEq, Sum.inl.injEq, Fin.mk.injEq] at he
    exact hij he.symm

theorem pl_ev_inl (i j : ℕ) (hj : j < m) (w : E n) :
    pl i (ev (some (Sum.inl ⟨j, hj⟩) : Idx m) w) = 0 := by
  rw [pl_ev, if_neg]; rintro ⟨_, h⟩; cases h

theorem Xl_ev_inl (i j : ℕ) (hj : j < m) (w : E n) :
    Xl i (ev (some (Sum.inl ⟨j, hj⟩) : Idx m) w) = if j < i then w else 0 := by
  rw [Xl_apply, xl_ev, if_neg (by simp), zero_add]
  simp_rw [Dl_ev_inl _ j hj]
  rw [Finset.sum_ite_eq' (Finset.range i) j (fun _ => w)]
  simp

theorem Dl_ev_inr (i j : ℕ) (hj : j < m) (w : E n) :
    Dl i (ev (some (Sum.inr ⟨j, hj⟩) : Idx m) w) = 0 := by
  rw [Dl_ev, if_neg]; rintro ⟨_, h⟩; cases h

theorem pl_ev_inr (i j : ℕ) (hj : j < m) (w : E n) :
    pl i (ev (some (Sum.inr ⟨j, hj⟩) : Idx m) w) = if i = j then w else 0 := by
  rw [pl_ev]
  by_cases hij : i = j
  · subst hij; rw [if_pos ⟨hj, rfl⟩, if_pos rfl]
  · rw [if_neg, if_neg hij]
    rintro ⟨h, he⟩
    simp only [Option.some.injEq, Sum.inr.injEq, Fin.mk.injEq] at he
    exact hij he.symm

theorem Xl_ev_inr (i j : ℕ) (hj : j < m) (w : E n) :
    Xl i (ev (some (Sum.inr ⟨j, hj⟩) : Idx m) w) = 0 := by
  rw [Xl_apply, xl_ev, if_neg (by simp), zero_add]
  simp [Dl_ev_inr _ j hj]

theorem Qd_ev_none (z : VS n m) (w : E n) : Qd z (ev none w) = 0 := by
  rw [Qd_apply]; simp [Dl_ev_none, pl_ev_none]

theorem Qd_ev_inl (z : VS n m) (j : ℕ) (hj : j < m) (w : E n) :
    Qd z (ev (some (Sum.inl ⟨j, hj⟩)) w) = inner ℝ (pl j z) w := by
  rw [Qd_apply]
  simp_rw [Dl_ev_inl _ j hj, pl_ev_inl _ j hj, inner_zero_left, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => (apply_ite (inner ℝ (pl i z)) (i = j) w 0))]
  simp_rw [inner_zero_right]
  rw [Finset.sum_ite_eq' (Finset.range m) j (fun i => inner ℝ (pl i z) w)]
  simp [hj]

theorem Qd_ev_inr (z : VS n m) (j : ℕ) (hj : j < m) (w : E n) :
    Qd z (ev (some (Sum.inr ⟨j, hj⟩)) w) = inner ℝ w (Dl j z) := by
  rw [Qd_apply]
  simp_rw [Dl_ev_inr _ j hj, pl_ev_inr _ j hj, inner_zero_right, zero_add]
  rw [Finset.sum_congr rfl (fun i _ => (apply_ite (fun a => inner ℝ a (Dl i z)) (i = j) w 0))]
  simp_rw [inner_zero_left]
  rw [Finset.sum_ite_eq' (Finset.range m) j (fun i => inner ℝ w (Dl i z))]
  simp [hj]

end evLemmas

/-! ## The discrete action functional -/

section Action

variable (F : ℝ → P n → ℝ) (N : ℕ)

/-- Sample times `(k+1)/N`. -/
def tk (N k : ℕ) : ℝ := ((k:ℝ) + 1) / N

/-- Hamiltonian part `(1/N) ∑_{k<N} F((k+1)/N, X_{k+1}, p_{k+1})`. -/
def Hpart (z : VS n (N + 1)) : ℝ :=
  ∑ k ∈ Finset.range N, (1 / (N:ℝ)) * F (tk N k) (Ll (k + 1) z)

/-- The discrete action without the bump term. -/
def W0 (z : VS n (N + 1)) : ℝ := Qf z - Hpart F N z

/-- The derivative of `W0 - s · g(x₀, p₀)`. -/
def Wd (g : P n → ℝ) (s : ℝ) (z : VS n (N + 1)) : VS n (N + 1) →L[ℝ] ℝ :=
  Qd z - ∑ k ∈ Finset.range N,
    (1 / (N:ℝ)) • (fderiv ℝ (F (tk N k)) (Ll (k + 1) z)).comp (Ll (k + 1))
    - s • (fderiv ℝ g (Ll 0 z)).comp (Ll 0)

theorem Wd_apply (g : P n → ℝ) (s : ℝ) (z v : VS n (N + 1)) :
    Wd F N g s z v = Qd z v - ∑ k ∈ Finset.range N,
      (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z) (Ll (k + 1) v)
      - s * fderiv ℝ g (Ll 0 z) (Ll 0 v) := by
  simp [Wd, ContinuousLinearMap.sum_apply]

theorem hasFDerivAt_W (hF : ∀ t, Differentiable ℝ (F t)) (g : P n → ℝ)
    (hg : Differentiable ℝ g) (s : ℝ) (z : VS n (N + 1)) :
    HasFDerivAt (fun z => W0 F N z - s * g (Ll 0 z)) (Wd F N g s z) z := by
  unfold W0 Hpart Wd
  apply HasFDerivAt.sub
  · apply (hasFDerivAt_Qf z).sub
    apply HasFDerivAt.fun_sum
    intro k _
    exact ((hF _ _).hasFDerivAt.comp z (Ll (k + 1)).hasFDerivAt).const_mul _
  · exact ((hg _).hasFDerivAt.comp z (Ll 0).hasFDerivAt).const_mul s

theorem eq_of_inner_eq {a b : E n} (h : ∀ w, inner ℝ a w = inner ℝ b w) : a = b :=
  ext_inner_right ℝ h

/-- **Critical point equations.** -/
theorem crit_equations (hF : ∀ t, Differentiable ℝ (F t)) (g : P n → ℝ)
    (hg : Differentiable ℝ g) (s : ℝ) (z : VS n (N + 1)) (hz : Wd F N g s z = 0) :
    Dl 0 z = s • gradP g (Ll 0 z) ∧
    (∀ k < N, Dl (k + 1) z = (1 / (N:ℝ)) • gradP (F (tk N k)) (Ll (k + 1) z)) ∧
    (∀ j ≤ N, pl j z = ∑ k ∈ (Finset.range N).filter (fun k => j ≤ k),
      (1 / (N:ℝ)) • gradX (F (tk N k)) (Ll (k + 1) z)) ∧
    (∑ k ∈ Finset.range N, (1 / (N:ℝ)) • gradX (F (tk N k)) (Ll (k + 1) z) +
      s • gradX g (Ll 0 z) = 0) := by
  have hv : ∀ v, Wd F N g s z v = 0 := fun v => by rw [hz]; rfl
  have h00 : ((0 : E n), (0 : E n)) = (0 : P n) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply eq_of_inner_eq
    intro w
    have h := hv (ev (some (Sum.inr ⟨0, Nat.succ_pos N⟩)) w)
    rw [Wd_apply, Qd_ev_inr] at h
    have hs : ∀ k ∈ Finset.range N, (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z)
        (Ll (k + 1) (ev (some (Sum.inr ⟨0, Nat.succ_pos N⟩)) w)) = 0 := by
      intro k _
      rw [Ll_apply (k + 1) (ev _ w), Xl_ev_inr, pl_ev_inr, if_neg (Nat.succ_ne_zero k), h00,
        map_zero, mul_zero]
    rw [Finset.sum_eq_zero hs, Ll_apply (0 : ℕ) (ev _ w), Xl_ev_inr, pl_ev_inr, if_pos rfl,
      fderiv_apply_inr g _ (hg _)] at h
    rw [inner_smul_left, real_inner_comm]
    simp only [RCLike.conj_to_real]
    linarith
  · intro k₀ hk₀
    apply eq_of_inner_eq
    intro w
    have hk1 : k₀ + 1 < N + 1 := by omega
    have h := hv (ev (some (Sum.inr ⟨k₀ + 1, hk1⟩)) w)
    rw [Wd_apply, Qd_ev_inr] at h
    have hs : ∑ k ∈ Finset.range N, (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z)
        (Ll (k + 1) (ev (some (Sum.inr ⟨k₀ + 1, hk1⟩)) w)) =
        (1 / (N:ℝ)) * inner ℝ (gradP (F (tk N k₀)) (Ll (k₀ + 1) z)) w := by
      rw [Finset.sum_eq_single k₀]
      · rw [Ll_apply (k₀ + 1) (ev _ w), Xl_ev_inr, pl_ev_inr, if_pos rfl,
          fderiv_apply_inr _ _ (hF _ _)]
      · intro k _ hk
        rw [Ll_apply (k + 1) (ev _ w), Xl_ev_inr, pl_ev_inr, if_neg (by omega), h00, map_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 hk₀) h
    rw [hs, Ll_apply (0 : ℕ) (ev _ w), Xl_ev_inr, pl_ev_inr, if_neg (by omega), h00, map_zero,
      mul_zero, sub_zero] at h
    rw [inner_smul_left]
    have hc := real_inner_comm w (Dl (k₀ + 1) z)
    simp only [RCLike.conj_to_real]
    linarith
  · intro j hj
    apply eq_of_inner_eq
    intro w
    have hj1 : j < N + 1 := by omega
    have h := hv (ev (some (Sum.inl ⟨j, hj1⟩)) w)
    rw [Wd_apply, Qd_ev_inl] at h
    have hs : ∀ k ∈ Finset.range N, (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z)
        (Ll (k + 1) (ev (some (Sum.inl ⟨j, hj1⟩)) w)) =
        if j ≤ k then (1 / (N:ℝ)) * inner ℝ (gradX (F (tk N k)) (Ll (k + 1) z)) w else 0 := by
      intro k _
      rw [Ll_apply (k + 1) (ev _ w), Xl_ev_inl, pl_ev_inl]
      by_cases hjk : j ≤ k
      · rw [if_pos (by omega), if_pos hjk, fderiv_apply_inl _ _ (hF _ _)]
      · rw [if_neg (by omega), if_neg hjk, h00, map_zero, mul_zero]
    rw [Finset.sum_congr rfl hs, ← Finset.sum_filter, Ll_apply (0 : ℕ) (ev _ w), Xl_ev_inl,
      pl_ev_inl, if_neg (Nat.not_lt_zero j), h00, map_zero, mul_zero, sub_zero] at h
    rw [sum_inner]
    simp_rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    linarith
  · apply eq_of_inner_eq
    intro w
    have h := hv (ev none w)
    rw [Wd_apply, Qd_ev_none] at h
    have hs : ∀ k ∈ Finset.range N, (1 / (N:ℝ)) * fderiv ℝ (F (tk N k)) (Ll (k + 1) z)
        (Ll (k + 1) (ev (none : Idx (N + 1)) w)) =
        (1 / (N:ℝ)) * inner ℝ (gradX (F (tk N k)) (Ll (k + 1) z)) w := by
      intro k _
      rw [Ll_apply (k + 1) (ev (none : Idx (N + 1)) w), Xl_ev_none, pl_ev_none, fderiv_apply_inl _ _ (hF _ _)]
    rw [Finset.sum_congr rfl hs, Ll_apply (0 : ℕ) (ev (none : Idx (N + 1)) w), Xl_ev_none, pl_ev_none,
      fderiv_apply_inl g _ (hg _)] at h
    rw [inner_add_left, sum_inner, inner_zero_left]
    simp_rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    linarith

end Action

end GradRange.ZSV

assert_standard_axioms GradRange.ZSV.crit_equations GradRange.ZSV.hasFDerivAt_W
