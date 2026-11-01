module
import all Mathlib.Basic.NNReal.Defs
import all Mathlib.Basic.Real.Basic

public import GradientRanges.Defs

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Existence and uniqueness of Hamiltonian flows

These justify that `IsHamFlow F φ` determines the genuine flow `φ_F^t` (`0 ≤ t ≤ 1`):
it exists and is unique for every compactly supported smooth Hamiltonian (on `ℝ²ⁿ`, or
on `Tⁿ × ℝⁿ` through the universal cover).
-/

open Set Metric Filter Topology
open scoped ContDiff NNReal

namespace GradRange

/-! ## Generic ODE facts -/

theorem exists_flow_of_bounded_lipschitz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (v : ℝ → X → X) (K C : ℝ≥0)
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, LipschitzWith K (v t))
    (hcont : ∀ x, ContinuousOn (fun t => v t x) (Icc 0 1))
    (hbd : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖v t x‖ ≤ C) :
    ∃ φ : ℝ → X → X, ∀ z, φ 0 z = z ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun s => φ s z) (v t (φ t z)) (Icc 0 1) t := by
  have : ∀ z : X, ∃ α : ℝ → X, α 0 = z ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt α (v t (α t)) (Icc 0 1) t := by
    intro z
    have hPL : IsPicardLindelof v (tmin := 0) (tmax := 1) ⟨0, by simp⟩ z C 0 C K := by
      refine ⟨fun t ht => (hlip t ht).lipschitzOnWith, fun x _ => hcont x,
        fun t ht x _ => hbd t ht x, ?_⟩
      simp
    exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self le_rfl)
  choose α h0 hα using this
  exact ⟨fun s z => α z s, fun z => ⟨h0 z, hα z⟩⟩

theorem flow_unique_of_lipschitz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) (K : ℝ≥0)
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, LipschitzWith K (v t)) (f g : ℝ → X)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt f (v t (f t)) (Icc 0 1) t)
    (hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt g (v t (g t)) (Icc 0 1) t)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 1) := by
  have key : ∀ (u : ℝ → X), (∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (v t (u t)) (Icc 0 1) t) →
      ∀ t ∈ Ico (0:ℝ) 1, HasDerivWithinAt u (v t (u t)) (Ici t) t := by
    intro u hu t ht
    have h1 := hu t (Ico_subset_Icc_self ht)
    apply h1.mono_of_mem_nhdsWithin
    have : Icc t 1 ∈ nhdsWithin t (Ici t) := Icc_mem_nhdsGE ht.2
    exact Filter.mem_of_superset this (Icc_subset_Icc ht.1 le_rfl)
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ) (K := K)
    (fun t ht => (hlip t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousWithinAt) (key f hf) (fun _ _ => mem_univ _)
    (fun t ht => (hg t ht).continuousWithinAt) (key g hg) (fun _ _ => mem_univ _) h0

/-- A continuous function on `ℝ × X` which, for `t ∈ [0,1]`, only takes the value `0` and
values already taken over a compact set, is bounded on `[0,1] × X`. -/
theorem exists_bound_of_reduce {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    (g : ℝ × X → Y) (hg : Continuous g) (S : Set X) (hS : IsCompact S)
    (hred : ∀ t ∈ Icc (0:ℝ) 1, ∀ z, g (t, z) = 0 ∨ ∃ z' ∈ S, g (t, z) = g (t, z')) :
    ∃ C : ℝ≥0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z, ‖g (t, z)‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨⟨max M 0, le_max_right _ _⟩, fun t ht z => ?_⟩
  change ‖g (t, z)‖ ≤ max M 0
  rcases hred t ht z with h | ⟨z', hz', h⟩
  · rw [h, norm_zero]; exact le_max_right _ _
  · rw [h]; exact le_trans (hM (t, z') ⟨ht, hz'⟩) (le_max_left _ _)

variable {n : ℕ}

/-! ## Regularity of Hamiltonian vector fields -/

/-- The symplectic gradient of a covector: `ℓ ↦ (ℓ ∘ inr, -ℓ ∘ inl)` read through the
Riesz isomorphism. -/
noncomputable def symGradL : (P n →L[ℝ] ℝ) →L[ℝ] P n :=
  ContinuousLinearMap.prod
    ((InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ (E n) (P n) ℝ).flip (ContinuousLinearMap.inr ℝ (E n) (E n))))
    (-((InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ (E n) (P n) ℝ).flip (ContinuousLinearMap.inl ℝ (E n) (E n)))))

theorem gradP_gradX_eq (H : P n → ℝ) (z : P n) (hH : DifferentiableAt ℝ H z) :
    (gradP H z, -gradX H z) = symGradL (fderiv ℝ H z) := by
  have hp : fderiv ℝ (fun p => H (z.1, p)) z.2 =
      (fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ (E n) (E n)) := by
    have h1 : HasFDerivAt (fun p => H (z.1, p))
        ((fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ (E n) (E n))) z.2 := by
      have := hH.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
      simpa only [Function.comp_def] using this
    exact h1.fderiv
  have hx : fderiv ℝ (fun x => H (x, z.2)) z.1 =
      (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ (E n) (E n)) := by
    have h1 : HasFDerivAt (fun x => H (x, z.2))
        ((fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ (E n) (E n))) z.1 := by
      have := hH.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
      simpa only [Function.comp_def] using this
    exact h1.fderiv
  simp only [gradP, gradX, gradient, hp, hx, symGradL]
  rfl

theorem fderiv_slice_eq (F : ℝ → P n → ℝ) (hF : Differentiable ℝ (Function.uncurry F))
    (t : ℝ) (z : P n) :
    fderiv ℝ (F t) z = (fderiv ℝ (Function.uncurry F) (t, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ (P n)) := by
  have h1 := (hF (t, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) t z)
  exact h1.fderiv

theorem hamVF_eq (F : ℝ → P n → ℝ) (hF : Differentiable ℝ (Function.uncurry F))
    (t : ℝ) (z : P n) :
    hamVF F t z = symGradL ((fderiv ℝ (Function.uncurry F) (t, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ (P n))) := by
  have hd : DifferentiableAt ℝ (F t) z := by
    have := (hF (t, z)).comp z (differentiableAt_const t |>.prodMk differentiableAt_id)
    exact this
  rw [← fderiv_slice_eq F hF, ← gradP_gradX_eq _ _ hd]
  rfl

theorem contDiff_hamVF (F : ℝ → P n → ℝ) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun q : ℝ × P n => hamVF F q.1 q.2) := by
  have hd : Differentiable ℝ (Function.uncurry F) := hF.differentiable (by simp)
  have : (fun q : ℝ × P n => hamVF F q.1 q.2) = fun q => symGradL
      ((fderiv ℝ (Function.uncurry F) q).comp (ContinuousLinearMap.inr ℝ ℝ (P n))) := by
    funext q
    exact hamVF_eq F hd q.1 q.2
  rw [this]
  have h2 : ContDiff ℝ ∞ (fun q => (fderiv ℝ (Function.uncurry F) q).comp
      (ContinuousLinearMap.inr ℝ ℝ (P n))) :=
    (hF.fderiv_right (by simp)).clm_comp contDiff_const
  exact symGradL.contDiff.comp h2

/-- If `F t` vanishes on an open set, so does the Hamiltonian vector field. -/
theorem hamVF_eq_zero_of_eventually (F : ℝ → P n → ℝ) (t : ℝ) (z : P n)
    (h : F t =ᶠ[𝓝 z] 0) : hamVF F t z = 0 := by
  have h1 : fderiv ℝ (F t) z = 0 := by
    rw [h.fderiv_eq]; simp
  have hd : DifferentiableAt ℝ (F t) z :=
    (differentiableAt_const (c := (0:ℝ))).congr_of_eventuallyEq h
  rw [hamVF, gradP_gradX_eq _ _ hd, h1, map_zero]

/-- If `F t` is invariant under a translation, so is the Hamiltonian vector field. -/
theorem hamVF_add (F : ℝ → P n → ℝ) (t : ℝ) (τ : P n) (h : ∀ z, F t (z + τ) = F t z)
    (hF : Differentiable ℝ (F t)) (z : P n) : hamVF F t (z + τ) = hamVF F t z := by
  have h1 : fderiv ℝ (F t) (z + τ) = fderiv ℝ (F t) z := by
    rw [← fderiv_comp_add_right]
    congr 1
    funext x; exact h x
  rw [hamVF, gradP_gradX_eq _ _ (hF _), h1, ← gradP_gradX_eq _ _ (hF _)]
  rfl

/-- Bounds and Lipschitz constants for a Hamiltonian vector field, given a compact set
to which all values reduce. -/
theorem hamVF_bounds (F : ℝ → P n → ℝ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (S : Set (P n)) (hS : IsCompact S)
    (hred : ∀ t ∈ Icc (0:ℝ) 1, ∀ z, (F t =ᶠ[𝓝 z] 0) ∨
      ∃ z' ∈ S, ∃ τ : P n, z = z' + τ ∧ ∀ w, F t (w + τ) = F t w) :
    ∃ K C : ℝ≥0, (∀ t ∈ Icc (0:ℝ) 1, LipschitzWith K (hamVF F t)) ∧
      (∀ x, ContinuousOn (fun t => hamVF F t x) (Icc 0 1)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖hamVF F t x‖ ≤ C) := by
  set W : ℝ × P n → P n := fun q => hamVF F q.1 q.2 with hW
  have hWs : ContDiff ℝ ∞ W := contDiff_hamVF F hF
  have hFt : ∀ t, Differentiable ℝ (F t) := by
    intro t
    have hd : Differentiable ℝ (Function.uncurry F) := hF.differentiable (by simp)
    intro z
    exact (hd (t, z)).comp z (differentiableAt_const t |>.prodMk differentiableAt_id)
  have hWt : ∀ t, ContDiff ℝ ∞ (hamVF F t) := by
    intro t
    have : hamVF F t = fun z => W (t, z) := rfl
    rw [this]
    exact hWs.comp (contDiff_const.prodMk contDiff_id)
  -- the spatial derivative
  set D : ℝ × P n → (P n →L[ℝ] P n) := fun q => fderiv ℝ (hamVF F q.1) q.2 with hD
  have hDeq : D = fun q => (fderiv ℝ W q).comp (ContinuousLinearMap.inr ℝ ℝ (P n)) := by
    funext q
    have h1 := ((hWs.differentiable (by simp)) q).hasFDerivAt.comp q.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
    exact h1.fderiv
  have hDc : Continuous D := by
    rw [hDeq]
    exact ((hWs.continuous_fderiv (by simp))).clm_comp continuous_const
  obtain ⟨C, hC⟩ := exists_bound_of_reduce W hWs.continuous S hS (by
    intro t ht z
    rcases hred t ht z with h | ⟨z', hz', τ, rfl, hτ⟩
    · exact Or.inl (hamVF_eq_zero_of_eventually F t z h)
    · exact Or.inr ⟨z', hz', hamVF_add F t τ hτ (hFt t) z'⟩)
  obtain ⟨K, hK⟩ := exists_bound_of_reduce D hDc S hS (by
    intro t ht z
    rcases hred t ht z with h | ⟨z', hz', τ, rfl, hτ⟩
    · left
      simp only [hD]
      have : hamVF F t =ᶠ[𝓝 z] 0 := by
        filter_upwards [h.eventually_nhds] with w hw
        exact hamVF_eq_zero_of_eventually F t w hw
      rw [this.fderiv_eq]; simp
    · right
      refine ⟨z', hz', ?_⟩
      simp only [hD]
      rw [← fderiv_comp_add_right]
      congr 1
      funext w
      exact hamVF_add F t τ hτ (hFt t) w)
  refine ⟨K, C, fun t ht => ?_, fun x => ?_, hC⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le ((hWt t).differentiable (by simp))
    intro x
    have := hK t ht x
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact this
  · have : Continuous (fun t => hamVF F t x) :=
      hWs.continuous.comp (continuous_id.prodMk continuous_const)
    exact this.continuousOn

/-! ## Flows on `ℝ²ⁿ` -/

theorem hamiltonian_reduce (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) :
    ∃ S : Set (P n), IsCompact S ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ z, (F t =ᶠ[𝓝 z] 0) ∨
      ∃ z' ∈ S, ∃ τ : P n, z = z' + τ ∧ ∀ w, F t (w + τ) = F t w := by
  obtain ⟨-, K, hK, hKz⟩ := hF
  refine ⟨K, hK, fun t ht z => ?_⟩
  by_cases hz : z ∈ K
  · exact Or.inr ⟨z, hz, 0, by simp, fun w => by simp⟩
  · left
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with w hw
    exact hKz t ht w hw

/-- Existence of the flow of a compactly supported Hamiltonian on `ℝ²ⁿ`. -/
theorem exists_hamFlow (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) :
    ∃ φ, IsHamFlow F φ := by
  obtain ⟨S, hS, hred⟩ := hamiltonian_reduce F hF
  obtain ⟨K, C, hlip, hcont, hbd⟩ := hamVF_bounds F hF.1 S hS hred
  exact exists_flow_of_bounded_lipschitz (hamVF F) K C hlip hcont hbd

/-- Uniqueness of solutions of Hamilton's equations on `[0,1]`. -/
theorem hamFlow_unique (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (φ : ℝ → P n → P n)
    (hφ : IsHamFlow F φ) (γ : ℝ → P n)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (hamVF F t (γ t)) (Icc 0 1) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t = φ t (γ 0) := by
  obtain ⟨S, hS, hred⟩ := hamiltonian_reduce F hF
  obtain ⟨K, C, hlip, hcont, hbd⟩ := hamVF_bounds F hF.1 S hS hred
  intro t ht
  exact flow_unique_of_lipschitz (hamVF F) K hlip γ (fun s => φ s (γ 0)) hγ
    (hφ (γ 0)).2 (hφ (γ 0)).1.symm ht

/-! ## Flows on `Tⁿ × ℝⁿ` (lifted) -/

theorem torusHamiltonian_reduce (F : ℝ → P n → ℝ) (hF : IsTorusHamiltonian F) :
    ∃ S : Set (P n), IsCompact S ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ z, (F t =ᶠ[𝓝 z] 0) ∨
      ∃ z' ∈ S, ∃ τ : P n, z = z' + τ ∧ ∀ w, F t (w + τ) = F t w := by
  obtain ⟨-, hper, C, hC⟩ := hF
  refine ⟨{z : P n | (∀ j, z.1 j ∈ Icc (0:ℝ) 1) ∧ ‖z.2‖ ≤ C}, ?_, fun t ht z => ?_⟩
  · apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed {z : P n | ∀ j, z.1 j ∈ Icc (0:ℝ) 1} := by
        rw [setOf_forall]
        exact isClosed_iInter fun j => isClosed_Icc.preimage
          (by fun_prop : Continuous fun z : P n => z.1 j)
      have h2 : IsClosed {z : P n | ‖z.2‖ ≤ C} := isClosed_le (by fun_prop) continuous_const
      exact h1.inter h2
    · rw [Metric.isBounded_iff_subset_closedBall (0 : P n)]
      refine ⟨max (Real.sqrt n) C, fun z hz => ?_⟩
      rw [mem_closedBall, dist_zero_right, Prod.norm_def]
      refine max_le (le_trans ?_ (le_max_left _ _)) (le_trans hz.2 (le_max_right _ _))
      rw [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ j, ‖z.1 j‖ ^ 2 ≤ ∑ _j : Fin n, (1:ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            have := hz.1 j
            rw [Real.norm_eq_abs, sq_abs]
            nlinarith [this.1, this.2]
        _ = n := by simp
  · by_cases hz : ‖z.2‖ ≤ C
    · right
      set m : Fin n → ℤ := fun j => ⌊z.1 j⌋
      refine ⟨(z.1 - intVec m, z.2), ⟨fun j => ?_, hz⟩, (intVec m, 0), ?_, fun w => ?_⟩
      · simp only [intVec, PiLp.sub_apply, m]
        constructor
        · have := Int.floor_le (z.1 j)
          linarith
        · have := Int.lt_floor_add_one (z.1 j)
          linarith
      · ext <;> simp
      · rw [show w + (intVec m, 0) = (w.1 + intVec m, w.2) by ext <;> simp]
        exact hper t w m
    · left
      push_neg at hz
      have : IsOpen {w : P n | C < ‖w.2‖} := isOpen_lt continuous_const
        (continuous_norm.comp continuous_snd)
      filter_upwards [this.mem_nhds hz] with w hw
      exact hC t ht w hw

/-- Existence of the flow of a compactly supported Hamiltonian on `Tⁿ × ℝⁿ` (lifted). -/
theorem exists_torusHamFlow (F : ℝ → P n → ℝ) (hF : IsTorusHamiltonian F) :
    ∃ φ, IsHamFlow F φ := by
  obtain ⟨S, hS, hred⟩ := torusHamiltonian_reduce F hF
  obtain ⟨K, C, hlip, hcont, hbd⟩ := hamVF_bounds F hF.1 S hS hred
  exact exists_flow_of_bounded_lipschitz (hamVF F) K C hlip hcont hbd

/-- Uniqueness for Hamiltonians on `Tⁿ × ℝⁿ` (lifted). -/
theorem torusHamFlow_unique (F : ℝ → P n → ℝ) (hF : IsTorusHamiltonian F)
    (φ : ℝ → P n → P n) (hφ : IsHamFlow F φ) (γ : ℝ → P n)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (hamVF F t (γ t)) (Icc 0 1) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t = φ t (γ 0) := by
  obtain ⟨S, hS, hred⟩ := torusHamiltonian_reduce F hF
  obtain ⟨K, C, hlip, hcont, hbd⟩ := hamVF_bounds F hF.1 S hS hred
  intro t ht
  exact flow_unique_of_lipschitz (hamVF F) K hlip γ (fun s => φ s (γ 0)) hγ
    (hφ (γ 0)).2 (hφ (γ 0)).1.symm ht

end GradRange
