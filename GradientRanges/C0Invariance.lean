module
import all Mathlib.Basic.Real.Basic

public import GradientRanges.Flow

@[expose] public section

/-!
# `C⁰`-invariance of displacement rigidity (Usher 2022, Proposition 1.4, case `W = M = ℝ²ⁿ`)

The proof follows Usher's argument:

* **Conjugation.** If `g` is a smooth symplectic diffeomorphism with smooth inverse `h` and
  `φ` is a Hamiltonian flow of `F`, then `t ↦ h ∘ φ t ∘ g` is a Hamiltonian flow of
  `K(t,x) = F(t, g x)` (`isHamFlow_conj`), `K` is again a compactly supported Hamiltonian
  (`isHamiltonian_conj`) and has the same Hofer length (`hoferLength_conj`).
* **Inverse convergence.** If homeomorphisms `G k` of a proper real normed space converge
  locally uniformly to a homeomorphism `ψ`, then `(G k)⁻¹ (y k) → ψ⁻¹ y` whenever `y k → y`
  (`tendsto_symm_of_tendstoLocallyUniformly`). This is the part of Arens' theorem used by
  Usher; it is proved here by a connectedness argument.
* **Reduction to bounded sets.** Displacement energy is monotone in `U`, so it suffices to
  treat bounded open `V`; then `ψ⁻¹(closure V)` is compact and compactness arguments apply.
-/

open Set Metric Filter Topology
open scoped ContDiff ENNReal

namespace GradRange

/-! ## Inverse convergence (the part of Arens' theorem that is needed) -/

/-- If homeomorphisms `G k` converge locally uniformly to the homeomorphism `ψ` and
`y k → y`, then `(G k)⁻¹ (y k) → ψ⁻¹ y`. -/
theorem tendsto_symm_of_tendstoLocallyUniformly {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [ProperSpace X]
    (G : ℕ → X ≃ₜ X) (ψ : X ≃ₜ X) (hG : TendstoLocallyUniformly (fun k => ⇑(G k)) ψ atTop)
    (y : ℕ → X) (y₀ : X) (hy : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun k => (G k).symm (y k)) atTop (𝓝 (ψ.symm y₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set w := ψ.symm y₀ with hw
  have hψw : ψ w = y₀ := by simp [hw]
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  -- a ball around `y₀` avoiding `ψ (sphere w r)`
  have hcl : IsClosed (ψ '' sphere w r) := ((isCompact_sphere w r).image ψ.continuous).isClosed
  have hy₀ : y₀ ∉ ψ '' sphere w r := by
    rintro ⟨x, hx, hxy⟩
    have : x = w := by rw [hw, ← hxy]; simp
    rw [this, mem_sphere, dist_self] at hx
    exact hr0.ne hx
  obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl y₀ hy₀
  set δ := ε' / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  -- uniform convergence on the compact sphere
  have hunif := (Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG) _ (isCompact_sphere w r))) δ hδ0
  have hGw : Tendsto (fun k => G k w) atTop (𝓝 y₀) := by
    have := hG.tendsto_comp (x := w) ψ.continuous.continuousAt tendsto_const_nhds
    rwa [hψw] at this
  filter_upwards [hunif, Metric.tendsto_nhds.1 hGw δ hδ0, Metric.tendsto_nhds.1 hy δ hδ0]
    with k hk1 hk2 hk3
  -- the connected ball `ball y₀ δ` misses the frontier of `G k (closedBall w r)`,
  -- and meets its interior, hence lies inside it
  set A := G k '' closedBall w r
  have hsub : ball y₀ δ ⊆ interior A := by
    apply (convex_ball y₀ δ).isPreconnected.subset_left_of_subset_union isOpen_interior
      isClosed_closure.isOpen_compl
    · exact disjoint_compl_right.mono_left interior_subset_closure
    · intro z hz
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      have hzf : z ∈ frontier A := ⟨hcon.2, hcon.1⟩
      rw [← Homeomorph.image_frontier] at hzf
      obtain ⟨x, hx, rfl⟩ := hzf
      have hx' := frontier_closedBall_subset_sphere hx
      have h1 := hk1 x hx'
      apply hball (show ψ x ∈ ball y₀ ε' from ?_) ⟨x, hx', rfl⟩
      rw [mem_ball] at hz ⊢
      calc dist (ψ x) y₀ ≤ dist (ψ x) (G k x) + dist (G k x) y₀ := dist_triangle _ _ _
        _ < δ + δ := add_lt_add h1 hz
        _ = ε' := by rw [hδ]; ring
    · refine ⟨G k w, mem_ball.2 hk2, ?_⟩
      have hop : IsOpen (G k '' ball w r) := (G k).isOpenMap _ isOpen_ball
      exact interior_maximal (image_mono ball_subset_closedBall) hop ⟨w, mem_ball_self hr0, rfl⟩
  obtain ⟨x, hx, hxy⟩ := interior_subset (hsub (mem_ball.2 hk3))
  rw [← hxy, Homeomorph.symm_apply_apply]
  rw [mem_closedBall] at hx
  linarith

/-! ## Symplectic linear algebra of Hamiltonian vector fields -/

variable {n : ℕ}

theorem omega0_hamVF (H : ℝ → P n → ℝ) (t : ℝ) (z : P n)
    (hH : DifferentiableAt ℝ (H t) z) (v : P n) :
    omega0 (hamVF H t z) v = fderiv ℝ (H t) z v := by
  have hp : HasFDerivAt (fun p => H t (z.1, p))
      ((fderiv ℝ (H t) z).comp (ContinuousLinearMap.inr ℝ (E n) (E n))) z.2 := by
    have := hH.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
    simpa only [Function.comp_def] using this
  have hx : HasFDerivAt (fun x => H t (x, z.2))
      ((fderiv ℝ (H t) z).comp (ContinuousLinearMap.inl ℝ (E n) (E n))) z.1 := by
    have := hH.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
    simpa only [Function.comp_def] using this
  have e1 : inner ℝ (gradP (H t) z) v.2 = fderiv ℝ (H t) z (0, v.2) := by
    rw [gradP, gradient, hp.fderiv, InnerProductSpace.toDual_symm_apply]; simp
  have e2 : inner ℝ v.1 (gradX (H t) z) = fderiv ℝ (H t) z (v.1, 0) := by
    rw [real_inner_comm, gradX, gradient, hx.fderiv, InnerProductSpace.toDual_symm_apply]; simp
  have : v = (v.1, 0) + (0, v.2) := by ext <;> simp
  simp only [omega0, hamVF, inner_neg_right, sub_neg_eq_add]
  rw [e1, e2, add_comm, ← map_add, ← this]

theorem omega0_nondeg (a b : P n) (h : ∀ v, omega0 a v = omega0 b v) : a = b := by
  have h1 : a.1 - b.1 = 0 := by
    have := h (0, a.1 - b.1)
    simp only [omega0, inner_zero_left, sub_zero] at this
    rw [← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, this, sub_self]
  have h2 : a.2 - b.2 = 0 := by
    have := h (a.2 - b.2, 0)
    simp only [omega0, inner_zero_right, zero_sub, neg_inj] at this
    rw [← inner_self_eq_zero (𝕜 := ℝ), inner_sub_right, this, sub_self]
  ext1
  · exact sub_eq_zero.1 h1
  · exact sub_eq_zero.1 h2

/-- Conjugating by a symplectic diffeomorphism transports Hamiltonian vector fields. -/
theorem hamVF_conj (g h : P n → P n) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgh : Function.LeftInverse h g) (hhg : Function.RightInverse h g)
    (hω : ∀ z v w, omega0 (fderiv ℝ g z v) (fderiv ℝ g z w) = omega0 v w)
    (F : ℝ → P n → ℝ) (t : ℝ) (hF : Differentiable ℝ (F t)) (w : P n) :
    hamVF (fun s x => F s (g x)) t (h w) = fderiv ℝ h w (hamVF F t w) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hhd : Differentiable ℝ h := hh.differentiable (by simp)
  set y := h w with hy
  have hgy : g y = w := hhg w
  have hD1 : ∀ u, fderiv ℝ h w (fderiv ℝ g y u) = u := by
    intro u
    have : HasFDerivAt (h ∘ g) ((fderiv ℝ h w).comp (fderiv ℝ g y)) y := by
      have := (hhd (g y)).hasFDerivAt.comp y (hgd y).hasFDerivAt
      rwa [hgy] at this
    have hid : h ∘ g = id := funext hgh
    rw [hid] at this
    have := congrArg (fun L => L u) ((hasFDerivAt_id y).unique this)
    simpa using this.symm
  have hD2 : ∀ u, fderiv ℝ g y (fderiv ℝ h w u) = u := by
    intro u
    have : HasFDerivAt (g ∘ h) ((fderiv ℝ g y).comp (fderiv ℝ h w)) w :=
      (hgd y).hasFDerivAt.comp w (hhd w).hasFDerivAt
    have hid : g ∘ h = id := funext hhg
    rw [hid] at this
    have := congrArg (fun L => L u) ((hasFDerivAt_id w).unique this)
    simpa using this.symm
  have hK : HasFDerivAt (fun x => F t (g x)) ((fderiv ℝ (F t) w).comp (fderiv ℝ g y)) y := by
    have := (hF (g y)).hasFDerivAt.comp y (hgd y).hasFDerivAt
    rwa [hgy] at this
  apply omega0_nondeg
  intro u
  rw [omega0_hamVF (fun s x => F s (g x)) t y hK.differentiableAt, hK.fderiv]
  conv_rhs => rw [← hD1 u, ← hω y, hD2, hD2]
  rw [omega0_hamVF F t w (hF w)]
  rfl

/-! ## Conjugated Hamiltonians -/

theorem isHamiltonian_conj (g h : P n → P n) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgh : Function.LeftInverse h g) (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) :
    IsHamiltonian (fun s x => F s (g x)) := by
  obtain ⟨hs, K, hK, hKz⟩ := hF
  refine ⟨?_, h '' K, hK.image hh.continuous, fun t ht z hz => hKz t ht (g z) ?_⟩
  · have : Function.uncurry (fun s x => F s (g x)) =
        Function.uncurry F ∘ (fun q : ℝ × P n => (q.1, g q.2)) := rfl
    rw [this]
    exact hs.comp (contDiff_fst.prodMk (hg.comp contDiff_snd))
  · intro hgz
    exact hz ⟨g z, hgz, hgh z⟩

theorem isHamFlow_conj (g h : P n → P n) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgh : Function.LeftInverse h g) (hhg : Function.RightInverse h g)
    (hω : ∀ z v w, omega0 (fderiv ℝ g z v) (fderiv ℝ g z w) = omega0 v w)
    (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (φ : ℝ → P n → P n) (hφ : IsHamFlow F φ) :
    IsHamFlow (fun s x => F s (g x)) (fun s x => h (φ s (g x))) := by
  have hFt : ∀ t, Differentiable ℝ (F t) := by
    intro t
    have hd : Differentiable ℝ (Function.uncurry F) := hF.1.differentiable (by simp)
    intro z
    exact (hd (t, z)).comp z (differentiableAt_const t |>.prodMk differentiableAt_id)
  have hhd : Differentiable ℝ h := hh.differentiable (by simp)
  intro z
  refine ⟨by simp only; rw [(hφ (g z)).1, hgh z], fun t ht => ?_⟩
  have := (hhd (φ t (g z))).hasFDerivAt.comp_hasDerivWithinAt t ((hφ (g z)).2 t ht)
  simp only
  rw [hamVF_conj g h hg hh hgh hhg hω F t (hFt t)]
  exact this

theorem hoferLength_conj (g : P n → P n) (hg : Function.Surjective g) (F : ℝ → P n → ℝ) :
    hoferLength (fun s x => F s (g x)) = hoferLength F := by
  unfold hoferLength
  congr 1
  funext t
  rw [hg.iSup_comp (F t), hg.iInf_comp (F t)]

/-! ## Continuity of the time-one map -/

theorem continuous_hamFlow_one (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (φ : ℝ → P n → P n)
    (hφ : IsHamFlow F φ) : Continuous (φ 1) := by
  obtain ⟨S, hS, hred⟩ := hamiltonian_reduce F hF
  obtain ⟨K, C, hlip, -, -⟩ := hamVF_bounds F hF.1 S hS hred
  have key : ∀ u : ℝ → P n,
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (hamVF F t (u t)) (Icc 0 1) t) →
      ∀ t ∈ Ico (0:ℝ) 1, HasDerivWithinAt u (hamVF F t (u t)) (Ici t) t := by
    intro u hu t ht
    have h1 := hu t (Ico_subset_Icc_self ht)
    apply h1.mono_of_mem_nhdsWithin
    have : Icc t 1 ∈ nhdsWithin t (Ici t) := Icc_mem_nhdsGE ht.2
    exact Filter.mem_of_superset this (Icc_subset_Icc ht.1 le_rfl)
  have hc : ∀ x, ContinuousOn (fun s => φ s x) (Icc 0 1) := fun x t ht =>
    ((hφ x).2 t ht).continuousWithinAt
  apply LipschitzWith.continuous (K := Real.toNNReal (Real.exp K))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have := dist_le_of_trajectories_ODE_of_mem (v := hamVF F) (s := fun _ => univ) (K := K)
    (fun t ht => (hlip t (Ico_subset_Icc_self ht)).lipschitzOnWith) (hc x)
    (key _ (hφ x).2) (fun _ _ => trivial) (hc y) (key _ (hφ y).2) (fun _ _ => trivial)
    (δ := dist x y) (by rw [(hφ x).1, (hφ y).1]) 1 (by simp)
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  simpa [mul_comm] using this

/-! ## Monotonicity of displacement energy -/

theorem displacementEnergy_mono {U W N : Set (P n)} (h : U ⊆ W) :
    displacementEnergy U N ≤ displacementEnergy W N := by
  apply sInf_le_sInf
  rintro e ⟨F, φ, hF, hφ, hd, rfl⟩
  exact ⟨F, φ, hF, hφ, hd.mono_left (image_mono (closure_mono h)), rfl⟩

/-! ## The main inequality -/

/-- Usher's inequality `(1.1)` with `W = M`, for bounded open `V`:
`e(V, ψ N) ≥ e(ψ⁻¹ V, N)`. -/
theorem displacementEnergy_symplecticHomeomorph_le (N : Set (P n)) (hN : IsClosed N)
    (ψ : P n ≃ₜ P n) (hψ : IsSymplecticHomeomorph ψ) (V : Set (P n))
    (hVb : Bornology.IsBounded V) :
    displacementEnergy (ψ ⁻¹' V) N ≤ displacementEnergy V (ψ '' N) := by
  obtain ⟨g, hg, hconv⟩ := hψ
  choose h hh hgh hhg using fun k => (hg k).2.1
  have hgs : ∀ k, ContDiff ℝ ∞ (g k) := fun k => (hg k).1
  let G : ℕ → P n ≃ₜ P n := fun k =>
    { toFun := g k, invFun := h k, left_inv := hgh k, right_inv := hhg k
      continuous_toFun := (hgs k).continuous, continuous_invFun := (hh k).continuous }
  apply le_sInf
  rintro e ⟨F, φ, hF, hφ, hd, rfl⟩
  have hC : IsCompact (closure (ψ ⁻¹' V)) := by
    rw [← ψ.preimage_closure]
    exact ψ.isCompact_preimage.2 hVb.isCompact_closure
  -- for some `k`, the conjugated flow displaces `closure (ψ⁻¹ V)` from `N`
  have hex : ∃ k, Disjoint ((fun x => h k (φ 1 (g k x))) '' closure (ψ ⁻¹' V)) N := by
    by_contra hcon
    push_neg at hcon
    have : ∀ k, ∃ x ∈ closure (ψ ⁻¹' V), h k (φ 1 (g k x)) ∈ N := by
      intro k
      obtain ⟨_, ⟨x, hx, rfl⟩, hxN⟩ := not_disjoint_iff.1 (hcon k)
      exact ⟨x, hx, hxN⟩
    choose x hxC hxN using this
    obtain ⟨x₀, hx₀, σ, hσ, hxσ⟩ := hC.tendsto_subseq hxC
    have hconvσ : TendstoLocallyUniformly (fun k => ⇑(G (σ k))) ψ atTop := by
      intro u hu z
      obtain ⟨t, ht, hev⟩ := hconv u hu z
      exact ⟨t, ht, hσ.tendsto_atTop.eventually hev⟩
    have hy : Tendsto (fun k => φ 1 (g (σ k) (x (σ k)))) atTop (𝓝 (φ 1 (ψ x₀))) :=
      ((continuous_hamFlow_one F hF φ hφ).tendsto _).comp
        (hconvσ.tendsto_comp ψ.continuous.continuousAt hxσ)
    have hlim := tendsto_symm_of_tendstoLocallyUniformly (fun k => G (σ k)) ψ hconvσ _ _ hy
    have hmem : ψ.symm (φ 1 (ψ x₀)) ∈ N :=
      hN.mem_of_tendsto hlim (Eventually.of_forall fun k => hxN (σ k))
    have hx₀' : ψ x₀ ∈ closure V := by
      rw [← ψ.preimage_closure] at hx₀
      exact hx₀
    apply Set.disjoint_left.1 hd ⟨ψ x₀, hx₀', rfl⟩
    exact ⟨_, hmem, by simp⟩
  obtain ⟨k, hk⟩ := hex
  apply sInf_le
  refine ⟨fun s x => F s (g k x), fun s x => h k (φ s (g k x)),
    isHamiltonian_conj (g k) (h k) (hgs k) (hh k) (hgh k) F hF,
    isHamFlow_conj (g k) (h k) (hgs k) (hh k) (hgh k) (hhg k) (hg k).2.2 F hF φ hφ, hk, ?_⟩
  rw [hoferLength_conj (g k) (hhg k).surjective F]

/-- **Usher 2022, Proposition 1.4** (closed case, `M = ℝ²ⁿ`). -/
theorem isDisplacementRigid_image (N : Set (P n)) (hN : IsClosed N)
    (hrig : IsDisplacementRigid N) (ψ : P n ≃ₜ P n) (hψ : IsSymplecticHomeomorph ψ) :
    IsDisplacementRigid (ψ '' N) := by
  intro V hV hVN
  obtain ⟨y, hyV, hyN⟩ := hVN
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV y hyV
  set V' := ball y r
  have h1 : displacementEnergy V' (ψ '' N) ≤ displacementEnergy V (ψ '' N) :=
    displacementEnergy_mono hrV
  have h2 := displacementEnergy_symplecticHomeomorph_le N hN ψ hψ V' isBounded_ball
  have h3 : displacementEnergy (ψ ⁻¹' V') N ≠ 0 := by
    apply hrig _ (isOpen_ball.preimage ψ.continuous)
    obtain ⟨x, hxN, rfl⟩ := hyN
    exact ⟨x, by simp [hr], hxN⟩
  intro h0
  apply h3
  exact le_antisymm (le_trans h2 (le_trans h1 h0.le)) zero_le

end GradRange
