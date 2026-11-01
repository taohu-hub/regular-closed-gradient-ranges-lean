module

public import GradientRanges.Oscillation
public import GradientRanges.Flow

@[expose] public section

/-!
# Lemma 2.2: the projection lemma
-/

open Set Metric Filter Topology
open scoped ContDiff

namespace GradRange

variable {n : ℕ}

/-- The cut-off autonomous Hamiltonian `F(x,p) = α(x) β(p) H(p)` of the paper: it has Hofer
length at most `2c` when `|H| ≤ c`, and its time-one map is the shear
`(x,p) ↦ (x + ∇H(p), p)` on `B_R × B(p₀,r)`. -/
theorem exists_shear_hamiltonian (H : E n → ℝ) (hH : ContDiff ℝ ∞ H) (c : ℝ)
    (hc : ∀ p, |H p| ≤ c) (p₀ : E n) (r R A : ℝ) (hr : 0 < r) (hR : 0 < R) (hA0 : 0 ≤ A)
    (hA : ∀ p ∈ closedBall p₀ r, ‖gradient H p‖ ≤ A) :
    ∃ F : ℝ → P n → ℝ, IsHamiltonian F ∧ hoferLength F ≤ 2 * c ∧
      ∀ φ, IsHamFlow F φ → ∀ x p, ‖x‖ < R → p ∈ ball p₀ r →
        φ 1 (x, p) = (x + gradient H p, p) := by
  let α : ContDiffBump (0 : E n) := ⟨R + A + 1, R + A + 2, by positivity, by linarith⟩
  let β : ContDiffBump p₀ := ⟨r, r + 1, hr, by linarith⟩
  set F : ℝ → P n → ℝ := fun _ z => α z.1 * β z.2 * H z.2 with hF
  have hαs : ContDiff ℝ ∞ α := α.contDiff
  have hβs : ContDiff ℝ ∞ β := β.contDiff
  have hFs : ContDiff ℝ ∞ (Function.uncurry F) := by
    have : Function.uncurry F = fun q : ℝ × P n => α q.2.1 * β q.2.2 * H q.2.2 := rfl
    rw [this]
    exact ((hαs.comp (contDiff_fst.comp contDiff_snd)).mul
      (hβs.comp (contDiff_snd.comp contDiff_snd))).mul (hH.comp (contDiff_snd.comp contDiff_snd))
  have hFc : ∀ t z, |F t z| ≤ c := by
    intro t z
    simp only [hF, abs_mul]
    have h1 : |α z.1| ≤ 1 := by rw [abs_of_nonneg α.nonneg]; exact α.le_one
    have h2 : |β z.2| ≤ 1 := by rw [abs_of_nonneg β.nonneg]; exact β.le_one
    calc |α z.1| * |β z.2| * |H z.2| ≤ 1 * 1 * c := by
          gcongr
          · exact hc _
      _ = c := by ring
  refine ⟨F, ⟨hFs, closedBall 0 (R + A + 2) ×ˢ closedBall p₀ (r + 1),
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _), ?_⟩, ?_, ?_⟩
  · intro t _ z hz
    simp only [mem_prod, not_and_or, mem_closedBall, not_le] at hz
    simp only [hF]
    rcases hz with h | h
    · rw [α.zero_of_le_dist h.le]; ring
    · rw [β.zero_of_le_dist h.le]; ring
  · have hint : ∀ t, (⨆ z, F t z) - (⨅ z, F t z) ≤ 2 * c := by
      intro t
      have h1 : (⨆ z, F t z) ≤ c := ciSup_le fun z => (abs_le.mp (hFc t z)).2
      have h2 : -c ≤ (⨅ z, F t z) := le_ciInf fun z => (abs_le.mp (hFc t z)).1
      linarith
    have hconst : (fun t => (⨆ z, F t z) - (⨅ z, F t z)) =
        fun _ => (⨆ z, F 0 z) - (⨅ z, F 0 z) := rfl
    unfold hoferLength
    rw [hconst, intervalIntegral.integral_const]
    simpa using hint 0
  · intro φ hφ x p hx hp
    set v := gradient H p with hv
    have hvA : ‖v‖ ≤ A := hA p (ball_subset_closedBall hp)
    set γ : ℝ → P n := fun t => (x + t • v, p) with hγ
    have hγ' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt γ (hamVF F t (γ t)) (Icc 0 1) t := by
      intro t ht
      have hpath : HasDerivAt γ (v, 0) t := by
        have := (((hasDerivAt_id t).smul_const v).const_add x).prodMk (hasDerivAt_const t p)
        simpa using this
      convert hpath.hasDerivWithinAt using 1
      -- the vector field along the path
      have hy : x + t • v ∈ ball (0 : E n) (R + A + 1) := by
        rw [mem_ball, dist_zero_right]
        calc ‖x + t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_add_le _ _
          _ = ‖x‖ + |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖x‖ + 1 * A := by
              gcongr
              rw [abs_of_nonneg ht.1]; exact ht.2
          _ < R + A + 1 := by linarith
      have hαe : (α : E n → ℝ) =ᶠ[𝓝 (x + t • v)] 1 := α.eventuallyEq_one_of_mem_ball hy
      have hβe : (β : E n → ℝ) =ᶠ[𝓝 p] 1 := β.eventuallyEq_one_of_mem_ball hp
      have hP : gradP (F t) (γ t) = v := by
        simp only [gradP, hγ, hF, gradient]
        have : (fun p' => α (x + t • v) * β p' * H p') =ᶠ[𝓝 p] H := by
          filter_upwards [hβe] with p' hp'
          rw [α.one_of_mem_closedBall (ball_subset_closedBall hy), hp']
          simp
        rw [this.fderiv_eq]
        rfl
      have hX : gradX (F t) (γ t) = 0 := by
        simp only [gradX, hγ, hF, gradient]
        have : (fun x' => α x' * β p * H p) =ᶠ[𝓝 (x + t • v)] fun _ => β p * H p := by
          filter_upwards [hαe] with x' hx'
          rw [hx']
          simp
        rw [this.fderiv_eq]
        simp
      simp only [hamVF, hP, hX, neg_zero]
    have := hamFlow_unique F ⟨hFs, closedBall 0 (R + A + 2) ×ˢ closedBall p₀ (r + 1),
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _), by
        intro t _ z hz
        simp only [mem_prod, not_and_or, mem_closedBall, not_le] at hz
        simp only [hF]
        rcases hz with h | h
        · rw [α.zero_of_le_dist h.le]; ring
        · rw [β.zero_of_le_dist h.le]; ring⟩ φ hφ γ hγ' 1 ⟨zero_le_one, le_rfl⟩
    simp only [hγ, zero_smul, add_zero, one_smul] at this
    exact this.symm

/-- If `e ≤ 2ε` for every `ε > 0`, then `e = 0`. -/
theorem ennreal_eq_zero_of_forall_le (e : ENNReal) (h : ∀ ε : ℝ, 0 < ε → e ≤ ENNReal.ofReal (2 * ε)) :
    e = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  have := h (ε / 2) (by positivity)
  rwa [show 2 * ((ε : ℝ) / 2) = ε by ring, ENNReal.ofReal_coe_nnreal] at this

/-- **Lemma 2.2.** Let `N ⊆ ℝ²ⁿ` be closed with `e(U,N) > 0` for every bounded open `U`
meeting `N`, and let `p₀ ∈ π_p(N)`. If `N ∩ π_p⁻¹(closedBall p₀ r₀)` is compact for some
`r₀ > 0`, then `p₀ ∈ closure (int π_p(N))`. -/
theorem lemma_2_2 (N : Set (P n)) (hN : IsClosed N)
    (hrig : ∀ U : Set (P n), IsOpen U → Bornology.IsBounded U → (U ∩ N).Nonempty →
      displacementEnergy U N ≠ 0)
    (p₀ : E n) (hp₀ : p₀ ∈ Prod.snd '' N) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hcpt : IsCompact (N ∩ Prod.snd ⁻¹' closedBall p₀ r₀)) :
    p₀ ∈ closure (interior (Prod.snd '' N)) := by
  by_contra hcl
  set E' := Prod.snd '' N with hE'
  rw [Metric.mem_closure_iff] at hcl
  push_neg at hcl
  obtain ⟨ε₀, hε₀, hfar⟩ := hcl
  set r := min (ε₀ / 2) (r₀ / 2) with hr
  have hr0 : 0 < r := by positivity
  have hrr₀ : r < r₀ := by rw [hr]; linarith [min_le_right (ε₀ / 2) (r₀ / 2)]
  have hrε : r < ε₀ := by rw [hr]; linarith [min_le_left (ε₀ / 2) (r₀ / 2)]
  set Nr := N ∩ Prod.snd ⁻¹' closedBall p₀ r with hNr
  have hNrc : IsCompact Nr := hcpt.of_isClosed_subset
    (hN.inter (isClosed_closedBall.preimage continuous_snd))
    (inter_subset_inter_right _ (preimage_mono (closedBall_subset_closedBall hrr₀.le)))
  set K := Prod.snd '' Nr with hK
  have hKc : IsCompact K := hNrc.image continuous_snd
  have hKi : interior K = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro q hq
    have hqE : q ∈ interior E' := interior_mono (image_mono inter_subset_left) hq
    have hqb : q ∈ closedBall p₀ r := by
      obtain ⟨z, hz, rfl⟩ := interior_subset hq
      exact hz.2
    have := hfar q hqE
    rw [mem_closedBall] at hqb
    rw [dist_comm] at hqb
    linarith
  obtain ⟨⟨x₀, p₀'⟩, hz₀N, rfl⟩ := hp₀
  simp only at *
  -- a radius bounding the `x`-coordinates of `Nr`
  obtain ⟨R₁, hR₁⟩ := (hNrc.image continuous_fst).isBounded.subset_closedBall 0
  set R := max R₁ ‖x₀‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hNrR : ∀ z ∈ Nr, ‖z.1‖ < R := by
    intro z hz
    have := hR₁ ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R₁ ‖x₀‖]
  set ρ := min (1 / 2) (r / 2) with hρ
  have hρ0 : 0 < ρ := by positivity
  set U : Set (P n) := ball x₀ ρ ×ˢ ball p₀' ρ with hU
  have hUo : IsOpen U := isOpen_ball.prod isOpen_ball
  have hUb : Bornology.IsBounded U := isBounded_ball.prod isBounded_ball
  have hUN : (U ∩ N).Nonempty := ⟨(x₀, p₀'), ⟨mem_ball_self hρ0, mem_ball_self hρ0⟩, hz₀N⟩
  have hclU : closure U ⊆ closedBall x₀ ρ ×ˢ closedBall p₀' ρ := by
    rw [hU, closure_prod_eq]
    exact prod_mono closure_ball_subset_closedBall closure_ball_subset_closedBall
  apply hrig U hUo hUb hUN
  apply ennreal_eq_zero_of_forall_le
  intro ε hε
  obtain ⟨H, hHs, -, ⟨c, hcε, hc⟩, hgrad⟩ := lemma_2_1 K hKc hKi ε (2 * R) hε (by positivity)
  -- a bound for `∇H` on `closedBall p₀ r`
  have hgc : Continuous (gradient H) :=
    continuous_gradient_of_contDiff H (hHs.of_le (by simp))
  obtain ⟨A, hA⟩ := (isCompact_closedBall p₀' r).exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨F, hF, hFL, hFφ⟩ := exists_shear_hamiltonian H hHs c hc p₀' r R (max A 0) hr0 hR0
    (le_max_right _ _) (fun p hp => le_trans (hA p hp) (le_max_left _ _))
  obtain ⟨φ, hφ⟩ := exists_hamFlow F hF
  calc displacementEnergy U N ≤ ENNReal.ofReal (hoferLength F) := by
        apply sInf_le
        refine ⟨F, φ, hF, hφ, ?_, rfl⟩
        rw [Set.disjoint_left]
        rintro _ ⟨⟨x, p⟩, hxp, rfl⟩ hmem
        have hxp' := hclU hxp
        simp only [mem_prod, mem_closedBall] at hxp'
        have hx : ‖x‖ < R := by
          have := norm_le_norm_add_norm_sub' x x₀
          rw [← dist_eq_norm] at this
          linarith [le_max_right R₁ ‖x₀‖, min_le_left (1/2 : ℝ) (r / 2)]
        have hp : p ∈ ball p₀' r := by
          rw [mem_ball]; linarith [min_le_right (1/2 : ℝ) (r / 2)]
        rw [hFφ φ hφ x p hx hp] at hmem
        have hmemNr : (x + gradient H p, p) ∈ Nr := ⟨hmem, ball_subset_closedBall hp⟩
        have h1 := hNrR _ hmemNr
        have hpK : p ∈ K := ⟨_, hmemNr, rfl⟩
        have h2 := hgrad p hpK
        simp only at h1
        have h3 : ‖gradient H p‖ ≤ ‖x + gradient H p‖ + ‖x‖ := by
          have := norm_sub_le (x + gradient H p) x
          simpa using this
        linarith
    _ ≤ ENNReal.ofReal (2 * ε) := by
        apply ENNReal.ofReal_le_ofReal
        linarith

end GradRange
