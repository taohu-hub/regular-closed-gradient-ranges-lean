module
import all Mathlib.Basic.Real.Basic

public import GradientRanges.Flow
public meta import ProofAudit

@[expose] public section

/-!
# Discrete (symplectic Euler) orbits and Riemann sums of the oscillation

* `discrete_orbit_close`: a sequence `y₀, …, y_N` satisfying the implicit symplectic Euler
  relations `y_{k+1} = y_k + (1/N) X_F((k+1)/N, (x_k, p_{k+1}))` stays uniformly close to the
  genuine Hamiltonian orbit of `y₀` once `N` is large (discrete Grönwall inequality).
* `riemann_osc_le`: right Riemann sums of `t ↦ max F(t,·) - min F(t,·)` are at most
  `hoferLength F + ε` once `N` is large.
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace GradRange

variable {n : ℕ}

/-- A uniform modulus of continuity in time, valid for any continuous function of `(t,z)`
which vanishes outside a fixed compact set for `t ∈ [0,1]`. -/
theorem time_modulus {Y : Type*} [NormedAddCommGroup Y] (g : ℝ × P n → Y) (hg : Continuous g)
    (K : Set (P n)) (hK : IsCompact K) (hz : ∀ t ∈ Icc (0:ℝ) 1, ∀ z ∉ K, g (t, z) = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ t' ∈ Icc (0:ℝ) 1, |t - t'| ≤ δ →
      ∀ z, ‖g (t, z) - g (t', z)‖ ≤ ε := by
  intro ε hε
  have huc := ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod hK).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc ε hε
  refine ⟨δ / 2, by positivity, fun t ht t' ht' htt z => ?_⟩
  by_cases hzK : z ∈ K
  · rw [← dist_eq_norm]
    refine (h (t, z) ⟨ht, hzK⟩ (t', z) ⟨ht', hzK⟩ ?_).le
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    calc max |t - t'| 0 ≤ δ / 2 := max_le htt (by positivity)
      _ < δ := by linarith
  · rw [hz t ht z hzK, hz t' ht' z hzK, sub_zero, norm_zero]; exact hε.le

/-- The Hamiltonian vector field of a compactly supported Hamiltonian vanishes off the
support for `t ∈ [0,1]`. -/
theorem hamVF_zero_off (F : ℝ → P n → ℝ) (K : Set (P n)) (hK : IsCompact K)
    (hKz : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∉ K, F t z = 0) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ z ∉ K, hamVF F t z = 0 := by
  intro t ht z hz
  apply hamVF_eq_zero_of_eventually
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with w hw
  exact hKz t ht w hw

/-- One step of the genuine flow is close to an explicit Euler step. -/
theorem flow_step_error (F : ℝ → P n → ℝ) (φ : ℝ → P n → P n) (hφ : IsHamFlow F φ)
    (K C : ℝ) (hK : ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖hamVF F t x - hamVF F t y‖ ≤ K * ‖x - y‖)
    (hC : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖hamVF F t x‖ ≤ C) (hK0 : 0 ≤ K)
    (ε δ : ℝ) (hδ : ∀ t ∈ Icc (0:ℝ) 1, ∀ t' ∈ Icc (0:ℝ) 1, |t - t'| ≤ δ →
      ∀ z, ‖hamVF F t z - hamVF F t' z‖ ≤ ε)
    (z₀ : P n) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hbaδ : b - a ≤ δ) :
    ‖φ b z₀ - φ a z₀ - (b - a) • hamVF F b (φ a z₀)‖ ≤ (b - a) * (ε + K * C * (b - a)) := by
  set γ : ℝ → P n := fun t => φ t z₀ with hγ
  have hsub : Icc a b ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
  have hder : ∀ t ∈ Icc a b, HasDerivWithinAt γ (hamVF F t (γ t)) (Icc a b) t :=
    fun t ht => ((hφ z₀).2 t (hsub ht)).mono hsub
  have hlip : ∀ t ∈ Icc a b, ‖γ t - γ a‖ ≤ C * (t - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hder
      (fun t ht => hC t (hsub (Ico_subset_Icc_self ht)) _)
  set v := hamVF F b (γ a) with hv
  have hder2 : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => γ t - t • v)
      (hamVF F t (γ t) - v) (Icc a b) t := by
    intro t ht
    have := (hder t ht).sub ((hasDerivWithinAt_id t (Icc a b)).smul_const v)
    simpa only [Pi.sub_def, Pi.smul_apply, id_eq, one_smul] using this
  have hbd : ∀ t ∈ Ico a b, ‖hamVF F t (γ t) - v‖ ≤ ε + K * C * (b - a) := by
    intro t ht
    have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hb' : b ∈ Icc (0:ℝ) 1 := ⟨ha.trans hab, hb⟩
    have h1 : ‖hamVF F t (γ t) - hamVF F b (γ t)‖ ≤ ε :=
      hδ t (hsub ht') b hb' (by rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]) _
    have h2 : ‖hamVF F b (γ t) - hamVF F b (γ a)‖ ≤ K * (C * (b - a)) :=
      (hK b hb' _ _).trans (mul_le_mul_of_nonneg_left
        ((hlip t ht').trans (mul_le_mul_of_nonneg_left (by linarith [ht.2])
          ((norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩ (γ 0))))) hK0)
    calc ‖hamVF F t (γ t) - v‖
        = ‖(hamVF F t (γ t) - hamVF F b (γ t)) + (hamVF F b (γ t) - hamVF F b (γ a))‖ := by
          rw [hv]; congr 1; abel
      _ ≤ ε + K * (C * (b - a)) := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = ε + K * C * (b - a) := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder2 hbd b ⟨hab, le_rfl⟩
  have e : φ b z₀ - φ a z₀ - (b - a) • hamVF F b (φ a z₀) =
      (γ b - b • v) - (γ a - a • v) := by
    simp only [hγ, hv, sub_smul]; abel
  rw [e]; linarith [this]

set_option maxHeartbeats 1000000 in
/-- **Convergence of the implicit symplectic Euler scheme.** For a compactly supported
Hamiltonian, every discrete orbit `y₀, …, y_N` of the scheme
`y_{k+1} = y_k + (1/N) X_F((k+1)/N, (x_k, p_{k+1}))` ends within `ε` of `φ_F¹(y₀)` once `N` is
large, uniformly in `y₀`. -/
theorem discrete_orbit_close (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (φ : ℝ → P n → P n)
    (hφ : IsHamFlow F φ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ y : ℕ → P n,
      (∀ k < N, y (k + 1) = y k + (1 / (N:ℝ)) •
        hamVF F (((k:ℝ) + 1) / N) ((y k).1, (y (k + 1)).2)) →
      ‖y N - φ 1 (y 0)‖ ≤ ε := by
  obtain ⟨S, hS, hred⟩ := hamiltonian_reduce F hF
  obtain ⟨K', C', hlip, -, hbd⟩ := hamVF_bounds F hF.1 S hS hred
  set K : ℝ := (K' : ℝ) with hKdef
  set C : ℝ := (C' : ℝ) with hCdef
  have hK0 : 0 ≤ K := K'.2
  have hC0 : 0 ≤ C := C'.2
  have hK : ∀ t ∈ Icc (0:ℝ) 1, ∀ x y, ‖hamVF F t x - hamVF F t y‖ ≤ K * ‖x - y‖ := by
    intro t ht x y
    have := (hlip t ht).dist_le_mul x y
    rwa [dist_eq_norm, dist_eq_norm] at this
  obtain ⟨K₀, hK₀, hK₀z⟩ := hF.2
  set ε₁ : ℝ := ε / (2 * Real.exp K) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := time_modulus (fun q : ℝ × P n => hamVF F q.1 q.2)
    (contDiff_hamVF F hF.1).continuous K₀ hK₀ (fun t ht z hz => hamVF_zero_off F K₀ hK₀ hK₀z t ht z hz)
    ε₁ hε₁0
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (max (1 / δ) (4 * K * C * Real.exp K / ε))
  refine ⟨N₁ + 1, Nat.succ_pos _, fun N hN y hy => ?_⟩
  have hNpos : (0:ℝ) < N := by
    have : (1:ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 N₁) hN
    linarith
  have hN₁N : (N₁ : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self N₁) hN
  set h : ℝ := 1 / N with hh
  have hh0 : 0 < h := by positivity
  have hNh : (N:ℝ) * h = 1 := by rw [hh]; field_simp
  have hhδ : h ≤ δ := by
    rw [hh, div_le_iff₀ hNpos]
    have := lt_of_le_of_lt (le_max_left _ _) (hN₁.trans hN₁N)
    rw [div_lt_iff₀ hδ0] at this
    linarith
  set D : ℝ := h * (ε₁ + 2 * K * C * h) with hD
  have hD0 : 0 ≤ D := by positivity
  set γ : ℝ → P n := fun t => φ t (y 0) with hγ
  have key : ∀ k : ℕ, k ≤ N →
      ‖y k - γ (k / N)‖ ≤ (1 + h * K) ^ k * (k * D) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hγ, (hφ (y 0)).1]
    | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have ek := ih hkN.le
      set a : ℝ := k / N with ha
      set b : ℝ := ((k:ℝ) + 1) / N with hb
      have ha0 : 0 ≤ a := by positivity
      have hab : b - a = h := by rw [ha, hb, hh]; field_simp; ring
      have hb1 : b ≤ 1 := by
        rw [hb, div_le_one hNpos]
        have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
        push_cast at this; linarith
      have hbI : b ∈ Icc (0:ℝ) 1 := ⟨by positivity, hb1⟩
      have hstep := flow_step_error F φ hφ K C hK (fun t ht x => hbd t ht x) hK0 ε₁ δ hδ (y 0)
        a b ha0 (by linarith) hb1 (by linarith)
      rw [hab] at hstep
      have hyk := hy k hkN
      set yt : P n := ((y k).1, (y (k + 1)).2) with hyt
      have hyty : ‖yt - y k‖ ≤ h * C := by
        have h1 : ‖yt - y k‖ ≤ ‖y (k + 1) - y k‖ := by
          rw [Prod.norm_def, Prod.norm_def]
          simp only [hyt, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
          exact max_le (by positivity) (le_max_right _ _)
        rw [hyk, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh0] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (hbd b hbI _) hh0.le)
      have hX : ‖hamVF F b yt - hamVF F b (γ a)‖ ≤ K * (h * C + ‖y k - γ a‖) := by
        refine (hK b hbI _ _).trans (mul_le_mul_of_nonneg_left ?_ hK0)
        calc ‖yt - γ a‖ = ‖(yt - y k) + (y k - γ a)‖ := by congr 1; abel
          _ ≤ ‖yt - y k‖ + ‖y k - γ a‖ := norm_add_le _ _
          _ ≤ h * C + ‖y k - γ a‖ := by linarith
      have hcast : ((k + 1 : ℕ) : ℝ) / N = b := by rw [hb]; push_cast; ring
      rw [hcast]
      have e : y (k + 1) - γ b = (y k - γ a) + h • (hamVF F b yt - hamVF F b (γ a))
          - (γ b - γ a - h • hamVF F b (γ a)) := by
        rw [hyk, smul_sub]; simp only [hγ, hh, hb]; abel
      have hrec : ‖y (k + 1) - γ b‖ ≤ (1 + h * K) * ‖y k - γ a‖ + D := by
        rw [e]
        have h1 := norm_sub_le ((y k - γ a) + h • (hamVF F b yt - hamVF F b (γ a)))
          (γ b - γ a - h • hamVF F b (γ a))
        have h2 := norm_add_le (y k - γ a) (h • (hamVF F b yt - hamVF F b (γ a)))
        have h3 : ‖h • (hamVF F b yt - hamVF F b (γ a))‖ =
            h * ‖hamVF F b yt - hamVF F b (γ a)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh0]
        have h4 := mul_le_mul_of_nonneg_left hX hh0.le
        have h5 : D = h * ε₁ + K * C * h * h + h * (K * (h * C)) := by rw [hD]; ring
        have h6 : h * (K * (h * C + ‖y k - γ a‖)) = h * (K * (h * C)) + h * K * ‖y k - γ a‖ := by
          ring
        have h7 : h * (ε₁ + K * C * h) = h * ε₁ + K * C * h * h := by ring
        linarith
      have hpow : 1 ≤ (1 + h * K) ^ (k + 1) := one_le_pow₀ (by nlinarith)
      have hpos : 0 ≤ 1 + h * K := by nlinarith
      have hA := mul_le_mul_of_nonneg_left ek hpos
      have hB := mul_le_mul_of_nonneg_right hpow hD0
      have e2 : (1 + h * K) * ((1 + h * K) ^ k * (k * D)) = (1 + h * K) ^ (k + 1) * (k * D) := by
        ring
      have e3 : (1 + h * K) ^ (k + 1) * (((k + 1 : ℕ) : ℝ) * D) =
          (1 + h * K) ^ (k + 1) * (k * D) + (1 + h * K) ^ (k + 1) * D := by push_cast; ring
      rw [e3]
      linarith
  have hfin := key N le_rfl
  rw [div_self hNpos.ne'] at hfin
  have hexp : (1 + h * K) ^ N ≤ Real.exp K := by
    calc (1 + h * K) ^ N ≤ Real.exp (h * K) ^ N := by
          apply pow_le_pow_left₀ (by nlinarith)
          have := Real.add_one_le_exp (h * K); linarith
      _ = Real.exp K := by rw [← Real.exp_nat_mul, ← mul_assoc, hNh, one_mul]
  have hND : (N:ℝ) * D = ε₁ + 2 * K * C / N := by
    rw [hD, ← mul_assoc, hNh, one_mul, hh]; ring
  have hsmall : 2 * K * C / N * Real.exp K ≤ ε / 2 := by
    have := lt_of_le_of_lt (le_max_right _ _) (hN₁.trans hN₁N)
    rw [div_lt_iff₀ hε] at this
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    nlinarith
  have hε₁e : ε₁ * Real.exp K = ε / 2 := by
    rw [hε₁]; field_simp
  have hfin' : ‖y N - φ 1 (y 0)‖ ≤ (1 + h * K) ^ N * (N * D) := hfin
  have hND0 : 0 ≤ (N:ℝ) * D := mul_nonneg hNpos.le hD0
  have h1 : (1 + h * K) ^ N * (N * D) ≤ Real.exp K * (N * D) :=
    mul_le_mul_of_nonneg_right hexp hND0
  have h2 : Real.exp K * (N * D) = ε₁ * Real.exp K + 2 * K * C / N * Real.exp K := by
    rw [hND]; ring
  linarith

/-- Oscillation `max F(t,·) - min F(t,·)` of a time slice. -/
def oscSlice (F : ℝ → P n → ℝ) (t : ℝ) : ℝ := (⨆ z, F t z) - ⨅ z, F t z

theorem hoferLength_eq_integral_oscSlice (F : ℝ → P n → ℝ) :
    hoferLength F = ∫ t in (0:ℝ)..1, oscSlice F t := rfl

/-- A compactly supported Hamiltonian is bounded on `[0,1] × ℝ²ⁿ`. -/
theorem hamiltonian_bounded (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) :
    ∃ B : ℝ, ∀ t ∈ Icc (0:ℝ) 1, ∀ z, |F t z| ≤ B := by
  obtain ⟨K, hK, hKz⟩ := hF.2
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    (hF.1.continuous.continuousOn)
  refine ⟨max B 0, fun t ht z => ?_⟩
  by_cases hz : z ∈ K
  · have := hB (t, z) ⟨ht, hz⟩
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [hKz t ht z hz, abs_zero]; exact le_max_right _ _

theorem iSup_le_iSup_add {f g : P n → ℝ} {e : ℝ} (hg : BddAbove (range g))
    (h : ∀ z, f z ≤ g z + e) : (⨆ z, f z) ≤ (⨆ z, g z) + e :=
  ciSup_le fun z => (h z).trans (add_le_add_left (le_ciSup hg z) _)

theorem iInf_le_iInf_add {f g : P n → ℝ} {e : ℝ} (hf : BddBelow (range f))
    (h : ∀ z, f z ≤ g z + e) : (⨅ z, f z) ≤ (⨅ z, g z) + e := by
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro z
  rw [sub_le_iff_le_add]
  exact (ciInf_le hf z).trans (h z)

/-- Right Riemann sums of the oscillation are eventually at most `hoferLength F + ε`. -/
theorem riemann_osc_le (F : ℝ → P n → ℝ) (hF : IsHamiltonian F) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (1 / (N:ℝ)) * ∑ k ∈ Finset.range N, oscSlice F (((k:ℝ) + 1) / N) ≤ hoferLength F + ε := by
  obtain ⟨B, hB⟩ := hamiltonian_bounded F hF
  obtain ⟨K, hK, hKz⟩ := hF.2
  obtain ⟨δ, hδ0, hδ⟩ := time_modulus (fun q : ℝ × P n => F q.1 q.2) hF.1.continuous K hK
    (fun t ht z hz => hKz t ht z hz) (ε / 4) (by positivity)
  have hbddA : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (range (F t)) := fun t ht =>
    ⟨B, by rintro _ ⟨z, rfl⟩; exact (le_abs_self _).trans (hB t ht z)⟩
  have hbddB : ∀ t ∈ Icc (0:ℝ) 1, BddBelow (range (F t)) := fun t ht =>
    ⟨-B, by rintro _ ⟨z, rfl⟩; exact (neg_le.1 ((neg_le_abs _).trans (hB t ht z)))⟩
  have hosc : ∀ t ∈ Icc (0:ℝ) 1, ∀ t' ∈ Icc (0:ℝ) 1, |t - t'| ≤ δ →
      oscSlice F t' ≤ oscSlice F t + ε / 2 := by
    intro t ht t' ht' htt
    have hz : ∀ z, |F t z - F t' z| ≤ ε / 4 := fun z => by
      have := hδ t ht t' ht' htt z; simpa [Real.norm_eq_abs] using this
    have h1 : (⨆ z, F t' z) ≤ (⨆ z, F t z) + ε / 4 :=
      iSup_le_iSup_add (hbddA t ht) (fun z => by
        have := hz z; rw [abs_le] at this; linarith)
    have h2 : (⨅ z, F t z) ≤ (⨅ z, F t' z) + ε / 4 :=
      iInf_le_iInf_add (hbddB t ht) (fun z => by
        have := hz z; rw [abs_le] at this; linarith)
    simp only [oscSlice]; linarith
  have hcont : ContinuousOn (oscSlice F) (Icc 0 1) := by
    rw [Metric.continuousOn_iff]
    intro t ht e he
    obtain ⟨δ', hδ'0, hδ'⟩ := time_modulus (fun q : ℝ × P n => F q.1 q.2) hF.1.continuous K hK
      (fun t ht z hz => hKz t ht z hz) (e / 4) (by positivity)
    refine ⟨δ', hδ'0, fun t' ht' hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have hz : ∀ (a b : ℝ), a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → |a - b| ≤ δ' →
        oscSlice F b ≤ oscSlice F a + e / 2 := by
      intro a b ha hb hab
      have hz : ∀ z, |F a z - F b z| ≤ e / 4 := fun z => by
        have := hδ' a ha b hb hab z; simpa [Real.norm_eq_abs] using this
      have h1 : (⨆ z, F b z) ≤ (⨆ z, F a z) + e / 4 :=
        iSup_le_iSup_add (hbddA a ha) (fun z => by
          have := hz z; rw [abs_le] at this; linarith)
      have h2 : (⨅ z, F a z) ≤ (⨅ z, F b z) + e / 4 :=
        iInf_le_iInf_add (hbddB a ha) (fun z => by
          have := hz z; rw [abs_le] at this; linarith)
      simp only [oscSlice]; linarith
    have := hz t t' ht ht' (by rw [abs_sub_comm]; exact hd.le)
    have := hz t' t ht' ht hd.le
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / δ)
  refine ⟨N₁ + 1, Nat.succ_pos _, fun N hN => ?_⟩
  have hNpos : (0:ℝ) < N := by
    have : (1:ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 N₁) hN
    linarith
  have hN₁N : (N₁ : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self N₁) hN
  have hhδ : 1 / (N:ℝ) ≤ δ := by
    rw [div_le_iff₀ hNpos]
    have := hN₁.trans hN₁N
    rw [div_lt_iff₀ hδ0] at this
    linarith
  set a : ℕ → ℝ := fun k => (k:ℝ) / N with ha
  have haI : ∀ k ≤ N, a k ∈ Icc (0:ℝ) 1 := fun k hk =>
    ⟨by positivity, by
      rw [ha, div_le_one hNpos]; exact_mod_cast hk⟩
  have hmono : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    simp only [ha]
    exact div_le_div_of_nonneg_right (by push_cast; linarith) hNpos.le
  have hint : ∀ k < N, IntervalIntegrable (oscSlice F) MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    apply (hcont.mono _).intervalIntegrable
    rw [uIcc_of_le (hmono k)]
    exact Icc_subset_Icc (haI k hk.le).1 (haI (k+1) hk).2
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = 0 := by simp [ha]
  have hNa : a N = 1 := by simp [ha, div_self hNpos.ne']
  rw [h0, hNa, ← hoferLength_eq_integral_oscSlice] at hsum
  have hpiece : ∀ k ∈ Finset.range N,
      (1 / (N:ℝ)) * oscSlice F (((k:ℝ) + 1) / N) - (1 / (N:ℝ)) * (ε / 2) ≤
        ∫ x in a k..a (k + 1), oscSlice F x := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hle : a k ≤ a (k + 1) := hmono k
    have hlen : a (k + 1) - a k = 1 / N := by simp only [ha]; push_cast; field_simp; ring
    have hc := intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint k hk)
      (f := fun _ => oscSlice F (((k:ℝ) + 1) / N) - ε / 2) (fun x hx => by
        have hxI : x ∈ Icc (0:ℝ) 1 := Icc_subset_Icc (haI k hk.le).1 (haI (k+1) hk).2 hx
        have hbI : ((k:ℝ) + 1) / N ∈ Icc (0:ℝ) 1 := by
          have := haI (k + 1) hk; simpa [ha] using this
        have hd : |x - ((k:ℝ) + 1) / N| ≤ δ := by
          have hb : a (k + 1) = ((k:ℝ) + 1) / N := by simp [ha]
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]
          linarith [hx.1, hx.2]
        have := hosc x hxI _ hbI hd
        linarith)
    rw [intervalIntegral.integral_const, hlen, smul_eq_mul] at hc
    linarith
  have := Finset.sum_le_sum hpiece
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at this
  have hN1 : (N:ℝ) * (1 / (N:ℝ) * (ε / 2)) = ε / 2 := by field_simp
  linarith

end GradRange

assert_standard_axioms GradRange.discrete_orbit_close GradRange.riemann_osc_le
