module

public import Mathlib

@[expose] public section

/-!
# Definitions for "Regular closed gradient ranges and asymptotic gradient values"

All objects follow the paper (arXiv:2609.05951v1).

* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; gradients are Mathlib's genuine (Fréchet) `gradient`.
* `ℝ²ⁿ = ℝⁿ_x × ℝⁿ_p` is modelled as `E n × E n` with the symplectic form
  `ω₀ = ∑ dx_j ∧ dp_j` and momentum projection `π_p = Prod.snd`.
* Compactly supported smooth Hamiltonians `F : [0,1] × M → ℝ`, their flows
  (`ẋ = ∇_p F`, `ṗ = -∇_x F`), Hofer length and displacement energy
  `e(U,N) = inf {𝓛(F) : φ_F¹(closure U) ∩ N = ∅}` (value `⊤ = +∞` if no such `F`).
* The cotangent bundle `T*Tⁿ = Tⁿ × ℝⁿ` is modelled through its universal cover
  `ℝⁿ × ℝⁿ`: Hamiltonians are `ℤⁿ`-periodic in `θ` and vanish for large `|η|`,
  subsets of `Tⁿ × ℝⁿ` are represented by subsets of the cover and their `ℤⁿ`-orbits.
-/

open Set Metric Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace GradRange

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Phase space `ℝ²ⁿ = ℝⁿ_x × ℝⁿ_p`. -/
abbrev P (n : ℕ) := E n × E n

variable {n : ℕ}

/-! ## Gradient ranges and asymptotic values -/

/-- The gradient range `G_f = {∇f(x) : x ∈ ℝⁿ}`. -/
def gradRange (f : E n → ℝ) : Set (E n) := range (gradient f)

/-- The asymptotic gradient values
`A_∞(f) = ⋂_{R>0} closure {∇f(x) : |x| ≥ R}`. -/
def asymptoticValues (f : E n → ℝ) : Set (E n) :=
  ⋂ (R : ℝ) (_ : 0 < R), closure (gradient f '' {x | R ≤ ‖x‖})

/-- The gradient graph `Γ_f = {(x, ∇f(x))}`. -/
def gradGraph (f : E n → ℝ) : Set (P n) := range (fun x => (x, gradient f x))

/-- The zero section `Z = ℝⁿ × {0}`. -/
def zeroSection (n : ℕ) : Set (P n) := {z | z.2 = 0}

/-- A function is affine if it is of the form `x ↦ ⟪a, x⟫ + c`. -/
def IsAffine (f : E n → ℝ) : Prop := ∃ (a : E n) (c : ℝ), ∀ x, f x = inner ℝ a x + c

/-! ## Symplectic structure -/

/-- The standard symplectic form `ω₀ = ∑ⱼ dxⱼ ∧ dpⱼ` on `ℝ²ⁿ`. -/
def omega0 (v w : P n) : ℝ := inner ℝ v.1 w.2 - inner ℝ w.1 v.2

/-- Partial gradient in `x`. -/
def gradX (H : P n → ℝ) (z : P n) : E n := gradient (fun x => H (x, z.2)) z.1

/-- Partial gradient in `p`. -/
def gradP (H : P n → ℝ) (z : P n) : E n := gradient (fun p => H (z.1, p)) z.2

/-- The Hamiltonian vector field `(∇_p F, -∇_x F)` of a time-dependent Hamiltonian. -/
def hamVF (F : ℝ → P n → ℝ) (t : ℝ) (z : P n) : P n := (gradP (F t) z, -gradX (F t) z)

/-- A smooth Hamiltonian on `[0,1] × ℝ²ⁿ` whose time slices are supported in one
compact set. -/
def IsHamiltonian (F : ℝ → P n → ℝ) : Prop :=
  ContDiff ℝ ∞ (Function.uncurry F) ∧
    ∃ K : Set (P n), IsCompact K ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∉ K, F t z = 0

/-- `φ` is the Hamiltonian flow of `F` on `[0,1]` (`φ 0 = id`, Hamilton's equations). -/
def IsHamFlow (F : ℝ → P n → ℝ) (φ : ℝ → P n → P n) : Prop :=
  ∀ z, φ 0 z = z ∧
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => φ s z) (hamVF F t (φ t z)) (Icc 0 1) t

/-- Hofer length `𝓛(F) = ∫₀¹ (max F(t,·) - min F(t,·)) dt`. -/
def hoferLength (F : ℝ → P n → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ((⨆ z, F t z) - ⨅ z, F t z)

/-- Displacement energy `e(U,N) = inf {𝓛(F) : φ_F¹(closure U) ∩ N = ∅}` in `ℝ²ⁿ`,
equal to `⊤ = +∞` if no compactly supported Hamiltonian displaces `closure U` from `N`. -/
def displacementEnergy (U N : Set (P n)) : ℝ≥0∞ :=
  sInf {e | ∃ (F : ℝ → P n → ℝ) (φ : ℝ → P n → P n), IsHamiltonian F ∧ IsHamFlow F φ ∧
    Disjoint (φ 1 '' closure U) N ∧ e = ENNReal.ofReal (hoferLength F)}

/-- A closed set `N` is displacement rigid if `e(U,N) > 0` for every open `U` meeting `N`. -/
def IsDisplacementRigid (N : Set (P n)) : Prop :=
  ∀ U : Set (P n), IsOpen U → (U ∩ N).Nonempty → displacementEnergy U N ≠ 0

/-! ## Lagrangian submanifolds and symplectic homeomorphisms -/

/-- `L ⊆ ℝ²ⁿ` is a compact smooth Lagrangian submanifold without boundary: `L` is compact
and near each of its points it is the image of a smooth embedding (an injective immersion
which is a homeomorphism onto its image) of an open subset of `ℝⁿ`, and `ω₀` vanishes on
the tangent spaces. -/
def IsCompactLagrangian (L : Set (P n)) : Prop :=
  IsCompact L ∧ ∀ z ∈ L, ∃ W : Set (P n), IsOpen W ∧ z ∈ W ∧
    ∃ (V : Set (E n)) (φ : E n → P n), IsOpen V ∧ ContDiffOn ℝ ∞ φ V ∧
      (∀ v ∈ V, Function.Injective (fderiv ℝ φ v)) ∧
      φ '' V = L ∩ W ∧ Topology.IsEmbedding (V.restrict φ) ∧
      ∀ v ∈ V, ∀ a b : E n, omega0 (fderiv ℝ φ v a) (fderiv ℝ φ v b) = 0

/-- A smooth diffeomorphism of `ℝ²ⁿ` preserving `ω₀`. -/
def IsSymplecticDiffeo (g : P n → P n) : Prop :=
  ContDiff ℝ ∞ g ∧
    (∃ h : P n → P n, ContDiff ℝ ∞ h ∧ Function.LeftInverse h g ∧ Function.RightInverse h g) ∧
    ∀ z v w, omega0 (fderiv ℝ g z v) (fderiv ℝ g z w) = omega0 v w

/-- A symplectic homeomorphism: a homeomorphism which is a locally uniform limit of smooth
diffeomorphisms preserving `ω₀`. -/
def IsSymplecticHomeomorph (ψ : P n ≃ₜ P n) : Prop :=
  ∃ g : ℕ → P n → P n, (∀ k, IsSymplecticDiffeo (g k)) ∧ TendstoLocallyUniformly g ψ atTop

/-! ## The cotangent bundle of the torus `Tⁿ × ℝⁿ`, through its universal cover -/

/-- The integer vector `m ∈ ℤⁿ ⊆ ℝⁿ`. -/
def intVec (m : Fin n → ℤ) : E n := WithLp.toLp 2 (fun j => (m j : ℝ))

/-- The preimage in `ℝⁿ × ℝⁿ` of the image of `S` in `Tⁿ × ℝⁿ`. -/
def latticeOrbit (S : Set (P n)) : Set (P n) :=
  {z | ∃ m : Fin n → ℤ, (z.1 + intVec m, z.2) ∈ S}

/-- A smooth compactly supported Hamiltonian on `[0,1] × (Tⁿ × ℝⁿ)`, written on the
universal cover: `ℤⁿ`-periodic in `θ`, vanishing for `|η|` large. -/
def IsTorusHamiltonian (F : ℝ → P n → ℝ) : Prop :=
  ContDiff ℝ ∞ (Function.uncurry F) ∧
    (∀ t (z : P n) (m : Fin n → ℤ), F t (z.1 + intVec m, z.2) = F t z) ∧
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : P n, C < ‖z.2‖ → F t z = 0

/-- Displacement energy `e_M(U,N)` in `M = Tⁿ × ℝⁿ`, for the images in `M` of
`U, N ⊆ ℝⁿ × ℝⁿ`. The closure of the image of `U` in `M` lifts to
`closure (latticeOrbit U)`. -/
def torusDisplacementEnergy (U N : Set (P n)) : ℝ≥0∞ :=
  sInf {e | ∃ (F : ℝ → P n → ℝ) (φ : ℝ → P n → P n), IsTorusHamiltonian F ∧ IsHamFlow F φ ∧
    Disjoint (φ 1 '' closure (latticeOrbit U)) (latticeOrbit N) ∧
    e = ENNReal.ofReal (hoferLength F)}

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient_of_contDiff (f : E n → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  have h := hf.continuous_fderiv (by norm_num)
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp h

end GradRange
