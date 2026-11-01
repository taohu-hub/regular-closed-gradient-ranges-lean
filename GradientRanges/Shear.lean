module

public import GradientRanges.Defs

@[expose] public section

/-!
# Shears by gradients of smooth functions are symplectic diffeomorphisms
-/
open Set Metric Filter Topology
open scoped ContDiff
namespace GradRange
variable {n : ℕ}

/-- The shear `(x,p) ↦ (x, p + ∇g(x))`. -/
noncomputable def shearMap (g : E n → ℝ) (z : P n) : P n := (z.1, z.2 + gradient g z.1)

theorem gradient_eq_comp (g : E n → ℝ) :
    gradient g = fun x => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ g x) := rfl

theorem contDiff_gradient_of_smooth (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (gradient g) := by
  rw [gradient_eq_comp]
  exact (InnerProductSpace.toDual ℝ (E n)).symm.contDiff.comp (hg.fderiv_right (by simp))

theorem fderiv_gradient_apply (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) (x b : E n) :
    fderiv ℝ (gradient g) x b =
      (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ (fderiv ℝ g) x b) := by
  have h1 : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have h2 := (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x h1
  rw [gradient_eq_comp]
  rw [show (fun x => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ g x)) =
    ((InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘
      fderiv ℝ g) from rfl, h2.fderiv]
  rfl

theorem isSymplecticDiffeo_shearMap (g : E n → ℝ) (hg : ContDiff ℝ ∞ g) :
    IsSymplecticDiffeo (shearMap g) := by
  have hG := contDiff_gradient_of_smooth g hg
  have hs : ContDiff ℝ ∞ (shearMap g) := by
    unfold shearMap
    exact contDiff_fst.prodMk (contDiff_snd.add (hG.comp contDiff_fst))
  refine ⟨hs, ⟨fun z => (z.1, z.2 - gradient g z.1), ?_, ?_, ?_⟩, ?_⟩
  · exact contDiff_fst.prodMk (contDiff_snd.sub (hG.comp contDiff_fst))
  · intro z; simp [shearMap]
  · intro z; simp [shearMap]
  · intro z v w
    have hD : ∀ u : P n, fderiv ℝ (shearMap g) z u = (u.1, u.2 + fderiv ℝ (gradient g) z.1 u.1) := by
      intro u
      have hGd : HasFDerivAt (gradient g) (fderiv ℝ (gradient g) z.1) z.1 :=
        (hG.differentiable (by simp) z.1).hasFDerivAt
      have h := (hasFDerivAt_fst (p := z)).prodMk
        ((hasFDerivAt_snd (p := z)).add (hGd.comp z hasFDerivAt_fst))
      have h' : HasFDerivAt (shearMap g) ((ContinuousLinearMap.fst ℝ (E n) (E n)).prod
          (ContinuousLinearMap.snd ℝ (E n) (E n) +
            (fderiv ℝ (gradient g) z.1).comp (ContinuousLinearMap.fst ℝ (E n) (E n)))) z := h
      rw [h'.fderiv]
      rfl
    have hsymm : IsSymmSndFDerivAt ℝ g z.1 :=
      hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    rw [hD, hD]
    simp only [omega0, inner_add_right, fderiv_gradient_apply g hg]
    have e1 : inner ℝ v.1 ((InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ (fderiv ℝ g) z.1 w.1))
        = fderiv ℝ (fderiv ℝ g) z.1 w.1 v.1 := by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have e2 : inner ℝ w.1 ((InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ (fderiv ℝ g) z.1 v.1))
        = fderiv ℝ (fderiv ℝ g) z.1 v.1 w.1 := by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [e1, e2, hsymm w.1 v.1]
    ring

end GradRange
