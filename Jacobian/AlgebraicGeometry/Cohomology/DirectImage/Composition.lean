import Jacobian.Algebra.Homology.CochainComplex.Resolution
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Jacobian.AlgebraicGeometry.Cohomology.Flasque
import Jacobian.CategoryTheory.Abelian.RightDerived.Resolution

/-!
# Acyclicity for composite direct images

If the positive higher direct images of a module vanish for both a morphism
and its composite, its direct image is acyclic for the second morphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

instance preservesFiniteLimits_pushforward {Y Z : Scheme.{u}} (h : Y ⟶ Z) :
    PreservesFiniteLimits (pushforward h) :=
  have := (pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- **Direct images along a composite.** If `R^q h_* G = 0` and `R^q (h ≫ f)_* G = 0` for all
`q > 0`, then `h_* G` is `f_*`-acyclic: an injective resolution `G ⟶ J` pushes forward to a
resolution `h_* G ⟶ h_* J` by flasque modules, and `f_* h_* J = (h ≫ f)_* J`. -/
theorem rightAcyclic_pushforward_obj_of_isZero {Y Z S : Scheme.{u}} (h : Y ⟶ Z) (f : Z ⟶ S)
    [HasInjectiveResolutions Y.Modules] [HasInjectiveResolutions Z.Modules] (G : Y.Modules)
    (hh : ∀ q, IsZero ((higherDirectImage h (q + 1)).obj G))
    (hhf : ∀ q, IsZero ((higherDirectImage (h ≫ f) (q + 1)).obj G)) :
    (pushforward f).rightAcyclic ((pushforward h).obj G) := by
  let J := injectiveResolution G
  let K := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hε : (pushforward h).map (J.ι.f 0) ≫ K.d 0 1 = 0 := by
    change (pushforward h).map (J.ι.f 0) ≫ (pushforward h).map (J.cocomplex.d 0 1) = 0
    rw [← Functor.map_comp, J.ι_f_zero_comp_complex_d, Functor.map_zero]
  have : Mono ((pushforward h).map (J.ι.f 0)) := inferInstance
  have h0 : (ShortComplex.mk _ _ hε).Exact :=
    J.exact₀.map_of_mono_of_preservesKernel (pushforward h) inferInstance inferInstance
  have hK (n : ℕ) : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hh n).of_iso (J.isoRightDerivedObj (pushforward h) (n + 1)).symm
  have := CochainComplex.quasiIso_fromSingle₀Equiv_symm _ hε h0 hK
  have hI (n : ℕ) : (pushforward f).rightAcyclic (K.X n) :=
    rightAcyclic_pushforward_of_isFlasque f _
      (isFlasque_pushforward h _ (isFlasque_of_injective _))
  intro q
  refine IsZero.of_iso ?_ ((pushforward f).rightDerivedObjIsoOfResolution
    ((CochainComplex.fromSingle₀Equiv K _).symm ⟨_, hε⟩) hI (q + 1))
  exact (hhf q).of_iso (HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (pushforwardComp h f) _).app J.cocomplex) (q + 1) ≪≫
      (J.isoRightDerivedObj (pushforward (h ≫ f)) (q + 1)).symm)

end AlgebraicGeometry.Scheme.Modules
