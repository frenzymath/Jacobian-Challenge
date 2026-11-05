import Jacobian.AlgebraicGeometry.Picard.Degree
import Jacobian.AlgebraicGeometry.Picard.Sheaf
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Degree parts of the relative Picard sheaf

The degree of a class on every field-valued fiber defines a subpresheaf.
Its fppf sheafification is the degree part of the relative Picard sheaf.
The resulting inclusion is injective on sections: sheafification preserves
local injectivity of the original subpresheaf inclusion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme
variable {k : Type u} [Field k] {X : Scheme.{u}}

def picardFibreDegree (f : X ⟶ Spec (.of k)) {T : Over (Spec (.of k))}
    (L : (picardPresheaf f).obj (.op T)) {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T) : ℤ :=
  letI : (Limits.pullback f
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).Over (Spec (.of K)) :=
    ⟨Limits.pullback.snd f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom⟩
  Modules.degree K ((fromSkeleton _).obj (Pic.map (baseChangeMap f t) L).val)

/-- The degree-`d` subfunctor of the Picard presheaf of `f : X ⟶ Spec k`: the classes
`ℒ ∈ Pic (X_T)` all of whose fibres have degree `d`, i.e. `deg ℒ_t = d` for every field-valued
point `t` of `T`.  It is a subfunctor because the fibres of the pullback of `ℒ` along `T' ⟶ T`
are among the fibres of `ℒ`.

For quasi-compact quasi-separated families, `mem_picardSubfunctorDegree_iff`
identifies this condition with constant degree on all residue-field fibers.
 -/
def picardSubfunctorDegree (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Subfunctor (picardPresheaf f) where
  obj T := {L | ∀ (K : Type u) [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T.unop),
      picardFibreDegree f L t = d}
  map := by
    rintro ⟨U⟩ ⟨V⟩ ⟨i⟩ L hL
    intro K _ _ t
    have h := hL K (t ≫ i)
    have e : Pic.map (baseChangeMap f (t ≫ i)) L =
        Pic.map (baseChangeMap f t) (Pic.map (baseChangeMap f i) L) := by
      rw [baseChangeMap_comp, Pic.map_comp]
    simp only [picardFibreDegree, e] at h
    exact h

/-- The degree-`d` part `Pic^d_{X/k}` of the relative Picard functor: the fppf sheafification of
the degree-`d` subfunctor `AlgebraicGeometry.picardSubfunctorDegree` of the Picard presheaf, in
the same way that `AlgebraicGeometry.picardFunctor` is the fppf sheafification of the whole
Picard presheaf.
 -/
def picardFunctorDegree (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Sheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
    (picardSubfunctorDegree f d).toFunctor


variable (f : X ⟶ Spec (.of k)) (d : ℤ)

/-- The inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}` of the degree-`d` part into the relative Picard
functor, induced by the inclusion of the degree-`d` subfunctor of the Picard presheaf. -/
def picardFunctorDegreeι : picardFunctorDegree f d ⟶ picardFunctor f :=
  ⟨sheafifyLift (fppfTopology.over (Spec (.of k)))
    ((picardSubfunctorDegree f d).ι ≫ toPicardFunctor f) (picardFunctor f).property⟩

/-- On the image of a class `M` of the degree-`d` subfunctor, the inclusion
`Pic^d_{X/k} ⟶ Pic_{X/k}` is the image of `M` in `Pic_{X/k}`. -/
lemma picardFunctorDegreeι_app_toSheafify {T : Over (Spec (.of k))}
    (M : (picardSubfunctorDegree f d).toFunctor.obj (.op T)) :
    (picardFunctorDegreeι f d).hom.app _
        ((toSheafify (fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f d).toFunctor).app _ M) =
      (toPicardFunctor f).app _ M.1 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_sheafifyLift (fppfTopology.over _)
    ((picardSubfunctorDegree f d).ι ≫ toPicardFunctor f) (picardFunctor f).property) (.op T)) M

/-- **`Pic^d_{X/k}` is a subsheaf of `Pic_{X/k}`**: the inclusion is injective on sections, as
the inclusion of the degree-`d` subfunctor is injective and sheafification preserves local
injectivity. -/
lemma injective_picardFunctorDegreeι_app (T : Over (Spec (.of k))) :
    Function.Injective ((picardFunctorDegreeι f d).hom.app (.op T)) := by
  let J := fppfTopology.over (Spec (.of k))
  let α := (picardSubfunctorDegree f d).ι ≫ toPicardFunctor f
  have : Presheaf.IsLocallyInjective J α := inferInstance
  have : Presheaf.IsLocallyInjective J (picardFunctorDegreeι f d).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α
      (toSheafify_sheafifyLift J α _)
  exact (Sheaf.isLocallyInjective_iff_injective _).1 this _


end AlgebraicGeometry
