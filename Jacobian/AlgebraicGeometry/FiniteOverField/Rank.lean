import Jacobian.AlgebraicGeometry.FiniteOverField
import Jacobian.AlgebraicGeometry.GlobalSections.Rank
import Jacobian.RingTheory.Flat.Rank
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Dimensions under finite flat morphisms of finite schemes

A finite flat morphism of constant rank between schemes finite over a field
multiplies the dimensions of their rings of global functions by its rank.
The scalar actions are induced by their structure morphisms.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite flat map of constant rank multiplies the dimensions of global functions. -/
theorem finrank_globalSections_eq_mul {baseField : Type u} [Field baseField]
    {source target : Scheme.{u}} (structureMap : target ⟶ Spec (.of baseField))
    [IsFinite structureMap] (morphism : source ⟶ target) [IsFinite morphism] [Flat morphism]
    (rank : ℕ) (constantRank : ∀ point : target, morphism.finrank point = rank) :
    letI := structureMap.ΓAlgebra
    letI := (morphism ≫ structureMap).ΓAlgebra
    Module.finrank baseField Γ(source, ⊤) = rank * Module.finrank baseField Γ(target, ⊤) := by
  letI := structureMap.ΓAlgebra
  letI := (morphism ≫ structureMap).ΓAlgebra
  letI := morphism.appTop.hom.toAlgebra
  letI : IsScalarTower baseField Γ(target, ⊤) Γ(source, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext scalar
      change ((ΓSpecIso (.of baseField)).inv ≫ (morphism ≫ structureMap).appTop).hom scalar =
        morphism.appTop.hom (((ΓSpecIso (.of baseField)).inv ≫ structureMap.appTop).hom scalar)
      rfl)
  letI : IsAffine target := isAffine_of_isAffineHom structureMap
  letI : IsAffine source := isAffine_of_isAffineHom morphism
  letI : Module.Finite baseField Γ(target, ⊤) := finite_globalSections_of_isFinite structureMap
  letI : Module.Finite Γ(target, ⊤) Γ(source, ⊤) := morphism.finite_appTop
  letI : Module.Flat Γ(target, ⊤) Γ(source, ⊤) := morphism.flat_appTop
  apply Module.finrank_eq_mul_of_rankAtStalk_eq
  intro prime
  have cartesian : IsPullback source.isoSpec.inv (Spec.map morphism.appTop)
      morphism target.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality morphism).symm⟩
  have rankEquality := Scheme.Hom.finrank_of_isPullback source.isoSpec.inv
    (Spec.map morphism.appTop) morphism target.isoSpec.inv cartesian prime
  have scalarMap : morphism.appTop =
      CommRingCat.ofHom (algebraMap Γ(target, ⊤) Γ(source, ⊤)) := rfl
  rw [scalarMap, Scheme.Hom.finrank_SpecMap_algebraMap] at rankEquality
  exact rankEquality.trans (constantRank (target.isoSpec.inv prime))

end AlgebraicGeometry.Scheme.Hom
