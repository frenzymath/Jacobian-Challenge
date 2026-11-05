import Jacobian.AlgebraicGeometry.FiniteOverField.Rank
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import Jacobian.AlgebraicGeometry.IdealSheaf.Twist

/-!
# Pullback of Cartier twists and finite closed subschemes

Flat pullback commutes with the twist by an effective Cartier divisor. For a
finite flat morphism of constant rank, the length of a finite closed subscheme
is multiplied by that rank after pullback.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {source target : Scheme.{u}}

/-- Flat pullback commutes with an effective Cartier twist. -/
def IsInvertible.pullbackTwistIso {ideal : target.IdealSheafData}
    (invertible : ideal.IsInvertible) (morphism : source ⟶ target) [Flat morphism]
    (moduleSheaf : target.Modules) :
    (Modules.pullback morphism).obj (ideal.twist moduleSheaf) ≅
      (ideal.comap morphism).twist ((Modules.pullback morphism).obj moduleSheaf) := by
  let comparison := Classical.choice
    (invertible.nonempty_pullback_dual_toModules_iso morphism
      (invertible.comap_of_flat morphism))
  exact Modules.pullbackTensorObjIso morphism moduleSheaf ideal.toModulesᵛ ≪≫
    whiskerLeftIso ((Modules.pullback morphism).obj moduleSheaf) comparison

/-- Pullback by a finite flat map of constant rank multiplies the length of a
finite closed subscheme by that rank. -/
theorem finrank_comap_eq_mul {baseField : Type u} [Field baseField]
    (sourceMap : source ⟶ Spec (.of baseField)) (targetMap : target ⟶ Spec (.of baseField))
    (morphism : source ⟶ target) [IsFinite morphism] [Flat morphism]
    (overBase : morphism ≫ targetMap = sourceMap) (rank : ℕ)
    (constantRank : ∀ point : target, morphism.finrank point = rank)
    (ideal : target.IdealSheafData) [IsFinite (ideal.subschemeι ≫ targetMap)] :
    letI := (ideal.subschemeι ≫ targetMap).ΓAlgebra
    letI := ((ideal.comap morphism).subschemeι ≫ sourceMap).ΓAlgebra
    Module.finrank baseField Γ((ideal.comap morphism).subscheme, ⊤) =
      rank * Module.finrank baseField Γ(ideal.subscheme, ⊤) := by
  let divisorMap := (ideal.comapIso morphism).hom ≫ pullback.snd morphism ideal.subschemeι
  have compatibility : divisorMap ≫ (ideal.subschemeι ≫ targetMap) =
      (ideal.comap morphism).subschemeι ≫ sourceMap := by
    calc
      divisorMap ≫ (ideal.subschemeι ≫ targetMap) =
          (ideal.comapIso morphism).hom ≫
            (pullback.snd morphism ideal.subschemeι ≫ ideal.subschemeι) ≫ targetMap := by
        simp only [divisorMap, Category.assoc]
      _ = (ideal.comapIso morphism).hom ≫
            (pullback.fst morphism ideal.subschemeι ≫ morphism) ≫ targetMap := by
        rw [← pullback.condition]
      _ = ((ideal.comapIso morphism).hom ≫ pullback.fst morphism ideal.subschemeι) ≫
            (morphism ≫ targetMap) := by simp only [Category.assoc]
      _ = (ideal.comap morphism).subschemeι ≫ sourceMap := by
        rw [ideal.comapIso_hom_fst, overBase]
  have divisorRank (point : ideal.subscheme) : divisorMap.finrank point = rank := by
    dsimp only [divisorMap]
    rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_snd]
    exact constantRank (ideal.subschemeι point)
  have dimensionEquality := Scheme.Hom.finrank_globalSections_eq_mul
    (ideal.subschemeι ≫ targetMap) divisorMap rank divisorRank
  let dimensionProperty : (baseField →+* Γ((ideal.comap morphism).subscheme, ⊤)) → Prop :=
    fun scalarMap ↦
      letI := (ideal.subschemeι ≫ targetMap).ΓAlgebra
      letI := scalarMap.toAlgebra
      Module.finrank baseField Γ((ideal.comap morphism).subscheme, ⊤) =
        rank * Module.finrank baseField Γ(ideal.subscheme, ⊤)
  have scalarEquality := congrArg
    (fun structureMap ↦ ((ΓSpecIso (.of baseField)).inv ≫ structureMap.appTop).hom)
    compatibility
  change dimensionProperty
    (((ΓSpecIso (.of baseField)).inv ≫
      (divisorMap ≫ (ideal.subschemeι ≫ targetMap)).appTop).hom) at dimensionEquality
  exact (congrArg dimensionProperty scalarEquality).mp dimensionEquality

end AlgebraicGeometry.Scheme.IdealSheafData
