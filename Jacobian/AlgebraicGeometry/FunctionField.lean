import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Function fields over a ground field

The structure morphism of an integral scheme gives its function field a ground-field
algebra structure. If some local ring has nonzero Krull dimension, the function
field contains a transcendental element over the ground field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The ground-field homomorphism into a local ring, induced by the structure morphism. -/
def Hom.structureStalk {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (morphism : scheme ⟶ Spec (.of baseField)) (point : scheme) :
    CommRingCat.of baseField ⟶ scheme.presheaf.stalk point :=
  (Scheme.ΓSpecIso (.of baseField)).inv ≫ morphism.appTop ≫
    scheme.presheaf.germ ⊤ point trivial

/-- Taking the spectrum of the ground-field map to a stalk gives the canonical
map from the local scheme to the base. -/
theorem Hom.Spec_map_structureStalk {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} (morphism : scheme ⟶ Spec (.of baseField)) (point : scheme) :
    Spec.map (morphism.structureStalk point) = scheme.fromSpecStalk point ≫ morphism := by
  rw [Hom.structureStalk, Spec.map_comp, Spec.map_comp,
    ← Scheme.fromSpecStalk_toSpecΓ scheme point]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The ground-field homomorphisms into stalks commute with specialization. -/
theorem Hom.structureStalk_stalkSpecializes {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} (morphism : scheme ⟶ Spec (.of baseField))
    {generalPoint specialPoint : scheme} (specialization : generalPoint ⤳ specialPoint) :
    morphism.structureStalk specialPoint ≫ scheme.presheaf.stalkSpecializes specialization =
      morphism.structureStalk generalPoint := by
  rw [Hom.structureStalk, Hom.structureStalk, Category.assoc, Category.assoc,
    TopCat.Presheaf.germ_stalkSpecializes]

/-- The canonical morphism from the spectrum of the function field, obtained from
the stalk at the generic point. -/
abbrev fromSpecFunctionField (scheme : Scheme.{u}) [IrreducibleSpace scheme] :
    Spec scheme.functionField ⟶ scheme :=
  scheme.fromSpecStalk (genericPoint scheme)

/-- The homomorphism from the ground field to the function field of an integral
scheme over that field. -/
abbrev functionFieldRingHom (baseField : Type u) [Field baseField] (scheme : Scheme.{u})
    [scheme.Over (Spec (.of baseField))] [IsIntegral scheme] :
    baseField →+* scheme.functionField :=
  (scheme.germToFunctionField ⊤ (h := ⟨⟨genericPoint scheme, trivial⟩⟩)).hom.comp
    (((Scheme.ΓSpecIso (.of baseField)).inv ≫
      (scheme ↘ Spec (.of baseField)).appTop).hom)

/-- A nonzero-dimensional local ring on an integral scheme over a field forces
the function field to contain an element transcendental over the ground field. -/
theorem exists_transcendental_functionField {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (.of baseField))] [IsIntegral scheme]
    (point : scheme) (positive_dimension : ringKrullDim (scheme.presheaf.stalk point) ≠ 0) :
    ∃ element : scheme.functionField,
      letI := (functionFieldRingHom baseField scheme).toAlgebra
      Transcendental baseField element := by
  let := (functionFieldRingHom baseField scheme).toAlgebra
  let coefficients : baseField →+* Γ(scheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of baseField)).inv ≫
      (scheme ↘ Spec (.of baseField)).appTop).hom
  letI : Nonempty (⊤ : scheme.Opens) := ⟨⟨point, trivial⟩⟩
  let : Algebra baseField (scheme.presheaf.stalk point) :=
    ((scheme.presheaf.germ ⊤ point trivial).hom.comp coefficients).toAlgebra
  by_contra! all_algebraic
  have : Algebra.IsAlgebraic baseField scheme.functionField :=
    ⟨fun element ↦ not_not.mp (all_algebraic element)⟩
  have injective : Function.Injective
      (algebraMap (scheme.presheaf.stalk point) scheme.functionField) :=
    IsFractionRing.injective _ _
  have : Algebra.IsAlgebraic baseField (scheme.presheaf.stalk point) :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq (RingHom.id baseField)
      (algebraMap (scheme.presheaf.stalk point) scheme.functionField)
      Function.surjective_id injective (by
        ext coefficient
        change scheme.germToFunctionField ⊤ (coefficients coefficient) =
          algebraMap (scheme.presheaf.stalk point) scheme.functionField
            (scheme.presheaf.germ ⊤ point trivial (coefficients coefficient))
        rw [Scheme.algebraMap_germ_eq_germToFunctionField])
  have local_field : IsField (scheme.presheaf.stalk point) :=
    (Algebra.IsIntegral.isField_iff_isField
      (algebraMap baseField _).injective).mp (Field.toIsField baseField)
  exact positive_dimension (ringKrullDim_eq_zero_of_isField local_field)

/-- Specialization induces an injective homomorphism between stalks of an
integral scheme. -/
theorem injective_stalkSpecializes {scheme : Scheme.{u}} [IsIntegral scheme]
    {generalPoint specialPoint : scheme} (specialization : generalPoint ⤳ specialPoint) :
    Function.Injective (scheme.presheaf.stalkSpecializes specialization) := by
  have injective := IsFractionRing.injective (scheme.presheaf.stalk specialPoint)
    scheme.functionField
  have composition := TopCat.Presheaf.stalkSpecializes_comp scheme.presheaf
    ((genericPoint_spec scheme).specializes trivial) specialization
  refine fun left right equality ↦ injective ?_
  change scheme.presheaf.stalkSpecializes _ left = scheme.presheaf.stalkSpecializes _ right
  rw [← composition, CommRingCat.comp_apply, CommRingCat.comp_apply, equality]

end AlgebraicGeometry.Scheme
