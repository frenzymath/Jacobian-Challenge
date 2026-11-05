import Jacobian.Algebra.Homology.DerivedCategory.KProjective
import Jacobian.Algebra.Homology.DerivedCategory.Perfect.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Perfect complexes and distinguished triangles

Perfect complexes are stable under shifts and extensions. The proof lifts
the connecting morphism to bounded projective representatives and uses its
mapping cone, again a bounded finite projective complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u w

open CategoryTheory Limits

namespace DerivedCategory

variable {baseRing : Type u} [CommRing baseRing]
  [HasDerivedCategory.{w} (ModuleCat.{u} baseRing)]

private lemma exists_map_of_isKProjective {source target : CochainComplex (ModuleCat.{u} baseRing) ℤ}
    [source.IsKProjective] (morphism : Q.obj source ⟶ Q.obj target) :
    ∃ lift : source ⟶ target, Q.map lift = morphism := by
  obtain ⟨homotopy_map, image_eq⟩ := (CochainComplex.IsKProjective.Qh_map_bijective source
    ((HomotopyCategory.quotient _ _).obj target)).surjective
    ((quotientCompQhIso (ModuleCat.{u} baseRing)).hom.app source ≫ morphism ≫
      (quotientCompQhIso (ModuleCat.{u} baseRing)).inv.app target)
  obtain ⟨lift, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} baseRing) (ComplexShape.up ℤ)).map_surjective homotopy_map
  refine ⟨lift, ?_⟩
  have naturality := quotientCompQhIso_hom_naturality (C := ModuleCat.{u} baseRing) lift
  rw [image_eq] at naturality
  rw [← cancel_epi ((quotientCompQhIso (ModuleCat.{u} baseRing)).hom.app source), ← naturality]
  simp

/-- Shifts of perfect objects are perfect. -/
lemma IsPerfect.shift {object : DerivedCategory (ModuleCat.{u} baseRing)}
    (perfect : object.IsPerfect) (shift : ℤ) : (object⟦shift⟧).IsPerfect := by
  obtain ⟨complex, lowerBound, upperBound, _, _, finite_projective, ⟨model⟩⟩ := perfect
  have := complex.isStrictlyGE_shift lowerBound shift (lowerBound - shift) (by omega)
  have := complex.isStrictlyLE_shift upperBound shift (upperBound - shift) (by omega)
  exact (isPerfect_Q_obj (complex⟦shift⟧) (lowerBound - shift) (upperBound - shift)
    fun degree ↦ finite_projective (degree + shift)).of_iso
      (((Q.commShiftIso shift).app complex) ≪≫ (shiftFunctor _ shift).mapIso model.symm)

/-- The mapping cone of a morphism of bounded finite projective complexes is perfect. -/
lemma isPerfect_Q_obj_mappingCone {source target : CochainComplex (ModuleCat.{u} baseRing) ℤ}
    (morphism : source ⟶ target) (sourceLower sourceUpper targetLower targetUpper : ℤ)
    [source.IsStrictlyGE sourceLower] [source.IsStrictlyLE sourceUpper]
    [target.IsStrictlyGE targetLower] [target.IsStrictlyLE targetUpper]
    (source_projective : ∀ degree, Module.Projective baseRing (source.X degree) ∧
      Module.Finite baseRing (source.X degree))
    (target_projective : ∀ degree, Module.Projective baseRing (target.X degree) ∧
      Module.Finite baseRing (target.X degree)) :
    (Q.obj (CochainComplex.mappingCone morphism)).IsPerfect := by
  have : (CochainComplex.mappingCone morphism).IsStrictlyGE (min (sourceLower - 1) targetLower) :=
    CochainComplex.isStrictlyGE_mappingCone morphism sourceLower targetLower _
  have : (CochainComplex.mappingCone morphism).IsStrictlyLE (max (sourceUpper - 1) targetUpper) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree above
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨source.isZero_of_isStrictlyLE sourceUpper _ (by omega),
      target.isZero_of_isStrictlyLE targetUpper _ (by omega)⟩
  refine isPerfect_Q_obj _ (min (sourceLower - 1) targetLower)
    (max (sourceUpper - 1) targetUpper) fun degree ↦ ?_
  let term_comparison := HomologicalComplex.homotopyCofiber.XIsoBiprod morphism degree
    (degree + 1) rfl ≪≫ ModuleCat.biprodIsoProd (source.X (degree + 1)) (target.X degree)
  have := (source_projective (degree + 1)).1
  have := (source_projective (degree + 1)).2
  have := (target_projective degree).1
  have := (target_projective degree).2
  exact ⟨Module.Projective.of_equiv term_comparison.toLinearEquiv.symm,
    Module.Finite.equiv term_comparison.toLinearEquiv.symm⟩

/-- In a distinguished triangle, perfectness of the outer terms implies perfectness of the middle. -/
lemma isPerfect_obj₂_of_distTriang
    (triangle : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} baseRing)))
    (distinguished : triangle ∈ distTriang _) (first_perfect : triangle.obj₁.IsPerfect)
    (last_perfect : triangle.obj₃.IsPerfect) : triangle.obj₂.IsPerfect := by
  obtain ⟨firstModel, firstLower, firstUpper, _, _, first_projective, ⟨first_comparison⟩⟩ := first_perfect
  obtain ⟨lastModel, lastLower, lastUpper, _, _, last_projective, ⟨last_comparison⟩⟩ := last_perfect
  have : ∀ degree, Projective (lastModel.X degree) := fun degree ↦ by
    have := (last_projective degree).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : lastModel.IsKProjective := CochainComplex.isKProjective_of_projective _ lastUpper
  have := firstModel.isStrictlyGE_shift firstLower 1 (firstLower - 1) (by omega)
  have := firstModel.isStrictlyLE_shift firstUpper 1 (firstUpper - 1) (by omega)
  obtain ⟨connecting, image_eq⟩ := exists_map_of_isKProjective
    (source := lastModel) (target := firstModel⟦(1 : ℤ)⟧)
    (last_comparison.inv ≫ triangle.mor₃ ≫ first_comparison.hom⟦(1 : ℤ)⟧' ≫
      ((Q.commShiftIso (1 : ℤ)).app firstModel).inv)
  have commutes : Q.map connecting ≫ ((Q.commShiftIso (1 : ℤ)).app firstModel).hom ≫
      first_comparison.inv⟦(1 : ℤ)⟧' = last_comparison.inv ≫ triangle.mor₃ := by
    rw [image_eq]
    simp [← Functor.map_comp]
  obtain ⟨triangle_comparison, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished connecting)
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ distinguished))
    (Arrow.isoMk last_comparison.symm (((Q.commShiftIso (1 : ℤ)).app firstModel) ≪≫
      (shiftFunctor _ 1).mapIso first_comparison.symm) commutes.symm)
  have cone_perfect := isPerfect_Q_obj_mappingCone connecting lastLower lastUpper
    (firstLower - 1) (firstUpper - 1) last_projective fun degree ↦ first_projective (degree + 1)
  exact ((cone_perfect.of_iso (Pretriangulated.Triangle.π₃.mapIso triangle_comparison)).shift (-1)).of_iso
    ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app _)

end DerivedCategory
