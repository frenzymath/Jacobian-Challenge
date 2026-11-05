import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Realizing derived isomorphisms by quasi-isomorphisms

An isomorphism from the image of a K-projective complex lifts to a
quasi-isomorphism of complexes. In particular, this applies to bounded-above
complexes of projective objects.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

namespace DerivedCategory

variable {category : Type*} [Category* category] [Abelian category] [HasDerivedCategory category]

/-- A derived isomorphism from a K-projective complex lifts to a quasi-isomorphism. -/
lemma exists_quasiIso_of_isKProjective {source target : CochainComplex category ℤ}
    [source.IsKProjective] (comparison : Q.obj source ≅ Q.obj target) :
    ∃ morphism : source ⟶ target, QuasiIso morphism := by
  obtain ⟨homotopy_map, image_eq⟩ := (CochainComplex.IsKProjective.Qh_map_bijective source
    ((HomotopyCategory.quotient _ _).obj target)).surjective
    ((quotientCompQhIso category).hom.app source ≫ comparison.hom ≫
      (quotientCompQhIso category).inv.app target)
  obtain ⟨morphism, rfl⟩ :=
    (HomotopyCategory.quotient category (ComplexShape.up ℤ)).map_surjective homotopy_map
  refine ⟨morphism, (isIso_Q_map_iff_quasiIso (C := category) morphism).1 ?_⟩
  have naturality := quotientCompQhIso_hom_naturality (C := category) morphism
  rw [image_eq] at naturality
  have image_eq' : Q.map morphism = comparison.hom := by
    rw [← cancel_epi ((quotientCompQhIso category).hom.app source), ← naturality]
    simp
  rw [image_eq']
  infer_instance

/-- A derived isomorphism from a bounded-above projective complex lifts to a quasi-isomorphism. -/
theorem exists_quasiIso_of_isStrictlyLE_of_projective {source target : CochainComplex category ℤ}
    (upperBound : ℤ) [source.IsStrictlyLE upperBound] [∀ degree, Projective (source.X degree)]
    (comparison : Q.obj source ≅ Q.obj target) : ∃ morphism : source ⟶ target, QuasiIso morphism := by
  have := CochainComplex.isKProjective_of_projective source upperBound
  exact exists_quasiIso_of_isKProjective comparison

end DerivedCategory
