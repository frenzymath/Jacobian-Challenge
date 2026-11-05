import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Sections of separated étale morphisms

A section of a separated étale morphism is both open and closed. If the source
of the morphism is preconnected and the base is nonempty, the section is an
isomorphism.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A section of a separated étale morphism with preconnected source is an
isomorphism when the base is nonempty. -/
theorem isIso_section_of_etale_connected {source base : Scheme.{u}}
    (morphism : source ⟶ base) [Etale morphism] [IsSeparated morphism]
    [PreconnectedSpace source] [Nonempty base]
    (sectionMap : base ⟶ source) (sectionCondition : sectionMap ≫ morphism = 𝟙 base) :
    IsIso sectionMap := by
  letI : MorphismProperty.HasOfPostcompProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ map etale ↦ by
        letI := etale
        exact inferInstanceAs (IsOpenImmersion (Limits.pullback.diagonal map)))
  have openComposite : IsOpenImmersion (sectionMap ≫ morphism) := by
    rw [sectionCondition]
    infer_instance
  haveI : IsOpenImmersion sectionMap := MorphismProperty.of_postcomp
    (W := @IsOpenImmersion) (W' := @Etale) sectionMap morphism inferInstance openComposite
  haveI : IsClosedImmersion (sectionMap ≫ morphism) := by
    rw [sectionCondition]
    infer_instance
  haveI : IsClosedImmersion sectionMap := IsClosedImmersion.of_comp sectionMap morphism
  have sectionRange : Set.range sectionMap = Set.univ :=
    (show IsClopen (Set.range sectionMap) from
      ⟨sectionMap.isClosedEmbedding.isClosed_range,
        sectionMap.isOpenEmbedding.isOpen_range⟩).eq_univ (Set.range_nonempty sectionMap)
  haveI : Surjective sectionMap := ⟨Set.range_eq_univ.mp sectionRange⟩
  exact (isIso_iff_isOpenImmersion_and_surjective sectionMap).mpr
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
