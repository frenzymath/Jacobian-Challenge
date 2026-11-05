import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local bijectivity on a covering family

A morphism of concrete presheaves is locally injective or locally surjective
if the corresponding property holds over every object mapping to a member of
a covering family.
-/

open Opposite

namespace CategoryTheory.Presheaf

universe concreteUniverse morphismUniverse objectUniverse
  valueMorphismUniverse valueObjectUniverse

variable {site : Type objectUniverse} [Category.{morphismUniverse} site]
  {topology : GrothendieckTopology site}
  {values : Type valueObjectUniverse} [Category.{valueMorphismUniverse} values]
  {morphisms : values → values → Type*} {underlying : values → Type concreteUniverse}
  [∀ source target, FunLike (morphisms source target) (underlying source) (underlying target)]
  [ConcreteCategory.{concreteUniverse} values morphisms]

/-- Injectivity over a covering family implies local injectivity. -/
lemma isLocallyInjective_of_coversTop {indices : Type*} {cover : indices → site}
    (coversTop : topology.CoversTop cover) {source target : siteᵒᵖ ⥤ values}
    (morphism : source ⟶ target)
    (injective : ∀ (object : site) (index : indices),
      (object ⟶ cover index) → Function.Injective (morphism.app (op object))) :
    IsLocallyInjective topology morphism where
  equalizerSieve_mem {object} firstSection secondSection equality := by
    refine topology.superset_covering ?_ (coversTop object.unop)
    rintro smallerObject restriction ⟨index, ⟨factor⟩⟩
    refine injective smallerObject index factor ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, equality]

/-- Surjectivity over a covering family implies local surjectivity. -/
lemma isLocallySurjective_of_coversTop {indices : Type*} {cover : indices → site}
    (coversTop : topology.CoversTop cover) {source target : siteᵒᵖ ⥤ values}
    (morphism : source ⟶ target)
    (surjective : ∀ (object : site) (index : indices),
      (object ⟶ cover index) → Function.Surjective (morphism.app (op object))) :
    IsLocallySurjective topology morphism where
  imageSieve_mem {object} element := by
    refine topology.superset_covering ?_ (coversTop object)
    rintro smallerObject restriction ⟨index, ⟨factor⟩⟩
    exact surjective smallerObject index factor _

end CategoryTheory.Presheaf
