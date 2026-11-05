import Jacobian.Algebra.Homology.DerivedCategory.Ext.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Exact functors and sheaf cohomology

An exact additive functor compatible with the constant integer sheaf acts on
sheaf cohomology. This construction uses the existing Ext definition of cohomology.
-/

noncomputable section

universe sourceUniverse sourceHomUniverse targetUniverse targetHomUniverse
  coefficientUniverse extUniverse

open CategoryTheory Abelian Limits

namespace CategoryTheory.Sheaf

variable {sourceSite : Type sourceUniverse} [Category.{sourceHomUniverse} sourceSite]
  {targetSite : Type targetUniverse} [Category.{targetHomUniverse} targetSite]
  {sourceTopology : GrothendieckTopology sourceSite}
  {targetTopology : GrothendieckTopology targetSite}
  [HasSheafify sourceTopology AddCommGrpCat.{coefficientUniverse}]
  [HasSheafify targetTopology AddCommGrpCat.{coefficientUniverse}]
  [HasExt.{extUniverse} (Sheaf sourceTopology AddCommGrpCat.{coefficientUniverse})]
  [HasExt.{extUniverse} (Sheaf targetTopology AddCommGrpCat.{coefficientUniverse})]
  (comparison : Sheaf sourceTopology AddCommGrpCat.{coefficientUniverse} ⥤
    Sheaf targetTopology AddCommGrpCat.{coefficientUniverse})
  [comparison.Additive] [PreservesFiniteLimits comparison] [PreservesFiniteColimits comparison]
  (constantIso : (constantSheaf targetTopology AddCommGrpCat.{coefficientUniverse}).obj
      (AddCommGrpCat.of (ULift ℤ)) ≅
    comparison.obj ((constantSheaf sourceTopology AddCommGrpCat.{coefficientUniverse}).obj
      (AddCommGrpCat.of (ULift ℤ))))
  (moduleSheaf : Sheaf sourceTopology AddCommGrpCat.{coefficientUniverse}) (degree : ℕ)

/-- Apply an exact functor to an Ext class and identify its source with the
constant integer sheaf on the target site. -/
def H.mapFunctor : H moduleSheaf degree →+ H (comparison.obj moduleSheaf) degree :=
  (Ext.precompAddEquiv constantIso _ degree).toAddMonoidHom.comp
    (comparison.mapExtAddHom _ moduleSheaf degree)

lemma H.mapFunctor_apply (cohomologyClass : H moduleSheaf degree) :
    H.mapFunctor comparison constantIso moduleSheaf degree cohomologyClass =
      (Ext.mk₀ constantIso.hom).comp (cohomologyClass.mapExactFunctor comparison)
        (zero_add degree) :=
  rfl

/-- The exact-functor map is natural in the coefficient sheaf. -/
lemma H.mapFunctor_map {targetSheaf : Sheaf sourceTopology AddCommGrpCat.{coefficientUniverse}}
    (coefficientMap : moduleSheaf ⟶ targetSheaf)
    (cohomologyClass : H moduleSheaf degree) :
    H.mapFunctor comparison constantIso targetSheaf degree
        (H.map coefficientMap degree cohomologyClass) =
      H.map (comparison.map coefficientMap) degree
        (H.mapFunctor comparison constantIso moduleSheaf degree cohomologyClass) := by
  simp only [H.mapFunctor_apply, H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add degree) (add_zero degree) (by omega)).symm

/-- A fully faithful exact functor preserving injectives gives a bijection on
cohomology when it preserves the constant integer sheaf. -/
theorem H.mapFunctor_bijective [comparison.Full] [comparison.Faithful]
    [EnoughInjectives (Sheaf sourceTopology AddCommGrpCat.{coefficientUniverse})]
    [comparison.PreservesInjectiveObjects] :
    Function.Bijective (H.mapFunctor comparison constantIso moduleSheaf degree) :=
  (Ext.precompAddEquiv constantIso _ degree).bijective.comp
    (Functor.mapExt_bijective_of_preservesInjectiveObjects comparison _ moduleSheaf degree)

end CategoryTheory.Sheaf
