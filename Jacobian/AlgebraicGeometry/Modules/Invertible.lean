import Jacobian.Algebra.Category.ModuleCat.Sheaf.Invertible
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Invertible module sheaves on schemes

An invertible module sheaf is locally isomorphic to the structure sheaf.
Restriction to an open subset agrees with pullback along its open immersion,
and pullback along an arbitrary scheme morphism preserves invertibility.

## References

* [The Stacks Project, Section 17.25: Invertible modules](https://stacks.math.columbia.edu/tag/01CR)
-/

noncomputable section

universe schemeUniverse

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {source target : Scheme.{schemeUniverse}}

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of the structure sheaf is the structure sheaf. -/
def pullbackObjUnitIso (morphism : source ⟶ target) :
    (pullback morphism).obj (SheafOfModules.unit target.ringCatSheaf) ≅
      SheafOfModules.unit source.ringCatSheaf := by
  letI : (Opens.map morphism.base).Final := ⟨fun _ ↦ IsCofiltered.isConnected _⟩
  exact asIso (C := SheafOfModules.{schemeUniverse} source.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit morphism.toRingCatSheafHom)

/-- The unit module sheaf restricts to the unit module sheaf on the over-site. -/
def overFunctorObjUnitIso (openSubset : target.Opens) :
    (SheafOfModules.overFunctor target.ringCatSheaf openSubset).obj
        (SheafOfModules.unit target.ringCatSheaf) ≅
      SheafOfModules.unit (target.ringCatSheaf.over openSubset) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between the over-site and an open subscheme preserves the unit. -/
def overEquivObjUnitIso (openSubset : target.Opens) :
    (overEquiv openSubset).functor.obj
        (SheafOfModules.unit (target.ringCatSheaf.over openSubset)) ≅
      SheafOfModules.unit openSubset.toScheme.ringCatSheaf :=
  (overEquiv openSubset).functor.mapIso (overFunctorObjUnitIso openSubset).symm ≪≫
    (overFunctorEquiv openSubset).app _ ≪≫ restrictUnitIso openSubset.ι

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the over-site corresponds to pullback to the open subscheme. -/
def overEquivObjOverIso (moduleSheaf : target.Modules) (openSubset : target.Opens) :
    (overEquiv openSubset).functor.obj (moduleSheaf.over openSubset) ≅
      (pullback openSubset.ι).obj moduleSheaf :=
  (overFunctorEquiv openSubset).app moduleSheaf ≪≫
    (restrictFunctorIsoPullback openSubset.ι).app moduleSheaf

/-- A trivialization on the over-site gives a trivialization on the open subscheme. -/
def pullbackIotaUnitIsoOfOverIso {moduleSheaf : target.Modules} {openSubset : target.Opens}
    (trivialization : moduleSheaf.over openSubset ≅
      SheafOfModules.unit (target.ringCatSheaf.over openSubset)) :
    (pullback openSubset.ι).obj moduleSheaf ≅
      SheafOfModules.unit openSubset.toScheme.ringCatSheaf :=
  (overEquivObjOverIso moduleSheaf openSubset).symm ≪≫
    (overEquiv openSubset).functor.mapIso trivialization ≪≫ overEquivObjUnitIso openSubset

/-- A trivialization on an open subscheme gives a trivialization on the over-site. -/
def overIsoUnitOfPullbackIotaIso {moduleSheaf : target.Modules} {openSubset : target.Opens}
    (trivialization : (pullback openSubset.ι).obj moduleSheaf ≅
      SheafOfModules.unit openSubset.toScheme.ringCatSheaf) :
    moduleSheaf.over openSubset ≅ SheafOfModules.unit (target.ringCatSheaf.over openSubset) :=
  (overEquiv openSubset).functor.preimageIso
    (overEquivObjOverIso moduleSheaf openSubset ≪≫ trivialization ≪≫
      (overEquivObjUnitIso openSubset).symm)

/-- Pullback carries a trivialization on an open subset to its inverse image. -/
def pullbackOverUnitIso (morphism : source ⟶ target) (moduleSheaf : target.Modules)
    (openSubset : target.Opens)
    (trivialization : moduleSheaf.over openSubset ≅
      SheafOfModules.unit (target.ringCatSheaf.over openSubset)) :
    ((pullback morphism).obj moduleSheaf).over (morphism ⁻¹ᵁ openSubset) ≅
      SheafOfModules.unit (source.ringCatSheaf.over (morphism ⁻¹ᵁ openSubset)) :=
  overIsoUnitOfPullbackIotaIso
    ((pullbackComp (morphism ⁻¹ᵁ openSubset).ι morphism).app moduleSheaf ≪≫
      (pullbackCongr (morphismRestrict_ι morphism openSubset).symm).app moduleSheaf ≪≫
      ((pullbackComp (morphism ∣_ openSubset) openSubset.ι).symm).app moduleSheaf ≪≫
      (pullback (morphism ∣_ openSubset)).mapIso (pullbackIotaUnitIsoOfOverIso trivialization) ≪≫
      pullbackObjUnitIso (morphism ∣_ openSubset))

set_option backward.isDefEq.respectTransparency false in
/-- An invertible module sheaf has a rank-one trivialization near every point. -/
theorem _root_.SheafOfModules.IsInvertible.exists_isoUnit
    {moduleSheaf : target.Modules} (invertible : moduleSheaf.IsInvertible) (point : target) :
    ∃ openSubset : target.Opens, point ∈ openSubset ∧
      Nonempty ((pullback openSubset.ι).obj moduleSheaf ≅
        SheafOfModules.unit openSubset.toScheme.ringCatSheaf) := by
  obtain ⟨indices, cover, coversTop, trivializations⟩ :=
    (SheafOfModules.isInvertible_iff_exists_over_unit.{schemeUniverse, schemeUniverse,
      schemeUniverse}).mp invertible
  have openCover : IsOpenCover cover := (Opens.coversTop_iff _ _).mp coversTop
  obtain ⟨index, membership⟩ := openCover.exists_mem point
  exact ⟨cover index, membership,
    ⟨pullbackIotaUnitIsoOfOverIso (trivializations index).some⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise rank-one trivializations characterize invertible module sheaves. -/
theorem isInvertible_iff_forall_exists_pullback_unit (moduleSheaf : target.Modules) :
    moduleSheaf.IsInvertible ↔ ∀ point : target, ∃ openSubset : target.Opens,
      point ∈ openSubset ∧ Nonempty ((pullback openSubset.ι).obj moduleSheaf ≅
        SheafOfModules.unit openSubset.toScheme.ringCatSheaf) := by
  refine ⟨fun invertible ↦ invertible.exists_isoUnit, fun trivializations ↦ ?_⟩
  choose cover membership trivialization using trivializations
  refine SheafOfModules.isInvertible_of_forall_over_unit.{schemeUniverse, schemeUniverse,
    schemeUniverse} (M := moduleSheaf) cover ?_ ?_
  · rw [Opens.coversTop_iff]
    exact IsOpenCover.mk (eq_top_iff.mpr fun point _ ↦
      Opens.mem_iSup.mpr ⟨point, membership point⟩)
  · intro point
    exact ⟨overIsoUnitOfPullbackIotaIso (trivialization point).some⟩

set_option backward.isDefEq.respectTransparency false in
/-- The structure sheaf is invertible on every scheme. -/
instance isInvertible_unit (scheme : Scheme.{schemeUniverse}) :
    (SheafOfModules.unit scheme.ringCatSheaf).IsInvertible :=
  (isInvertible_iff_forall_exists_pullback_unit _).mpr fun _ ↦
    ⟨⊤, trivial, ⟨pullbackObjUnitIso _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along a scheme morphism preserves invertible module sheaves. -/
theorem _root_.SheafOfModules.IsInvertible.pullback {morphism : source ⟶ target}
    {moduleSheaf : target.Modules} (invertible : moduleSheaf.IsInvertible) :
    ((pullback morphism).obj moduleSheaf).IsInvertible := by
  obtain ⟨indices, cover, coversTop, trivializations⟩ :=
    (SheafOfModules.isInvertible_iff_exists_over_unit.{schemeUniverse, schemeUniverse,
      schemeUniverse}).mp invertible
  refine SheafOfModules.isInvertible_of_forall_over_unit.{schemeUniverse, schemeUniverse,
    schemeUniverse} (fun index : indices ↦ morphism ⁻¹ᵁ cover index) ?_ ?_
  · have openCover : IsOpenCover cover := (Opens.coversTop_iff _ _).mp coversTop
    rw [Opens.coversTop_iff]
    refine IsOpenCover.mk (eq_top_iff.mpr fun point _ ↦ ?_)
    obtain ⟨index, membership⟩ := openCover.exists_mem (morphism.base point)
    exact Opens.mem_iSup.mpr ⟨index, membership⟩
  · intro index
    exact ⟨pullbackOverUnitIso morphism moduleSheaf (cover index) (trivializations index).some⟩

/-- The pullback of an invertible module sheaf is invertible. -/
instance isInvertible_pullback (morphism : source ⟶ target) (moduleSheaf : target.Modules)
    [invertible : moduleSheaf.IsInvertible] : ((pullback morphism).obj moduleSheaf).IsInvertible :=
  invertible.pullback

end AlgebraicGeometry.Scheme.Modules
