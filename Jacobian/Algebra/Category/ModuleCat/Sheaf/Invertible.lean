import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Locally free sheaves of rank one

Local generators indexed by a one-element type describe locally free sheaves
of rank one. The property is invariant under isomorphism, and local
trivializations provide such generators.

In this API, `IsInvertible` means locally free of rank one. For structure
sheaves of schemes this is the usual notion of an invertible module. On a
general ringed site, the converse from tensor invertibility to local rank one
need not hold; no such converse is asserted here.

-/

noncomputable section

universe ringUniverse morphismUniverse objectUniverse

open CategoryTheory Limits

variable {site : Type objectUniverse} [Category.{morphismUniverse} site]
  {topology : GrothendieckTopology site} {ringSheaf : Sheaf topology RingCat.{ringUniverse}}

namespace SheafOfModules

section

variable [HasWeakSheafify topology AddCommGrpCat.{ringUniverse}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- The free module sheaf on a one-element type is the unit module sheaf. -/
def freeUniqueIso (indices : Type ringUniverse) [Unique indices] :
    free (R := ringSheaf) indices ≅ unit ringSheaf :=
  coproductUniqueIso (fun _ : indices ↦ unit ringSheaf)

end

section

variable [∀ object, HasWeakSheafify (topology.over object) AddCommGrpCat.{ringUniverse}]
  [∀ object, (topology.over object).WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

namespace LocalGeneratorsData

/-- Locally free generators with exactly one generator on each member of the cover. -/
class IsInvertibleData {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (generators : moduleSheaf.LocalGeneratorsData) : Prop
    extends generators.IsLocallyFreeData where
  nonempty_unique (index : generators.I) : Nonempty (Unique (generators.generators index).I)

/-- Transport local generators along an isomorphism of module sheaves. -/
@[simps]
def ofIso {moduleSheaf targetSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (generators : moduleSheaf.LocalGeneratorsData) (isomorphism : moduleSheaf ≅ targetSheaf) :
    targetSheaf.LocalGeneratorsData where
  I := generators.I
  X := generators.X
  coversTop := generators.coversTop
  generators index := (generators.generators index).ofEpi
    (((overFunctor ringSheaf (generators.X index)).mapIso isomorphism).hom)

set_option backward.isDefEq.respectTransparency false in
instance isLocallyFreeData_ofIso {moduleSheaf targetSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (generators : moduleSheaf.LocalGeneratorsData) [generators.IsLocallyFreeData]
    (isomorphism : moduleSheaf ≅ targetSheaf) : (generators.ofIso isomorphism).IsLocallyFreeData where
  isIso index := by
    change IsIso ((generators.generators index).ofEpi _).π
    rw [GeneratingSections.ofEpi_π]
    infer_instance

instance isInvertibleData_ofIso {moduleSheaf targetSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (generators : moduleSheaf.LocalGeneratorsData) [generators.IsInvertibleData]
    (isomorphism : moduleSheaf ≅ targetSheaf) : (generators.ofIso isomorphism).IsInvertibleData where
  nonempty_unique index := IsInvertibleData.nonempty_unique (generators := generators) index

instance IsInvertibleData.shrink {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (generators : moduleSheaf.LocalGeneratorsData) [generators.IsInvertibleData] :
    generators.shrink.IsInvertibleData where
  nonempty_unique index :=
    IsInvertibleData.nonempty_unique (generators := generators) index.2.choose

end LocalGeneratorsData

/-- A module sheaf is invertible if it is locally free of rank one. -/
class IsInvertible (moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf) : Prop where
  exists_isInvertibleData :
    ∃ generators : LocalGeneratorsData.{objectUniverse} moduleSheaf, generators.IsInvertibleData

/-- Rank-one local generators establish invertibility, regardless of the size of their cover. -/
theorem LocalGeneratorsData.isInvertible {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (generators : moduleSheaf.LocalGeneratorsData) [generators.IsInvertibleData] :
    moduleSheaf.IsInvertible :=
  ⟨generators.shrink, inferInstance⟩

instance (priority := 100) IsInvertible.isLocallyFree
    (moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf) [property : moduleSheaf.IsInvertible] :
    moduleSheaf.IsLocallyFree :=
  have := property.exists_isInvertibleData.choose_spec
  ⟨property.exists_isInvertibleData.choose, inferInstance⟩

/-- Invertibility is invariant under isomorphism of module sheaves. -/
theorem IsInvertible.of_iso {moduleSheaf targetSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (isomorphism : moduleSheaf ≅ targetSheaf) [property : moduleSheaf.IsInvertible] :
    targetSheaf.IsInvertible := by
  obtain ⟨generators, generatorsProperty⟩ := property.exists_isInvertibleData
  exact (generators.ofIso isomorphism).isInvertible

end

section

variable [HasWeakSheafify topology AddCommGrpCat.{ringUniverse}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]
  [∀ object, HasSheafify (topology.over object) AddCommGrpCat.{ringUniverse}]
  [HasBinaryProducts site]
  [∀ object, (topology.over object).WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

instance (indices : Type ringUniverse) [Unique indices] :
    (free.generatingSections (R := ringSheaf) indices).localGeneratorsData.IsInvertibleData where
  nonempty_unique _ := ⟨inferInstanceAs (Unique indices)⟩

instance (indices : Type ringUniverse) [Unique indices] :
    (free (R := ringSheaf) indices).IsInvertible :=
  (free.generatingSections indices).localGeneratorsData.isInvertible

instance : (unit ringSheaf).IsInvertible :=
  IsInvertible.of_iso (freeUniqueIso (ringSheaf := ringSheaf) PUnit.{ringUniverse + 1})

end

section

variable [HasWeakSheafify topology AddCommGrpCat.{ringUniverse}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- A trivialization supplies a single generating section. -/
def generatingSectionsOfUnitIso {M : SheafOfModules.{ringUniverse} ringSheaf}
    (e : M ≅ unit ringSheaf) : M.GeneratingSections :=
  (free.generatingSections PUnit.{ringUniverse + 1}).ofEpi (freeUniqueIso _ ≪≫ e.symm).hom

instance {M : SheafOfModules.{ringUniverse} ringSheaf} (e : M ≅ unit ringSheaf) :
    Unique (generatingSectionsOfUnitIso e).I :=
  inferInstanceAs (Unique PUnit.{ringUniverse + 1})

set_option backward.isDefEq.respectTransparency false in
instance {M : SheafOfModules.{ringUniverse} ringSheaf} (e : M ≅ unit ringSheaf) :
    IsIso (generatingSectionsOfUnitIso e).π := by
  rw [generatingSectionsOfUnitIso, GeneratingSections.ofEpi_π]
  infer_instance

end

section

variable [∀ object, HasWeakSheafify (topology.over object) AddCommGrpCat.{ringUniverse}]
  [∀ object, (topology.over object).WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- Local trivializations determine rank-one local generators. -/
@[simps]
def localGeneratorsDataOfUnitIso {M : SheafOfModules.{ringUniverse} ringSheaf}
    {I : Type objectUniverse} (X : I → site) (hX : topology.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (ringSheaf.over (X i)))) :
    M.LocalGeneratorsData where
  I := I
  X := X
  coversTop := hX
  generators i := generatingSectionsOfUnitIso (h i).some

set_option backward.isDefEq.respectTransparency false in
instance isInvertibleData_localGeneratorsDataOfUnitIso
    {M : SheafOfModules.{ringUniverse} ringSheaf} {I : Type objectUniverse}
    (X : I → site) (hX : topology.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (ringSheaf.over (X i)))) :
    (localGeneratorsDataOfUnitIso X hX h).IsInvertibleData where
  isIso i := by rw [localGeneratorsDataOfUnitIso_generators]; infer_instance
  nonempty_unique i := by
    rw [localGeneratorsDataOfUnitIso_generators]
    exact ⟨inferInstance⟩

/-- A module sheaf trivial on a covering family is invertible. -/
theorem isInvertible_of_forall_over_unit {M : SheafOfModules.{ringUniverse} ringSheaf}
    {I : Type objectUniverse} (X : I → site) (hX : topology.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (ringSheaf.over (X i)))) : M.IsInvertible :=
  (localGeneratorsDataOfUnitIso X hX h).isInvertible

/-- Invertibility is equivalent to local triviality on a covering family. -/
theorem isInvertible_iff_exists_over_unit {M : SheafOfModules.{ringUniverse} ringSheaf} :
    M.IsInvertible ↔ ∃ (I : Type objectUniverse) (X : I → site), topology.CoversTop X ∧
      ∀ i, Nonempty (M.over (X i) ≅ unit (ringSheaf.over (X i))) := by
  constructor
  · rintro ⟨q, hq⟩
    have := hq
    refine ⟨q.I, q.X, q.coversTop, fun i ↦ ?_⟩
    obtain ⟨hu⟩ := LocalGeneratorsData.IsInvertibleData.nonempty_unique (generators := q) i
    have := hu
    exact ⟨(asIso (q.generators i).π).symm ≪≫ freeUniqueIso _⟩
  · rintro ⟨I, X, hX, h⟩
    exact isInvertible_of_forall_over_unit X hX h

end

end SheafOfModules
