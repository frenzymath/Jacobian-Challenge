import Jacobian.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Presentations and quasi-coherence of module sheaves

Free module sheaves have presentations with no relations. This gives a presentation
of the unit module sheaf and proves that it is quasi-coherent. Colimit-preserving
functors carrying the unit to the unit preserve finite presentations.

The native notions of invertibility and finite local freeness imply
quasi-coherence through their locally free generators. No alternative notion of
invertibility is needed.
-/

noncomputable section

universe ringUniverse morphismUniverse objectUniverse
  targetMorphismUniverse targetObjectUniverse

open CategoryTheory Limits

namespace SheafOfModules

variable {site : Type objectUniverse} [Category.{morphismUniverse} site]
  {topology : GrothendieckTopology site}
  {ringSheaf : Sheaf topology RingCat.{ringUniverse}}

section Presentations

variable [HasSheafify topology AddCommGrpCat.{ringUniverse}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- The free module sheaf has a presentation with its given generators and no relations. -/
def presentationFree (indices : Type ringUniverse) :
    (free (R := ringSheaf) indices).Presentation :=
  presentationOfIsCokernelFree (ι := PEmpty.{ringUniverse + 1})
    (0 : free _ ⟶ free (R := ringSheaf) indices) (𝟙 _) (by simp)
    (CokernelCofork.IsColimit.ofId _ rfl)

instance presentationFree_isFinite (indices : Type ringUniverse) [Finite indices] :
    (presentationFree (ringSheaf := ringSheaf) indices).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite indices)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite PEmpty.{ringUniverse + 1})⟩

/-- A presentation of the unit module sheaf on one generator and no relations. -/
def presentationUnit : (unit ringSheaf).Presentation :=
  (presentationFree (ringSheaf := ringSheaf) PUnit.{ringUniverse + 1}).ofIsIso
    (freeUniqueIso PUnit.{ringUniverse + 1}).hom

instance presentationUnit_isFinite : (presentationUnit (ringSheaf := ringSheaf)).IsFinite := by
  dsimp only [presentationUnit]
  infer_instance

variable {targetSite : Type targetObjectUniverse} [Category.{targetMorphismUniverse} targetSite]
  {targetTopology : GrothendieckTopology targetSite}
  {targetRingSheaf : Sheaf targetTopology RingCat.{ringUniverse}}
  [HasSheafify targetTopology AddCommGrpCat.{ringUniverse}]
  [targetTopology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

set_option backward.isDefEq.respectTransparency false in
/-- A colimit-preserving functor carrying the unit to the unit preserves finite presentations. -/
instance Presentation.isFinite_map {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (presentation : moduleSheaf.Presentation) [presentation.IsFinite]
    (functor : SheafOfModules.{ringUniverse} ringSheaf ⥤
      SheafOfModules.{ringUniverse} targetRingSheaf)
    [PreservesColimitsOfSize.{ringUniverse, ringUniverse} functor]
    (unitIso : unit targetRingSheaf ≅ functor.obj (unit ringSheaf)) :
    (presentation.map functor unitIso).IsFinite where
  isFiniteType_generators := ⟨by rw [Presentation.map_generators_I]; infer_instance⟩
  isFiniteType_relations := ⟨by rw [Presentation.map_relations_I]; infer_instance⟩

end Presentations

section Quasicoherence

variable [∀ object, HasSheafify (topology.over object) AddCommGrpCat.{ringUniverse}]
  [∀ object, (topology.over object).WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- An invertible module sheaf is quasi-coherent, since it is locally free of rank one. -/
theorem IsInvertible.isQuasicoherent {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (invertible : moduleSheaf.IsInvertible) : moduleSheaf.IsQuasicoherent := by
  letI : moduleSheaf.IsInvertible := invertible
  infer_instance

/-- Finite local freeness of a specified rank implies quasi-coherence. -/
theorem IsFiniteLocallyFreeOfRank.isQuasicoherent
    (moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf) (rank : ℕ)
    [moduleSheaf.IsFiniteLocallyFreeOfRank rank] : moduleSheaf.IsQuasicoherent := by
  letI := IsFiniteLocallyFreeOfRank.isLocallyFree moduleSheaf rank
  infer_instance

variable [HasBinaryProducts site] [HasSheafify topology AddCommGrpCat.{ringUniverse}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- The unit module sheaf is quasi-coherent. -/
instance isQuasicoherent_unit : (unit ringSheaf).IsQuasicoherent :=
  (presentationUnit (ringSheaf := ringSheaf)).isQuasicoherent

end Quasicoherence

end SheafOfModules
