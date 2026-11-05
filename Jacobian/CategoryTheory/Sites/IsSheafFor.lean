import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Recovery of sections from commuting squares

For a separated presheaf, a section pulled back along a morphism is determined by
its restrictions to a covering family. Commuting squares let these restrictions
be computed from sections on a covering family of the target.
-/

universe objectUniverse morphismUniverse sectionUniverse indexUniverse

open Opposite

namespace CategoryTheory.Presieve.IsSeparatedFor

/-- A pulled-back section agrees with a given section if they agree on a family
for which the presheaf is separated. The restrictions of the target section may
be computed on the other sides of commuting squares. -/
theorem map_eq_of_commutative_squares
    {Base : Type objectUniverse} [Category.{morphismUniverse} Base]
    (presheaf : Baseᵒᵖ ⥤ Type sectionUniverse)
    {source target : Base} {ChartIndex : Type indexUniverse}
    {sourceCharts targetCharts : ChartIndex → Base}
    (sourceMaps : ∀ chartIndex, sourceCharts chartIndex ⟶ source)
    (targetMaps : ∀ chartIndex, targetCharts chartIndex ⟶ target)
    (projection : source ⟶ target)
    (chartProjections : ∀ chartIndex, sourceCharts chartIndex ⟶ targetCharts chartIndex)
    (squares : ∀ chartIndex, chartProjections chartIndex ≫ targetMaps chartIndex =
      sourceMaps chartIndex ≫ projection)
    (separated : IsSeparatedFor presheaf (ofArrows sourceCharts sourceMaps))
    (targetSection : presheaf.obj (op target))
    (sourceSection : presheaf.obj (op source))
    (localSections : ∀ chartIndex, presheaf.obj (op (targetCharts chartIndex)))
    (restrictions : ∀ chartIndex,
      presheaf.map (targetMaps chartIndex).op targetSection = localSections chartIndex)
    (recovery : ∀ chartIndex,
      presheaf.map (chartProjections chartIndex).op (localSections chartIndex) =
        presheaf.map (sourceMaps chartIndex).op sourceSection) :
    presheaf.map projection.op targetSection = sourceSection := by
  apply separated.ext
  intro testObject testMap membership
  rcases membership with ⟨chartIndex⟩
  calc
    _ = presheaf.map (sourceMaps chartIndex ≫ projection).op targetSection := by
      simp only [op_comp, Functor.map_comp_apply]
    _ = presheaf.map (chartProjections chartIndex ≫ targetMaps chartIndex).op
        targetSection := by rw [squares chartIndex]
    _ = presheaf.map (chartProjections chartIndex).op
        (presheaf.map (targetMaps chartIndex).op targetSection) := by
      simp only [op_comp, Functor.map_comp_apply]
    _ = presheaf.map (chartProjections chartIndex).op (localSections chartIndex) :=
      congrArg (presheaf.map (chartProjections chartIndex).op) (restrictions chartIndex)
    _ = _ := recovery chartIndex

end CategoryTheory.Presieve.IsSeparatedFor
