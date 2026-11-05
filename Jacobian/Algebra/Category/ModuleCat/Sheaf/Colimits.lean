import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Colimits of underlying abelian sheaves

Forgetting the module structure commutes with sheafification and hence with
colimits. In particular the underlying abelian-sheaf functor is exact.
-/

universe w w' v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

instance additive_toSheaf : (toSheaf.{v} R).Additive where
  map_add := by intros; ext U x; rfl

instance preservesZeroMorphisms_toSheaf : (toSheaf.{v} R).PreservesZeroMorphisms where
  map_zero := by intros; ext U x; rfl

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The functor `SheafOfModules.toSheaf R` to sheaves of abelian groups preserves colimits: a
diagram of sheaves of modules is the sheafification of its underlying diagram of presheaves of
modules, and sheafification followed by `toSheaf` is `toPresheaf` followed by the
sheafification of presheaves of abelian groups, which both preserve colimits. -/
instance preservesColimitsOfShape_toSheaf (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (toSheaf.{v} R) where
  preservesColimit {F} := by
    let L := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
    let G := F ⋙ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj))
    let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
    have : PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{v}) :=
      (sheafificationAdjunction J AddCommGrpCat.{v}).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimit G (L ⋙ toSheaf.{v} R) :=
      preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
    let hc := colimit.isColimit G
    have : PreservesColimit (G ⋙ L) (toSheaf.{v} R) :=
      preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
        (isColimitOfPreserves (L ⋙ toSheaf.{v} R) hc)
    exact preservesColimit_of_iso_diagram (toSheaf.{v} R) e

/-- `SheafOfModules.toSheaf R` preserves finite colimits. -/
instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) where
  preservesFiniteColimits _ := inferInstance

end SheafOfModules
