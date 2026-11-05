import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Pullback of constant sheaves

The pullback along a continuous functor of sites preserving a terminal object
commutes with the constant sheaf functor.
-/

noncomputable section

universe categoryUniverse morphismUniverse

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {sourceSite targetSite : Type*} [Category* sourceSite] [Category* targetSite]
  (siteFunctor : sourceSite ⥤ targetSite)
  (coefficients : Type categoryUniverse) [Category.{morphismUniverse} coefficients]
  (sourceTopology : GrothendieckTopology sourceSite)
  (targetTopology : GrothendieckTopology targetSite)
  [siteFunctor.IsContinuous sourceTopology targetTopology]

/-- Evaluation of the direct image of a sheaf is evaluation at the image object. -/
def Functor.sheafPushforwardContinuousCompSheafSectionsObjIso
    (object : sourceSiteᵒᵖ) :
    siteFunctor.sheafPushforwardContinuous coefficients sourceTopology targetTopology ⋙
        (sheafSections sourceTopology coefficients).obj object ≅
      (sheafSections targetTopology coefficients).obj (siteFunctor.op.obj object) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro sourceSheaf targetSheaf coefficientMap
    change coefficientMap.hom.app (siteFunctor.op.obj object) ≫ 𝟙 _ =
      𝟙 _ ≫ coefficientMap.hom.app (siteFunctor.op.obj object)
    simp only [Category.comp_id, Category.id_comp])

variable [HasWeakSheafify sourceTopology coefficients]
  [HasWeakSheafify targetTopology coefficients]
  [(siteFunctor.sheafPushforwardContinuous coefficients sourceTopology targetTopology).IsRightAdjoint]

/-- Pullback commutes with constant sheaves if the functor of sites preserves
a terminal object. -/
def Functor.constantSheafsheafPullbackIso {terminalObject : sourceSite}
    (sourceTerminal : IsTerminal terminalObject)
    (targetTerminal : IsTerminal (siteFunctor.obj terminalObject)) :
    constantSheaf sourceTopology coefficients ⋙
        siteFunctor.sheafPullback coefficients sourceTopology targetTopology ≅
      constantSheaf targetTopology coefficients :=
  (((constantSheafAdj sourceTopology coefficients sourceTerminal).comp
    (siteFunctor.sheafAdjunctionContinuous coefficients sourceTopology targetTopology)).ofNatIsoRight
      (siteFunctor.sheafPushforwardContinuousCompSheafSectionsObjIso coefficients
        sourceTopology targetTopology (op terminalObject))).leftAdjointUniq
    (constantSheafAdj targetTopology coefficients targetTerminal)

end CategoryTheory
