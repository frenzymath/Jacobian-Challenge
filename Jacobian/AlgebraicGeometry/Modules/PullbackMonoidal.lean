import Jacobian.AlgebraicGeometry.Modules.Invertible
import Jacobian.AlgebraicGeometry.Modules.Tensor
import Jacobian.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Pullback preserves tensor products

Pullback of module sheaves along a scheme morphism is a monoidal functor.
The monoidal structure is induced from pullback of module presheaves through
sheafification. In particular, pullback commutes with tensor product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory MonoidalCategory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {source target : Scheme.{schemeUniverse}}

/-- The ring-presheaf morphism underlying a scheme morphism, with commutative coefficients. -/
def Hom.toRingCatPresheafHom (morphism : source ⟶ target) :
    target.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{schemeUniverse} ⟶
      ((Opens.map morphism.base).op ⋙ source.sheaf.obj) ⋙
        forget₂ CommRingCat RingCat.{schemeUniverse} :=
  Functor.whiskerRight morphism.c (forget₂ CommRingCat RingCat)

namespace Modules

variable (morphism : source ⟶ target)

/-- Inverse image of opens preserves binary products, which are intersections. -/
instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map morphism.base) where
  preservesLimit {diagram} := ⟨fun {cone} limiting ↦ ⟨
    { lift := fun testCone ↦ homOfLE (by
        have intersection : diagram.obj ⟨.left⟩ ⊓ diagram.obj ⟨.right⟩ ≤ cone.pt :=
          leOfHom (limiting.lift
            { pt := diagram.obj ⟨.left⟩ ⊓ diagram.obj ⟨.right⟩
              π := Discrete.natTrans (fun index ↦ match index with
                | ⟨.left⟩ => homOfLE inf_le_left
                | ⟨.right⟩ => homOfLE inf_le_right) })
        have leftBound : testCone.pt ≤
            (Opens.map morphism.base).obj (diagram.obj ⟨.left⟩) :=
          leOfHom (testCone.π.app ⟨.left⟩)
        have rightBound : testCone.pt ≤
            (Opens.map morphism.base).obj (diagram.obj ⟨.right⟩) :=
          leOfHom (testCone.π.app ⟨.right⟩)
        exact (le_inf leftBound rightBound).trans
          (leOfHom ((Opens.map morphism.base).map (homOfLE intersection))))
      fac := fun _ _ ↦ Subsingleton.elim _ _
      uniq := fun _ _ _ ↦ Subsingleton.elim _ _ }⟩⟩

/-- Inverse image of opens preserves the terminal object, the whole space. -/
instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map morphism.base) where
  preservesLimit {diagram} := ⟨fun {cone} limiting ↦ ⟨
    { lift := fun _ ↦ homOfLE (by
        have topBound : (⊤ : target.Opens) ≤ cone.pt := leOfHom (limiting.lift
          { pt := ⊤, π := Discrete.natTrans (fun index ↦ index.as.elim) })
        exact le_top.trans (leOfHom ((Opens.map morphism.base).map (homOfLE topBound))))
      fac := fun _ _ ↦ Subsingleton.elim _ _
      uniq := fun _ _ _ ↦ Subsingleton.elim _ _ }⟩⟩

/-- Pullback of module presheaves followed by sheafification is monoidal. -/
@[instance_reducible]
def presheafPullbackCompSheafificationMonoidal :
    (_root_.PresheafOfModules.pullbackOfCommRingCat (F := Opens.map morphism.base)
      (R := source.sheaf.obj) (S := target.sheaf.obj) morphism.toRingCatPresheafHom ⋙
      sheafification source).Monoidal :=
  @Functor.Monoidal.instComp _ _ _ _ _ _ _ _ _
    (_root_.PresheafOfModules.pullbackOfCommRingCat (F := Opens.map morphism.base)
      (R := source.sheaf.obj) (S := target.sheaf.obj) morphism.toRingCatPresheafHom)
    (sheafification source) inferInstance (sheafificationMonoidal (scheme := source))

attribute [local instance] presheafPullbackCompSheafificationMonoidal

variable (source) in
/-- Sheafification of module presheaves is localization at locally bijective morphisms. -/
instance sheafificationIsLocalization : (sheafification source).IsLocalization
    ((Opens.grothendieckTopology source).W.inverseImage
      (_root_.PresheafOfModules.toPresheaf source.ringCatSheaf.obj)) :=
  inferInstanceAs
    ((_root_.PresheafOfModules.sheafification.{schemeUniverse}
      (𝟙 source.ringCatSheaf.obj)).IsLocalization
        ((Opens.grothendieckTopology source).W.inverseImage
          (_root_.PresheafOfModules.toPresheaf source.ringCatSheaf.obj)))

/-- Pullback of sheaves lifts pullback of presheaves followed by sheafification. -/
instance pullbackLocalizationLifting :
    Localization.Lifting (sheafification target)
      ((Opens.grothendieckTopology target).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf target.ringCatSheaf.obj))
      (_root_.PresheafOfModules.pullbackOfCommRingCat (F := Opens.map morphism.base)
        (R := source.sheaf.obj) (S := target.sheaf.obj) morphism.toRingCatPresheafHom ⋙
        sheafification source) (pullback morphism) :=
  ⟨SheafOfModules.sheafificationCompPullback morphism.toRingCatSheafHom⟩

/-- Pullback of module sheaves preserves tensor products and the structure sheaf. -/
instance pullbackMonoidal : (pullback morphism).Monoidal :=
  @Localization.Monoidal.functorMonoidalOfComp _ _ _ _ _ _
    (presheafMonoidalCategory (scheme := target)) _ _
    (sheafification target)
    ((Opens.grothendieckTopology target).W.inverseImage
      (_root_.PresheafOfModules.toPresheaf target.ringCatSheaf.obj)) _
    (sheafificationMonoidal (scheme := target))
    (pullback morphism)
    (_root_.PresheafOfModules.pullbackOfCommRingCat (F := Opens.map morphism.base)
      (R := source.sheaf.obj) (S := target.sheaf.obj) morphism.toRingCatPresheafHom ⋙
      sheafification source)
    (presheafPullbackCompSheafificationMonoidal morphism) _ _

/-- Pullback commutes with tensor product of module sheaves. -/
def pullbackTensorObjIso (moduleSheaf targetSheaf : target.Modules) :
    (pullback morphism).obj (moduleSheaf ⊗ targetSheaf) ≅
      (pullback morphism).obj moduleSheaf ⊗ (pullback morphism).obj targetSheaf :=
  Functor.Monoidal.μIso (pullback morphism) moduleSheaf targetSheaf |>.symm

/-- Tensoring preserves an isomorphism on an open subset. -/
lemma isIso_restrict_whiskerLeft (moduleSheaf : target.Modules)
    {sourceModule targetModule : target.Modules} (moduleMap : sourceModule ⟶ targetModule)
    (openSubset : target.Opens)
    [IsIso ((restrictFunctor openSubset.ι).map moduleMap)] :
    IsIso ((restrictFunctor openSubset.ι).map (moduleSheaf ◁ moduleMap)) := by
  rw [NatIso.isIso_map_iff (restrictFunctorIsoPullback openSubset.ι)]
  have : IsIso ((pullback openSubset.ι).map moduleMap) := by
    rw [← NatIso.isIso_map_iff (restrictFunctorIsoPullback openSubset.ι)]
    infer_instance
  rw [Functor.Monoidal.map_whiskerLeft]
  infer_instance

end Modules

end AlgebraicGeometry.Scheme
