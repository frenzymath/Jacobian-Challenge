import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.CategoryTheory.Sites.ConstantSheaf
import Jacobian.CategoryTheory.Sites.SheafCohomology.Functor
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Pullback on cohomology of module sheaves

Exact inverse image of abelian sheaves, followed by the adjoint coefficient map,
defines pullback on the cohomology of a module sheaf. The map is semilinear for
the induced homomorphism on global functions.
-/

noncomputable section

universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {source target : Scheme.{schemeUniverse}}

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-image functor on abelian sheaves associated to a scheme morphism. -/
def abelianInverseImage (morphism : source ⟶ target) :
    Sheaf (Opens.grothendieckTopology target) AddCommGrpCat.{schemeUniverse} ⥤
      Sheaf (Opens.grothendieckTopology source) AddCommGrpCat.{schemeUniverse} :=
  (Opens.map morphism.base).sheafPullback AddCommGrpCat.{schemeUniverse}
    (Opens.grothendieckTopology target) (Opens.grothendieckTopology source)

instance (morphism : source ⟶ target) :
    PreservesFiniteLimits (abelianInverseImage morphism) := by
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{schemeUniverse})
    (Opens.map morphism.base)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

instance (morphism : source ⟶ target) :
    PreservesFiniteColimits (abelianInverseImage morphism) := by
  have := ((Opens.map morphism.base).sheafAdjunctionContinuous AddCommGrpCat.{schemeUniverse}
    (Opens.grothendieckTopology target)
    (Opens.grothendieckTopology source)).leftAdjoint_preservesColimits
  exact inferInstanceAs (PreservesFiniteColimits
    ((Opens.map morphism.base).sheafPullback AddCommGrpCat.{schemeUniverse}
      (Opens.grothendieckTopology target) (Opens.grothendieckTopology source)))

instance (morphism : source ⟶ target) : (abelianInverseImage morphism).Additive := by
  have : ((Opens.map morphism.base).sheafPushforwardContinuous AddCommGrpCat.{schemeUniverse}
      (Opens.grothendieckTopology target) (Opens.grothendieckTopology source)).Additive :=
    ⟨by intros; ext openSubset sectionValue; rfl⟩
  exact ((Opens.map morphism.base).sheafAdjunctionContinuous AddCommGrpCat.{schemeUniverse}
    (Opens.grothendieckTopology target)
    (Opens.grothendieckTopology source)).left_adjoint_additive

/-- Inverse image preserves the constant integer sheaf. -/
def abelianInverseImageConstantIso (morphism : source ⟶ target) :
    (abelianInverseImage morphism).obj
        ((constantSheaf (Opens.grothendieckTopology target)
          AddCommGrpCat.{schemeUniverse}).obj (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))) ≅
      (constantSheaf (Opens.grothendieckTopology source)
        AddCommGrpCat.{schemeUniverse}).obj (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ)) :=
  ((Opens.map morphism.base).constantSheafsheafPullbackIso AddCommGrpCat.{schemeUniverse}
    (Opens.grothendieckTopology target) (Opens.grothendieckTopology source)
    isTerminalTop isTerminalTop).app (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))

set_option backward.isDefEq.respectTransparency false in
/-- The abelian-sheaf coefficient map adjoint to a morphism into direct image. -/
def adjointCoefficientMap (morphism : source ⟶ target)
    {moduleSheaf : target.Modules} {targetSheaf : source.Modules}
    (coefficientMap : moduleSheaf ⟶ (pushforward morphism).obj targetSheaf) :
    (abelianInverseImage morphism).obj
        ((SheafOfModules.toSheaf target.ringCatSheaf).obj moduleSheaf) ⟶
      (SheafOfModules.toSheaf source.ringCatSheaf).obj targetSheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{schemeUniverse}
    morphism.base).homEquiv _ _ |>.symm
      ((SheafOfModules.toSheaf target.ringCatSheaf).map coefficientMap)

set_option backward.isDefEq.respectTransparency false in
lemma adjointCoefficientMap_naturality (morphism : source ⟶ target)
    {sourceSheaf sourceSheaf' : target.Modules} {targetSheaf targetSheaf' : source.Modules}
    (coefficientMap : sourceSheaf ⟶ (pushforward morphism).obj targetSheaf)
    (coefficientMap' : sourceSheaf' ⟶ (pushforward morphism).obj targetSheaf')
    (sourceMap : sourceSheaf ⟶ sourceSheaf') (targetMap : targetSheaf ⟶ targetSheaf')
    (commutes : sourceMap ≫ coefficientMap' = coefficientMap ≫ (pushforward morphism).map targetMap) :
    (abelianInverseImage morphism).map
        ((SheafOfModules.toSheaf target.ringCatSheaf).map sourceMap) ≫
        adjointCoefficientMap morphism coefficientMap' =
      adjointCoefficientMap morphism coefficientMap ≫
        (SheafOfModules.toSheaf source.ringCatSheaf).map targetMap := by
  apply (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{schemeUniverse}
    morphism.base).homEquiv_naturality_right_square
  change (SheafOfModules.toSheaf target.ringCatSheaf).map sourceMap ≫
      (SheafOfModules.toSheaf target.ringCatSheaf).map coefficientMap' =
    (SheafOfModules.toSheaf target.ringCatSheaf).map coefficientMap ≫
      (SheafOfModules.toSheaf target.ringCatSheaf).map ((pushforward morphism).map targetMap)
  rw [← Functor.map_comp, ← Functor.map_comp, commutes]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on cohomology with an arbitrary adjoint coefficient map. -/
def H.mapOfAdjunction (morphism : source ⟶ target)
    {moduleSheaf : target.Modules} {targetSheaf : source.Modules}
    (coefficientMap : moduleSheaf ⟶ (pushforward morphism).obj targetSheaf) (degree : ℕ) :
    moduleSheaf.H degree →+ targetSheaf.H degree :=
  (Sheaf.H.map (adjointCoefficientMap morphism coefficientMap) degree).comp
    (Sheaf.H.mapFunctor (abelianInverseImage morphism)
      (abelianInverseImageConstantIso morphism).symm
      ((SheafOfModules.toSheaf target.ringCatSheaf).obj moduleSheaf) degree)

set_option backward.isDefEq.respectTransparency false in
lemma H.mapOfAdjunction_naturality (morphism : source ⟶ target)
    {sourceSheaf sourceSheaf' : target.Modules} {targetSheaf targetSheaf' : source.Modules}
    (coefficientMap : sourceSheaf ⟶ (pushforward morphism).obj targetSheaf)
    (coefficientMap' : sourceSheaf' ⟶ (pushforward morphism).obj targetSheaf')
    (sourceMap : sourceSheaf ⟶ sourceSheaf') (targetMap : targetSheaf ⟶ targetSheaf')
    (commutes : sourceMap ≫ coefficientMap' = coefficientMap ≫ (pushforward morphism).map targetMap)
    (degree : ℕ) (cohomologyClass : sourceSheaf.H degree) :
    H.mapOfAdjunction morphism coefficientMap' degree
        (H.map sourceMap degree cohomologyClass) =
      H.map targetMap degree (H.mapOfAdjunction morphism coefficientMap degree cohomologyClass) := by
  change Sheaf.H.map _ degree
      (Sheaf.H.mapFunctor _ _ _ degree (Sheaf.H.map _ degree cohomologyClass)) =
    Sheaf.H.map _ degree (Sheaf.H.map _ degree (Sheaf.H.mapFunctor _ _ _ degree cohomologyClass))
  rw [Sheaf.H.mapFunctor_map, ← Sheaf.H.map_comp_apply,
    adjointCoefficientMap_naturality morphism coefficientMap coefficientMap' sourceMap
      targetMap commutes, Sheaf.H.map_comp_apply]

lemma H.mapOfAdjunction_smul (morphism : source ⟶ target)
    {moduleSheaf : target.Modules} {targetSheaf : source.Modules}
    (coefficientMap : moduleSheaf ⟶ (pushforward morphism).obj targetSheaf)
    (degree : ℕ) (scalar : Γ(target, ⊤)) (cohomologyClass : moduleSheaf.H degree) :
    H.mapOfAdjunction morphism coefficientMap degree (scalar • cohomologyClass) =
      morphism.appTop scalar • H.mapOfAdjunction morphism coefficientMap degree cohomologyClass := by
  change H.mapOfAdjunction morphism coefficientMap degree
      (H.map (moduleSheaf.smulHom scalar) degree cohomologyClass) =
    H.map (targetSheaf.smulHom (morphism.appTop scalar)) degree
      (H.mapOfAdjunction morphism coefficientMap degree cohomologyClass)
  apply H.mapOfAdjunction_naturality
  rw [pushforward_map_smulHom]
  exact smulHom_naturality coefficientMap scalar

/-- Pullback on cohomology is semilinear over the map on global functions. -/
def H.pullback (morphism : source ⟶ target) (moduleSheaf : target.Modules) (degree : ℕ) :
    moduleSheaf.H degree →ₛₗ[morphism.appTop.hom] ((pullback morphism).obj moduleSheaf).H degree where
  toFun := H.mapOfAdjunction morphism
    ((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf) degree
  map_add' := map_add _
  map_smul' := H.mapOfAdjunction_smul morphism
    ((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf) degree

/-- Cohomological pullback is natural in the module sheaf. -/
lemma H.pullback_naturality (morphism : source ⟶ target)
    {moduleSheaf targetSheaf : target.Modules} (coefficientMap : moduleSheaf ⟶ targetSheaf)
    (degree : ℕ) (cohomologyClass : moduleSheaf.H degree) :
    H.pullback morphism targetSheaf degree (H.map coefficientMap degree cohomologyClass) =
      H.map ((Modules.pullback morphism).map coefficientMap) degree
        (H.pullback morphism moduleSheaf degree cohomologyClass) := by
  exact H.mapOfAdjunction_naturality morphism
    ((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf)
    ((pullbackPushforwardAdjunction morphism).unit.app targetSheaf)
    coefficientMap ((Modules.pullback morphism).map coefficientMap)
    ((pullbackPushforwardAdjunction morphism).unit.naturality coefficientMap)
    degree cohomologyClass

end AlgebraicGeometry.Scheme.Modules
