import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import Jacobian.CategoryTheory.Sites.Descent.PullHom

/-!
# Gluing coefficient modules pulled back from local models

Chosen double and triple overlaps turn transition maps between pulled-back
coefficient modules into native descent data. Effective Zariski descent realizes
these data, and compatible local isomorphisms identify the pullback of the
realization with the original module sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse chartUniverse categoryHomUniverse categoryObjectUniverse

open CategoryTheory Limits Opposite
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open CategoryTheory.Pseudofunctor.DescentData'

namespace AlgebraicGeometry.Scheme.Modules.Gluing

section Coherence

private lemma comp_eq_of_conjugates {category : Type*} [Category category]
    {source localSource middle localMiddle target localTarget : category}
    {firstMorphism : source ⟶ middle} {secondMorphism : middle ⟶ target}
    {compositeMorphism : source ⟶ target}
    (sourceComparison : source ⟶ localSource) (firstMap : localSource ⟶ localMiddle)
    (middleComparison : localMiddle ⟶ middle) (middleInverse : middle ⟶ localMiddle)
    (secondMap : localMiddle ⟶ localTarget) (targetComparison : localTarget ⟶ target)
    (compositeMap : localSource ⟶ localTarget)
    (firstFactorization : firstMorphism = sourceComparison ≫ firstMap ≫ middleComparison)
    (secondFactorization : secondMorphism = middleInverse ≫ secondMap ≫ targetComparison)
    (compositeFactorization : compositeMorphism =
      sourceComparison ≫ compositeMap ≫ targetComparison)
    (middleIdentity : middleComparison ≫ middleInverse = 𝟙 _)
    (cocycle : firstMap ≫ secondMap = compositeMap) :
    firstMorphism ≫ secondMorphism = compositeMorphism := by
  calc
    _ = (sourceComparison ≫ firstMap ≫ middleComparison) ≫
        (middleInverse ≫ secondMap ≫ targetComparison) :=
      congrArg₂ (fun first second => first ≫ second) firstFactorization secondFactorization
    _ = sourceComparison ≫ firstMap ≫ (middleComparison ≫ middleInverse) ≫
        secondMap ≫ targetComparison := by simp only [Category.assoc]
    _ = sourceComparison ≫ (firstMap ≫ secondMap) ≫ targetComparison := by
      rw [middleIdentity, Category.id_comp]
      simp only [Category.assoc]
    _ = sourceComparison ≫ compositeMap ≫ targetComparison :=
      congrArg (fun composite => sourceComparison ≫ composite ≫ targetComparison) cocycle
    _ = _ := compositeFactorization.symm

private lemma comp_eq_of_inverse_factorizations {category : Type*} [Category category]
    {source middle target common : category}
    {firstMorphism : source ⟶ middle} {secondMorphism : middle ⟶ target}
    {compositeMorphism : source ⟶ target}
    (sourceComparison : source ⟶ common) (middleInverse : common ⟶ middle)
    (middleComparison : middle ⟶ common) (targetComparison : common ⟶ target)
    (firstFactorization : firstMorphism = sourceComparison ≫ middleInverse)
    (secondFactorization : secondMorphism = middleComparison ≫ targetComparison)
    (compositeFactorization : compositeMorphism = sourceComparison ≫ targetComparison)
    (middleIdentity : middleInverse ≫ middleComparison = 𝟙 _) :
    firstMorphism ≫ secondMorphism = compositeMorphism := by
  calc
    _ = (sourceComparison ≫ middleInverse) ≫ (middleComparison ≫ targetComparison) :=
      congrArg₂ (fun first second => first ≫ second) firstFactorization secondFactorization
    _ = sourceComparison ≫ (middleInverse ≫ middleComparison) ≫ targetComparison := by
      simp only [Category.assoc]
    _ = sourceComparison ≫ targetComparison := by rw [middleIdentity, Category.id_comp]
    _ = _ := compositeFactorization.symm

private lemma comp_eq_of_cat_conjugates
    {localCategory commonCategory : Cat.{categoryHomUniverse, categoryObjectUniverse}}
    {direct iterated : localCategory ⟶ commonCategory}
    (comparison : direct ≅ iterated) (localObject : localCategory)
    {source localSource target localTarget : commonCategory}
    {firstMorphism : source ⟶ iterated.toFunctor.obj localObject}
    {secondMorphism : iterated.toFunctor.obj localObject ⟶ target}
    {compositeMorphism : source ⟶ target}
    (sourceComparison : source ⟶ localSource)
    (firstMap : localSource ⟶ direct.toFunctor.obj localObject)
    (secondMap : direct.toFunctor.obj localObject ⟶ localTarget)
    (targetComparison : localTarget ⟶ target) (compositeMap : localSource ⟶ localTarget)
    (firstFactorization : firstMorphism = sourceComparison ≫ firstMap ≫
      comparison.hom.toNatTrans.app localObject)
    (secondFactorization : secondMorphism = comparison.inv.toNatTrans.app localObject ≫
      secondMap ≫ targetComparison)
    (compositeFactorization : compositeMorphism =
      sourceComparison ≫ compositeMap ≫ targetComparison)
    (cocycle : firstMap ≫ secondMap = compositeMap) :
    firstMorphism ≫ secondMorphism = compositeMorphism :=
  comp_eq_of_conjugates sourceComparison firstMap
    (comparison.hom.toNatTrans.app localObject) (comparison.inv.toNatTrans.app localObject)
    secondMap targetComparison compositeMap firstFactorization secondFactorization
    compositeFactorization (Cat.Hom.hom_inv_id_toNatTrans_app comparison localObject) cocycle

lemma op_toLoc_comp_eq {charts testScheme compositeScheme : Scheme.{schemeUniverse}} {chartMaps : charts ⟶ testScheme} {furtherMap : testScheme ⟶ compositeScheme} {fg : charts ⟶ compositeScheme} (baseChange : chartMaps ≫ furtherMap = fg) :
    furtherMap.op.toLoc ≫ chartMaps.op.toLoc = fg.op.toLoc := by
  subst baseChange
  rfl

/-- `pullHom` of a morphism conjugated by the comparison isomorphisms `mapComp'`. -/
lemma pullHom_mapComp'_conj ⦃firstScheme secondScheme firstBase secondBase : Scheme.{schemeUniverse}⦄ ⦃firstModule : modulesPseudofunctor.obj (.mk (op firstScheme))⦄
    ⦃secondModule : modulesPseudofunctor.obj (.mk (op secondScheme))⦄ (firstChange : firstBase ⟶ firstScheme) (secondChange : secondBase ⟶ secondScheme) ⦃testScheme : Scheme.{schemeUniverse}⦄ (firstProjection : testScheme ⟶ firstBase)
    (secondProjection : testScheme ⟶ secondBase) (firstComposite : testScheme ⟶ firstScheme) (secondComposite : testScheme ⟶ secondScheme) (hx₁ : firstProjection ≫ firstChange = firstComposite) (hx₂ : secondProjection ≫ secondChange = secondComposite)
    (coefficientMap : (modulesPseudofunctor.map firstComposite.op.toLoc).toFunctor.obj firstModule ⟶ (modulesPseudofunctor.map secondComposite.op.toLoc).toFunctor.obj secondModule)
    ⦃furtherScheme : Scheme.{schemeUniverse}⦄ (testLift : furtherScheme ⟶ testScheme) (firstMap : furtherScheme ⟶ firstBase) (secondMap : furtherScheme ⟶ secondBase) (hl₁ : testLift ≫ firstProjection = firstMap)
    (hl₂ : testLift ≫ secondProjection = secondMap) (firstFurtherComposite : furtherScheme ⟶ firstScheme) (secondFurtherComposite : furtherScheme ⟶ secondScheme) (hy₁ : firstMap ≫ firstChange = firstFurtherComposite)
    (hy₂ : secondMap ≫ secondChange = secondFurtherComposite) :
    pullHom ((modulesPseudofunctor.mapComp' firstChange.op.toLoc firstProjection.op.toLoc firstComposite.op.toLoc
        (op_toLoc_comp_eq hx₁)).inv.toNatTrans.app firstModule ≫ coefficientMap ≫
        (modulesPseudofunctor.mapComp' secondChange.op.toLoc secondProjection.op.toLoc secondComposite.op.toLoc
          (op_toLoc_comp_eq hx₂)).hom.toNatTrans.app secondModule) testLift firstMap secondMap hl₁ hl₂ =
      (modulesPseudofunctor.mapComp' firstChange.op.toLoc firstMap.op.toLoc firstFurtherComposite.op.toLoc
          (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app firstModule ≫
        pullHom coefficientMap testLift firstFurtherComposite secondFurtherComposite (by rw [← hy₁, ← hx₁, ← hl₁, Category.assoc])
          (by rw [← hy₂, ← hx₂, ← hl₂, Category.assoc]) ≫
        (modulesPseudofunctor.mapComp' secondChange.op.toLoc secondMap.op.toLoc secondFurtherComposite.op.toLoc
          (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app secondModule := by
  subst hx₁ hx₂ hl₁ hl₂ hy₁ hy₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [modulesPseudofunctor.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl rfl (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ rfl rfl (by cat_disch)]

/-- `pullHom` of a comparison isomorphism `mapComp'` is a comparison isomorphism. -/
lemma pullHom_mapComp'_inv {baseScheme changedBase testScheme : Scheme.{schemeUniverse}} (baseChange : changedBase ⟶ baseScheme) (firstProjection : testScheme ⟶ changedBase) (compositeProjection : testScheme ⟶ baseScheme)
    (hxh : firstProjection ≫ baseChange = compositeProjection) (sourceModule : modulesPseudofunctor.obj (.mk (op baseScheme))) ⦃furtherScheme : Scheme.{schemeUniverse}⦄ (furtherMap : furtherScheme ⟶ testScheme) (firstLift : furtherScheme ⟶ changedBase)
    (compositeLift : furtherScheme ⟶ baseScheme) (hgx : furtherMap ≫ firstProjection = firstLift) (hgxh : furtherMap ≫ compositeProjection = compositeLift) :
    pullHom (M₁ := (modulesPseudofunctor.map baseChange.op.toLoc).toFunctor.obj sourceModule) (M₂ := sourceModule)
        ((modulesPseudofunctor.mapComp' baseChange.op.toLoc firstProjection.op.toLoc compositeProjection.op.toLoc
          (op_toLoc_comp_eq hxh)).inv.toNatTrans.app sourceModule) furtherMap firstLift compositeLift hgx hgxh =
      (modulesPseudofunctor.mapComp' baseChange.op.toLoc firstLift.op.toLoc compositeLift.op.toLoc
        (op_toLoc_comp_eq (by rw [← hgxh, ← hxh, ← hgx, Category.assoc]))).inv.toNatTrans.app
          sourceModule := by
  subst hxh hgx hgxh
  dsimp [pullHom]
  rw [modulesPseudofunctor.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ rfl rfl (by cat_disch)]
  simp

/-- `pullHom` of a morphism conjugated by the inverses of the comparison isomorphisms
`mapComp'`. -/
lemma pullHom_mapComp'_conj_symm ⦃firstScheme secondScheme firstBase secondBase : Scheme.{schemeUniverse}⦄ ⦃firstModule : modulesPseudofunctor.obj (.mk (op firstScheme))⦄
    ⦃secondModule : modulesPseudofunctor.obj (.mk (op secondScheme))⦄ (firstProjection : firstBase ⟶ firstScheme) (secondProjection : secondBase ⟶ secondScheme) ⦃testScheme : Scheme.{schemeUniverse}⦄ (firstChange : testScheme ⟶ firstBase)
    (secondChange : testScheme ⟶ secondBase) (firstComposite : testScheme ⟶ firstScheme) (secondComposite : testScheme ⟶ secondScheme) (hx₁ : firstChange ≫ firstProjection = firstComposite) (hx₂ : secondChange ≫ secondProjection = secondComposite)
    (coefficientMap : (modulesPseudofunctor.map firstChange.op.toLoc).toFunctor.obj ((modulesPseudofunctor.map firstProjection.op.toLoc).toFunctor.obj firstModule) ⟶
      (modulesPseudofunctor.map secondChange.op.toLoc).toFunctor.obj ((modulesPseudofunctor.map secondProjection.op.toLoc).toFunctor.obj secondModule))
    ⦃furtherScheme : Scheme.{schemeUniverse}⦄ (testLift : furtherScheme ⟶ testScheme) (firstLift : furtherScheme ⟶ firstBase) (secondLift : furtherScheme ⟶ secondBase) (hz₁ : testLift ≫ firstChange = firstLift)
    (hz₂ : testLift ≫ secondChange = secondLift) (firstFurtherComposite : furtherScheme ⟶ firstScheme) (secondFurtherComposite : furtherScheme ⟶ secondScheme) (hy₁ : firstLift ≫ firstProjection = firstFurtherComposite)
    (hy₂ : secondLift ≫ secondProjection = secondFurtherComposite) :
    pullHom ((modulesPseudofunctor.mapComp' firstProjection.op.toLoc firstChange.op.toLoc firstComposite.op.toLoc
        (op_toLoc_comp_eq hx₁)).hom.toNatTrans.app firstModule ≫ coefficientMap ≫
        (modulesPseudofunctor.mapComp' secondProjection.op.toLoc secondChange.op.toLoc secondComposite.op.toLoc
          (op_toLoc_comp_eq hx₂)).inv.toNatTrans.app secondModule) testLift firstFurtherComposite secondFurtherComposite
        (by rw [← hy₁, ← hx₁, ← hz₁, Category.assoc])
        (by rw [← hy₂, ← hx₂, ← hz₂, Category.assoc]) =
      (modulesPseudofunctor.mapComp' firstProjection.op.toLoc firstLift.op.toLoc firstFurtherComposite.op.toLoc
          (op_toLoc_comp_eq hy₁)).hom.toNatTrans.app firstModule ≫
        pullHom coefficientMap testLift firstLift secondLift hz₁ hz₂ ≫
        (modulesPseudofunctor.mapComp' secondProjection.op.toLoc secondLift.op.toLoc secondFurtherComposite.op.toLoc
          (op_toLoc_comp_eq hy₂)).inv.toNatTrans.app secondModule := by
  subst hx₁ hx₂ hz₁ hz₂ hy₁ hy₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [modulesPseudofunctor.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc _ _ _ _ _ _ rfl rfl
      (by cat_disch),
    modulesPseudofunctor.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ rfl rfl (by cat_disch)]

/-- Morphisms with equal pullbacks have equal `pullHom`s. -/
lemma pullHom_eq_pullHom_of_map_eq ⦃firstScheme secondScheme : Scheme.{schemeUniverse}⦄ ⦃firstModule : modulesPseudofunctor.obj (.mk (op firstScheme))⦄
    ⦃secondModule : modulesPseudofunctor.obj (.mk (op secondScheme))⦄ ⦃testScheme : Scheme.{schemeUniverse}⦄ ⦃firstMap : testScheme ⟶ firstScheme⦄ ⦃secondMap : testScheme ⟶ secondScheme⦄
    {firstCoefficientMap secondCoefficientMap : (modulesPseudofunctor.map firstMap.op.toLoc).toFunctor.obj firstModule ⟶ (modulesPseudofunctor.map secondMap.op.toLoc).toFunctor.obj secondModule}
    ⦃furtherScheme : Scheme.{schemeUniverse}⦄ (furtherMap : furtherScheme ⟶ testScheme) (firstPullback : furtherScheme ⟶ firstScheme) (secondPullback : furtherScheme ⟶ secondScheme) (hgf₁ : furtherMap ≫ firstMap = firstPullback)
    (hgf₂ : furtherMap ≫ secondMap = secondPullback)
    (baseChange : (modulesPseudofunctor.map furtherMap.op.toLoc).toFunctor.map firstCoefficientMap = (modulesPseudofunctor.map furtherMap.op.toLoc).toFunctor.map secondCoefficientMap) :
    pullHom firstCoefficientMap furtherMap firstPullback secondPullback hgf₁ hgf₂ = pullHom secondCoefficientMap furtherMap firstPullback secondPullback hgf₁ hgf₂ := by
  simp only [pullHom, baseChange]

/-- Morphisms with equal `pullHom`s have equal pullbacks. -/
lemma map_eq_map_of_pullHom_eq ⦃firstScheme secondScheme : Scheme.{schemeUniverse}⦄ ⦃firstModule : modulesPseudofunctor.obj (.mk (op firstScheme))⦄
    ⦃secondModule : modulesPseudofunctor.obj (.mk (op secondScheme))⦄ ⦃testScheme : Scheme.{schemeUniverse}⦄ ⦃firstMap : testScheme ⟶ firstScheme⦄ ⦃secondMap : testScheme ⟶ secondScheme⦄
    {firstCoefficientMap secondCoefficientMap : (modulesPseudofunctor.map firstMap.op.toLoc).toFunctor.obj firstModule ⟶ (modulesPseudofunctor.map secondMap.op.toLoc).toFunctor.obj secondModule}
    ⦃furtherScheme : Scheme.{schemeUniverse}⦄ (furtherMap : furtherScheme ⟶ testScheme) (firstPullback : furtherScheme ⟶ firstScheme) (secondPullback : furtherScheme ⟶ secondScheme) (hgf₁ : furtherMap ≫ firstMap = firstPullback)
    (hgf₂ : furtherMap ≫ secondMap = secondPullback) (baseChange : pullHom firstCoefficientMap furtherMap firstPullback secondPullback hgf₁ hgf₂ = pullHom secondCoefficientMap furtherMap firstPullback secondPullback hgf₁ hgf₂) :
    (modulesPseudofunctor.map furtherMap.op.toLoc).toFunctor.map firstCoefficientMap = (modulesPseudofunctor.map furtherMap.op.toLoc).toFunctor.map secondCoefficientMap := by
  rw [map_eq_pullHom firstCoefficientMap furtherMap firstPullback secondPullback hgf₁ hgf₂, map_eq_pullHom secondCoefficientMap furtherMap firstPullback secondPullback hgf₁ hgf₂, baseChange]


end Coherence



section Data

variable {Chart : Type chartUniverse} {baseScheme : Scheme.{schemeUniverse}} {charts : Chart → Scheme.{schemeUniverse}} {chartMaps : ∀ chartIndex, charts chartIndex ⟶ baseScheme}
  {squares : ∀ chartIndex secondIndex, ChosenPullback (chartMaps chartIndex) (chartMaps secondIndex)}
  (tripleSquares : ∀ firstIndex secondIndex thirdIndex, ChosenPullback₃ (squares firstIndex secondIndex) (squares secondIndex thirdIndex) (squares firstIndex thirdIndex))
  {coefficientSchemes : Chart → Scheme.{schemeUniverse}} (coefficientMaps : ∀ chartIndex, charts chartIndex ⟶ coefficientSchemes chartIndex) (coefficients : ∀ chartIndex, modulesPseudofunctor.obj (.mk (op (coefficientSchemes chartIndex))))
  (transitionMaps : ∀ chartIndex secondIndex, (modulesPseudofunctor.map ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ⟶
    (modulesPseudofunctor.map ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex).op.toLoc).toFunctor.obj (coefficients secondIndex))

/-- The morphisms of a descent datum for the objects `(coefficientMaps chartIndex)^* (coefficients chartIndex)` obtained from gluing
morphisms `transitionMaps chartIndex secondIndex : ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex)^* (coefficients chartIndex) ⟶ ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex)^* (coefficients secondIndex)`, by conjugation
with the comparison isomorphisms `mapComp'`. -/
noncomputable def glueHom (chartIndex secondIndex : Chart) :
    (modulesPseudofunctor.map (squares chartIndex secondIndex).p₁.op.toLoc).toFunctor.obj ((modulesPseudofunctor.map (coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex)) ⟶
      (modulesPseudofunctor.map (squares chartIndex secondIndex).p₂.op.toLoc).toFunctor.obj ((modulesPseudofunctor.map (coefficientMaps secondIndex).op.toLoc).toFunctor.obj (coefficients secondIndex)) :=
  (modulesPseudofunctor.mapComp' (coefficientMaps chartIndex).op.toLoc (squares chartIndex secondIndex).p₁.op.toLoc ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex).op.toLoc
      (op_toLoc_comp_eq rfl)).inv.toNatTrans.app (coefficients chartIndex) ≫ transitionMaps chartIndex secondIndex ≫
    (modulesPseudofunctor.mapComp' (coefficientMaps secondIndex).op.toLoc (squares chartIndex secondIndex).p₂.op.toLoc ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex).op.toLoc
      (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (coefficients secondIndex)

lemma pullHom'_glueHom ⦃testScheme : Scheme.{schemeUniverse}⦄ (structureMap : testScheme ⟶ baseScheme) ⦃firstIndex secondIndex : Chart⦄ (firstMap : testScheme ⟶ charts firstIndex) (secondMap : testScheme ⟶ charts secondIndex)
    (hf₁ : firstMap ≫ chartMaps firstIndex = structureMap) (hf₂ : secondMap ≫ chartMaps secondIndex = structureMap) (testProjection : testScheme ⟶ (squares firstIndex secondIndex).pullback)
    (hp₁ : testProjection ≫ (squares firstIndex secondIndex).p₁ = firstMap) (hp₂ : testProjection ≫ (squares firstIndex secondIndex).p₂ = secondMap) (firstFurtherComposite : testScheme ⟶ coefficientSchemes firstIndex)
    (secondFurtherComposite : testScheme ⟶ coefficientSchemes secondIndex) (hy₁ : firstMap ≫ coefficientMaps firstIndex = firstFurtherComposite) (hy₂ : secondMap ≫ coefficientMaps secondIndex = secondFurtherComposite) :
    pullHom' (glueHom coefficientMaps coefficients transitionMaps) structureMap firstMap secondMap hf₁ hf₂ =
      (modulesPseudofunctor.mapComp' (coefficientMaps firstIndex).op.toLoc firstMap.op.toLoc firstFurtherComposite.op.toLoc
          (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app (coefficients firstIndex) ≫
        pullHom (transitionMaps firstIndex secondIndex) testProjection firstFurtherComposite secondFurtherComposite (by rw [← hy₁, ← hp₁, Category.assoc])
          (by rw [← hy₂, ← hp₂, Category.assoc]) ≫
        (modulesPseudofunctor.mapComp' (coefficientMaps secondIndex).op.toLoc secondMap.op.toLoc secondFurtherComposite.op.toLoc
          (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app (coefficients secondIndex) := by
  rw [pullHom'_eq_pullHom _ _ _ _ testProjection hf₁ hf₂ hp₁ hp₂]
  exact pullHom_mapComp'_conj _ _ _ _ _ _ rfl rfl (transitionMaps firstIndex secondIndex) testProjection firstMap secondMap hp₁ hp₂ firstFurtherComposite secondFurtherComposite hy₁ hy₂

variable {coefficientMaps coefficients} in
/-- The left hand side of the identity condition for gluing morphisms, along sections `diagonals chartIndex` of
the diagonals. -/
noncomputable def glueSelfLHS (diagonals : ∀ chartIndex, charts chartIndex ⟶ (squares chartIndex chartIndex).pullback)
    (hd₁ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₁ = 𝟙 _) (hd₂ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₂ = 𝟙 _) (chartIndex : Chart) :=
  pullHom (transitionMaps chartIndex chartIndex) (diagonals chartIndex) (coefficientMaps chartIndex) (coefficientMaps chartIndex) (by rw [reassoc_of% (hd₁ chartIndex)])
    (by rw [reassoc_of% (hd₂ chartIndex)])

variable {coefficientMaps coefficients transitionMaps} in
/-- The identity condition for gluing morphisms, along sections `diagonals chartIndex` of the diagonals. -/
def GlueSelf (diagonals : ∀ chartIndex, charts chartIndex ⟶ (squares chartIndex chartIndex).pullback) (hd₁ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₁ = 𝟙 _)
    (hd₂ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₂ = 𝟙 _) : Prop :=
  ∀ chartIndex, glueSelfLHS transitionMaps diagonals hd₁ hd₂ chartIndex = 𝟙 _

variable {coefficientMaps coefficients} in
/-- The left hand side of the cocycle condition for gluing morphisms. -/
noncomputable def glueCocLHS (firstIndex secondIndex thirdIndex : Chart) :=
  pullHom (transitionMaps firstIndex secondIndex) (tripleSquares firstIndex secondIndex thirdIndex).p₁₂ ((tripleSquares firstIndex secondIndex thirdIndex).p₁ ≫ coefficientMaps firstIndex)
      ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ coefficientMaps secondIndex) (ChosenPullback₃.p₁₂_p₁_assoc _ _)
      (ChosenPullback₃.p₁₂_p₂_assoc _ _) ≫
    pullHom (transitionMaps secondIndex thirdIndex) (tripleSquares firstIndex secondIndex thirdIndex).p₂₃ ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ coefficientMaps secondIndex)
      ((tripleSquares firstIndex secondIndex thirdIndex).p₃ ≫ coefficientMaps thirdIndex) (ChosenPullback₃.p₂₃_p₂_assoc _ _)
      (ChosenPullback₃.p₂₃_p₃_assoc _ _)

variable {coefficientMaps coefficients} in
/-- The right hand side of the cocycle condition for gluing morphisms. -/
noncomputable def glueCocRHS (firstIndex secondIndex thirdIndex : Chart) :=
  pullHom (transitionMaps firstIndex thirdIndex) (tripleSquares firstIndex secondIndex thirdIndex).p₁₃ ((tripleSquares firstIndex secondIndex thirdIndex).p₁ ≫ coefficientMaps firstIndex)
      ((tripleSquares firstIndex secondIndex thirdIndex).p₃ ≫ coefficientMaps thirdIndex) (ChosenPullback₃.p₁₃_p₁_assoc _ _)
      (ChosenPullback₃.p₁₃_p₃_assoc _ _)

variable {coefficientMaps coefficients} in
/-- The cocycle condition for gluing morphisms. -/
def GlueCocycle : Prop :=
  ∀ firstIndex secondIndex thirdIndex, glueCocLHS tripleSquares transitionMaps firstIndex secondIndex thirdIndex = glueCocRHS tripleSquares transitionMaps firstIndex secondIndex thirdIndex

variable {diagonals : ∀ chartIndex, charts chartIndex ⟶ (squares chartIndex chartIndex).pullback} {hd₁ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₁ = 𝟙 _}
  {hd₂ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₂ = 𝟙 _}

private lemma ofGlue_pullHom'_hom_self (hself : GlueSelf (transitionMaps := transitionMaps) diagonals hd₁ hd₂)
  (chartIndex : Chart) :
    pullHom' (glueHom coefficientMaps coefficients transitionMaps) (chartMaps chartIndex) (𝟙 _) (𝟙 _) = 𝟙 _ := by
  have hs := hself chartIndex
  rw [glueSelfLHS] at hs
  rw [pullHom'_glueHom coefficientMaps coefficients transitionMaps (chartMaps chartIndex) (𝟙 _) (𝟙 _)
      (Category.id_comp _) (Category.id_comp _) (diagonals chartIndex) (hd₁ chartIndex) (hd₂ chartIndex)
      (coefficientMaps chartIndex) (coefficientMaps chartIndex) (Category.id_comp _) (Category.id_comp _), hs,
    Category.id_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
  rfl

private lemma ofGlue_pullHom'_hom_comp_aux {firstIndex secondIndex : Chart}
    {testScheme : Scheme.{schemeUniverse}} (structureMap : testScheme ⟶ baseScheme)
    (firstMap : testScheme ⟶ charts firstIndex) (secondMap : testScheme ⟶ charts secondIndex)
    (firstFactorization : firstMap ≫ chartMaps firstIndex = structureMap)
    (secondFactorization : secondMap ≫ chartMaps secondIndex = structureMap)
    (testProjection : testScheme ⟶ (squares firstIndex secondIndex).pullback)
    (firstProjection : testProjection ≫ (squares firstIndex secondIndex).p₁ = firstMap)
    (secondProjection : testProjection ≫ (squares firstIndex secondIndex).p₂ = secondMap) :
    pullHom' (glueHom coefficientMaps coefficients transitionMaps)
        structureMap firstMap secondMap firstFactorization secondFactorization =
      (modulesPseudofunctor.mapComp' (coefficientMaps firstIndex).op.toLoc
          firstMap.op.toLoc (firstMap ≫ coefficientMaps firstIndex).op.toLoc
          (op_toLoc_comp_eq rfl)).inv.toNatTrans.app (coefficients firstIndex) ≫
        pullHom (transitionMaps firstIndex secondIndex)
          testProjection (firstMap ≫ coefficientMaps firstIndex)
          (secondMap ≫ coefficientMaps secondIndex)
          (by rw [reassoc_of% firstProjection]) (by rw [reassoc_of% secondProjection]) ≫
        (modulesPseudofunctor.mapComp' (coefficientMaps secondIndex).op.toLoc
          secondMap.op.toLoc (secondMap ≫ coefficientMaps secondIndex).op.toLoc
          (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (coefficients secondIndex) := by
  exact pullHom'_glueHom coefficientMaps coefficients transitionMaps structureMap
    firstMap secondMap firstFactorization secondFactorization testProjection
    firstProjection secondProjection (firstMap ≫ coefficientMaps firstIndex)
    (secondMap ≫ coefficientMaps secondIndex) rfl rfl

private noncomputable def gluingPullHom'
    {testScheme : Scheme.{schemeUniverse}} (structureMap : testScheme ⟶ baseScheme)
    {firstIndex secondIndex : Chart} (firstMap : testScheme ⟶ charts firstIndex)
    (secondMap : testScheme ⟶ charts secondIndex)
    (firstFactorization : firstMap ≫ chartMaps firstIndex = structureMap)
    (secondFactorization : secondMap ≫ chartMaps secondIndex = structureMap) :=
  pullHom' (glueHom coefficientMaps coefficients transitionMaps)
    structureMap firstMap secondMap firstFactorization secondFactorization

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private lemma ofGlue_pullHom'_hom_comp (hcoc : GlueCocycle tripleSquares transitionMaps)
    (firstIndex secondIndex thirdIndex : Chart) :
    let tripleSquare := tripleSquares firstIndex secondIndex thirdIndex
    let firstMorphism := gluingPullHom' coefficientMaps coefficients transitionMaps
      tripleSquare.p tripleSquare.p₁ tripleSquare.p₂
      (by simp) (by simp)
    let secondMorphism := gluingPullHom' coefficientMaps coefficients transitionMaps
      tripleSquare.p tripleSquare.p₂ tripleSquare.p₃
      (by simp) (by simp)
    let compositeMorphism := gluingPullHom' coefficientMaps coefficients transitionMaps
      tripleSquare.p tripleSquare.p₁ tripleSquare.p₃
      (by simp) (by simp)
    firstMorphism ≫ secondMorphism = compositeMorphism := by
    dsimp only
    have hc := hcoc firstIndex secondIndex thirdIndex
    dsimp only [glueCocLHS, glueCocRHS] at hc
    let firstMorphism := gluingPullHom' coefficientMaps coefficients transitionMaps
      (tripleSquares firstIndex secondIndex thirdIndex).p
      (tripleSquares firstIndex secondIndex thirdIndex).p₁
      (tripleSquares firstIndex secondIndex thirdIndex).p₂ (by simp) (by simp)
    let secondMorphism := gluingPullHom' coefficientMaps coefficients transitionMaps
      (tripleSquares firstIndex secondIndex thirdIndex).p
      (tripleSquares firstIndex secondIndex thirdIndex).p₂
      (tripleSquares firstIndex secondIndex thirdIndex).p₃ (by simp) (by simp)
    let compositeMorphism := gluingPullHom' coefficientMaps coefficients transitionMaps
      (tripleSquares firstIndex secondIndex thirdIndex).p
      (tripleSquares firstIndex secondIndex thirdIndex).p₁
      (tripleSquares firstIndex secondIndex thirdIndex).p₃ (by simp) (by simp)
    let firstFactorization := ofGlue_pullHom'_hom_comp_aux coefficientMaps coefficients transitionMaps
      (tripleSquares firstIndex secondIndex thirdIndex).p
      (tripleSquares firstIndex secondIndex thirdIndex).p₁
      (tripleSquares firstIndex secondIndex thirdIndex).p₂ (by simp) (by simp)
      (tripleSquares firstIndex secondIndex thirdIndex).p₁₂
      (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _)
    let secondFactorization := ofGlue_pullHom'_hom_comp_aux coefficientMaps coefficients transitionMaps
      (tripleSquares firstIndex secondIndex thirdIndex).p
      (tripleSquares firstIndex secondIndex thirdIndex).p₂
      (tripleSquares firstIndex secondIndex thirdIndex).p₃ (by simp) (by simp)
      (tripleSquares firstIndex secondIndex thirdIndex).p₂₃
      (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _)
    let compositeFactorization := ofGlue_pullHom'_hom_comp_aux coefficientMaps coefficients transitionMaps
      (tripleSquares firstIndex secondIndex thirdIndex).p
      (tripleSquares firstIndex secondIndex thirdIndex).p₁
      (tripleSquares firstIndex secondIndex thirdIndex).p₃ (by simp) (by simp)
      (tripleSquares firstIndex secondIndex thirdIndex).p₁₃
      (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _)
    have hcomp : firstMorphism ≫ secondMorphism = compositeMorphism :=
      comp_eq_of_cat_conjugates
        (localCategory := modulesPseudofunctor.obj
          (.mk (op (coefficientSchemes secondIndex))))
        (commonCategory := modulesPseudofunctor.obj
          (.mk (op (tripleSquares firstIndex secondIndex thirdIndex).pullback)))
        (direct := modulesPseudofunctor.map
          ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫
            coefficientMaps secondIndex).op.toLoc)
        (iterated := modulesPseudofunctor.map (coefficientMaps secondIndex).op.toLoc ≫
          modulesPseudofunctor.map
            (tripleSquares firstIndex secondIndex thirdIndex).p₂.op.toLoc)
        (firstMorphism := firstMorphism) (secondMorphism := secondMorphism)
        (compositeMorphism := compositeMorphism)
        (modulesPseudofunctor.mapComp' (coefficientMaps secondIndex).op.toLoc
          (tripleSquares firstIndex secondIndex thirdIndex).p₂.op.toLoc
          ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ coefficientMaps secondIndex).op.toLoc
          (op_toLoc_comp_eq rfl)) (coefficients secondIndex) _ _ _ _ _
        firstFactorization secondFactorization compositeFactorization hc
    exact hcomp

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- **The descent datum defined by gluing morphisms** satisfying the identity and cocycle
conditions: the objects are `(coefficientMaps chartIndex)^* (coefficients chartIndex)`, and the morphisms are the gluing morphisms
conjugated with the comparison isomorphisms `mapComp'`. -/
noncomputable def ofGlue (hself : GlueSelf (transitionMaps := transitionMaps) diagonals hd₁ hd₂) (hcoc : GlueCocycle tripleSquares transitionMaps) :
    modulesPseudofunctor.DescentData' squares tripleSquares where
  obj chartIndex := (modulesPseudofunctor.map (coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex)
  hom := glueHom coefficientMaps coefficients transitionMaps
  pullHom'_hom_self :=
    ofGlue_pullHom'_hom_self (coefficientMaps := coefficientMaps) (coefficients := coefficients)
      (transitionMaps := transitionMaps) hself
  pullHom'_hom_comp :=
    by
      simpa only [gluingPullHom'] using
        ofGlue_pullHom'_hom_comp tripleSquares coefficientMaps coefficients transitionMaps hcoc

@[simp]
lemma ofGlue_obj (hself : GlueSelf (transitionMaps := transitionMaps) diagonals hd₁ hd₂) (hcoc : GlueCocycle tripleSquares transitionMaps) (chartIndex : Chart) :
    (ofGlue tripleSquares coefficientMaps coefficients transitionMaps hself hcoc).obj chartIndex = (modulesPseudofunctor.map (coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) := rfl

lemma ofGlue_hom (hself : GlueSelf (transitionMaps := transitionMaps) diagonals hd₁ hd₂) (hcoc : GlueCocycle tripleSquares transitionMaps) :
    (ofGlue tripleSquares coefficientMaps coefficients transitionMaps hself hcoc).hom = glueHom coefficientMaps coefficients transitionMaps := rfl

variable {tripleSquares coefficientMaps coefficients transitionMaps}

/-- The components of an isomorphism from the descent datum of `sourceModule` to the descent datum
`ofGlue`, pulled back to the chosen pullbacks, are compatible with the gluing morphisms. -/
lemma pullHom_comp_eq_of_iso_ofGlue {hself : GlueSelf (transitionMaps := transitionMaps) diagonals hd₁ hd₂}
    {hcoc : GlueCocycle tripleSquares transitionMaps} {sourceModule : modulesPseudofunctor.obj (.mk (op baseScheme))}
    (realization : (modulesPseudofunctor.toDescentData chartMaps).obj sourceModule ⟶ (ofGlue tripleSquares coefficientMaps coefficients transitionMaps hself hcoc).descentData) (chartIndex secondIndex : Chart) :
    pullHom (realization.hom chartIndex) (squares chartIndex secondIndex).p₁ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex) (by simp) rfl ≫ transitionMaps chartIndex secondIndex =
      pullHom (realization.hom secondIndex) (squares chartIndex secondIndex).p₂ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex) (by simp) rfl := by
  have hc := realization.comm (squares chartIndex secondIndex).p (squares chartIndex secondIndex).p₁ (squares chartIndex secondIndex).p₂ (by simp) (by simp)
  rw [map_eq_pullHom (realization.hom chartIndex) (squares chartIndex secondIndex).p₁ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex) (by simp) rfl,
    map_eq_pullHom (realization.hom secondIndex) (squares chartIndex secondIndex).p₂ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex) (by simp) rfl] at hc
  rw [descentData_hom, ofGlue_hom, pullHom'_glueHom coefficientMaps coefficients transitionMaps _ _ _ _ _ (𝟙 _) (Category.id_comp _)
    (Category.id_comp _) _ _ rfl rfl, pullHom_id] at hc
  erw [DescentData.ofObj_hom] at hc
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hc
  rw [← cancel_epi ((modulesPseudofunctor.mapComp' (chartMaps chartIndex).op.toLoc (squares chartIndex secondIndex).p₁.op.toLoc (squares chartIndex secondIndex).p.op.toLoc
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app sourceModule),
    ← cancel_mono ((modulesPseudofunctor.mapComp' (coefficientMaps secondIndex).op.toLoc (squares chartIndex secondIndex).p₂.op.toLoc
      ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex).op.toLoc (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (coefficients secondIndex))]
  simpa only [Category.assoc] using hc

end Data

/-- **Gluing isomorphisms.** If `modulesPseudofunctor.toDescentData chartMaps` is fully faithful, isomorphisms between the
pullbacks of two objects along the `chartMaps chartIndex` which agree on the chosen pullbacks come from an
isomorphism between the objects. -/
lemma nonempty_iso_of_pullHom_eq {Chart : Type chartUniverse} {baseScheme : Scheme.{schemeUniverse}} {charts : Chart → Scheme.{schemeUniverse}} {chartMaps : ∀ chartIndex, charts chartIndex ⟶ baseScheme}
    (squares : ∀ chartIndex secondIndex, ChosenPullback (chartMaps chartIndex) (chartMaps secondIndex))
    (hf : ∀ sourceModule targetModule : modulesPseudofunctor.obj (.mk (op baseScheme)),
      Function.Bijective ((modulesPseudofunctor.toDescentData chartMaps).map : (sourceModule ⟶ targetModule) → _))
    {sourceModule targetModule : modulesPseudofunctor.obj (.mk (op baseScheme))}
    (localComparisons : ∀ chartIndex, (modulesPseudofunctor.map (chartMaps chartIndex).op.toLoc).toFunctor.obj sourceModule ≅ (modulesPseudofunctor.map (chartMaps chartIndex).op.toLoc).toFunctor.obj targetModule)
    (hσ : ∀ chartIndex secondIndex, pullHom (localComparisons chartIndex).hom (squares chartIndex secondIndex).p₁ (squares chartIndex secondIndex).p (squares chartIndex secondIndex).p (by simp) (by simp) =
      pullHom (localComparisons secondIndex).hom (squares chartIndex secondIndex).p₂ (squares chartIndex secondIndex).p (squares chartIndex secondIndex).p (by simp) (by simp)) :
    Nonempty (sourceModule ≅ targetModule) := by
  have key ⦃testScheme : Scheme.{schemeUniverse}⦄ (structureMap : testScheme ⟶ baseScheme) ⦃firstIndex secondIndex : Chart⦄ (firstMap : testScheme ⟶ charts firstIndex) (secondMap : testScheme ⟶ charts secondIndex)
      (hf₁ : firstMap ≫ chartMaps firstIndex = structureMap) (hf₂ : secondMap ≫ chartMaps secondIndex = structureMap) :
      pullHom (localComparisons firstIndex).hom firstMap structureMap structureMap hf₁ hf₁ = pullHom (localComparisons secondIndex).hom secondMap structureMap structureMap hf₂ hf₂ := by
    obtain ⟨testLift, hl₁, hl₂⟩ := (squares firstIndex secondIndex).isPullback.exists_lift firstMap secondMap (by rw [hf₁, hf₂])
    have hl : testLift ≫ (squares firstIndex secondIndex).p = structureMap := by rw [← (squares firstIndex secondIndex).hp₁, reassoc_of% hl₁, hf₁]
    rw [pullHom_congr_left (localComparisons firstIndex).hom hl₁.symm structureMap structureMap hf₁ hf₁,
      pullHom_congr_left (localComparisons secondIndex).hom hl₂.symm structureMap structureMap hf₂ hf₂,
      ← pullHom_pullHom (localComparisons firstIndex).hom (squares firstIndex secondIndex).p₁ (squares firstIndex secondIndex).p (squares firstIndex secondIndex).p testLift structureMap structureMap,
      ← pullHom_pullHom (localComparisons secondIndex).hom (squares firstIndex secondIndex).p₂ (squares firstIndex secondIndex).p (squares firstIndex secondIndex).p testLift structureMap structureMap, hσ]
  let descentComparison : (modulesPseudofunctor.toDescentData chartMaps).obj sourceModule ≅ (modulesPseudofunctor.toDescentData chartMaps).obj targetModule :=
    DescentData.isoMk localComparisons (fun testScheme structureMap firstIndex secondIndex firstMap secondMap hf₁ hf₂ ↦ by
      erw [DescentData.ofObj_hom, DescentData.ofObj_hom]
      rw [map_eq_pullHom (localComparisons firstIndex).hom firstMap structureMap structureMap hf₁ hf₁, map_eq_pullHom (localComparisons secondIndex).hom secondMap structureMap structureMap hf₂ hf₂,
        key structureMap firstMap secondMap hf₁ hf₂]
      simp)
  obtain ⟨forwardMap, ha⟩ := (hf sourceModule targetModule).2 descentComparison.hom
  obtain ⟨inverseMap, hb⟩ := (hf targetModule sourceModule).2 descentComparison.inv
  exact ⟨⟨forwardMap, inverseMap, (hf sourceModule sourceModule).1 (by
      rw [Functor.map_comp, ha, hb, descentComparison.hom_inv_id,
        CategoryTheory.Functor.map_id (modulesPseudofunctor.toDescentData chartMaps) sourceModule]),
    (hf targetModule targetModule).1 (by
      rw [Functor.map_comp, ha, hb, descentComparison.inv_hom_id,
        CategoryTheory.Functor.map_id (modulesPseudofunctor.toDescentData chartMaps) targetModule])⟩⟩

section Data

variable {Chart : Type chartUniverse} {baseScheme : Scheme.{schemeUniverse}} {charts : Chart → Scheme.{schemeUniverse}} {chartMaps : ∀ chartIndex, charts chartIndex ⟶ baseScheme}
  {squares : ∀ chartIndex secondIndex, ChosenPullback (chartMaps chartIndex) (chartMaps secondIndex)}
  {tripleSquares : ∀ firstIndex secondIndex thirdIndex, ChosenPullback₃ (squares firstIndex secondIndex) (squares secondIndex thirdIndex) (squares firstIndex thirdIndex)}
  {coefficientSchemes : Chart → Scheme.{schemeUniverse}} {coefficientMaps : ∀ chartIndex, charts chartIndex ⟶ coefficientSchemes chartIndex} {coefficients : ∀ chartIndex, modulesPseudofunctor.obj (.mk (op (coefficientSchemes chartIndex)))}
  {transitionMaps : ∀ chartIndex secondIndex, (modulesPseudofunctor.map ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ⟶
    (modulesPseudofunctor.map ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex).op.toLoc).toFunctor.obj (coefficients secondIndex)}
  {diagonals : ∀ chartIndex, charts chartIndex ⟶ (squares chartIndex chartIndex).pullback} {hd₁ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₁ = 𝟙 _}
  {hd₂ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₂ = 𝟙 _}

/-- **Comparison with forwardMap glued object.** Let `sourceModule` over `baseScheme` effectively descend the descent datum
defined by gluing morphisms `transitionMaps`. Let `baseChange : changedBase ⟶ baseScheme` and `changedChartMaps chartIndex : changedCharts chartIndex ⟶ changedBase` be a family over the
`chartMaps chartIndex` (via `chartChanges chartIndex : changedCharts chartIndex ⟶ charts chartIndex`, and `secondChange chartIndex secondIndex` on the chosen pullbacks), for which
`modulesPseudofunctor.toDescentData changedChartMaps` is fully faithful. If `targetModule` over `changedBase` comes with isomorphisms
`comparisons chartIndex : (changedCoefficientMaps chartIndex)^* (coefficients chartIndex) ≅ (changedChartMaps chartIndex)^* targetModule`, where `changedCoefficientMaps chartIndex = chartChanges chartIndex ≫ coefficientMaps chartIndex`, inducing the pullbacks of the gluing
morphisms, then `baseChange^* sourceModule ≅ targetModule`. -/
theorem nonempty_map_iso_of_ofGlue {hself : GlueSelf (transitionMaps := transitionMaps) diagonals hd₁ hd₂}
    {hcoc : GlueCocycle tripleSquares transitionMaps} {sourceModule : modulesPseudofunctor.obj (.mk (op baseScheme))}
    (realization : (modulesPseudofunctor.toDescentData chartMaps).obj sourceModule ≅ (ofGlue tripleSquares coefficientMaps coefficients transitionMaps hself hcoc).descentData)
    {changedBase : Scheme.{schemeUniverse}} {changedCharts : Chart → Scheme.{schemeUniverse}} {changedChartMaps : ∀ chartIndex, changedCharts chartIndex ⟶ changedBase} (changedSquares : ∀ chartIndex secondIndex, ChosenPullback (changedChartMaps chartIndex) (changedChartMaps secondIndex))
    (hf' : ∀ sourceModule targetModule : modulesPseudofunctor.obj (.mk (op changedBase)),
      Function.Bijective ((modulesPseudofunctor.toDescentData changedChartMaps).map : (sourceModule ⟶ targetModule) → _))
    (baseChange : changedBase ⟶ baseScheme) (chartChanges : ∀ chartIndex, changedCharts chartIndex ⟶ charts chartIndex) (hr : ∀ chartIndex, chartChanges chartIndex ≫ chartMaps chartIndex = changedChartMaps chartIndex ≫ baseChange)
    (secondChange : ∀ chartIndex secondIndex, (changedSquares chartIndex secondIndex).pullback ⟶ (squares chartIndex secondIndex).pullback)
    (hr₂₁ : ∀ chartIndex secondIndex, secondChange chartIndex secondIndex ≫ (squares chartIndex secondIndex).p₁ = (changedSquares chartIndex secondIndex).p₁ ≫ chartChanges chartIndex)
    (hr₂₂ : ∀ chartIndex secondIndex, secondChange chartIndex secondIndex ≫ (squares chartIndex secondIndex).p₂ = (changedSquares chartIndex secondIndex).p₂ ≫ chartChanges secondIndex)
    (changedCoefficientMaps : ∀ chartIndex, changedCharts chartIndex ⟶ coefficientSchemes chartIndex) (hm : ∀ chartIndex, chartChanges chartIndex ≫ coefficientMaps chartIndex = changedCoefficientMaps chartIndex) (targetModule : modulesPseudofunctor.obj (.mk (op changedBase)))
    (comparisons : ∀ chartIndex, (modulesPseudofunctor.map (changedCoefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ≅
      (modulesPseudofunctor.map (changedChartMaps chartIndex).op.toLoc).toFunctor.obj targetModule)
    (hε : ∀ chartIndex secondIndex, pullHom (transitionMaps chartIndex secondIndex) (secondChange chartIndex secondIndex) ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex)
        (by rw [reassoc_of% (hr₂₁ chartIndex secondIndex), hm]) (by rw [reassoc_of% (hr₂₂ chartIndex secondIndex), hm]) =
      pullHom (comparisons chartIndex).hom (changedSquares chartIndex secondIndex).p₁ ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) (changedSquares chartIndex secondIndex).p rfl (by simp) ≫
        pullHom (comparisons secondIndex).inv (changedSquares chartIndex secondIndex).p₂ (changedSquares chartIndex secondIndex).p ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex) (by simp) rfl) :
    Nonempty ((modulesPseudofunctor.map baseChange.op.toLoc).toFunctor.obj sourceModule ≅ targetModule) := by
  let testLift (chartIndex : Chart) : (modulesPseudofunctor.map (chartMaps chartIndex).op.toLoc).toFunctor.obj sourceModule ≅
      (modulesPseudofunctor.map (coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) :=
    { hom := realization.hom.hom chartIndex
      inv := realization.inv.hom chartIndex
      hom_inv_id := by rw [← DescentData.comp_hom, realization.hom_inv_id]; rfl
      inv_hom_id := by rw [← DescentData.comp_hom, realization.inv_hom_id]; rfl }
  have hl : ∀ chartIndex secondIndex, pullHom (testLift chartIndex).hom (squares chartIndex secondIndex).p₁ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex) (by simp) rfl ≫
      transitionMaps chartIndex secondIndex = pullHom (testLift secondIndex).hom (squares chartIndex secondIndex).p₂ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex) (by simp) rfl :=
    pullHom_comp_eq_of_iso_ofGlue realization.hom
  let compositionComparisons (chartIndex : Chart) : (modulesPseudofunctor.map (changedChartMaps chartIndex).op.toLoc).toFunctor.obj ((modulesPseudofunctor.map baseChange.op.toLoc).toFunctor.obj sourceModule) ≅
      (modulesPseudofunctor.map (changedChartMaps chartIndex ≫ baseChange).op.toLoc).toFunctor.obj sourceModule :=
    { hom := (modulesPseudofunctor.mapComp' baseChange.op.toLoc (changedChartMaps chartIndex).op.toLoc (changedChartMaps chartIndex ≫ baseChange).op.toLoc
        (op_toLoc_comp_eq rfl)).inv.toNatTrans.app sourceModule
      inv := (modulesPseudofunctor.mapComp' baseChange.op.toLoc (changedChartMaps chartIndex).op.toLoc (changedChartMaps chartIndex ≫ baseChange).op.toLoc
        (op_toLoc_comp_eq rfl)).hom.toNatTrans.app sourceModule
      hom_inv_id := by simp
      inv_hom_id := by simp }
  let pulledComparisons (chartIndex : Chart) : (modulesPseudofunctor.map (changedChartMaps chartIndex ≫ baseChange).op.toLoc).toFunctor.obj sourceModule ≅
      (modulesPseudofunctor.map (changedCoefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) :=
    { hom := pullHom (testLift chartIndex).hom (chartChanges chartIndex) (changedChartMaps chartIndex ≫ baseChange) (changedCoefficientMaps chartIndex) (hr chartIndex) (hm chartIndex)
      inv := pullHom (testLift chartIndex).inv (chartChanges chartIndex) (changedCoefficientMaps chartIndex) (changedChartMaps chartIndex ≫ baseChange) (hm chartIndex) (hr chartIndex)
      hom_inv_id := by rw [← pullHom_comp, Iso.hom_inv_id, pullHom_id_eq_id]
      inv_hom_id := by rw [← pullHom_comp, Iso.inv_hom_id, pullHom_id_eq_id] }
  let localComparisons (chartIndex : Chart) := compositionComparisons chartIndex ≪≫ pulledComparisons chartIndex ≪≫ comparisons chartIndex
  have hq (chartIndex secondIndex : Chart) : secondChange chartIndex secondIndex ≫ (squares chartIndex secondIndex).p = (changedSquares chartIndex secondIndex).p ≫ baseChange := by
    rw [← (squares chartIndex secondIndex).hp₁, reassoc_of% (hr₂₁ chartIndex secondIndex), hr, ← Category.assoc, (changedSquares chartIndex secondIndex).hp₁]
  have hρ₁ (chartIndex secondIndex : Chart) : pullHom (pullHom (testLift chartIndex).hom (chartChanges chartIndex) (changedChartMaps chartIndex ≫ baseChange) (changedCoefficientMaps chartIndex) (hr chartIndex) (hm chartIndex))
      (changedSquares chartIndex secondIndex).p₁ ((changedSquares chartIndex secondIndex).p ≫ baseChange) ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) (by simp) rfl =
      pullHom (pullHom (testLift chartIndex).hom (squares chartIndex secondIndex).p₁ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex) (by simp) rfl)
        (secondChange chartIndex secondIndex) ((changedSquares chartIndex secondIndex).p ≫ baseChange) ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) (hq chartIndex secondIndex)
        (by rw [reassoc_of% (hr₂₁ chartIndex secondIndex), hm]) := by
    rw [pullHom_pullHom, pullHom_pullHom]
    exact pullHom_congr_left _ (hr₂₁ chartIndex secondIndex).symm _ _ _ _
  have hρ₂ (chartIndex secondIndex : Chart) : pullHom (pullHom (testLift secondIndex).hom (chartChanges secondIndex) (changedChartMaps secondIndex ≫ baseChange) (changedCoefficientMaps secondIndex) (hr secondIndex) (hm secondIndex))
      (changedSquares chartIndex secondIndex).p₂ ((changedSquares chartIndex secondIndex).p ≫ baseChange) ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex) (by simp) rfl =
      pullHom (pullHom (testLift secondIndex).hom (squares chartIndex secondIndex).p₂ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex) (by simp) rfl)
        (secondChange chartIndex secondIndex) ((changedSquares chartIndex secondIndex).p ≫ baseChange) ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex) (hq chartIndex secondIndex)
        (by rw [reassoc_of% (hr₂₂ chartIndex secondIndex), hm]) := by
    rw [pullHom_pullHom, pullHom_pullHom]
    exact pullHom_congr_left _ (hr₂₂ chartIndex secondIndex).symm _ _ _ _
  refine nonempty_iso_of_pullHom_eq changedSquares hf' localComparisons fun chartIndex secondIndex ↦ ?_
  simp only [localComparisons, compositionComparisons, pulledComparisons, Iso.trans_hom]
  rw [pullHom_comp _ _ (changedSquares chartIndex secondIndex).p₁ (changedSquares chartIndex secondIndex).p ((changedSquares chartIndex secondIndex).p ≫ baseChange) (changedSquares chartIndex secondIndex).p (by simp)
      (by simp) (by simp),
    pullHom_comp _ _ (changedSquares chartIndex secondIndex).p₁ ((changedSquares chartIndex secondIndex).p ≫ baseChange) ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) (changedSquares chartIndex secondIndex).p
      (by simp) rfl (by simp),
    pullHom_comp _ _ (changedSquares chartIndex secondIndex).p₂ (changedSquares chartIndex secondIndex).p ((changedSquares chartIndex secondIndex).p ≫ baseChange) (changedSquares chartIndex secondIndex).p (by simp)
      (by simp) (by simp),
    pullHom_comp _ _ (changedSquares chartIndex secondIndex).p₂ ((changedSquares chartIndex secondIndex).p ≫ baseChange) ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex) (changedSquares chartIndex secondIndex).p
      (by simp) rfl (by simp),
    pullHom_mapComp'_inv (hxh := rfl), pullHom_mapComp'_inv (hxh := rfl), hρ₁, hρ₂]
  have hε' : pullHom (comparisons chartIndex).hom (changedSquares chartIndex secondIndex).p₁ ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) (changedSquares chartIndex secondIndex).p rfl (by simp) =
      pullHom (transitionMaps chartIndex secondIndex) (secondChange chartIndex secondIndex) ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex) ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex)
        (by rw [reassoc_of% (hr₂₁ chartIndex secondIndex), hm]) (by rw [reassoc_of% (hr₂₂ chartIndex secondIndex), hm]) ≫
      pullHom (comparisons secondIndex).hom (changedSquares chartIndex secondIndex).p₂ ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex) (changedSquares chartIndex secondIndex).p rfl (by simp) := by
    rw [hε, Category.assoc, ← pullHom_comp, Iso.inv_hom_id, pullHom_id_eq_id, Category.comp_id]
  rw [hε', ← pullHom_comp_assoc, hl chartIndex secondIndex]

section IsoGlueHom

variable (squares) {targetModule : modulesPseudofunctor.obj (.mk (op baseScheme))}
  (comparisons : ∀ chartIndex, (modulesPseudofunctor.map (coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ≅ (modulesPseudofunctor.map (chartMaps chartIndex).op.toLoc).toFunctor.obj targetModule)

/-- The gluing morphisms induced by isomorphisms `comparisons chartIndex : (coefficientMaps chartIndex)^* (coefficients chartIndex) ≅ (chartMaps chartIndex)^* targetModule`. -/
noncomputable def isoGlueHom (chartIndex secondIndex : Chart) :
    (modulesPseudofunctor.map ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ⟶
      (modulesPseudofunctor.map ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex).op.toLoc).toFunctor.obj (coefficients secondIndex) :=
  pullHom (comparisons chartIndex).hom (squares chartIndex secondIndex).p₁ ((squares chartIndex secondIndex).p₁ ≫ coefficientMaps chartIndex) (squares chartIndex secondIndex).p rfl (by simp) ≫
    pullHom (comparisons secondIndex).inv (squares chartIndex secondIndex).p₂ (squares chartIndex secondIndex).p ((squares chartIndex secondIndex).p₂ ≫ coefficientMaps secondIndex) (by simp) rfl

variable {squares}

private lemma pullHom_isoGlueHom {firstIndex secondIndex : Chart}
    {testScheme : Scheme.{schemeUniverse}} (structureMap : testScheme ⟶ baseScheme)
    (firstMap : testScheme ⟶ charts firstIndex) (secondMap : testScheme ⟶ charts secondIndex)
    (firstFactorization : firstMap ≫ chartMaps firstIndex = structureMap)
    (secondFactorization : secondMap ≫ chartMaps secondIndex = structureMap)
    (testProjection : testScheme ⟶ (squares firstIndex secondIndex).pullback)
    (firstProjection : testProjection ≫ (squares firstIndex secondIndex).p₁ = firstMap)
    (secondProjection : testProjection ≫ (squares firstIndex secondIndex).p₂ = secondMap)
    (baseProjection : testProjection ≫ (squares firstIndex secondIndex).p = structureMap) :
    pullHom (isoGlueHom squares comparisons firstIndex secondIndex) testProjection
        (firstMap ≫ coefficientMaps firstIndex) (secondMap ≫ coefficientMaps secondIndex)
        (by rw [reassoc_of% firstProjection]) (by rw [reassoc_of% secondProjection]) =
      pullHom (comparisons firstIndex).hom firstMap (firstMap ≫ coefficientMaps firstIndex)
          structureMap rfl firstFactorization ≫
        pullHom (comparisons secondIndex).inv secondMap structureMap
          (secondMap ≫ coefficientMaps secondIndex) secondFactorization rfl := by
  dsimp only [isoGlueHom]
  rw [pullHom_comp _ _ testProjection (firstMap ≫ coefficientMaps firstIndex) structureMap
    (secondMap ≫ coefficientMaps secondIndex) (by rw [reassoc_of% firstProjection])
    baseProjection (by rw [reassoc_of% secondProjection]), pullHom_pullHom, pullHom_pullHom]
  exact congrArg₂ (fun first second => first ≫ second)
    (pullHom_congr_left (comparisons firstIndex).hom firstProjection _ _ _ _)
    (pullHom_congr_left (comparisons secondIndex).inv secondProjection _ _ _ _)

lemma glueSelf_isoGlueHom (diagonals : ∀ chartIndex, charts chartIndex ⟶ (squares chartIndex chartIndex).pullback)
    (hd₁ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₁ = 𝟙 _) (hd₂ : ∀ chartIndex, diagonals chartIndex ≫ (squares chartIndex chartIndex).p₂ = 𝟙 _) :
    GlueSelf (transitionMaps := isoGlueHom squares comparisons) diagonals hd₁ hd₂ := fun chartIndex ↦ by
  have hp : diagonals chartIndex ≫ (squares chartIndex chartIndex).p = chartMaps chartIndex := by rw [← (squares chartIndex chartIndex).hp₁, reassoc_of% (hd₁ chartIndex)]
  rw [glueSelfLHS, isoGlueHom,
    pullHom_comp _ _ _ _ (chartMaps chartIndex) _ (by rw [reassoc_of% (hd₁ chartIndex)]) (by simp [hp])
      (by rw [reassoc_of% (hd₂ chartIndex)]), pullHom_pullHom, pullHom_pullHom,
    pullHom_congr_left _ (hd₁ chartIndex) _ _ _ _, pullHom_congr_left (comparisons chartIndex).inv (hd₂ chartIndex) _ _ _ _,
    pullHom_id, pullHom_id, Iso.hom_inv_id]

lemma glueCocycle_isoGlueHom : GlueCocycle tripleSquares (isoGlueHom squares comparisons) :=
  fun firstIndex secondIndex thirdIndex => by
  have firstPullback := pullHom_isoGlueHom comparisons
    (tripleSquares firstIndex secondIndex thirdIndex).p
    (tripleSquares firstIndex secondIndex thirdIndex).p₁
    (tripleSquares firstIndex secondIndex thirdIndex).p₂ (by simp) (by simp)
    (tripleSquares firstIndex secondIndex thirdIndex).p₁₂
    (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) (by simp)
  have secondPullback := pullHom_isoGlueHom comparisons
    (tripleSquares firstIndex secondIndex thirdIndex).p
    (tripleSquares firstIndex secondIndex thirdIndex).p₂
    (tripleSquares firstIndex secondIndex thirdIndex).p₃ (by simp) (by simp)
    (tripleSquares firstIndex secondIndex thirdIndex).p₂₃
    (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) (by simp)
  have compositePullback := pullHom_isoGlueHom comparisons
    (tripleSquares firstIndex secondIndex thirdIndex).p
    (tripleSquares firstIndex secondIndex thirdIndex).p₁
    (tripleSquares firstIndex secondIndex thirdIndex).p₃ (by simp) (by simp)
    (tripleSquares firstIndex secondIndex thirdIndex).p₁₃
    (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _) (by simp)
  have middleIdentity :
      pullHom (comparisons secondIndex).inv
          (tripleSquares firstIndex secondIndex thirdIndex).p₂
          (tripleSquares firstIndex secondIndex thirdIndex).p
          ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ coefficientMaps secondIndex)
          (by simp) rfl ≫
        pullHom (comparisons secondIndex).hom
          (tripleSquares firstIndex secondIndex thirdIndex).p₂
          ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ coefficientMaps secondIndex)
          (tripleSquares firstIndex secondIndex thirdIndex).p rfl (by simp) = 𝟙 _ := by
    calc
      _ = pullHom ((comparisons secondIndex).inv ≫ (comparisons secondIndex).hom)
          (tripleSquares firstIndex secondIndex thirdIndex).p₂
          (tripleSquares firstIndex secondIndex thirdIndex).p
          (tripleSquares firstIndex secondIndex thirdIndex).p (by simp) (by simp) :=
        (pullHom_comp (comparisons secondIndex).inv (comparisons secondIndex).hom
          (tripleSquares firstIndex secondIndex thirdIndex).p₂
          (tripleSquares firstIndex secondIndex thirdIndex).p
          ((tripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ coefficientMaps secondIndex)
          (tripleSquares firstIndex secondIndex thirdIndex).p (by simp) rfl (by simp)).symm
      _ = pullHom (𝟙 _)
          (tripleSquares firstIndex secondIndex thirdIndex).p₂
          (tripleSquares firstIndex secondIndex thirdIndex).p
          (tripleSquares firstIndex secondIndex thirdIndex).p (by simp) (by simp) :=
        congrArg (fun coefficientMap => pullHom coefficientMap
          (tripleSquares firstIndex secondIndex thirdIndex).p₂
          (tripleSquares firstIndex secondIndex thirdIndex).p
          (tripleSquares firstIndex secondIndex thirdIndex).p (by simp) (by simp))
          (comparisons secondIndex).inv_hom_id
      _ = _ := pullHom_id_eq_id _ _ _
  dsimp only [glueCocLHS, glueCocRHS]
  exact comp_eq_of_inverse_factorizations _ _ _ _
    firstPullback secondPullback compositePullback middleIdentity

end IsoGlueHom

section Pull

variable {changedBase : Scheme.{schemeUniverse}} {changedCharts : Chart → Scheme.{schemeUniverse}} {changedChartMaps : ∀ chartIndex, changedCharts chartIndex ⟶ changedBase} {changedSquares : ∀ chartIndex secondIndex, ChosenPullback (changedChartMaps chartIndex) (changedChartMaps secondIndex)}
  {chartChanges : ∀ chartIndex, changedCharts chartIndex ⟶ charts chartIndex} (secondChange : ∀ chartIndex secondIndex, (changedSquares chartIndex secondIndex).pullback ⟶ (squares chartIndex secondIndex).pullback)
  (hr₂₁ : ∀ chartIndex secondIndex, secondChange chartIndex secondIndex ≫ (squares chartIndex secondIndex).p₁ = (changedSquares chartIndex secondIndex).p₁ ≫ chartChanges chartIndex)
  (hr₂₂ : ∀ chartIndex secondIndex, secondChange chartIndex secondIndex ≫ (squares chartIndex secondIndex).p₂ = (changedSquares chartIndex secondIndex).p₂ ≫ chartChanges secondIndex)
  {changedCoefficientMaps : ∀ chartIndex, changedCharts chartIndex ⟶ coefficientSchemes chartIndex} (hμ : ∀ chartIndex, chartChanges chartIndex ≫ coefficientMaps chartIndex = changedCoefficientMaps chartIndex)

/-- The pullback of gluing morphisms along morphisms `secondChange chartIndex secondIndex` between the chosen pullbacks of
two families, compatible with morphisms `chartChanges chartIndex` between their members. -/
noncomputable def pullGlue (chartIndex secondIndex : Chart) :
    (modulesPseudofunctor.map ((changedSquares chartIndex secondIndex).p₁ ≫ changedCoefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ⟶
      (modulesPseudofunctor.map ((changedSquares chartIndex secondIndex).p₂ ≫ changedCoefficientMaps secondIndex).op.toLoc).toFunctor.obj (coefficients secondIndex) :=
  pullHom (transitionMaps chartIndex secondIndex) (secondChange chartIndex secondIndex) _ _ (by rw [reassoc_of% (hr₂₁ chartIndex secondIndex), hμ])
    (by rw [reassoc_of% (hr₂₂ chartIndex secondIndex), hμ])

lemma pullHom_glueSelfLHS (changedDiagonals : ∀ chartIndex, changedCharts chartIndex ⟶ (changedSquares chartIndex chartIndex).pullback)
    (hd'₁ : ∀ chartIndex, changedDiagonals chartIndex ≫ (changedSquares chartIndex chartIndex).p₁ = 𝟙 _) (hd'₂ : ∀ chartIndex, changedDiagonals chartIndex ≫ (changedSquares chartIndex chartIndex).p₂ = 𝟙 _)
    (hd : ∀ chartIndex, changedDiagonals chartIndex ≫ secondChange chartIndex chartIndex = chartChanges chartIndex ≫ diagonals chartIndex) (chartIndex : Chart) :
    pullHom (glueSelfLHS transitionMaps diagonals hd₁ hd₂ chartIndex) (chartChanges chartIndex) (changedCoefficientMaps chartIndex) (changedCoefficientMaps chartIndex) (hμ chartIndex) (hμ chartIndex) =
      glueSelfLHS (pullGlue (transitionMaps := transitionMaps) secondChange hr₂₁ hr₂₂ hμ) changedDiagonals hd'₁ hd'₂ chartIndex := by
  rw [glueSelfLHS, glueSelfLHS, pullGlue, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (hd chartIndex).symm _ _ _ _

variable (tripleSquares) {changedTripleSquares : ∀ firstIndex secondIndex thirdIndex, ChosenPullback₃ (changedSquares firstIndex secondIndex) (changedSquares secondIndex thirdIndex) (changedSquares firstIndex thirdIndex)}
  (r₃ : ∀ firstIndex secondIndex thirdIndex, (changedTripleSquares firstIndex secondIndex thirdIndex).pullback ⟶ (tripleSquares firstIndex secondIndex thirdIndex).pullback)
  (h₁₂ : ∀ firstIndex secondIndex thirdIndex, r₃ firstIndex secondIndex thirdIndex ≫ (tripleSquares firstIndex secondIndex thirdIndex).p₁₂ = (changedTripleSquares firstIndex secondIndex thirdIndex).p₁₂ ≫ secondChange firstIndex secondIndex)
  (h₂₃ : ∀ firstIndex secondIndex thirdIndex, r₃ firstIndex secondIndex thirdIndex ≫ (tripleSquares firstIndex secondIndex thirdIndex).p₂₃ = (changedTripleSquares firstIndex secondIndex thirdIndex).p₂₃ ≫ secondChange secondIndex thirdIndex)
  (h₁₃ : ∀ firstIndex secondIndex thirdIndex, r₃ firstIndex secondIndex thirdIndex ≫ (tripleSquares firstIndex secondIndex thirdIndex).p₁₃ = (changedTripleSquares firstIndex secondIndex thirdIndex).p₁₃ ≫ secondChange firstIndex thirdIndex)
  (hr₃₁ : ∀ firstIndex secondIndex thirdIndex, r₃ firstIndex secondIndex thirdIndex ≫ (tripleSquares firstIndex secondIndex thirdIndex).p₁ = (changedTripleSquares firstIndex secondIndex thirdIndex).p₁ ≫ chartChanges firstIndex)
  (hr₃₂ : ∀ firstIndex secondIndex thirdIndex, r₃ firstIndex secondIndex thirdIndex ≫ (tripleSquares firstIndex secondIndex thirdIndex).p₂ = (changedTripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ chartChanges secondIndex)
  (hr₃₃ : ∀ firstIndex secondIndex thirdIndex, r₃ firstIndex secondIndex thirdIndex ≫ (tripleSquares firstIndex secondIndex thirdIndex).p₃ = (changedTripleSquares firstIndex secondIndex thirdIndex).p₃ ≫ chartChanges thirdIndex)

include h₁₂ h₂₃ hr₃₂ in
lemma pullHom_glueCocLHS (firstIndex secondIndex thirdIndex : Chart) :
    pullHom (glueCocLHS tripleSquares transitionMaps firstIndex secondIndex thirdIndex) (r₃ firstIndex secondIndex thirdIndex) ((changedTripleSquares firstIndex secondIndex thirdIndex).p₁ ≫ changedCoefficientMaps firstIndex)
        ((changedTripleSquares firstIndex secondIndex thirdIndex).p₃ ≫ changedCoefficientMaps thirdIndex) (by rw [reassoc_of% (hr₃₁ firstIndex secondIndex thirdIndex), hμ])
        (by rw [reassoc_of% (hr₃₃ firstIndex secondIndex thirdIndex), hμ]) =
      glueCocLHS changedTripleSquares (pullGlue (transitionMaps := transitionMaps) secondChange hr₂₁ hr₂₂ hμ) firstIndex secondIndex thirdIndex := by
  rw [glueCocLHS, glueCocLHS, pullHom_comp _ _ _ _ ((changedTripleSquares firstIndex secondIndex thirdIndex).p₂ ≫ changedCoefficientMaps secondIndex) _
    (by rw [reassoc_of% (hr₃₁ firstIndex secondIndex thirdIndex), hμ]) (by rw [reassoc_of% (hr₃₂ firstIndex secondIndex thirdIndex), hμ])
    (by rw [reassoc_of% (hr₃₃ firstIndex secondIndex thirdIndex), hμ]), pullGlue, pullGlue,
    pullHom_pullHom, pullHom_pullHom, pullHom_pullHom, pullHom_pullHom]
  exact congrArg₂ (· ≫ ·) (pullHom_congr_left _ (h₁₂ firstIndex secondIndex thirdIndex) _ _ _ _)
    (pullHom_congr_left _ (h₂₃ firstIndex secondIndex thirdIndex) _ _ _ _)

include h₁₃ in
lemma pullHom_glueCocRHS (firstIndex secondIndex thirdIndex : Chart) :
    pullHom (glueCocRHS tripleSquares transitionMaps firstIndex secondIndex thirdIndex) (r₃ firstIndex secondIndex thirdIndex) ((changedTripleSquares firstIndex secondIndex thirdIndex).p₁ ≫ changedCoefficientMaps firstIndex)
        ((changedTripleSquares firstIndex secondIndex thirdIndex).p₃ ≫ changedCoefficientMaps thirdIndex) (by rw [reassoc_of% (hr₃₁ firstIndex secondIndex thirdIndex), hμ])
        (by rw [reassoc_of% (hr₃₃ firstIndex secondIndex thirdIndex), hμ]) =
      glueCocRHS changedTripleSquares (pullGlue (transitionMaps := transitionMaps) secondChange hr₂₁ hr₂₂ hμ) firstIndex secondIndex thirdIndex := by
  rw [glueCocRHS, glueCocRHS, pullGlue, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (h₁₃ firstIndex secondIndex thirdIndex) _ _ _ _

end Pull

end Data

end AlgebraicGeometry.Scheme.Modules.Gluing
