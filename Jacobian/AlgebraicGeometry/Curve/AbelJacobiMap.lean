import Jacobian.AlgebraicGeometry.Curve.AbelJacobiDegree
import Jacobian.AlgebraicGeometry.Picard.RepresentedBaseChange

/-!
# The represented Abel–Jacobi morphism

The inverse diagonal ideal tensored with the constant-section ideal defines a
degree-zero Picard class. A representation of the degree-zero Picard sheaf
therefore gives its unique classifying morphism. The marked point maps to the
identity for every tensor-compatible representing group, and the morphism
commutes with extension of the ground field.

The parameter of the diagonal family is its first factor. A factor interchange
puts this family in the convention of the relative Picard presheaf, whose
parameter is the second factor.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules MonObj

namespace AlgebraicGeometry.Curve

variable {baseField : Type u} [Field baseField]

private theorem parameterSwap_isPullback (curve : Curve baseField) :
    IsPullback (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv
      (pullback.snd curve.carrier.hom curve.carrier.hom)
      (pullback.fst curve.carrier.hom curve.carrier.hom) (𝟙 curve.carrier.left) :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The diagonal-minus-constant class, with the parameter in the Picard convention. -/
def abelJacobiClass (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    (picardPresheaf curve.carrier.hom).obj (.op curve.carrier) :=
  Scheme.Pic.map (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv
    (Scheme.Pic.mk (abelJacobiFamily curve rationalPoint point_over))

/-- The Abel–Jacobi class has degree zero on every field-valued fibre. -/
theorem abelJacobiClass_mem (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    abelJacobiClass curve rationalPoint point_over ∈
      (picardSubfunctorDegree curve.carrier.hom 0).obj (.op curve.carrier) := by
  intro extensionField _ _ point
  let structureMap := pullback.snd curve.carrier.hom
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).hom
  let fiberMap := baseChangeMap curve.carrier.hom point ≫
    (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv
  letI : (pullback curve.carrier.hom
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).hom).Over
        (Spec (.of extensionField)) := ⟨structureMap⟩
  have square : IsPullback fiberMap structureMap
      (pullback.fst curve.carrier.hom curve.carrier.hom) point.left := by
    simpa only [Category.comp_id] using
      (isPullback_baseChangeMap curve.carrier.hom point).paste_horiz
        (parameterSwap_isPullback curve)
  change Scheme.Pic.degree extensionField
    (Scheme.Pic.map (baseChangeMap curve.carrier.hom point)
      (abelJacobiClass curve rationalPoint point_over)) = 0
  rw [abelJacobiClass, ← Scheme.Pic.map_comp, Scheme.Pic.map_mk, Scheme.Pic.degree_mk]
  exact degree_pullback_abelJacobiFamily_eq_zero curve rationalPoint point_over
    fiberMap structureMap point.left square

/-- The morphism classifying the actual diagonal-minus-constant family. -/
def abelJacobiMap (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {representing : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      representing) : curve.carrier ⟶ representing :=
  representation.homEquiv.symm
    ((toSheafify (Scheme.fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegree curve.carrier.hom 0).toFunctor).app (.op curve.carrier)
        ⟨abelJacobiClass curve rationalPoint point_over,
          abelJacobiClass_mem curve rationalPoint point_over⟩)

/-- The classifying morphism has the specified full Picard class. -/
theorem abelJacobiMap_classifies (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {representing : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      representing) :
    (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op curve.carrier)
        (representation.homEquiv (abelJacobiMap curve rationalPoint point_over representation)) =
      (toPicardFunctor curve.carrier.hom).app (.op curve.carrier)
        (abelJacobiClass curve rationalPoint point_over) := by
  rw [abelJacobiMap, Equiv.apply_symm_apply]
  exact picardFunctorDegreeι_app_toSheafify curve.carrier.hom 0 _

/-- The specified full Picard class determines the Abel–Jacobi morphism uniquely. -/
theorem abelJacobiMap_unique (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {representing : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      representing) (candidate : curve.carrier ⟶ representing)
    (classifies : (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op curve.carrier)
        (representation.homEquiv candidate) =
      (toPicardFunctor curve.carrier.hom).app (.op curve.carrier)
        (abelJacobiClass curve rationalPoint point_over)) :
    candidate = abelJacobiMap curve rationalPoint point_over representation := by
  apply representation.homEquiv.injective
  apply injective_picardFunctorDegreeι_app curve.carrier.hom 0 curve.carrier
  exact classifies.trans (abelJacobiMap_classifies curve rationalPoint point_over
    representation).symm

/-- Restriction of the classifier computes the pullback of its actual family. -/
theorem abelJacobiMap_classifies_pullback (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {representing : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      representing) {parameter : Over (Spec (.of baseField))}
    (restriction : parameter ⟶ curve.carrier) :
    (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op parameter)
        (representation.homEquiv
          (restriction ≫ abelJacobiMap curve rationalPoint point_over representation)) =
      (toPicardFunctor curve.carrier.hom).app (.op parameter)
        (Scheme.Pic.map (baseChangeMap curve.carrier.hom restriction)
          (abelJacobiClass curve rationalPoint point_over)) := by
  rw [representation.homEquiv_comp,
    (picardFunctorDegreeι curve.carrier.hom 0).hom.naturality_apply,
    abelJacobiMap_classifies, ← (toPicardFunctor curve.carrier.hom).naturality_apply]
  rfl

private theorem section_isPullback {source baseScheme parameter total : Scheme.{u}}
    {familyMap : total ⟶ source} {projection : total ⟶ parameter}
    {originalProjection : source ⟶ baseScheme} {parameterMap : parameter ⟶ baseScheme}
    (square : IsPullback familyMap projection originalProjection parameterMap)
    (originalSection : baseScheme ⟶ source)
    (section_eq : originalSection ≫ originalProjection = 𝟙 _)
    (pulledSection : parameter ⟶ total)
    (section_map : pulledSection ≫ familyMap = parameterMap ≫ originalSection)
    (section_projection : pulledSection ≫ projection = 𝟙 _) :
    IsPullback pulledSection parameterMap familyMap originalSection := by
  apply IsPullback.flip
  refine IsPullback.of_bot (h₃₁ := parameterMap) ?_ section_map.symm square
  change IsPullback parameterMap (pulledSection ≫ projection)
    (originalSection ≫ originalProjection) parameterMap
  rw [section_projection, section_eq]
  exact IsPullback.of_id_snd

private theorem ker_comap_of_isPullback {source total parameter baseScheme : Scheme.{u}}
    {originalSection : baseScheme ⟶ source} [IsClosedImmersion originalSection]
    {pulledSection : parameter ⟶ total} {familyMap : total ⟶ source}
    {parameterMap : parameter ⟶ baseScheme}
    (square : IsPullback pulledSection parameterMap familyMap originalSection) :
    originalSection.ker.comap familyMap = pulledSection.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion originalSection familyMap,
    ← Scheme.Hom.ker_comp_of_isIso square.isoPullback.hom,
    square.isoPullback_hom_fst]

private theorem section_closed {source baseScheme : Scheme.{u}}
    (projection : source ⟶ baseScheme) [IsSeparated projection]
    (originalSection : baseScheme ⟶ source)
    (section_eq : originalSection ≫ projection = 𝟙 _) :
    IsClosedImmersion originalSection := by
  haveI : IsClosedImmersion (originalSection ≫ projection) := by
    rw [section_eq]
    infer_instance
  exact IsClosedImmersion.of_comp originalSection projection

private def markedPullbackIso (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {total : Scheme.{u}}
    (familyMap : total ⟶ pullback curve.carrier.hom curve.carrier.hom)
    (projection : total ⟶ Spec (.of baseField))
    (square : IsPullback familyMap projection
      (pullback.fst curve.carrier.hom curve.carrier.hom) rationalPoint) :
    (Scheme.Modules.pullback familyMap).obj (abelJacobiFamily curve rationalPoint point_over) ≅
      Scheme.Modules.unit total := by
  haveI := section_closed (pullback.fst curve.carrier.hom curve.carrier.hom)
    (diagonal curve) (diagonal_fst curve)
  haveI := section_closed (pullback.fst curve.carrier.hom curve.carrier.hom)
    (constantSection curve rationalPoint point_over)
    (constantSection_fst curve rationalPoint point_over)
  have marked_eq : rationalPoint ≫ diagonal curve =
      rationalPoint ≫ constantSection curve rationalPoint point_over := by
    apply pullback.hom_ext
    · simp [diagonal, constantSection, Category.assoc]
    · simp only [diagonal, constantSection, Category.assoc,
        pullback.lift_snd, Category.comp_id]
      simpa only [Category.assoc, Category.id_comp] using
        (congrArg (fun morphism ↦ morphism ≫ rationalPoint) point_over).symm
  let pulledSection := square.lift (rationalPoint ≫ diagonal curve) (𝟙 _) (by simp)
  have diagonalSquare : IsPullback pulledSection rationalPoint familyMap (diagonal curve) :=
    section_isPullback square (diagonal curve) (diagonal_fst curve)
      pulledSection (square.lift_fst _ _ _) (square.lift_snd _ _ _)
  have constantSquare : IsPullback pulledSection rationalPoint familyMap
      (constantSection curve rationalPoint point_over) :=
    section_isPullback square (constantSection curve rationalPoint point_over)
      (constantSection_fst curve rationalPoint point_over) pulledSection
      ((square.lift_fst _ _ _).trans marked_eq) (square.lift_snd _ _ _)
  have diagonalRelative := isRelativeEffectiveCartier_diagonal curve
  have constantRelative := isRelativeEffectiveCartier_constantSection curve rationalPoint point_over
  have diagonalInvertible := diagonalRelative.1.comap_of_isPullback diagonalRelative.2 square
  have constantInvertible := constantRelative.1.comap_of_isPullback constantRelative.2 square
  let diagonalIso := Classical.choice
    (diagonalRelative.1.nonempty_pullback_toModules_iso familyMap diagonalInvertible)
  let constantIso := Classical.choice
    (constantRelative.1.nonempty_pullback_toModules_iso familyMap constantInvertible)
  have ideals_eq : ((constantSection curve rationalPoint point_over).ker.comap familyMap) =
      ((diagonal curve).ker.comap familyMap) :=
    (ker_comap_of_isPullback constantSquare).trans
      (ker_comap_of_isPullback diagonalSquare).symm
  let idealIso := constantIso ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.toModules ideals_eq) ≪≫ diagonalIso.symm
  exact Scheme.Modules.pullbackTensorObjIso familyMap _ _ ≪≫
    (Iso.refl _ ⊗ᵢ idealIso) ≪≫
    (Scheme.Modules.pullbackTensorObjIso familyMap _ _).symm ≪≫
    (Scheme.Modules.pullback familyMap).mapIso (diagonalDualTensorIsoUnit curve) ≪≫
    Scheme.Modules.pullbackObjUnitIso familyMap

/-- The actual family restricted to the marked parameter is trivial. -/
theorem abelJacobiClass_map_point (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    Scheme.Pic.map (baseChangeMap curve.carrier.hom
        (Over.homMk rationalPoint point_over :
          Over.mk (𝟙 (Spec (.of baseField))) ⟶ curve.carrier))
        (abelJacobiClass curve rationalPoint point_over) =
      Scheme.Pic.mk (Scheme.Modules.unit
        (pullback curve.carrier.hom (𝟙 (Spec (.of baseField))))) := by
  let point : Over.mk (𝟙 (Spec (.of baseField))) ⟶ curve.carrier :=
    Over.homMk rationalPoint point_over
  let familyMap := baseChangeMap curve.carrier.hom point ≫
    (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv
  have square : IsPullback familyMap
      (pullback.snd curve.carrier.hom (Over.mk (𝟙 (Spec (.of baseField)))).hom)
      (pullback.fst curve.carrier.hom curve.carrier.hom) rationalPoint := by
    have pasted := (isPullback_baseChangeMap curve.carrier.hom point).paste_horiz
      (parameterSwap_isPullback curve)
    have point_left : point.left = rationalPoint := rfl
    rw [Category.comp_id, point_left] at pasted
    exact pasted
  rw [abelJacobiClass, ← Scheme.Pic.map_comp, Scheme.Pic.map_mk]
  exact (Scheme.Pic.mk_eq_mk_iff _ _).2
    ⟨markedPullbackIso curve rationalPoint point_over familyMap _ square⟩

/-- Tensor-compatible representations send the marked point to the group identity. -/
theorem abelJacobiMap_point (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {representingGroup : CommGrp (Over (Spec (.of baseField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      representingGroup.X)
    (compatibility : PicardTensorCompatible curve.carrier.hom representingGroup representation) :
    (Over.homMk rationalPoint point_over : Over.mk (𝟙 _) ⟶ curve.carrier) ≫
        abelJacobiMap curve rationalPoint point_over representation = 1 := by
  apply representation.homEquiv.injective
  apply injective_picardFunctorDegreeι_app curve.carrier.hom 0 (Over.mk (𝟙 _))
  rw [abelJacobiMap_classifies_pullback, abelJacobiClass_map_point]
  exact (compatibility.1 _).symm

private def productMap {source baseScheme extendedSource extendedBase : Scheme.{u}}
    {structureMap : source ⟶ baseScheme} {extendedMap : extendedSource ⟶ extendedBase}
    {coefficientMap : extendedSource ⟶ source} {baseMap : extendedBase ⟶ baseScheme}
    (square : IsPullback coefficientMap extendedMap structureMap baseMap) :
    pullback extendedMap extendedMap ⟶ pullback structureMap structureMap :=
  pullback.lift (pullback.fst extendedMap extendedMap ≫ coefficientMap)
    (pullback.snd extendedMap extendedMap ≫ coefficientMap) (by
      simp only [Category.assoc, square.w]
      rw [← Category.assoc, ← Category.assoc, pullback.condition])

private theorem productMap_isPullback
    {source baseScheme extendedSource extendedBase : Scheme.{u}}
    {structureMap : source ⟶ baseScheme} {extendedMap : extendedSource ⟶ extendedBase}
    {coefficientMap : extendedSource ⟶ source} {baseMap : extendedBase ⟶ baseScheme}
    (square : IsPullback coefficientMap extendedMap structureMap baseMap) :
    IsPullback (productMap square) (pullback.fst extendedMap extendedMap)
      (pullback.fst structureMap structureMap) coefficientMap := by
  have outerSquare : IsPullback (productMap square ≫ pullback.snd structureMap structureMap)
      (pullback.fst extendedMap extendedMap) structureMap (coefficientMap ≫ structureMap) := by
    rw [show productMap square ≫ pullback.snd structureMap structureMap =
      pullback.snd extendedMap extendedMap ≫ coefficientMap from pullback.lift_snd _ _ _,
      square.w]
    exact (IsPullback.of_hasPullback extendedMap extendedMap).flip.paste_horiz square
  exact outerSquare.of_right (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback structureMap structureMap).flip

variable {extensionField : Type u} [Field extensionField] [Algebra baseField extensionField]

/-- The marked rational point on the actual field-extended curve. -/
def baseChangePoint (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    Spec (.of extensionField) ⟶ ((baseChange baseField extensionField).obj curve).carrier.left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)) ≫ rationalPoint)
    (𝟙 _) (by simp [Category.assoc, point_over])

/-- The extended marked point is a section over the extended field. -/
@[reassoc (attr := simp)]
theorem baseChangePoint_over (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    baseChangePoint (extensionField := extensionField) curve rationalPoint point_over ≫
      ((baseChange baseField extensionField).obj curve).carrier.hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

private def familyBaseChangeIso (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    (Scheme.Modules.pullback (productMap (IsPullback.of_hasPullback curve.carrier.hom
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))))).obj
        (abelJacobiFamily curve rationalPoint point_over) ≅
      abelJacobiFamily ((baseChange baseField extensionField).obj curve)
        (baseChangePoint curve rationalPoint point_over)
        (baseChangePoint_over curve rationalPoint point_over) := by
  let extended := (baseChange baseField extensionField).obj curve
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  let coefficientMap : extended.carrier.left ⟶ curve.carrier.left :=
    pullback.fst curve.carrier.hom fieldMap
  let square : IsPullback coefficientMap extended.carrier.hom curve.carrier.hom fieldMap :=
    IsPullback.of_hasPullback curve.carrier.hom fieldMap
  let familyMap := productMap square
  have familySquare := productMap_isPullback square
  haveI := section_closed (pullback.fst curve.carrier.hom curve.carrier.hom)
    (diagonal curve) (diagonal_fst curve)
  haveI := section_closed (pullback.fst curve.carrier.hom curve.carrier.hom)
    (constantSection curve rationalPoint point_over)
    (constantSection_fst curve rationalPoint point_over)
  have diagonal_map : diagonal extended ≫ familyMap = coefficientMap ≫ diagonal curve := by
    apply pullback.hom_ext <;>
      simp [diagonal, familyMap, productMap, Category.assoc] <;>
      exact Category.id_comp coefficientMap
  have point_projection : baseChangePoint curve rationalPoint point_over ≫ coefficientMap =
      fieldMap ≫ rationalPoint := by
    change pullback.lift (fieldMap ≫ rationalPoint) (𝟙 _) _ ≫
      pullback.fst curve.carrier.hom fieldMap = fieldMap ≫ rationalPoint
    exact pullback.lift_fst _ _ _
  have constant_map : constantSection extended (baseChangePoint curve rationalPoint point_over)
      (baseChangePoint_over curve rationalPoint point_over) ≫ familyMap =
        coefficientMap ≫ constantSection curve rationalPoint point_over := by
    apply pullback.hom_ext
    · simp [constantSection, familyMap, productMap, Category.assoc]
    · simp only [constantSection, familyMap, productMap, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc]
      refine (congrArg (fun morphism ↦ extended.carrier.hom ≫ morphism)
        point_projection).trans ?_
      simpa only [Category.assoc] using
        congrArg (fun morphism ↦ morphism ≫ rationalPoint) square.w.symm
  have diagonalSquare := section_isPullback familySquare (diagonal curve)
    (diagonal_fst curve) (diagonal extended) diagonal_map (diagonal_fst extended)
  have constantSquare := section_isPullback familySquare
    (constantSection curve rationalPoint point_over)
    (constantSection_fst curve rationalPoint point_over)
    (constantSection extended (baseChangePoint curve rationalPoint point_over)
      (baseChangePoint_over curve rationalPoint point_over)) constant_map
    (constantSection_fst extended _ _)
  have diagonal_eq := ker_comap_of_isPullback diagonalSquare
  have constant_eq := ker_comap_of_isPullback constantSquare
  have diagonalRelative := isRelativeEffectiveCartier_diagonal curve
  have constantRelative := isRelativeEffectiveCartier_constantSection curve rationalPoint point_over
  have diagonalInvertible := diagonalRelative.1.comap_of_isPullback diagonalRelative.2 familySquare
  have constantInvertible := constantRelative.1.comap_of_isPullback constantRelative.2 familySquare
  let diagonalIso := Classical.choice
    (diagonalRelative.1.nonempty_pullback_dual_toModules_iso familyMap diagonalInvertible)
  let constantIso := Classical.choice
    (constantRelative.1.nonempty_pullback_toModules_iso familyMap constantInvertible)
  exact Scheme.Modules.pullbackTensorObjIso familyMap _ _ ≪≫
    ((diagonalIso ≪≫ eqToIso (congrArg (fun ideal ↦ ideal.toModulesᵛ) diagonal_eq)) ⊗ᵢ
      (constantIso ≪≫ eqToIso (congrArg Scheme.IdealSheafData.toModules constant_eq)))

/-- The Abel–Jacobi classifier commutes with field extension and the represented
Picard comparison for arbitrary supplied tensor-compatible groups. -/
theorem abelJacobiMap_baseChange (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {sourceGroup : CommGrp (Over (Spec (.of baseField)))}
    {extendedGroup : CommGrp (Over (Spec (.of extensionField)))}
    (sourceRepresentation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      sourceGroup.X)
    (extendedRepresentation : (picardFunctorDegree
      ((baseChange baseField extensionField).obj curve).carrier.hom 0).obj.RepresentableBy
        extendedGroup.X)
    (sourceCompatibility : PicardTensorCompatible curve.carrier.hom sourceGroup
      sourceRepresentation)
    (extendedCompatibility : PicardTensorCompatible
      ((baseChange baseField extensionField).obj curve).carrier.hom extendedGroup
        extendedRepresentation) :
    (AlgebraicGeometry.baseChange baseField extensionField).map
        (abelJacobiMap curve rationalPoint point_over sourceRepresentation) ≫
      (PicardTensorCompatible.baseChangeIso sourceCompatibility extendedCompatibility).hom.hom.hom.hom =
    abelJacobiMap ((baseChange baseField extensionField).obj curve)
      (baseChangePoint curve rationalPoint point_over)
      (baseChangePoint_over curve rationalPoint point_over) extendedRepresentation := by
  let extended := (baseChange baseField extensionField).obj curve
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  let square : IsPullback (pullback.fst curve.carrier.hom fieldMap)
      extended.carrier.hom curve.carrier.hom fieldMap :=
    IsPullback.of_hasPullback curve.carrier.hom fieldMap
  let restriction : (Over.map fieldMap).obj extended.carrier ⟶ curve.carrier :=
    Over.homMk (pullback.fst curve.carrier.hom fieldMap) pullback.condition
  let sourceLine := (Scheme.Modules.pullback (baseChangeMap curve.carrier.hom restriction)).obj
    ((Scheme.Modules.pullback
      (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv).obj
        (abelJacobiFamily curve rationalPoint point_over))
  have adjoint_eq : baseChangeHomMulEquiv sourceGroup extended.carrier
      ((AlgebraicGeometry.baseChange baseField extensionField).map
        (abelJacobiMap curve rationalPoint point_over sourceRepresentation)) =
      restriction ≫ abelJacobiMap curve rationalPoint point_over sourceRepresentation := by
    apply Over.OverMorphism.ext
    change pullback.lift
      (pullback.fst curve.carrier.hom fieldMap ≫
        (abelJacobiMap curve rationalPoint point_over sourceRepresentation).left)
      (pullback.snd curve.carrier.hom fieldMap)
      (by rw [Category.assoc, Over.w, pullback.condition]) ≫
      pullback.fst sourceGroup.X.hom fieldMap =
      pullback.fst curve.carrier.hom fieldMap ≫
        (abelJacobiMap curve rationalPoint point_over sourceRepresentation).left
    exact pullback.lift_fst _ _ _
  have sourceClassifies : (picardFunctorDegreeι curve.carrier.hom 0).hom.app
      (.op ((Over.map fieldMap).obj extended.carrier))
      (sourceRepresentation.homEquiv
        (baseChangeHomMulEquiv sourceGroup extended.carrier
          ((AlgebraicGeometry.baseChange baseField extensionField).map
            (abelJacobiMap curve rationalPoint point_over sourceRepresentation)))) =
      (toPicardFunctor curve.carrier.hom).app _ (Scheme.Pic.mk sourceLine) := by
    rw [adjoint_eq]
    simpa only [abelJacobiClass, Scheme.Pic.map_mk] using
      abelJacobiMap_classifies_pullback curve rationalPoint point_over sourceRepresentation restriction
  have classifies := PicardTensorCompatible.baseChangeIso_class
    sourceCompatibility extendedCompatibility extended.carrier
      ((AlgebraicGeometry.baseChange baseField extensionField).map
        (abelJacobiMap curve rationalPoint point_over sourceRepresentation))
      sourceLine sourceClassifies
  apply abelJacobiMap_unique extended (baseChangePoint curve rationalPoint point_over)
    (baseChangePoint_over curve rationalPoint point_over) extendedRepresentation
  refine classifies.trans (congrArg ((toPicardFunctor extended.carrier.hom).app
    (.op extended.carrier)) ?_)
  have comparison_eq : (pullbackIsoOfIsPullback square extended.carrier).hom ≫
      baseChangeMap curve.carrier.hom restriction ≫
        (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv =
      (pullbackSymmetry extended.carrier.hom extended.carrier.hom).inv ≫ productMap square := by
    apply pullback.hom_ext <;>
      simp [Category.assoc, baseChangeMap, restriction, productMap]
  change Scheme.Pic.mk ((Scheme.Modules.pullback
      (pullbackIsoOfIsPullback square extended.carrier).hom).obj sourceLine) =
    Scheme.Pic.map (pullbackSymmetry extended.carrier.hom extended.carrier.hom).inv
      (Scheme.Pic.mk (abelJacobiFamily extended _ _))
  calc
    _ = Scheme.Pic.map (pullbackIsoOfIsPullback square extended.carrier).hom
        (Scheme.Pic.map (baseChangeMap curve.carrier.hom restriction)
          (Scheme.Pic.map (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv
            (Scheme.Pic.mk (abelJacobiFamily curve rationalPoint point_over)))) := by
      rw [Scheme.Pic.map_mk, Scheme.Pic.map_mk, Scheme.Pic.map_mk]
    _ = Scheme.Pic.map ((pullbackIsoOfIsPullback square extended.carrier).hom ≫
        baseChangeMap curve.carrier.hom restriction ≫
          (pullbackSymmetry curve.carrier.hom curve.carrier.hom).inv)
        (Scheme.Pic.mk (abelJacobiFamily curve rationalPoint point_over)) := by
      rw [Scheme.Pic.map_comp, Scheme.Pic.map_comp]
    _ = Scheme.Pic.map
        ((pullbackSymmetry extended.carrier.hom extended.carrier.hom).inv ≫ productMap square)
        (Scheme.Pic.mk (abelJacobiFamily curve rationalPoint point_over)) :=
      congrArg (fun morphism ↦ Scheme.Pic.map morphism
        (Scheme.Pic.mk (abelJacobiFamily curve rationalPoint point_over))) comparison_eq
    _ = _ := by
      rw [Scheme.Pic.map_comp, Scheme.Pic.map_mk]
      apply congrArg
        (Scheme.Pic.map (pullbackSymmetry extended.carrier.hom extended.carrier.hom).inv)
      exact (Scheme.Pic.mk_eq_mk_iff _ _).2
        ⟨familyBaseChangeIso curve rationalPoint point_over⟩

end AlgebraicGeometry.Curve
