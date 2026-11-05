import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Fibres

/-!
# The endpoint divisors of a pencil

The coordinate-normalized trivializations give isomorphisms of the actual
pulled section arrows at the two endpoints. Their zero ideals are therefore
the original zero ideals, not just closed sets with the same support.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open CategoryTheory.Limits (zero_comp comp_zero)
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  (structureMap : source ⟶ Spec (.of baseField))

/-- The copy of the source over a normalized endpoint of the parameter line. -/
def endpointInclusion (coordinate : ULift.{u} (Fin 2)) :
    source ⟶ Limits.pullback structureMap
      (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) :=
  Limits.pullback.lift (𝟙 source) (structureMap ≫ endpoint coordinate) (by
    simp only [Category.assoc, endpoint_over, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem endpointInclusion_curve (coordinate : ULift.{u} (Fin 2)) :
    endpointInclusion structureMap coordinate ≫ Limits.pullback.fst _ _ = 𝟙 source :=
  Limits.pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem endpointInclusion_parameter (coordinate : ULift.{u} (Fin 2)) :
    endpointInclusion structureMap coordinate ≫ Limits.pullback.snd _ _ =
      structureMap ≫ endpoint coordinate := Limits.pullback.lift_snd ..

/-- The comparison with the source module at an endpoint. -/
def endpointCurveIso (coordinate : ULift.{u} (Fin 2)) (moduleSheaf : source.Modules) :
    (pullback (endpointInclusion structureMap coordinate)).obj
      ((pullback (Limits.pullback.fst _ _)).obj moduleSheaf) ≅ moduleSheaf :=
  pullbackCompOfEq (endpointInclusion structureMap coordinate) (Limits.pullback.fst _ _)
    (𝟙 source) (endpointInclusion_curve structureMap coordinate) moduleSheaf ≪≫
      (pullbackId source).app moduleSheaf

@[reassoc]
theorem endpointCurveIso_naturality (coordinate : ULift.{u} (Fin 2))
    {firstModule secondModule : source.Modules} (moduleMap : firstModule ⟶ secondModule) :
    (pullback (endpointInclusion structureMap coordinate)).map
        ((pullback (Limits.pullback.fst _ _)).map moduleMap) ≫
          (endpointCurveIso structureMap coordinate secondModule).hom =
      (endpointCurveIso structureMap coordinate firstModule).hom ≫ moduleMap := by
  dsimp only [endpointCurveIso, Iso.trans_hom]
  rw [← Category.assoc, pullbackCompOfEq_naturality, Category.assoc]
  have naturality : (pullback (𝟙 source)).map moduleMap ≫
      ((pullbackId source).app secondModule).hom =
        ((pullbackId source).app firstModule).hom ≫ moduleMap :=
    (pullbackId source).hom.naturality moduleMap
  rw [naturality, Category.assoc]

/-- The parameter's structure-module factor at an endpoint. -/
def endpointParameterSourceIso (coordinate : ULift.{u} (Fin 2)) :
    (pullback (endpointInclusion structureMap coordinate)).obj
      ((pullback (Limits.pullback.snd _ _)).obj
        (unit (ProjectiveLine.relativeLine (Spec (.of baseField))))) ≅ unit source :=
  parameterPullbackIso (endpointInclusion structureMap coordinate) (Limits.pullback.snd _ _)
    structureMap (endpoint coordinate) (endpointInclusion_parameter structureMap coordinate)
    (unit (ProjectiveLine.relativeLine (Spec (.of baseField)))) ≪≫
      (pullback structureMap).mapIso (pullbackObjUnitIso (endpoint coordinate)) ≪≫
        pullbackObjUnitIso structureMap

/-- The parameter's twisting-line factor, normalized by its nonzero coordinate. -/
def endpointParameterLineIso (coordinate : ULift.{u} (Fin 2)) :
    (pullback (endpointInclusion structureMap coordinate)).obj
      ((pullback (Limits.pullback.snd _ _)).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)) ≅ unit source :=
  parameterPullbackIso (endpointInclusion structureMap coordinate) (Limits.pullback.snd _ _)
    structureMap (endpoint coordinate) (endpointInclusion_parameter structureMap coordinate)
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1) ≪≫
      (pullback structureMap).mapIso (endpointCoordinateIso coordinate) ≪≫
        pullbackObjUnitIso structureMap

private theorem endpointParameter_conjugate
    (endpointCoordinate coordinate : ULift.{u} (Fin 2)) :
    (endpointParameterSourceIso structureMap endpointCoordinate).inv ≫
      (pullback (endpointInclusion structureMap endpointCoordinate)).map
        ((pullback (Limits.pullback.snd _ _)).map
          (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
            coordinate 1)) ≫ (endpointParameterLineIso structureMap endpointCoordinate).hom =
      (pullbackObjUnitIso structureMap).inv ≫
        (pullback structureMap).map (parameterCoefficient (endpoint endpointCoordinate)
          (endpointCoordinateIso endpointCoordinate)
          (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
            coordinate 1)) ≫ (pullbackObjUnitIso structureMap).hom := by
  let inclusion := endpointInclusion structureMap endpointCoordinate
  let projection := Limits.pullback.snd structureMap
    (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))
  let coordinateMap := ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2))
    (Spec (.of baseField)) coordinate 1
  let unitComparison := parameterPullbackIso inclusion projection structureMap
    (endpoint endpointCoordinate) (endpointInclusion_parameter structureMap endpointCoordinate)
    (unit (ProjectiveLine.relativeLine (Spec (.of baseField))))
  let lineComparison := parameterPullbackIso inclusion projection structureMap
    (endpoint endpointCoordinate) (endpointInclusion_parameter structureMap endpointCoordinate)
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)
  have naturality := parameterPullbackIso_naturality inclusion projection structureMap
    (endpoint endpointCoordinate) (endpointInclusion_parameter structureMap endpointCoordinate)
    coordinateMap
  have conjugation : unitComparison.inv ≫
      (pullback inclusion).map ((pullback projection).map coordinateMap) ≫ lineComparison.hom =
        (pullback structureMap).map ((pullback (endpoint endpointCoordinate)).map coordinateMap) :=
    (congrArg (fun moduleMap ↦ unitComparison.inv ≫ moduleMap) naturality).trans
      (Iso.inv_hom_id_assoc unitComparison
        ((pullback structureMap).map ((pullback (endpoint endpointCoordinate)).map coordinateMap)))
  have comparison := congrArg
    (fun moduleMap : (pullback structureMap).obj
        ((pullback (endpoint endpointCoordinate)).obj
          (unit (ProjectiveLine.relativeLine (Spec (.of baseField))))) ⟶
        (pullback structureMap).obj ((pullback (endpoint endpointCoordinate)).obj
          (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)) ↦
      (pullbackObjUnitIso structureMap).inv ≫
        (pullback structureMap).map (pullbackObjUnitIso (endpoint endpointCoordinate)).inv ≫
          moduleMap ≫ (pullback structureMap).map (endpointCoordinateIso endpointCoordinate).hom ≫
            (pullbackObjUnitIso structureMap).hom) conjugation
  simpa only [unitComparison, lineComparison, inclusion, projection, coordinateMap,
    endpointParameterSourceIso, endpointParameterLineIso, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, parameterCoefficient,
    Functor.map_comp, Category.assoc] using comparison

/-- The source-arrow comparison at an endpoint. -/
def endpointSourceIso (coordinate : ULift.{u} (Fin 2)) :
    (pullback (endpointInclusion structureMap coordinate)).obj
      (unit (Limits.pullback structureMap
        (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)))) ≅ unit source :=
  pulledSourceIso (endpointInclusion structureMap coordinate)
    (Limits.pullback.fst _ _) (Limits.pullback.snd _ _) ≪≫
      (endpointCurveIso structureMap coordinate (unit source) ⊗ᵢ
        endpointParameterSourceIso structureMap coordinate) ≪≫ ρ_ (unit source)

/-- The twisting line of the pencil restricts to its original line at each endpoint. -/
def endpointLineIso (coordinate : ULift.{u} (Fin 2)) (lineBundle : source.Modules) :
    (pullback (endpointInclusion structureMap coordinate)).obj
      (projectiveLineBundle structureMap lineBundle) ≅ lineBundle :=
  (Functor.Monoidal.μIso (pullback (endpointInclusion structureMap coordinate))
    ((pullback (Limits.pullback.fst _ _)).obj lineBundle)
    ((pullback (Limits.pullback.snd _ _)).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1))).symm ≪≫
        (endpointCurveIso structureMap coordinate lineBundle ⊗ᵢ
          endpointParameterLineIso structureMap coordinate) ≪≫ ρ_ lineBundle

private theorem endpoint_comparison
    (endpointCoordinate otherCoordinate : ULift.{u} (Fin 2))
    (distinct : otherCoordinate ≠ endpointCoordinate)
    {lineBundle : source.Modules} (firstSection secondSection : unit source ⟶ lineBundle) :
    (endpointSourceIso structureMap endpointCoordinate).inv ≫
      (pullback (endpointInclusion structureMap endpointCoordinate)).map
        (pencilSection (Limits.pullback.fst _ _) (Limits.pullback.snd _ _)
          firstSection secondSection
          (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
            endpointCoordinate 1)
          (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
            otherCoordinate 1)) ≫
      (endpointLineIso structureMap endpointCoordinate lineBundle).hom = firstSection := by
  let inclusion := endpointInclusion structureMap endpointCoordinate
  let sourceProjection := Limits.pullback.fst structureMap
    (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))
  let parameterProjection := Limits.pullback.snd structureMap
    (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))
  let sourceUnitIso := endpointCurveIso structureMap endpointCoordinate (unit source)
  let sourceLineIso := endpointCurveIso structureMap endpointCoordinate lineBundle
  let parameterUnitIso := endpointParameterSourceIso structureMap endpointCoordinate
  let parameterLineIso := endpointParameterLineIso structureMap endpointCoordinate
  have sectionComparison (sectionMap : unit source ⟶ lineBundle) :
      sourceUnitIso.inv ≫ (pullback inclusion).map
          ((pullback sourceProjection).map sectionMap) ≫ sourceLineIso.hom = sectionMap := by
    have naturality := endpointCurveIso_naturality structureMap endpointCoordinate sectionMap
    exact (congrArg (fun moduleMap ↦ sourceUnitIso.inv ≫ moduleMap) naturality).trans
      (Iso.inv_hom_id_assoc sourceUnitIso sectionMap)
  have firstCoefficient : parameterUnitIso.inv ≫ (pullback inclusion).map
      ((pullback parameterProjection).map
        (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
          endpointCoordinate 1)) ≫ parameterLineIso.hom = 𝟙 _ := by
    rw [endpointParameter_conjugate, endpointCoefficient_self,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  have secondCoefficient : parameterUnitIso.inv ≫ (pullback inclusion).map
      ((pullback parameterProjection).map
        (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
          otherCoordinate 1)) ≫ parameterLineIso.hom = 0 := by
    rw [endpointParameter_conjugate, endpointCoefficient_other _ _ distinct,
      Functor.map_zero, zero_comp, comp_zero]
  have tensorConjugation
      (firstMap secondMap : (pullback inclusion).obj
          ((pullback sourceProjection).obj (unit source)) ⟶
        (pullback inclusion).obj ((pullback sourceProjection).obj lineBundle))
      (firstScalar secondScalar : (pullback inclusion).obj
          ((pullback parameterProjection).obj
            (unit (ProjectiveLine.relativeLine (Spec (.of baseField))))) ⟶
        (pullback inclusion).obj ((pullback parameterProjection).obj
          (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1))) :
      (sourceUnitIso ⊗ᵢ parameterUnitIso).inv ≫
        (firstMap ⊗ₘ firstScalar + secondMap ⊗ₘ secondScalar) ≫
          (sourceLineIso ⊗ᵢ parameterLineIso).hom =
      (sourceUnitIso.inv ≫ firstMap ≫ sourceLineIso.hom) ⊗ₘ
        (parameterUnitIso.inv ≫ firstScalar ≫ parameterLineIso.hom) +
      (sourceUnitIso.inv ≫ secondMap ≫ sourceLineIso.hom) ⊗ₘ
        (parameterUnitIso.inv ≫ secondScalar ≫ parameterLineIso.hom) := by
    simp only [Preadditive.comp_add, Preadditive.add_comp, tensorIso_inv,
      tensorIso_hom, tensorHom_comp_tensorHom, Category.assoc]
  calc
    _ = (ρ_ (unit source)).inv ≫ ((sourceUnitIso ⊗ᵢ parameterUnitIso).inv ≫
        ((pulledSourceIso inclusion sourceProjection parameterProjection).inv ≫
          (pullback inclusion).map (pencilSection sourceProjection parameterProjection
            firstSection secondSection
            (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
              endpointCoordinate 1)
            (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
              otherCoordinate 1)) ≫
          (Functor.Monoidal.μIso (pullback inclusion)
            ((pullback sourceProjection).obj lineBundle)
            ((pullback parameterProjection).obj
              (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1))).inv) ≫
        (sourceLineIso ⊗ᵢ parameterLineIso).hom) ≫ (ρ_ lineBundle).hom := by
      simp only [inclusion, sourceProjection, parameterProjection, sourceUnitIso,
        sourceLineIso, parameterUnitIso, parameterLineIso, endpointSourceIso, endpointLineIso,
        Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = (ρ_ (unit source)).inv ≫ (firstSection ⊗ₘ 𝟙 (unit source)) ≫ (ρ_ lineBundle).hom := by
      have pulledFormula := pulledSourceIso_inv_comp inclusion sourceProjection parameterProjection
        (sourceLine := lineBundle)
        (parameterLine := ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)
        firstSection secondSection
        (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
          endpointCoordinate 1)
        (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
          otherCoordinate 1)
      have transportedFormula := congrArg
        (fun tensorMap :
            (pullback inclusion).obj ((pullback sourceProjection).obj (unit source)) ⊗
              (pullback inclusion).obj ((pullback parameterProjection).obj
                (unit (ProjectiveLine.relativeLine (Spec (.of baseField))))) ⟶
            (pullback inclusion).obj ((pullback sourceProjection).obj lineBundle) ⊗
              (pullback inclusion).obj ((pullback parameterProjection).obj
                (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)) ↦
          (ρ_ (unit source)).inv ≫
            ((sourceUnitIso ⊗ᵢ parameterUnitIso).inv ≫ tensorMap ≫
              (sourceLineIso ⊗ᵢ parameterLineIso).hom) ≫ (ρ_ lineBundle).hom) pulledFormula
      refine transportedFormula.trans ?_
      rw [tensorConjugation, sectionComparison firstSection,
        sectionComparison secondSection, firstCoefficient, secondCoefficient]
      have zeroTensor : secondSection ⊗ₘ (0 : unit source ⟶ unit source) = 0 := by
        apply (cancel_epi (λ_ (unit source)).inv).mp
        rw [comp_zero]
        apply unit_hom_ext
        rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, leftUnitor_inv_app]
        change (secondSection ⊗ₘ (0 : unit source ⟶ unit source)).app ⊤
          (tmulSection (unitSectionsEquiv ⊤ (1 : Γ(source, ⊤)))
            (unitSectionsEquiv ⊤ (1 : Γ(source, ⊤)))) = 0
        rw [tensorHom_app_tmulSection]
        change tmulSection (secondSection.app ⊤ (1 : Γ(source, ⊤)))
          (0 : Γ(unit source, ⊤)) = 0
        exact tmulSection_zero _
      rw [zeroTensor, add_zero]
    _ = firstSection := by
      have naturality : (firstSection ⊗ₘ 𝟙 (unit source)) ≫ (ρ_ lineBundle).hom =
          (ρ_ (unit source)).hom ≫ firstSection :=
        (congrArg (fun moduleMap : unit source ⊗ unit source ⟶ lineBundle ⊗ unit source ↦
          moduleMap ≫ (ρ_ lineBundle).hom) (tensorHom_id firstSection (unit source))).trans
            (rightUnitor_naturality firstSection)
      exact (congrArg (fun moduleMap : unit source ⊗ unit source ⟶ lineBundle ↦
        (ρ_ (unit source)).inv ≫ moduleMap) naturality).trans
          (Iso.inv_hom_id_assoc (ρ_ (unit source)) firstSection)

/-- At the first endpoint the pencil is the first section, as a module arrow. -/
theorem projectiveLineSection_first {lineBundle : source.Modules}
    (firstSection secondSection : unit source ⟶ lineBundle) :
    (endpointSourceIso structureMap ⟨0⟩).inv ≫
      (pullback (endpointInclusion structureMap ⟨0⟩)).map
        (projectiveLineSection structureMap firstSection secondSection) ≫
      (endpointLineIso structureMap ⟨0⟩ lineBundle).hom = firstSection :=
  endpoint_comparison structureMap ⟨0⟩ ⟨1⟩ (by decide) firstSection secondSection

/-- At the second endpoint the pencil is the second section, as a module arrow. -/
theorem projectiveLineSection_second {lineBundle : source.Modules}
    (firstSection secondSection : unit source ⟶ lineBundle) :
    (endpointSourceIso structureMap ⟨1⟩).inv ≫
      (pullback (endpointInclusion structureMap ⟨1⟩)).map
        (projectiveLineSection structureMap firstSection secondSection) ≫
      (endpointLineIso structureMap ⟨1⟩ lineBundle).hom = secondSection := by
  have swap : projectiveLineSection structureMap firstSection secondSection =
      pencilSection (Limits.pullback.fst _ _) (Limits.pullback.snd _ _)
        secondSection firstSection
        (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) ⟨1⟩ 1)
        (ProjectiveSpace.twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) ⟨0⟩ 1) := by
    dsimp only [projectiveLineSection, pencilSection]
    rw [add_comm]
  rw [swap]
  exact endpoint_comparison structureMap ⟨1⟩ ⟨0⟩ (by decide) secondSection firstSection

/-- The first endpoint is exactly the zero ideal of the first section. -/
theorem projectiveLineIdeal_first {lineBundle : source.Modules} [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle) :
    (projectiveLineIdeal structureMap firstSection secondSection).comap
      (endpointInclusion structureMap ⟨0⟩) = firstSection.zeroLocus := by
  rw [projectiveLineIdeal, Hom.comap_zeroLocus]
  apply Hom.zeroLocus_eq_of_arrowIso
  refine Arrow.isoMk (endpointSourceIso structureMap ⟨0⟩)
    (endpointLineIso structureMap ⟨0⟩ lineBundle) ?_
  change (endpointSourceIso structureMap ⟨0⟩).hom ≫ firstSection =
    (pullback (endpointInclusion structureMap ⟨0⟩)).map
      (projectiveLineSection structureMap firstSection secondSection) ≫
        (endpointLineIso structureMap ⟨0⟩ lineBundle).hom
  apply (cancel_epi (endpointSourceIso structureMap ⟨0⟩).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (projectiveLineSection_first structureMap firstSection secondSection).symm

/-- The second endpoint is exactly the zero ideal of the second section. -/
theorem projectiveLineIdeal_second {lineBundle : source.Modules} [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle) :
    (projectiveLineIdeal structureMap firstSection secondSection).comap
      (endpointInclusion structureMap ⟨1⟩) = secondSection.zeroLocus := by
  rw [projectiveLineIdeal, Hom.comap_zeroLocus]
  apply Hom.zeroLocus_eq_of_arrowIso
  refine Arrow.isoMk (endpointSourceIso structureMap ⟨1⟩)
    (endpointLineIso structureMap ⟨1⟩ lineBundle) ?_
  change (endpointSourceIso structureMap ⟨1⟩).hom ≫ secondSection =
    (pullback (endpointInclusion structureMap ⟨1⟩)).map
      (projectiveLineSection structureMap firstSection secondSection) ≫
        (endpointLineIso structureMap ⟨1⟩ lineBundle).hom
  apply (cancel_epi (endpointSourceIso structureMap ⟨1⟩).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (projectiveLineSection_second structureMap firstSection secondSection).symm

end AlgebraicGeometry.SectionPencil
