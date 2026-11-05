import Jacobian.AlgebraicGeometry.AbelianVariety.RationalCurves
import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Endpoints
import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange
import Jacobian.AlgebraicGeometry.Picard.DegreeTranslation

/-!
# The Hilbert family of an independent pencil

The tensor factor from the parameter line does not change fibre degrees.
Together with residue-fibre nonvanishing, this constructs a finite flat divisor
over the whole projective line. Its two endpoint ideals are the prescribed zero
ideals. Every morphism from a representing Hilbert scheme to an abelian variety
therefore has the same value on these endpoints.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]

/-- The Picard class of the actual external tensor product defining the pencil. -/
theorem projectiveLineBundle_class (lineBundle : source.Modules) [lineBundle.IsInvertible] :
    Scheme.Pic.mk (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle) =
      Scheme.Pic.map (Limits.pullback.fst (source ↘ Spec (.of baseField))
          (ProjectiveLine.relativeLineOver baseField).hom) (Scheme.Pic.mk lineBundle) *
        Scheme.Pic.map (Limits.pullback.snd (source ↘ Spec (.of baseField))
          (ProjectiveLine.relativeLineOver baseField).hom)
            (@Scheme.Pic.mk (ProjectiveLine.relativeLine (Spec (.of baseField)))
              (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)
              (ProjectiveSpace.isInvertible_twist (ULift.{u} (Fin 2))
                (Spec (.of baseField)) 1)) := by
  letI := ProjectiveSpace.isInvertible_twist (ULift.{u} (Fin 2))
    (Spec (.of baseField)) 1
  dsimp only [projectiveLineBundle, pencilLine, ProjectiveLine.relativeLineOver,
    ProjectiveLine.relativeLine, Over.mk, Over.hom, CostructuredArrow.mk]
  rw [Scheme.Pic.mk_tensorObj, ← Scheme.Pic.map_mk, ← Scheme.Pic.map_mk]

/-- The parameter line contributes no degree on any field-valued fibre. -/
theorem projectiveLineBundle_fieldDegree [IsProper (source ↘ Spec (.of baseField))]
    (lineBundle : source.Modules) [lineBundle.IsInvertible]
    {extensionField : Type u} [Field extensionField] [Algebra baseField extensionField]
    (parameterPoint : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap baseField extensionField))) ⟶ ProjectiveLine.relativeLineOver baseField) :
    picardFibreDegree (source ↘ Spec (.of baseField))
      (T := ProjectiveLine.relativeLineOver baseField)
      (Scheme.Pic.mk (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle))
      parameterPoint = lineBundle.degree baseField := by
  let firstClass : (Limits.pullback (source ↘ Spec (.of baseField))
      (ProjectiveLine.relativeLineOver baseField).hom).Pic :=
    Scheme.Pic.map (Limits.pullback.fst (source ↘ Spec (.of baseField))
      (ProjectiveLine.relativeLineOver baseField).hom) (Scheme.Pic.mk lineBundle)
  let parameterClass : (ProjectiveLine.relativeLineOver baseField).left.Pic :=
    @Scheme.Pic.mk (ProjectiveLine.relativeLine (Spec (.of baseField)))
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)
      (ProjectiveSpace.isInvertible_twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1)
  have degreeInvariant := picardPresheafDegree_mul_map_snd
    (f := source ↘ Spec (.of baseField)) (T := ProjectiveLine.relativeLineOver baseField)
    firstClass parameterClass (parameterPoint.left (IsLocalRing.closedPoint extensionField))
  have classEquation :
      Scheme.Pic.mk (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle) =
        firstClass * Scheme.Pic.map (Limits.pullback.snd (source ↘ Spec (.of baseField))
          (ProjectiveLine.relativeLineOver baseField).hom) parameterClass :=
    projectiveLineBundle_class lineBundle
  have tensorComparison := picardFibreDegree_eq_picardPresheafDegree
    (source ↘ Spec (.of baseField))
    (firstClass * Scheme.Pic.map (Limits.pullback.snd (source ↘ Spec (.of baseField))
      (ProjectiveLine.relativeLineOver baseField).hom) parameterClass)
    parameterPoint (IsLocalRing.closedPoint extensionField)
  have firstComparison := picardFibreDegree_eq_picardPresheafDegree
    (source ↘ Spec (.of baseField)) firstClass parameterPoint
    (IsLocalRing.closedPoint extensionField)
  have firstDegree : picardFibreDegree (source ↘ Spec (.of baseField))
      firstClass parameterPoint = lineBundle.degree baseField :=
    (picardFibreDegree_map_fst (baseField := baseField) (curve := source)
      (parameter := ProjectiveLine.relativeLineOver baseField)
      (Scheme.Pic.mk lineBundle) parameterPoint).trans (Scheme.Pic.degree_mk baseField lineBundle)
  exact (congrArg
    (fun coefficient : (Limits.pullback (source ↘ Spec (.of baseField))
        (ProjectiveLine.relativeLineOver baseField).hom).Pic =>
      picardFibreDegree (source ↘ Spec (.of baseField)) coefficient parameterPoint)
    classEquation).trans
      (tensorComparison.trans (degreeInvariant.trans (firstComparison.symm.trans firstDegree)))

/-- The same degree is obtained on every literal residue-field fibre. -/
theorem projectiveLineBundle_residueDegree [IsProper (source ↘ Spec (.of baseField))]
    (lineBundle : source.Modules) [lineBundle.IsInvertible]
    (point : ProjectiveLine.relativeLine (Spec (.of baseField))) :
    fibreDegree (Limits.pullback.snd (source ↘ Spec (.of baseField))
        (ProjectiveLine.relativeLineOver baseField).hom)
      (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle) point =
        lineBundle.degree baseField := by
  have membership : Scheme.Pic.mk
      (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle) ∈
      (picardSubfunctorDegree (source ↘ Spec (.of baseField))
        (lineBundle.degree baseField)).obj (op (ProjectiveLine.relativeLineOver baseField)) := by
    intro extensionField _ _ parameterPoint
    exact projectiveLineBundle_fieldDegree lineBundle parameterPoint
  have constantDegree := (mem_picardSubfunctorDegree_iff (source ↘ Spec (.of baseField))
    (T := ProjectiveLine.relativeLineOver baseField)
    (Scheme.Pic.mk (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle))
    (lineBundle.degree baseField)).mp membership point
  let projection := Limits.pullback.snd (source ↘ Spec (.of baseField))
    (ProjectiveLine.relativeLineOver baseField).hom
  letI := projection.fiberOverSpecResidueField point
  have residueComparison := picardPresheafDegree_eq_degree
    (source ↘ Spec (.of baseField)) (T := ProjectiveLine.relativeLineOver baseField)
    (Scheme.Pic.mk (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle)) point
  have chosenComparison := degree_congr
    ((ProjectiveLine.relativeLineOver baseField).left.residueField point)
    ((Scheme.Modules.pullback (projection.fiberι point)).mapIso (Scheme.Pic.mkIso
      (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle)))
  exact chosenComparison.symm.trans (residueComparison.symm.trans constantDegree)

variable [IsProper (source ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [GeometricallyIntegral (source ↘ Spec (.of baseField))]

/-- The actual finite flat degree-`degree` divisor defined by an independent pencil. -/
def pencilPoint (degree : ℕ) (lineBundle : source.Modules) [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle)
    (independent : LinearIndependent baseField
      ![(H.zeroLinearEquiv lineBundle).symm (firstSection.app ⊤ (1 : Γ(source, ⊤))),
        (H.zeroLinearEquiv lineBundle).symm (secondSection.app ⊤ (1 : Γ(source, ⊤)))])
    (degreeEquation : lineBundle.degree baseField = degree) :
    (hilbertPresheaf (source ↘ Spec (.of baseField)) degree).obj
      (op (ProjectiveLine.relativeLineOver baseField)) :=
  hilbertPoint (source ↘ Spec (.of baseField)) degree (ProjectiveLine.relativeLineOver baseField)
    (projectiveLineBundle (source ↘ Spec (.of baseField)) lineBundle)
    (projectiveLineSection (source ↘ Spec (.of baseField)) firstSection secondSection)
    (projectiveLineSection_residue_fibre_ne_zero_of_sections lineBundle
      firstSection secondSection independent)
    (fun point ↦ (projectiveLineBundle_residueDegree lineBundle point).trans degreeEquation)

@[simp]
theorem pencilPoint_val (degree : ℕ) (lineBundle : source.Modules) [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle)
    (independent : LinearIndependent baseField
      ![(H.zeroLinearEquiv lineBundle).symm (firstSection.app ⊤ (1 : Γ(source, ⊤))),
        (H.zeroLinearEquiv lineBundle).symm (secondSection.app ⊤ (1 : Γ(source, ⊤)))])
    (degreeEquation : lineBundle.degree baseField = degree) :
    (pencilPoint degree lineBundle firstSection secondSection independent degreeEquation).val =
      projectiveLineIdeal (source ↘ Spec (.of baseField)) firstSection secondSection := rfl

/-- The endpoint as a morphism of parameter schemes over the base field. -/
def endpointOver (coordinate : ULift.{u} (Fin 2)) :
    𝟙_ (Over (Spec (.of baseField))) ⟶ ProjectiveLine.relativeLineOver baseField :=
  Over.homMk (endpoint coordinate) (endpoint_over coordinate)

private theorem baseChangeMap_endpoint (coordinate : ULift.{u} (Fin 2)) :
    baseChangeMap (source ↘ Spec (.of baseField)) (endpointOver (baseField := baseField) coordinate) =
      Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) ≫
        endpointInclusion (source ↘ Spec (.of baseField)) coordinate := by
  have projectionEquation :
      Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) ≫
          (source ↘ Spec (.of baseField)) =
        Limits.pullback.snd (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) :=
    (Limits.pullback.condition (f := source ↘ Spec (.of baseField))
      (g := 𝟙 (Spec (.of baseField)))).trans (Category.comp_id _)
  apply Limits.pullback.hom_ext
  · simp only [baseChangeMap, Limits.pullback.lift_fst]
    change Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) =
      (Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) ≫
        endpointInclusion (source ↘ Spec (.of baseField)) coordinate) ≫
          Limits.pullback.fst (source ↘ Spec (.of baseField))
            (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))
    rw [Category.assoc,
      endpointInclusion_curve (source ↘ Spec (.of baseField)) coordinate, Category.comp_id]
  · simp only [baseChangeMap, Limits.pullback.lift_snd]
    change Limits.pullback.snd (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) ≫
        endpoint coordinate =
      (Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))) ≫
        endpointInclusion (source ↘ Spec (.of baseField)) coordinate) ≫
          Limits.pullback.snd (source ↘ Spec (.of baseField))
            (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))
    rw [Category.assoc,
      endpointInclusion_parameter (source ↘ Spec (.of baseField)) coordinate]
    simpa only [Category.assoc] using congrArg
      (fun baseMap : Limits.pullback (source ↘ Spec (.of baseField))
          (𝟙 (Spec (.of baseField))) ⟶ Spec (.of baseField) => baseMap ≫ endpoint coordinate)
      projectionEquation.symm

/-- Pulling the Hilbert pencil to the first endpoint recovers the first zero ideal. -/
theorem pencilPoint_first_val (degree : ℕ) (lineBundle : source.Modules) [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle)
    (independent : LinearIndependent baseField
      ![(H.zeroLinearEquiv lineBundle).symm (firstSection.app ⊤ (1 : Γ(source, ⊤))),
        (H.zeroLinearEquiv lineBundle).symm (secondSection.app ⊤ (1 : Γ(source, ⊤)))])
    (degreeEquation : lineBundle.degree baseField = degree) :
    ((hilbertPresheaf (source ↘ Spec (.of baseField)) degree).map (endpointOver ⟨0⟩).op
      (pencilPoint degree lineBundle firstSection secondSection independent degreeEquation)).val =
        firstSection.zeroLocus.comap
          (Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField)))) := by
  change (projectiveLineIdeal (source ↘ Spec (.of baseField)) firstSection secondSection).comap
    (baseChangeMap _ (endpointOver ⟨0⟩)) = _
  rw [baseChangeMap_endpoint, Scheme.IdealSheafData.comap_comp, projectiveLineIdeal_first]

/-- Pulling the Hilbert pencil to the second endpoint recovers the second zero ideal. -/
theorem pencilPoint_second_val (degree : ℕ) (lineBundle : source.Modules) [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle)
    (independent : LinearIndependent baseField
      ![(H.zeroLinearEquiv lineBundle).symm (firstSection.app ⊤ (1 : Γ(source, ⊤))),
        (H.zeroLinearEquiv lineBundle).symm (secondSection.app ⊤ (1 : Γ(source, ⊤)))])
    (degreeEquation : lineBundle.degree baseField = degree) :
    ((hilbertPresheaf (source ↘ Spec (.of baseField)) degree).map (endpointOver ⟨1⟩).op
      (pencilPoint degree lineBundle firstSection secondSection independent degreeEquation)).val =
        secondSection.zeroLocus.comap
          (Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField)))) := by
  change (projectiveLineIdeal (source ↘ Spec (.of baseField)) firstSection secondSection).comap
    (baseChangeMap _ (endpointOver ⟨1⟩)) = _
  rw [baseChangeMap_endpoint, Scheme.IdealSheafData.comap_comp, projectiveLineIdeal_second]

/-- Every map from a representing Hilbert scheme to an abelian variety identifies
the two actual zero divisors in an independent pencil. -/
theorem independent_sections_image_eq (degree : ℕ)
    {representative : Over (Spec (.of baseField))}
    (representation : (hilbertPresheaf (source ↘ Spec (.of baseField)) degree).RepresentableBy
      representative)
    (variety : AbelianVariety baseField) (morphism : representative ⟶ variety.group.X)
    (lineBundle : source.Modules) [lineBundle.IsInvertible]
    (firstSection secondSection : unit source ⟶ lineBundle)
    (independent : LinearIndependent baseField
      ![(H.zeroLinearEquiv lineBundle).symm (firstSection.app ⊤ (1 : Γ(source, ⊤))),
        (H.zeroLinearEquiv lineBundle).symm (secondSection.app ⊤ (1 : Γ(source, ⊤)))])
    (degreeEquation : lineBundle.degree baseField = degree)
    (firstDivisor secondDivisor : (hilbertPresheaf (source ↘ Spec (.of baseField)) degree).obj
      (op (𝟙_ (Over (Spec (.of baseField))))))
    (firstIdeal : firstDivisor.val = firstSection.zeroLocus.comap
      (Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField)))))
    (secondIdeal : secondDivisor.val = secondSection.zeroLocus.comap
      (Limits.pullback.fst (source ↘ Spec (.of baseField)) (𝟙 (Spec (.of baseField))))) :
    representation.homEquiv.symm firstDivisor ≫ morphism =
      representation.homEquiv.symm secondDivisor ≫ morphism := by
  let pencil := pencilPoint degree lineBundle firstSection secondSection independent degreeEquation
  let pencilMap := representation.homEquiv.symm pencil
  have firstPoint : (hilbertPresheaf (source ↘ Spec (.of baseField)) degree).map
      (endpointOver ⟨0⟩).op pencil = firstDivisor := by
    apply Subtype.ext
    exact (pencilPoint_first_val degree lineBundle firstSection secondSection independent
      degreeEquation).trans firstIdeal.symm
  have secondPoint : (hilbertPresheaf (source ↘ Spec (.of baseField)) degree).map
      (endpointOver ⟨1⟩).op pencil = secondDivisor := by
    apply Subtype.ext
    exact (pencilPoint_second_val degree lineBundle firstSection secondSection independent
      degreeEquation).trans secondIdeal.symm
  obtain ⟨constant, constantEquation, -⟩ :=
    AbelianVariety.RationalCurves.existsUnique_constant variety (pencilMap ≫ morphism)
  have firstMap : endpointOver ⟨0⟩ ≫ pencilMap = representation.homEquiv.symm firstDivisor := by
    rw [Functor.RepresentableBy.comp_homEquiv_symm, firstPoint]
  have secondMap : endpointOver ⟨1⟩ ≫ pencilMap = representation.homEquiv.symm secondDivisor := by
    rw [Functor.RepresentableBy.comp_homEquiv_symm, secondPoint]
  rw [← firstMap, ← secondMap, Category.assoc, Category.assoc, constantEquation]
  simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]

end AlgebraicGeometry.SectionPencil
