import Jacobian.AlgebraicGeometry.AbelianVariety.Albanese
import Jacobian.AlgebraicGeometry.Descent.LocalSections
import Jacobian.AlgebraicGeometry.Group.Rigidity
import Jacobian.AlgebraicGeometry.Hilbert.CurveGeometry
import Jacobian.AlgebraicGeometry.Hilbert.TranslatedAbelMap.FieldConstancy
import Jacobian.AlgebraicGeometry.Hilbert.TranslatedAbelMap.LocalSections

/-!
# The Albanese property of the Abel–Jacobi map

For a smooth proper geometrically irreducible pointed curve over any field,
its Abel–Jacobi map to a tensor-compatible representative of the degree-zero
Picard sheaf is Albanese. The ordered sum of a curve map descends to the
degree-`2g+1` Hilbert scheme. Actual affine local sections and field-fibre
constancy then descend it to the Picard representative. Restriction to the
marked tuple recovers the curve map, and rigidity makes the resulting pointed
map a group homomorphism. No restriction on the genus or the field is needed.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry.Curve

variable {baseField : Type u} [Field baseField]

local instance curveOver (curve : Curve baseField) :
    curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩

private theorem existsUnique_translatedAbel_factorization
    (curve : PointedCurve baseField) (variety : AbelianVariety baseField)
    (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      variety.group.X)
    {hilbertScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).RepresentableBy hilbertScheme)
    (target : AbelianVariety baseField) (morphism : hilbertScheme ⟶ target.group.X) :
    ∃! factorMap : variety.group.X ⟶ target.group.X,
      Hilbert.translatedAbelMap curve.curve
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
          (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
          (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation representation ≫
        factorMap = morphism := by
  letI : Smooth curve.curve.carrier.hom :=
    SmoothOfRelativeDimension.smooth 1 curve.curve.carrier.hom
  letI : GeometricallyIntegral curve.curve.carrier.hom :=
    Smooth.geometricallyIntegral curve.curve.carrier.hom
  letI : SmoothOfRelativeDimension
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1) hilbertScheme.hom :=
    smoothOfRelativeDimension_of_representableBy_hilbertPresheaf curve.curve.carrier.hom
      (isRepresentable_hilbertPresheaf_curve curve.curve.carrier.hom) _ _ hilbertRepresentation
  letI : Smooth hilbertScheme.hom :=
    SmoothOfRelativeDimension.smooth
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1) hilbertScheme.hom
  letI : IsReduced hilbertScheme.left := Smooth.isReduced_of_field hilbertScheme.hom
  letI : IsReduced variety.group.X.left := Smooth.isReduced_of_field variety.group.X.hom
  apply Scheme.existsUnique_factorization_of_local_sections_of_field_tests _ morphism
  · intro point
    obtain ⟨openSubset, _, point_mem, sectionMap, section_fac⟩ :=
      Hilbert.translatedAbelMap_has_affine_local_sections curve representation
        hilbertRepresentation point
    exact ⟨openSubset, point_mem, sectionMap, section_fac⟩
  · exact Hilbert.translatedAbelMap_field_image_eq curve hilbertRepresentation
      representation target morphism

private theorem isAlbanese_of_hilbert_representative
    (curve : PointedCurve baseField) (variety : AbelianVariety baseField)
    (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      variety.group.X)
    (tensorCompatible : PicardTensorCompatible curve.curve.carrier.hom variety.group
      representation)
    {hilbertScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).RepresentableBy hilbertScheme) :
    IsAlbanese curve.point variety
      (abelJacobiMap curve.curve curve.point.left (by simpa using Over.w curve.point)
        representation) := by
  let abelMap := abelJacobiMap curve.curve curve.point.left
    (by simpa using Over.w curve.point) representation
  have normalizedOne : curve.point ≫ abelMap = 1 := by
    exact abelJacobiMap_point curve.curve curve.point.left
      (by simpa using Over.w curve.point) representation tensorCompatible
  have normalized : curve.point ≫ abelMap = η[variety.group.X] := by
    simpa only [CategoryTheory.Hom.one_def,
      SemiCartesianMonoidalCategory.toUnit_unit, Category.id_comp] using normalizedOne
  refine ⟨normalized, ?_⟩
  intro target morphism morphism_normalized
  let degree := 2 * curve.curve.carrier.left.arithmeticGenus baseField
  let translatedMap := Hilbert.translatedAbelMap curve.curve (degree + 1)
    (curve.pointIdealClass ^ (degree + 1)) (curve.degreeHom_pointIdealClass_pow _)
    hilbertRepresentation representation
  let orderedMap := Hilbert.OrderedDivisors.map curve.curve.carrier.hom hilbertRepresentation
  obtain ⟨hilbertMap, hilbert_fac, hilbert_unique⟩ :=
    Hilbert.OrderedDivisors.existsUnique_abelianSum_descent curve.curve curve.point (degree + 1)
      hilbertRepresentation target.group morphism
  obtain ⟨factorMap, factor_fac, factor_unique⟩ :=
    existsUnique_translatedAbel_factorization curve variety representation
      hilbertRepresentation target hilbertMap
  have orderedComparison : orderedMap ≫ translatedMap =
      Hilbert.OrderedDivisors.abelianSum curve.curve variety.group abelMap (degree + 1) :=
    Hilbert.OrderedDivisors.map_translatedAbelMap_eq_abelianSum curve representation
      tensorCompatible (degree + 1) hilbertRepresentation
  have morphism_normalizedOne : curve.point ≫ morphism = 1 := by
    simpa only [CategoryTheory.Hom.one_def,
      SemiCartesianMonoidalCategory.toUnit_unit, Category.id_comp] using morphism_normalized
  have factor_on_curve : abelMap ≫ factorMap = morphism := by
    calc
      abelMap ≫ factorMap = (Hilbert.OrderedDivisors.markedTuple curve degree ≫
          Hilbert.OrderedDivisors.abelianSum curve.curve variety.group abelMap
            (degree + 1)) ≫ factorMap := by
        rw [Hilbert.OrderedDivisors.markedTuple_abelianSum curve variety.group
          abelMap normalizedOne]
      _ = Hilbert.OrderedDivisors.markedTuple curve degree ≫
          (orderedMap ≫ translatedMap) ≫ factorMap := by
        simp only [orderedComparison, Category.assoc]
      _ = Hilbert.OrderedDivisors.markedTuple curve degree ≫ (orderedMap ≫ hilbertMap) := by
        simpa only [Category.assoc] using congrArg
          (fun arrow ↦ Hilbert.OrderedDivisors.markedTuple curve degree ≫ orderedMap ≫ arrow)
          factor_fac
      _ = morphism := by
        rw [hilbert_fac, Hilbert.OrderedDivisors.markedTuple_abelianSum curve target.group
          morphism morphism_normalizedOne]
  have factor_normalized : η[variety.group.X] ≫ factorMap = η[target.group.X] := by
    rw [← normalized, Category.assoc, factor_on_curve, morphism_normalized]
  letI : GeometricallyIntegral variety.group.X.hom :=
    Smooth.geometricallyIntegral variety.group.X.hom
  letI : IsMonHom factorMap :=
    isMonHom_of_isProper_of_geometricallyIntegral factorMap factor_normalized
  let groupMap : variety.group ⟶ target.group :=
    InducedCategory.homMk (Grp.homMk factorMap)
  refine ⟨groupMap, factor_on_curve, ?_⟩
  intro otherMap other_fac
  apply CommGrp.hom_ext
  change otherMap.hom.hom.hom = factorMap
  apply factor_unique otherMap.hom.hom.hom
  apply hilbert_unique (translatedMap ≫ otherMap.hom.hom.hom)
  calc
    orderedMap ≫ translatedMap ≫ otherMap.hom.hom.hom =
        Hilbert.OrderedDivisors.abelianSum curve.curve variety.group abelMap
          (degree + 1) ≫ otherMap.hom.hom.hom := by
      rw [← Category.assoc, orderedComparison]
    _ = Hilbert.OrderedDivisors.abelianSum curve.curve target.group morphism (degree + 1) := by
      have comparison := Hilbert.OrderedDivisors.abelianSum_groupHom curve variety.group
        target.group abelMap otherMap (degree + 1)
      change Hilbert.OrderedDivisors.abelianSum curve.curve variety.group abelMap (degree + 1) ≫
          otherMap.hom.hom.hom =
        Hilbert.OrderedDivisors.abelianSum curve.curve target.group
          (abelMap ≫ otherMap.hom.hom.hom) (degree + 1) at comparison
      have other_equation : abelMap ≫ otherMap.hom.hom.hom = morphism := other_fac
      simpa only [other_equation] using comparison

/-- The Abel–Jacobi map to any tensor-compatible degree-zero Picard representative
has the Albanese universal property over the original field. -/
theorem isAlbanese_abelJacobiMap (curve : Curve baseField)
    (point : 𝟙_ (Over (Spec (.of baseField))) ⟶ curve.carrier)
    (variety : AbelianVariety baseField)
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      variety.group.X)
    (tensorCompatible : PicardTensorCompatible curve.carrier.hom variety.group representation) :
    IsAlbanese point variety
      (abelJacobiMap curve point.left (by simpa using Over.w point) representation) := by
  letI : Smooth curve.carrier.hom := SmoothOfRelativeDimension.smooth 1 curve.carrier.hom
  letI : GeometricallyIntegral curve.carrier.hom :=
    Smooth.geometricallyIntegral curve.carrier.hom
  obtain ⟨hilbertScheme, ⟨hilbertRepresentation⟩⟩ :=
    isRepresentable_hilbertPresheaf_curve curve.carrier.hom
      (2 * curve.carrier.left.arithmeticGenus baseField + 1)
  exact isAlbanese_of_hilbert_representative ⟨curve, point⟩ variety representation
    tensorCompatible hilbertRepresentation

end AlgebraicGeometry.Curve
