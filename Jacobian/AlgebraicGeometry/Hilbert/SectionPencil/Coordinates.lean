import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Pullback
import Jacobian.AlgebraicGeometry.Modules.Discrete
import Jacobian.AlgebraicGeometry.Modules.RestrictionIsomorphism
import Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial
import Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.ZeroLocus

/-!
# Coordinates of a pencil at field-valued points

The nonvanishing loci of the two coordinate sections cover the relative
projective line. At its normalized endpoints, the nonzero coordinate gives a
specified trivialization and the other coordinate is the zero module map.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open CategoryTheory.Limits (zero_comp comp_zero)
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.SectionPencil

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem coordinate_zeroLocus (base : Scheme.{u})
    (coordinate : ULift.{u} (Fin 2)) :
    Scheme.Modules.Hom.zeroLocus
        (twistPowSection (ULift.{u} (Fin 2)) base coordinate 1) =
      (Scheme.Modules.Hom.zeroLocus (Proj.unitToTwist
        (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate))).comap
          (toIntegralModel (ULift.{u} (Fin 2)) base) := by
  let modelMap := toIntegralModel (ULift.{u} (Fin 2)) base
  let modelSection := Proj.unitToTwist
    (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate)
  have sectionEquation : twistPowSection (ULift.{u} (Fin 2)) base coordinate 1 =
      (pullbackObjUnitIso modelMap).inv ≫ (pullback modelMap).map modelSection := by
    simp only [modelMap, modelSection, twistPowSection, unitIsoTwistZero, twistMulX,
      Proj.unitToTwist, Proj.unitIsoTwistZero, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom, eqToHom_refl, Category.comp_id,
      Functor.map_comp, Category.assoc]
    apply congrArg (fun multiplication =>
      (pullbackObjUnitIso modelMap).inv ≫
        (pullback modelMap).map Proj.unitToTwistZero ≫
        (pullback modelMap).map multiplication)
    change Proj.twistMul ((0 : ℕ) : ℤ)
        (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate) =
      Proj.twistMul (0 : ℤ)
        (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate)
    rfl
  letI : (unit ℙ(ULift.{u} (Fin 2); base)).IsInvertible :=
    Scheme.Modules.isInvertible_unit _
  let pulledSection := (pullback modelMap).map modelSection
  have comparison :
      Arrow.mk ((pullbackObjUnitIso modelMap).inv ≫ pulledSection) ≅
        Arrow.mk pulledSection :=
    Arrow.isoMk (pullbackObjUnitIso modelMap).symm (Iso.refl _) (by
      change (pullbackObjUnitIso modelMap).inv ≫ pulledSection =
        ((pullbackObjUnitIso modelMap).inv ≫ pulledSection) ≫ 𝟙 _
      exact (Category.comp_id _).symm)
  rw [sectionEquation]
  exact (Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso
    ((pullbackObjUnitIso modelMap).inv ≫ pulledSection) pulledSection comparison).trans
        (Scheme.Modules.Hom.comap_zeroLocus modelMap modelSection).symm

/-- The two coordinate sections have their prescribed standard nonvanishing opens. -/
theorem compl_support_zeroLocus_coordinate (base : Scheme.{u})
    (coordinate : ULift.{u} (Fin 2)) :
    (Scheme.Modules.Hom.zeroLocus
      (twistPowSection (ULift.{u} (Fin 2)) base coordinate 1)).support.compl =
      standardOpen (ULift.{u} (Fin 2)) base coordinate := by
  rw [coordinate_zeroLocus, Scheme.IdealSheafData.support_comap]
  change (toIntegralModel (ULift.{u} (Fin 2)) base) ⁻¹ᵁ
      (Scheme.Modules.Hom.zeroLocus (Proj.unitToTwist
        (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate))).support.compl = _
  rw [Proj.compl_support_zeroLocus_unitToTwist
    (Proj.exists_mem_basicOpen_homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))]
  rfl

/-- The two pulled coordinate maps cannot both vanish at a field-valued point. -/
theorem coordinate_pullback_ne_zero {baseField extensionField : Type u}
    [Field baseField] [Field extensionField]
    (parameterPoint : Spec (.of extensionField) ⟶
      ProjectiveLine.relativeLine (Spec (.of baseField))) :
    (pullback parameterPoint).map
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) ⟨0⟩ 1) ≠ 0 ∨
      (pullback parameterPoint).map
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) ⟨1⟩ 1) ≠ 0 := by
  classical
  by_contra vanishing
  push_neg at vanishing
  have allVanishing (coordinate : ULift.{u} (Fin 2)) :
      (pullback parameterPoint).map
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1) = 0 := by
    obtain ⟨coordinate⟩ := coordinate
    fin_cases coordinate
    · exact vanishing.1
    · exact vanishing.2
  let fieldPoint : Spec (.of extensionField) := Classical.arbitrary _
  have covered : parameterPoint fieldPoint ∈
      ⨆ coordinate, standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate := by
    rw [iSup_standardOpen]
    trivial
  obtain ⟨coordinate, membership⟩ := Opens.mem_iSup.mp covered
  have zeroIdeal : (Scheme.Modules.Hom.zeroLocus
      (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
        coordinate 1)).comap parameterPoint = ⊥ := by
    rw [Scheme.Modules.Hom.comap_zeroLocus, allVanishing]
    exact (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).mpr rfl
  have inSupport : fieldPoint ∈ ((Scheme.Modules.Hom.zeroLocus
      (twistPowSection (ULift.{u} (Fin 2))
        (Spec (.of baseField)) coordinate 1)).comap parameterPoint).support := by
    rw [zeroIdeal, Scheme.IdealSheafData.support_bot]
    trivial
  rw [Scheme.IdealSheafData.support_comap] at inSupport
  have outsideSupport : parameterPoint fieldPoint ∉
      (Scheme.Modules.Hom.zeroLocus
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1)).support := by
    rw [← compl_support_zeroLocus_coordinate] at membership
    exact membership
  exact outsideSupport inSupport

/-- A field-valued point trivializes the pulled coordinate line. -/
def fieldCoordinateIso {baseField extensionField : Type u}
    [Field baseField] [Field extensionField]
    (parameterPoint : Spec (.of extensionField) ⟶
      ProjectiveLine.relativeLine (Spec (.of baseField))) :
    (pullback parameterPoint).obj
        (twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1) ≅
      unit (Spec (.of extensionField)) :=
  Classical.choice (nonempty_iso_unit_of_discrete _)

/-- The coefficients in any such trivialization are not both zero. -/
theorem parameterCoefficients_ne_zero {baseField extensionField : Type u}
    [Field baseField] [Field extensionField]
    (parameterPoint : Spec (.of extensionField) ⟶
      ProjectiveLine.relativeLine (Spec (.of baseField)))
    (trivialization : (pullback parameterPoint).obj
      (twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1) ≅ unit (Spec (.of extensionField))) :
    (parameterCoefficient parameterPoint trivialization
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) ⟨0⟩ 1)).app ⊤
          (1 : Γ(Spec (.of extensionField), ⊤)) ≠ 0 ∨
      (parameterCoefficient parameterPoint trivialization
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) ⟨1⟩ 1)).app ⊤
          (1 : Γ(Spec (.of extensionField), ⊤)) ≠ 0 := by
  have nonzero := coordinate_pullback_ne_zero parameterPoint
  have zeroCoefficient (coordinate : ULift.{u} (Fin 2))
      (vanishing : (parameterCoefficient parameterPoint trivialization
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1)).app ⊤
          (1 : Γ(Spec (.of extensionField), ⊤)) = 0) :
      (pullback parameterPoint).map
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1) = 0 := by
    have zeroMap : parameterCoefficient parameterPoint trivialization
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1) = 0 := by
      apply unit_hom_ext
      exact vanishing
    have conjugation := congrArg
      (fun moduleMap : unit (Spec (.of extensionField)) ⟶ unit (Spec (.of extensionField)) ↦
        (pullbackObjUnitIso parameterPoint).hom ≫ moduleMap ≫ trivialization.inv) zeroMap
    simpa only [parameterCoefficient, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id, comp_zero, zero_comp] using conjugation
  rcases nonzero with firstNonzero | secondNonzero
  · exact Or.inl fun vanishing ↦ firstNonzero (zeroCoefficient ⟨0⟩ vanishing)
  · exact Or.inr fun vanishing ↦ secondNonzero (zeroCoefficient ⟨1⟩ vanishing)

/-- The two normalized endpoints, with the chosen coordinate equal to one. -/
def endpoint {baseField : Type u} [Field baseField] (coordinate : ULift.{u} (Fin 2)) :
    Spec (.of baseField) ⟶ ProjectiveLine.relativeLine (Spec (.of baseField)) :=
  ProjectiveLine.normalized (𝟙 (Spec (.of baseField))) coordinate 0

@[reassoc (attr := simp)]
theorem endpoint_over {baseField : Type u} [Field baseField]
    (coordinate : ULift.{u} (Fin 2)) :
    endpoint (baseField := baseField) coordinate ≫
        ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField) =
      𝟙 (Spec (.of baseField)) :=
  ProjectiveLine.normalized_over ..

theorem endpoint_preimage_standardOpen {baseField : Type u} [Field baseField]
    (endpointCoordinate coordinate : ULift.{u} (Fin 2)) :
    endpoint (baseField := baseField) endpointCoordinate ⁻¹ᵁ
        standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate =
      if coordinate = endpointCoordinate then ⊤ else ⊥ := by
  classical
  unfold endpoint ProjectiveLine.normalized
  rw [homOfSections_preimage_standardOpen]
  by_cases equality : coordinate = endpointCoordinate
  · simp only [ProjectiveLine.normalizedSections, equality, if_pos True.intro,
      Scheme.basicOpen_one]
  · simp only [ProjectiveLine.normalizedSections, if_neg equality, Scheme.basicOpen_zero]

/-- The other coordinate vanishes as a module map at a normalized endpoint. -/
theorem endpoint_other_coordinate {baseField : Type u} [Field baseField]
    (endpointCoordinate coordinate : ULift.{u} (Fin 2)) (distinct : coordinate ≠ endpointCoordinate) :
    (pullback (endpoint (baseField := baseField) endpointCoordinate)).map
      (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1) = 0 := by
  let parameterPoint := endpoint (baseField := baseField) endpointCoordinate
  have emptyPreimage : parameterPoint ⁻¹ᵁ
      standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate = ⊥ := by
    rw [endpoint_preimage_standardOpen, if_neg distinct]
  have fullSupport : ((Scheme.Modules.Hom.zeroLocus
      (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField))
        coordinate 1)).comap parameterPoint).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    apply TopologicalSpace.Closeds.ext
    ext fieldPoint
    have outsideOpen : parameterPoint fieldPoint ∉
        standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate := by
      intro membership
      have preimageMembership : fieldPoint ∈ parameterPoint ⁻¹ᵁ
          standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate := membership
      rw [emptyPreimage] at preimageMembership
      exact preimageMembership
    have supportMembership : parameterPoint fieldPoint ∈
        (Scheme.Modules.Hom.zeroLocus
          (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1)).support := by
      by_contra outside
      exact outsideOpen (by rw [← compl_support_zeroLocus_coordinate]; exact outside)
    change (parameterPoint fieldPoint ∈
      (Scheme.Modules.Hom.zeroLocus
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1)).support) ↔ True
    exact iff_true_intro supportMembership
  have zeroIdeal := Scheme.IdealSheafData.support_eq_top_iff.mp fullSupport
  rw [Scheme.Modules.Hom.comap_zeroLocus] at zeroIdeal
  exact (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).mp zeroIdeal

/-- Its chosen coordinate trivializes the twisting line at a normalized endpoint. -/
theorem endpoint_coordinate_isIso {baseField : Type u} [Field baseField]
    (coordinate : ULift.{u} (Fin 2)) :
    IsIso ((pullbackObjUnitIso (endpoint (baseField := baseField) coordinate)).inv ≫
      (pullback (endpoint (baseField := baseField) coordinate)).map
        (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1)) := by
  let parameterPoint := endpoint (baseField := baseField) coordinate
  let coordinateMap := twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1
  have fullPreimage : parameterPoint ⁻¹ᵁ
      standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate = ⊤ := by
    rw [endpoint_preimage_standardOpen, if_pos rfl]
  letI := Scheme.Modules.isIso_restrict_pullback_map parameterPoint coordinateMap
    (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate)
  have mapIsIso : IsIso ((pullback parameterPoint).map coordinateMap) :=
    Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen
      ((pullback parameterPoint).map coordinateMap) fun openSubset _ ↦
        Scheme.Modules.bijective_app_of_isIso_restrict
          ((pullback parameterPoint).map coordinateMap)
          (W := parameterPoint ⁻¹ᵁ
            standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate)
          (V := openSubset) (by rw [fullPreimage]; exact le_top)
  letI := mapIsIso
  infer_instance

/-- The coordinate-normalized trivialization at either endpoint. -/
def endpointCoordinateIso {baseField : Type u} [Field baseField]
    (coordinate : ULift.{u} (Fin 2)) :
    (pullback (endpoint (baseField := baseField) coordinate)).obj
      (twist (ULift.{u} (Fin 2)) (Spec (.of baseField)) 1) ≅ unit (Spec (.of baseField)) := by
  letI := endpoint_coordinate_isIso (baseField := baseField) coordinate
  exact (asIso ((pullbackObjUnitIso (endpoint (baseField := baseField) coordinate)).inv ≫
    (pullback (endpoint (baseField := baseField) coordinate)).map
      (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1))).symm

@[simp]
theorem endpointCoefficient_self {baseField : Type u} [Field baseField]
    (coordinate : ULift.{u} (Fin 2)) :
    parameterCoefficient (endpoint (baseField := baseField) coordinate) (endpointCoordinateIso coordinate)
      (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1) = 𝟙 _ := by
  dsimp only [parameterCoefficient, endpointCoordinateIso, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc, IsIso.hom_inv_id]

@[simp]
theorem endpointCoefficient_other {baseField : Type u} [Field baseField]
    (endpointCoordinate coordinate : ULift.{u} (Fin 2)) (distinct : coordinate ≠ endpointCoordinate) :
    parameterCoefficient (endpoint (baseField := baseField) endpointCoordinate)
      (endpointCoordinateIso endpointCoordinate)
      (twistPowSection (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate 1) = 0 := by
  rw [parameterCoefficient, endpoint_other_coordinate _ _ distinct, zero_comp, comp_zero]

end AlgebraicGeometry.SectionPencil
