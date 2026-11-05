import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.EulerCharacteristic
import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange
import Jacobian.AlgebraicGeometry.Picard.LocalRepresentatives

/-!
# The degree of a section of the relative Picard sheaf

Fibre degree descends from invertible sheaves to sections of the fppf Picard
sheaf. It is independent of local representatives and natural in the parameter
scheme. For a proper flat family locally of finite presentation it is locally
constant, by local constancy of the two fibre Euler characteristics.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{u}} (family : source ⟶ base)

private theorem exists_local_degree {parameter : Over base}
    (sectionValue : (picardFunctor family).obj.obj (op parameter)) (point : parameter.left) :
    ∃ (degree : ℤ) (localParameter : Over base) (restriction : localParameter ⟶ parameter)
      (lineClass : (picardPresheaf family).obj (op localParameter))
      (localPoint : localParameter.left),
      (toPicardFunctor family).app (op localParameter) lineClass =
        (picardFunctor family).obj.map restriction.op sectionValue ∧
      restriction.left localPoint = point ∧ Flat restriction.left ∧
      LocallyOfFinitePresentation restriction.left ∧
      picardPresheafDegree family lineClass localPoint = degree := by
  obtain ⟨localParameter, restriction, lineClass, localPoint, compatibility,
    image_eq, flat, locallyPresented⟩ := exists_picardClass_representative family sectionValue point
  exact ⟨_, localParameter, restriction, lineClass, localPoint, compatibility,
    image_eq, flat, locallyPresented, rfl⟩

/-- The fibre degree of a section of the relative Picard sheaf, computed on
an fppf local representative at each point of the parameter scheme. -/
def picardDegree {parameter : Over base}
    (sectionValue : (picardFunctor family).obj.obj (op parameter)) (point : parameter.left) : ℤ :=
  (exists_local_degree family sectionValue point).choose

variable [QuasiCompact family] [QuasiSeparated family]

/-- Equal sections represented by two line-bundle classes have the same
fibre-degree function. -/
theorem picardPresheafDegree_eq_of_toPicardFunctor_eq {parameter : Over base}
    {firstClass secondClass : (picardPresheaf family).obj (op parameter)}
    (equality : (toPicardFunctor family).app (op parameter) firstClass =
      (toPicardFunctor family).app (op parameter) secondClass) :
    picardPresheafDegree family firstClass = picardPresheafDegree family secondClass := by
  funext point
  obtain ⟨localParameter, restriction, localPoint, localEquality, image_eq, _, _⟩ :=
    exists_picardClass_eq_of_toPicardFunctor_eq family equality point
  rw [← image_eq, ← picardPresheafDegree_map, ← picardPresheafDegree_map]
  exact congrArg (fun lineClass ↦ picardPresheafDegree family lineClass localPoint) localEquality

/-- Two local representatives of the same Picard-sheaf section have equal
degrees at points with the same image. -/
theorem picardPresheafDegree_eq_of_toPicardFunctor_eq_map {parameter : Over base}
    (sectionValue : (picardFunctor family).obj.obj (op parameter))
    {firstParameter secondParameter : Over base}
    (firstMap : firstParameter ⟶ parameter) (secondMap : secondParameter ⟶ parameter)
    (firstClass : (picardPresheaf family).obj (op firstParameter))
    (secondClass : (picardPresheaf family).obj (op secondParameter))
    (firstCompatibility : (toPicardFunctor family).app (op firstParameter) firstClass =
      (picardFunctor family).obj.map firstMap.op sectionValue)
    (secondCompatibility : (toPicardFunctor family).app (op secondParameter) secondClass =
      (picardFunctor family).obj.map secondMap.op sectionValue)
    (firstPoint : firstParameter.left) (secondPoint : secondParameter.left)
    (image_eq : firstMap.left firstPoint = secondMap.left secondPoint) :
    picardPresheafDegree family firstClass firstPoint =
      picardPresheafDegree family secondClass secondPoint := by
  let common : Over base := Over.mk (pullback.fst firstMap.left secondMap.left ≫ firstParameter.hom)
  let firstProjection : common ⟶ firstParameter :=
    Over.homMk (pullback.fst firstMap.left secondMap.left)
  let secondProjection : common ⟶ secondParameter :=
    Over.homMk (pullback.snd firstMap.left secondMap.left) (by
      simp only [common, Over.mk_hom, ← Over.w firstMap, ← Over.w secondMap,
        pullback.condition_assoc])
  have square : firstProjection ≫ firstMap = secondProjection ≫ secondMap := by
    ext
    simp [firstProjection, secondProjection, pullback.condition]
  obtain ⟨commonPoint, rfl, rfl⟩ :=
    Scheme.Pullback.exists_preimage_pullback firstPoint secondPoint image_eq
  have firstProjection_eq : pullback.fst firstMap.left secondMap.left commonPoint =
      firstProjection.left commonPoint := rfl
  have secondProjection_eq : pullback.snd firstMap.left secondMap.left commonPoint =
      secondProjection.left commonPoint := rfl
  rw [firstProjection_eq, secondProjection_eq,
    ← picardPresheafDegree_map, ← picardPresheafDegree_map]
  have equalImages : (toPicardFunctor family).app (op common)
      ((picardPresheaf family).map firstProjection.op firstClass) =
      (toPicardFunctor family).app (op common)
        ((picardPresheaf family).map secondProjection.op secondClass) := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
      firstCompatibility, secondCompatibility, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, square]
  rw [picardPresheafDegree_eq_of_toPicardFunctor_eq family equalImages]

/-- Any local representative computes the degree at the image of its point. -/
theorem picardDegree_eq {parameter : Over base}
    (sectionValue : (picardFunctor family).obj.obj (op parameter))
    {localParameter : Over base} (restriction : localParameter ⟶ parameter)
    (lineClass : (picardPresheaf family).obj (op localParameter))
    (compatibility : (toPicardFunctor family).app (op localParameter) lineClass =
      (picardFunctor family).obj.map restriction.op sectionValue)
    (localPoint : localParameter.left) :
    picardDegree family sectionValue (restriction.left localPoint) =
      picardPresheafDegree family lineClass localPoint := by
  obtain ⟨otherParameter, otherMap, otherClass, otherPoint, otherCompatibility,
    image_eq, _, _, degree_eq⟩ :=
      (exists_local_degree family sectionValue (restriction.left localPoint)).choose_spec
  rw [picardDegree, ← degree_eq]
  exact picardPresheafDegree_eq_of_toPicardFunctor_eq_map family sectionValue
    otherMap restriction otherClass lineClass otherCompatibility compatibility
    otherPoint localPoint image_eq

/-- On globally represented sections, the descended degree is the original
fibre-degree function of the invertible sheaf class. -/
theorem picardDegree_toPicardFunctor {parameter : Over base}
    (lineClass : (picardPresheaf family).obj (op parameter)) :
    picardDegree family ((toPicardFunctor family).app (op parameter) lineClass) =
      picardPresheafDegree family lineClass := by
  funext point
  exact picardDegree_eq family _ (𝟙 parameter) lineClass (by simp) point

/-- Relative Picard degree is natural under every change of parameter scheme. -/
theorem picardDegree_map {parameter changedParameter : Over base}
    (restriction : changedParameter ⟶ parameter)
    (sectionValue : (picardFunctor family).obj.obj (op parameter))
    (point : changedParameter.left) :
    picardDegree family ((picardFunctor family).obj.map restriction.op sectionValue) point =
      picardDegree family sectionValue (restriction.left point) := by
  obtain ⟨_, localParameter, localMap, lineClass, localPoint, compatibility, rfl, _, _, _⟩ :=
    exists_local_degree family ((picardFunctor family).obj.map restriction.op sectionValue) point
  rw [picardDegree_eq family _ localMap lineClass compatibility localPoint,
    show restriction.left (localMap.left localPoint) = (localMap ≫ restriction).left localPoint
      by simp,
    picardDegree_eq family sectionValue (localMap ≫ restriction) lineClass
      (by rw [compatibility, op_comp, Functor.map_comp_apply]) localPoint]

omit [QuasiCompact family] [QuasiSeparated family] in
/-- Fibre degree of an invertible sheaf is locally constant in a proper flat
family locally of finite presentation. -/
theorem isLocallyConstant_picardPresheafDegree [IsProper family]
    [LocallyOfFinitePresentation family] [Flat family] {parameter : Over base}
    (lineClass : (picardPresheaf family).obj (op parameter)) :
    IsLocallyConstant (picardPresheafDegree family lineClass) := by
  have := Modules.isGrothendieckAbelian (pullback family parameter.hom)
  have := Pic.isInvertible lineClass
  exact (Modules.isLocallyConstant_eulerCharFiber _ _
    (Modules.isFlatOver_of_isInvertible _ _)).sub
    (Modules.isLocallyConstant_eulerCharFiber _ _ (Modules.isFlatOver_of_isInvertible _ _))

omit [QuasiCompact family] [QuasiSeparated family] in
/-- Degree of a Picard-sheaf section is locally constant for proper flat
families locally of finite presentation. -/
theorem isLocallyConstant_picardDegree [IsProper family] [LocallyOfFinitePresentation family]
    [Flat family] {parameter : Over base}
    (sectionValue : (picardFunctor family).obj.obj (op parameter)) :
    IsLocallyConstant (picardDegree family sectionValue) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro point
  obtain ⟨_, localParameter, restriction, lineClass, localPoint, compatibility, rfl, _, _, _⟩ :=
    exists_local_degree family sectionValue point
  have openDegree := (isLocallyConstant_picardPresheafDegree family lineClass).isOpen_fiber
    (picardPresheafDegree family lineClass localPoint)
  refine ⟨restriction.left.base ''
    (picardPresheafDegree family lineClass ⁻¹' {picardPresheafDegree family lineClass localPoint}),
    restriction.left.isOpenMap _ openDegree, ⟨localPoint, rfl, rfl⟩, ?_⟩
  rintro _ ⟨otherPoint, membership, rfl⟩
  rw [picardDegree_eq family sectionValue restriction lineClass compatibility otherPoint,
    picardDegree_eq family sectionValue restriction lineClass compatibility localPoint]
  exact membership

end AlgebraicGeometry
