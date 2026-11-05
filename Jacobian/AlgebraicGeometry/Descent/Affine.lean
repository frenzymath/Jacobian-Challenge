import Jacobian.AlgebraicGeometry.Descent.AffineCoaction
import Jacobian.AlgebraicGeometry.Descent.InvariantOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

variable {source base : Scheme.{schemeUniverse}} {baseMap : source ⟶ base}
  {representation : Over source}

private theorem transport_left_eq_comp_toHom (datum : DescentDatum baseMap representation)
    {test : Scheme.{schemeUniverse}}
    (comparison : test ⟶ Limits.pullback (representation.hom ≫ baseMap) baseMap)
    {firstMap secondMap : test ⟶ source} (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (first_eq : firstMap = comparison ≫ Limits.pullback.fst _ _ ≫ representation.hom)
    (second_eq : secondMap = comparison ≫ Limits.pullback.snd _ _)
    (point : Over.mk firstMap ⟶ representation)
    (point_eq : point.left = comparison ≫ Limits.pullback.fst _ _) :
    (datum.transport firstMap secondMap equality point).left = comparison ≫ datum.toHom := by
  rw [datum.transport_left_eq_lift_toHom]
  congr 1
  apply pullback.hom_ext <;> simp [point_eq, second_eq]

theorem coactionMap_toHom (datum : DescentDatum baseMap representation) :
    coactionMap baseMap representation.hom datum.toHom datum.toHom_comp_hom ≫ datum.toHom =
      coactionForget baseMap representation.hom ≫ datum.toHom := by
  have firstCompatibility :
      (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ ≫ representation.hom) ≫ baseMap =
      (Limits.pullback.fst (Limits.pullback.snd (representation.hom ≫ baseMap) baseMap ≫
        baseMap) baseMap ≫ Limits.pullback.snd _ _) ≫ baseMap := by
    simp [Limits.pullback.condition]
  have secondCompatibility :
      (Limits.pullback.fst (Limits.pullback.snd (representation.hom ≫ baseMap) baseMap ≫
        baseMap) baseMap ≫ Limits.pullback.snd _ _) ≫ baseMap =
      Limits.pullback.snd (Limits.pullback.snd (representation.hom ≫ baseMap) baseMap ≫
        baseMap) baseMap ≫ baseMap := by
    simp [Limits.pullback.condition]
  have transport_eq : datum.transport _ _ firstCompatibility
      (Over.homMk (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) rfl) =
      Over.homMk (Limits.pullback.fst _ _ ≫ datum.toHom) (by simp) := by
    ext
    exact datum.transport_left_eq_comp_toHom _ firstCompatibility
      (by simp) (by simp) _ (by simp)
  rw [← datum.transport_left_eq_comp_toHom _ secondCompatibility (by simp) (by simp)
    (Over.homMk (Limits.pullback.fst _ _ ≫ datum.toHom) (by simp)) (by simp),
    ← transport_eq, datum.transport_transport,
    ← datum.transport_left_eq_comp_toHom _ (firstCompatibility.trans secondCompatibility)
      (by simp) (by simp)
      (Over.homMk (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) rfl) (by simp)]

theorem isEffective_of_isAffine [IsAffine source] [IsAffine base]
    [Flat baseMap] [Surjective baseMap] [IsAffine representation.left]
    (datum : DescentDatum baseMap representation) : datum.IsEffective := by
  obtain ⟨descendedScheme, descendedStructure, descentMap, cartesian, invariant⟩ :=
    exists_isPullback_of_coaction baseMap representation.hom datum.toHom
      datum.toHom_comp_hom datum.lift_toHom datum.coactionMap_toHom
  refine ⟨Over.mk descendedStructure, descentMap, cartesian, fun firstMap secondMap equality point ↦ ?_⟩
  rw [datum.transport_left_eq_lift_toHom, Category.assoc, invariant,
    Limits.pullback.lift_fst_assoc]

end CategoryTheory.Over.DescentDatum
