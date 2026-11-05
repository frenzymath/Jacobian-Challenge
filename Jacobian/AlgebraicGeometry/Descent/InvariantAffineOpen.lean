import Jacobian.AlgebraicGeometry.Descent.InvariantOpen
import Jacobian.AlgebraicGeometry.Morphisms.FiniteLocallyFree
import Jacobian.AlgebraicGeometry.Norm.BasicOpen
import Jacobian.AlgebraicGeometry.AffineScheme.FiniteSet
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Invariant affine neighbourhoods

For finite flat morphisms locally of finite presentation, descent orbits are finite.
Prime avoidance and the norm of a section produce an invariant affine neighbourhood
of each point whenever each finite subset of a fibre has an affine neighbourhood.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {source base : Scheme.{schemeUniverse}} {projection : source ⟶ base}
  {representation : Over source} (datum : DescentDatum projection representation)

@[reassoc]
private theorem toHom_comp_hom_comp :
    datum.toHom ≫ representation.hom ≫ projection =
      pullback.fst (representation.hom ≫ projection) projection ≫ representation.hom ≫ projection := by
  rw [toHom_comp_hom_assoc, pullback.condition]

private theorem toHom_apply_hom_comp (orbitPoint : ↥(Limits.pullback (representation.hom ≫ projection) projection)) :
    (representation.hom ≫ projection) (datum.toHom orbitPoint) =
      (representation.hom ≫ projection)
        (pullback.fst (representation.hom ≫ projection) projection orbitPoint) := by
  rw [← Scheme.Hom.comp_apply, datum.toHom_comp_hom_comp, Scheme.Hom.comp_apply]

private theorem exists_fst_eq_toHom_eq (point : representation.left) :
    ∃ orbitPoint, pullback.fst (representation.hom ≫ projection) projection orbitPoint = point ∧ datum.toHom orbitPoint = point := by
  refine ⟨pullback.lift (𝟙 representation.left) representation.hom (by simp) point, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl
  · rw [← Scheme.Hom.comp_apply, lift_toHom]
    rfl

private theorem lift_fst_snd_condition {testScheme : Scheme.{schemeUniverse}}
    (firstPoint secondPoint : testScheme ⟶ Limits.pullback (representation.hom ≫ projection) projection)
    (compatibility : firstPoint ≫ datum.toHom = secondPoint ≫ pullback.fst (representation.hom ≫ projection) projection) :
    (firstPoint ≫ pullback.fst (representation.hom ≫ projection) projection) ≫
        representation.hom ≫ projection =
      (secondPoint ≫ pullback.snd (representation.hom ≫ projection) projection) ≫ projection := by
  rw [Category.assoc, ← datum.toHom_comp_hom_comp, reassoc_of% compatibility, pullback.condition,
    Category.assoc]

private theorem lift_fst_snd_toHom {testScheme : Scheme.{schemeUniverse}}
    (firstPoint secondPoint : testScheme ⟶ Limits.pullback (representation.hom ≫ projection) projection)
    (compatibility : firstPoint ≫ datum.toHom = secondPoint ≫ pullback.fst (representation.hom ≫ projection) projection) :
    pullback.lift (firstPoint ≫ pullback.fst (representation.hom ≫ projection) projection)
      (secondPoint ≫ pullback.snd (representation.hom ≫ projection) projection)
      (datum.lift_fst_snd_condition firstPoint secondPoint compatibility) ≫ datum.toHom = secondPoint ≫ datum.toHom := by
  have first_eq : (firstPoint ≫ pullback.fst (representation.hom ≫ projection) projection ≫ representation.hom) ≫ projection =
      (firstPoint ≫ pullback.snd (representation.hom ≫ projection) projection) ≫ projection := by
    simp only [Category.assoc, pullback.condition]
  have second_eq :
      (firstPoint ≫ pullback.snd (representation.hom ≫ projection) projection) ≫ projection =
        (secondPoint ≫ pullback.snd (representation.hom ≫ projection) projection) ≫ projection := by
    simp only [Category.assoc, ← pullback.condition, ← reassoc_of% compatibility, datum.toHom_comp_hom_comp]
  let firstSection : Over.mk (firstPoint ≫ pullback.fst (representation.hom ≫ projection) projection ≫ representation.hom) ⟶ representation :=
    Over.homMk (firstPoint ≫ pullback.fst (representation.hom ≫ projection) projection) (by simp)
  let secondSection : Over.mk (firstPoint ≫ pullback.snd (representation.hom ≫ projection) projection) ⟶ representation :=
    Over.homMk (secondPoint ≫ pullback.fst (representation.hom ≫ projection) projection) (by
      rw [← compatibility, Category.assoc, toHom_comp_hom]
      rfl)
  have transport_eq : (datum.transport _ _ first_eq firstSection).left = secondSection.left := by
    rw [datum.transport_left_eq_lift_toHom]
    refine (congrArg (· ≫ datum.toHom) ?_).trans compatibility
    ext <;> simp [firstSection]
  have cocycle_eq := datum.transport_left_eq_lift_toHom _ _ (first_eq.trans second_eq) firstSection
  rw [← datum.transport_transport _ _ _ first_eq second_eq, datum.transport_left_congr second_eq second_eq _ secondSection rfl rfl transport_eq,
    datum.transport_left_eq_lift_toHom] at cocycle_eq
  refine cocycle_eq.symm.trans ?_
  congr 1
  ext <;> simp [secondSection]

private theorem exists_fst_eq_toHom_eq_of_toHom_eq_fst
    (firstOrbitPoint secondOrbitPoint : ↥(Limits.pullback (representation.hom ≫ projection) projection))
    (hypothesis : datum.toHom firstOrbitPoint = pullback.fst (representation.hom ≫ projection) projection secondOrbitPoint) :
    ∃ combinedOrbitPoint,
      pullback.fst (representation.hom ≫ projection) projection combinedOrbitPoint =
        pullback.fst (representation.hom ≫ projection) projection firstOrbitPoint ∧
      datum.toHom combinedOrbitPoint = datum.toHom secondOrbitPoint := by
  obtain ⟨witness, first_projection_eq, second_projection_eq⟩ := Scheme.Pullback.exists_preimage_pullback firstOrbitPoint secondOrbitPoint hypothesis
  refine ⟨pullback.lift _ _ (datum.lift_fst_snd_condition _ _ pullback.condition) witness, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, first_projection_eq]
  · rw [← Scheme.Hom.comp_apply, datum.lift_fst_snd_toHom _ _ pullback.condition,
      Scheme.Hom.comp_apply, second_projection_eq]

private theorem isInvariant_of_forall_mem_iff (openSubset : representation.left.Opens) (orbitSet : Set representation.left)
    (open_iff : ∀ point, point ∈ openSubset ↔ ∀ orbitPoint,
      pullback.fst (representation.hom ≫ projection) projection orbitPoint = point →
        datum.toHom orbitPoint ∈ orbitSet) :
    datum.IsInvariant openSubset := by
  refine (datum.isInvariant_iff openSubset).mpr fun orbitPoint orbit_eq ↦ (open_iff _).mpr fun nextOrbitPoint nextOrbit_eq ↦ ?_
  obtain ⟨combinedOrbitPoint, projection_eq, transport_eq⟩ := datum.exists_fst_eq_toHom_eq_of_toHom_eq_fst orbitPoint nextOrbitPoint nextOrbit_eq.symm
  exact transport_eq ▸ (open_iff _).mp orbit_eq combinedOrbitPoint projection_eq

private theorem isOpen_setOf_forall_toHom_mem [IsFinite projection] {orbitSet : Set representation.left} (set_open : IsOpen orbitSet) :
    IsOpen {point | ∀ orbitPoint,
      pullback.fst (representation.hom ≫ projection) projection orbitPoint = point →
        datum.toHom orbitPoint ∈ orbitSet} := by
  have complement_eq : {point | ∀ orbitPoint,
      pullback.fst (representation.hom ≫ projection) projection orbitPoint = point →
        datum.toHom orbitPoint ∈ orbitSet} =
      (pullback.fst (representation.hom ≫ projection) projection '' (datum.toHom ⁻¹' orbitSetᶜ))ᶜ := by
    ext point
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage,
      not_exists, not_and]
    exact forall_congr' fun orbitPoint ↦
      ⟨fun hypothesis orbit_eq point_mem ↦ orbit_eq (hypothesis point_mem),
        fun hypothesis point_mem ↦ by_contra (hypothesis · point_mem)⟩
  rw [complement_eq, isOpen_compl_iff]
  exact (pullback.fst (representation.hom ≫ projection) projection).isClosedMap _
    (set_open.isClosed_compl.preimage datum.toHom.continuous)

/-- Finite fibres contained in affine opens give invariant affine neighbourhoods for firstPoint
finite, flat morphism locally of finite presentation. -/
theorem exists_isInvariant_isAffineOpen_of_fibre [IsFinite projection] [Flat projection]
    [LocallyOfFinitePresentation projection] (datum : DescentDatum projection representation)
    (finite_affine : ∀ (basePoint : base) (finiteSet : Set representation.left), finiteSet.Finite →
      (∀ point ∈ finiteSet, (representation.hom ≫ projection) point = basePoint) →
      ∃ openSubset : representation.left.Opens, IsAffineOpen openSubset ∧ finiteSet ⊆ openSubset)
    (basePoint : representation.left) :
    ∃ openSubset : representation.left.Opens, basePoint ∈ openSubset ∧ datum.IsInvariant openSubset ∧ IsAffineOpen openSubset ∧
      ∃ baseOpen : base.Opens, IsAffineOpen baseOpen ∧ openSubset ≤ (representation.hom ≫ projection) ⁻¹ᵁ baseOpen := by
  obtain ⟨baseOpen, baseOpen_affine, basePoint_mem, free_sections⟩ :=
    projection.exists_isAffineOpen_mem_free_app ((representation.hom ≫ projection) basePoint)

  let orbit := datum.toHom '' (pullback.fst (representation.hom ≫ projection) projection ⁻¹' {basePoint})
  have orbit_finite : orbit.Finite :=
    ((pullback.fst (representation.hom ≫ projection) projection).finite_preimage_singleton basePoint).image _
  obtain ⟨affineOpen, affineOpen_affine, orbit_affine⟩ := finite_affine ((representation.hom ≫ projection) basePoint) orbit orbit_finite (by
    rintro _ ⟨orbitPoint, orbit_eq, rfl⟩
    rw [datum.toHom_apply_hom_comp, Set.mem_singleton_iff.mp orbit_eq])
  let wholeOrbitOpen : representation.left.Opens := ⟨_, datum.isOpen_setOf_forall_toHom_mem
    (affineOpen ⊓ (representation.hom ≫ projection) ⁻¹ᵁ baseOpen).isOpen⟩
  have wholeOrbit_le : wholeOrbitOpen ≤ affineOpen ⊓ (representation.hom ≫ projection) ⁻¹ᵁ baseOpen := fun point point_mem ↦ by
    obtain ⟨orbitPoint, projection_eq, transport_eq⟩ := datum.exists_fst_eq_toHom_eq point
    exact transport_eq ▸ point_mem orbitPoint projection_eq
  have orbit_wholeOrbit : orbit ⊆ wholeOrbitOpen := by
    rintro _ ⟨firstOrbitPoint, firstOrbit_eq, rfl⟩ orbitPoint orbit_eq
    obtain ⟨combinedOrbitPoint, projection_eq, transport_eq⟩ := datum.exists_fst_eq_toHom_eq_of_toHom_eq_fst firstOrbitPoint orbitPoint orbit_eq.symm
    have combinedOrbit_mem : datum.toHom orbitPoint ∈ orbit := ⟨combinedOrbitPoint, projection_eq.trans firstOrbit_eq, transport_eq⟩
    refine ⟨orbit_affine combinedOrbit_mem, ?_⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← transport_eq, datum.toHom_apply_hom_comp, projection_eq,
      Set.mem_singleton_iff.mp firstOrbit_eq]
    exact basePoint_mem

  obtain ⟨localSection, orbit_basicOpen, basicOpen_wholeOrbit⟩ :=
    affineOpen_affine.exists_basicOpen_le_of_finite
      (O := wholeOrbitOpen ⊓ affineOpen) inf_le_right orbit_finite
    (Set.subset_inter orbit_wholeOrbit orbit_affine)
  have basicOpen_baseOpen : representation.left.basicOpen localSection ≤ (representation.hom ≫ projection) ⁻¹ᵁ baseOpen :=
    basicOpen_wholeOrbit.trans (inf_le_left.trans (wholeOrbit_le.trans inf_le_right))
  have free_pullback_sections := free_app_of_isPullback (IsPullback.of_hasPullback (representation.hom ≫ projection) projection) baseOpen_affine
    (baseOpen_affine.preimage projection) (affineOpen_affine.basicOpen localSection) basicOpen_baseOpen free_sections
  have projection_open_le :
      pullback.fst (representation.hom ≫ projection) projection ⁻¹ᵁ
        representation.left.basicOpen localSection ≤ datum.toHom ⁻¹ᵁ affineOpen :=
    fun orbitPoint orbit_eq ↦ ((inf_le_left : wholeOrbitOpen ⊓ affineOpen ≤ wholeOrbitOpen) (basicOpen_wholeOrbit orbit_eq) orbitPoint rfl).1

  let pulledSection := datum.toHom.appLE affineOpen
    (pullback.fst (representation.hom ≫ projection) projection ⁻¹ᵁ
      representation.left.basicOpen localSection) projection_open_le localSection
  letI := ((pullback.fst (representation.hom ≫ projection) projection).app (representation.left.basicOpen localSection)).hom.toAlgebra
  let normSection := Algebra.norm Γ(representation.left, representation.left.basicOpen localSection) pulledSection
  have key (point : representation.left) : point ∈ representation.left.basicOpen normSection ↔
      ∀ orbitPoint, pullback.fst (representation.hom ≫ projection) projection orbitPoint = point →
        datum.toHom orbitPoint ∈ representation.left.basicOpen localSection := by
    have norm_iff (point_mem : point ∈ representation.left.basicOpen localSection) :=
      mem_basicOpen_norm_of_free _ (affineOpen_affine.basicOpen localSection) free_pullback_sections pulledSection point_mem
    refine ⟨fun point_mem orbitPoint orbit_eq ↦ ?_, fun point_mem ↦ ?_⟩
    · have := (norm_iff (representation.left.basicOpen_le normSection point_mem)).mp point_mem orbitPoint orbit_eq
      rw [Scheme.basicOpen_appLE] at this
      exact this.2
    · obtain ⟨orbitPoint, projection_eq, transport_eq⟩ := datum.exists_fst_eq_toHom_eq point
      have point_basicOpen : point ∈ representation.left.basicOpen localSection := transport_eq ▸ point_mem orbitPoint projection_eq
      refine (norm_iff point_basicOpen).mpr fun orbitPoint orbit_eq ↦ ?_
      rw [Scheme.basicOpen_appLE]
      refine ⟨?_, point_mem orbitPoint orbit_eq⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, orbit_eq]
      exact point_basicOpen
  exact ⟨representation.left.basicOpen normSection, (key basePoint).mpr fun orbitPoint orbit_eq ↦ orbit_basicOpen ⟨orbitPoint, orbit_eq, rfl⟩,
    datum.isInvariant_of_forall_mem_iff _ _ key, (affineOpen_affine.basicOpen localSection).basicOpen normSection, baseOpen, baseOpen_affine,
    (representation.left.basicOpen_le normSection).trans basicOpen_baseOpen⟩

/-- The affine-neighbourhood property for finite sets passes to invariant neighbourhoods. -/
theorem exists_isInvariant_isAffineOpen [IsFinite projection] [Flat projection] [LocallyOfFinitePresentation projection]
    (datum : DescentDatum projection representation)
    (finite_affine : ∀ finiteSet : Set representation.left, finiteSet.Finite →
      ∃ openSubset : representation.left.Opens, IsAffineOpen openSubset ∧ finiteSet ⊆ openSubset)
    (basePoint : representation.left) :
    ∃ openSubset : representation.left.Opens, basePoint ∈ openSubset ∧ datum.IsInvariant openSubset ∧ IsAffineOpen openSubset ∧
      ∃ baseOpen : base.Opens, IsAffineOpen baseOpen ∧ openSubset ≤ (representation.hom ≫ projection) ⁻¹ᵁ baseOpen :=
  datum.exists_isInvariant_isAffineOpen_of_fibre (fun _ finiteSet finiteSet_finite _ ↦ finite_affine finiteSet finiteSet_finite) basePoint

end CategoryTheory.Over.DescentDatum
