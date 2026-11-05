import Jacobian.AlgebraicGeometry.Group.CartierDivisors
import Jacobian.AlgebraicGeometry.Picard.LocalizationAwayRigidity

/-!
# Ample families on smooth irreducible groups

Translated Cartier complements provide affine covers. Rigidity of line bundles
along localized affine space identifies their divisor line bundles, giving a
finite affine nonvanishing cover by sections of one invertible module.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe schemeUniverse

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

section AlgClosed

variable {baseField : Type schemeUniverse} [Field baseField] [IsAlgClosed baseField]

local notation "pt" => unitPoint baseField

section Group

variable (group : Over (Spec (.of baseField))) [GrpObj group]

omit [GrpObj group] in

theorem hasAmpleFamily_of_forall_isAffineOpen [LocallyOfFiniteType group.hom]
    [QuasiCompact group.hom] [IsIntegral group.left]
    (hG : ∀ point : group.left, UniqueFactorizationMonoid (group.left.presheaf.stalk point)) {dimension : ℕ}
    (localizer : MvPolynomial (Fin dimension) baseField)
    (imageIdeal : (group ⊗ Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap baseField (Localization.Away localizer))))).left.IdealSheafData) (hE : imageIdeal.IsInvertible)
    (haff : ∀ rationalPoint, IsAffineOpen (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ rationalPoint)).left).support.compl)
    (hcov : ∀ point : group.left, IsClosed {point} →
      ∃ rationalPoint, point ∉ (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ rationalPoint)).left).support) :
    group.left.HasAmpleFamily := by
  have : CompactSpace group.left := QuasiCompact.compactSpace_of_compactSpace group.hom
  have : JacobsonSpace group.left := LocallyOfFiniteType.jacobsonSpace group.hom
  let indexType := {rationalPoint // ∃ point, point ∉ (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ rationalPoint)).left).support}
  have hT (familyIndex : indexType) : (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ familyIndex.1)).left).IsInvertible := by
    refine (hE.isLocallyPrincipal.comap _).isInvertible fun compatibility ↦ ?_
    obtain ⟨point, hx⟩ := familyIndex.2
    exact hx (by rw [compatibility, Scheme.IdealSheafData.support_bot]; trivial)
  obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := group.left)).exists_closed_singleton
    ⟨Classical.arbitrary _, trivial⟩
  obtain ⟨v₀, hv₀⟩ := hcov x₀ hx₀
  let t₀ : indexType := ⟨v₀, x₀, hv₀⟩
  have he (familyIndex : indexType) : Nonempty ((imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ familyIndex.1)).left).toModulesᵛ ≅
      (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ t₀.1)).left).toModulesᵛ) := by
    obtain ⟨firstEquivalence⟩ := hE.nonempty_pullback_dual_toModules_iso _ (hT familyIndex)
    obtain ⟨secondEquivalence⟩ := hE.nonempty_pullback_dual_toModules_iso _ (hT t₀)
    obtain ⟨equivalence⟩ := @nonempty_iso_pullback_lift_of_isAlgClosed_mvPolynomial
      baseField _ _ group.left _ hG group.hom dimension localizer
      familyIndex.1.left t₀.1.left (Over.w familyIndex.1) (Over.w t₀.1)
      imageIdeal.toModulesᵛ hE.isInvertible_dual_toModules
    exact ⟨firstEquivalence.symm ≪≫ equivalence ≪≫ secondEquivalence⟩
  have := (hT t₀).isInvertible_dual_toModules
  have hs (familyIndex : indexType) := (hT familyIndex).exists_zeroLocus_eq_of_iso (he familyIndex).some
  refine Scheme.HasAmpleFamily.of_forall_isClosed _ (fun familyIndex ↦ (hs familyIndex).choose) (fun familyIndex ↦ ?_)
    fun point hx ↦ ?_
  · rw [(hs familyIndex).choose_spec]
    exact haff familyIndex.1
  · obtain ⟨rationalPoint, hv⟩ := hcov point hx
    exact ⟨⟨rationalPoint, point, hv⟩, by rw [(hs _).choose_spec]; exact hv⟩

omit [IsAlgClosed baseField] in

instance GrpObj.flat_mul_left [Flat group.hom] : Flat μ[group].left := by
  have compatibility : μ[group] = (CategoryTheory.GrpObj.shearIso group).hom ≫ snd group group := by
    simp [CategoryTheory.GrpObj.shearIso, Hom.mul_def]
  have : IsIso (CategoryTheory.GrpObj.shearIso group).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (CategoryTheory.GrpObj.shearIso group)).hom)
  rw [compatibility, Over.comp_left, Over.snd_left]
  infer_instance

theorem GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace [LocallyOfFiniteType group.hom]
    [QuasiCompact group.hom] [Smooth group.hom] [IrreducibleSpace group.left] :
    group.left.HasAmpleFamily := by
  have := IsRegular.of_smooth group.hom
  have := LocallyOfFiniteType.isLocallyNoetherian group.hom
  have := QuasiCompact.compactSpace_of_compactSpace group.hom
  have : IsNoetherian group.left := {}
  have : IsIntegral group.left := IsRegular.isIntegral group.left
  have hG := IsRegular.uniqueFactorizationMonoid_stalk (scheme := group.left)
  have : group.left.IsSeparated := ⟨by rw [← terminal.comp_from group.hom]; infer_instance⟩
  obtain ⟨x₀⟩ : Nonempty group.left := inferInstance
  obtain ⟨affineOpen, hU, hx₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := x₀) (U := ⊤) trivial
  obtain ⟨cartierIdeal, hJ, hJU⟩ := group.left.exists_isInvertible_support_eq_compl hG hU ⟨x₀, hx₀U⟩
  obtain ⟨chart, chartImmersion, dimension, localizer, finiteMap, hj, hWa, hWne, hr, hπf, hπfl, hπlfp, hcomm⟩ :=
    exists_finite_flat_chart group.left group.hom
  have := smooth_specMap_algebraMap_localizationAway localizer
  have := geometricallyIrreducible_specMap_algebraMap_localizationAway hr
  let parameterSpace : Over (Spec (.of baseField)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))))
  let jo : Over.mk (chartImmersion ≫ group.hom) ⟶ group := Over.homMk chartImmersion
  let πo : Over.mk (chartImmersion ≫ group.hom) ⟶ parameterSpace := Over.homMk finiteMap hcomm.symm
  have : LocallyOfFiniteType (Over.mk (chartImmersion ≫ group.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (chartImmersion ≫ group.hom))
  have : LocallyOfFiniteType parameterSpace.hom := inferInstanceAs (LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer)))))
  have : LocallyOfFiniteType (group ⊗ Over.mk (chartImmersion ≫ group.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst group.hom (chartImmersion ≫ group.hom) ≫ group.hom))
  have : Smooth (group ⊗ parameterSpace).hom := inferInstanceAs (Smooth (pullback.fst group.hom
    (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer)))) ≫ group.hom))
  have := IsRegular.of_smooth (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))))
  have : IsDomain (Localization.Away localizer) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have : CompactSpace (group ⊗ Over.mk (chartImmersion ≫ group.hom)).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd group.hom (chartImmersion ≫ group.hom))
  have := IsRegular.of_smooth (group ⊗ parameterSpace).hom
  have := LocallyOfFiniteType.isLocallyNoetherian (group ⊗ parameterSpace).hom
  have : IrreducibleSpace (group ⊗ parameterSpace).left :=
    inferInstanceAs (IrreducibleSpace ↥(Limits.pullback group.hom
      (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))))))
  have : IsIntegral (group ⊗ parameterSpace).left := IsRegular.isIntegral _
  have : IsFinite (group ◁ πo).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (MorphismProperty.id_mem _ _) hπf (by simp) hcomm
  have : Flat (group ◁ πo).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (MorphismProperty.id_mem _ _) hπfl (by simp) hcomm
  have : Flat ((group ◁ jo) ≫ μ[group]).left := by
    rw [Over.comp_left, Over.whiskerLeft_left]
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.pullbackMap
      (MorphismProperty.id_mem _ _) (inferInstanceAs (Flat chartImmersion)) (by simp) (by simp)) inferInstance
  obtain ⟨imageIdeal, hE, hEs⟩ := Scheme.Hom.exists_isInvertible_support_eq_image (group ◁ πo).left
    IsRegular.uniqueFactorizationMonoid_stalk (hJ.comap_of_flat ((group ◁ jo) ≫ μ[group]).left)
  have : IsFinite πo.left := hπf
  have : Flat jo.left := inferInstanceAs (Flat chartImmersion)
  have : CompactSpace (Over.mk (chartImmersion ≫ group.hom)).left := inferInstanceAs (CompactSpace chart)
  have hsurj : Function.Surjective finiteMap := by
    have hcl : IsClopen (Set.range finiteMap) := ⟨finiteMap.isClosedMap.isClosed_range, finiteMap.isOpenMap.isOpen_range⟩
    exact Set.range_eq_univ.mp (hcl.eq_univ ⟨_, hWne.some, rfl⟩)
  refine hasAmpleFamily_of_forall_isAffineOpen group hG localizer imageIdeal hE (fun rationalPoint ↦ ?_) fun point hx ↦ ?_
  · rw [GrpObj.compl_support_comap_eq group jo πo cartierIdeal imageIdeal hEs hJU rationalPoint]
    have := finite_hom_comp_eq πo rationalPoint
    obtain ⟨member, hw, -⟩ := (left_apply_mem_image_iff πo isClosed_univ rationalPoint).mp (by
      obtain ⟨targetPoint, hy⟩ := hsurj (rationalPoint.left (unitPoint baseField))
      exact ⟨targetPoint, trivial, hy⟩)
    have : Nonempty {member // member ≫ πo = rationalPoint} := ⟨⟨member, hw⟩⟩
    exact IsAffineOpen.iInf fun member ↦ hU.preimage _
  · have : Nonempty parameterSpace.left := ⟨finiteMap hWne.some⟩
    exact GrpObj.exists_notMem_support_comap group jo πo cartierIdeal imageIdeal
      (fun C hC ↦ Scheme.Hom.exists_isInvertible_support_eq_image finiteMap
        IsRegular.uniqueFactorizationMonoid_stalk hC) hJ hEs point hx

end Group

end AlgClosed

end AlgebraicGeometry
