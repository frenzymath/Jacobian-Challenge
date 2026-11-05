import Jacobian.AlgebraicGeometry.Modules.Flat
import Jacobian.AlgebraicGeometry.Modules.BaseChange
import Jacobian.AlgebraicGeometry.Pullbacks.AffineOpen
import Jacobian.RingTheory.Flat.TensorProduct

/-!
# Affine-local criteria for relative flatness

Relative flatness of a quasi-coherent module is local on the source. Over an
affine base, flatness of the sections of a pullback on products of affine opens
is equivalent to flatness of the corresponding scalar-extended module.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory Opposite Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme baseScheme : Scheme.{u}}

/-- Relative flatness of a quasi-coherent module follows from flatness of
affine sections on a neighborhood of every point over each affine base open. -/
theorem isFlatOver_of_forall_exists_nhds (structureMap : sourceScheme ⟶ baseScheme) (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsQuasicoherent]
    (h : ∀ (baseOpen : baseScheme.affineOpens) (point : sourceScheme), point ∈ structureMap ⁻¹ᵁ baseOpen.1 → ∃ neighborhood : sourceScheme.Opens, point ∈ neighborhood ∧
      ∀ (openSubset : sourceScheme.affineOpens) (inclusion : openSubset.1 ≤ structureMap ⁻¹ᵁ baseOpen.1), openSubset.1 ≤ neighborhood →
        letI : Module Γ(baseScheme, baseOpen.1) Γ(moduleSheaf, openSubset.1) := Module.compHom _ (structureMap.appLE baseOpen.1 openSubset.1 inclusion).hom
        Module.Flat Γ(baseScheme, baseOpen.1) Γ(moduleSheaf, openSubset.1)) :
    moduleSheaf.IsFlatOver structureMap := by
  intro baseOpen sourceOpen inclusion
  let : Algebra Γ(baseScheme, baseOpen.1) Γ(sourceScheme, sourceOpen.1) := (structureMap.appLE baseOpen.1 sourceOpen.1 inclusion).hom.toAlgebra
  let : Module Γ(baseScheme, baseOpen.1) Γ(moduleSheaf, sourceOpen.1) := Module.compHom _ (structureMap.appLE baseOpen.1 sourceOpen.1 inclusion).hom
  have : IsScalarTower Γ(baseScheme, baseOpen.1) Γ(sourceScheme, sourceOpen.1) Γ(moduleSheaf, sourceOpen.1) := ⟨fun coefficient scalar moduleElement ↦ mul_smul _ _ _⟩
  choose neighborhood hxN hN using fun point : sourceOpen.1 ↦ h baseOpen point (inclusion point.2)
  choose localizer hgN hxg using fun point : sourceOpen.1 ↦ sourceOpen.2.exists_basicOpen_le ⟨point.1, hxN point⟩ point.2
  let localizers : Set Γ(sourceScheme, sourceOpen.1) := Set.range localizer
  have spn : Ideal.span localizers = ⊤ := by
    rw [← sourceOpen.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun element ↦ sourceScheme.basicOpen_le _) fun point hx ↦ ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨localizer ⟨point, hx⟩, ⟨point, hx⟩, rfl⟩, hxg ⟨point, hx⟩⟩
  let Mₛ (element : localizers) : Type u := Γ(moduleSheaf, sourceScheme.basicOpen element.1)
  have hle (element : localizers) : sourceScheme.basicOpen element.1 ≤ structureMap ⁻¹ᵁ baseOpen.1 := (sourceScheme.basicOpen_le _).trans inclusion
  let (element : localizers) : Module Γ(sourceScheme, sourceOpen.1) (Mₛ element) :=
    Module.compHom _ (algebraMap Γ(sourceScheme, sourceOpen.1) Γ(sourceScheme, sourceScheme.basicOpen element.1))
  let (element : localizers) : Module Γ(baseScheme, baseOpen.1) (Mₛ element) := Module.compHom _ (structureMap.appLE baseOpen.1 _ (hle element)).hom
  have (element : localizers) : IsScalarTower Γ(baseScheme, baseOpen.1) Γ(sourceScheme, sourceOpen.1) (Mₛ element) := by
    refine ⟨fun coefficient scalar moduleElement ↦ ?_⟩
    change (algebraMap Γ(sourceScheme, sourceOpen.1) Γ(sourceScheme, sourceScheme.basicOpen element.1) ((structureMap.appLE baseOpen.1 sourceOpen.1 inclusion).hom coefficient * scalar)) • moduleElement =
      (structureMap.appLE baseOpen.1 _ (hle element)).hom coefficient • (algebraMap Γ(sourceScheme, sourceOpen.1) Γ(sourceScheme, sourceScheme.basicOpen element.1) scalar • moduleElement)
    rw [map_mul, mul_smul]
    congr 1
    rw [← structureMap.appLE_map inclusion (homOfLE (sourceScheme.basicOpen_le element.1)).op]
    rfl
  let gₛ (element : localizers) : Γ(moduleSheaf, sourceOpen.1) →ₗ[Γ(sourceScheme, sourceOpen.1)] Mₛ element :=
    { toFun := moduleSheaf.presheaf.map (homOfLE (sourceScheme.basicOpen_le element.1)).op
      map_add' := map_add _
      map_smul' := map_smul moduleSheaf _ }
  have (element : localizers) : IsLocalizedModule.Away element.1 (gₛ element) := isLocalizedModule_basicOpen moduleSheaf sourceOpen.2 element.1
  refine Module.flat_of_isLocalized_span Γ(sourceScheme, sourceOpen.1) Γ(moduleSheaf, sourceOpen.1) localizers spn Mₛ gₛ fun element ↦ ?_
  obtain ⟨_, ⟨point, rfl⟩⟩ := element
  exact hN point ⟨_, sourceOpen.2.basicOpen _⟩ (hle _) (hgN point)

section PullbackFst

variable {affineBase firstScheme secondScheme : Scheme.{u}} [IsAffine affineBase] (gY : firstScheme ⟶ affineBase) (gZ : secondScheme ⟶ affineBase) (moduleSheaf : firstScheme.Modules)
  [moduleSheaf.IsQuasicoherent] {sourceOpen : firstScheme.Opens} {baseOpen : secondScheme.Opens}

set_option backward.isDefEq.respectTransparency false in
/-- Flatness of the scalar-extended affine sections implies flatness of
sections of the pulled-back module on every smaller affine open of the
corresponding product open. -/
theorem flat_sections_pullback_fst_of_flat_baseChange
    (hW : IsAffineOpen sourceOpen) (hV : IsAffineOpen baseOpen)
    {openSubset : (Limits.pullback gY gZ).Opens} (hU : IsAffineOpen openSubset)
    (hUle : openSubset ≤ pullback.fst gY gZ ⁻¹ᵁ sourceOpen ⊓ pullback.snd gY gZ ⁻¹ᵁ baseOpen)
    (hflat : letI := (gZ.appLE ⊤ baseOpen le_top).hom.toAlgebra
      letI : Module Γ(affineBase, ⊤) Γ(moduleSheaf, sourceOpen) := Module.compHom _ (gY.appLE ⊤ sourceOpen le_top).hom
      Module.Flat Γ(secondScheme, baseOpen) (Γ(secondScheme, baseOpen) ⊗[Γ(affineBase, ⊤)] Γ(moduleSheaf, sourceOpen))) :
    letI : Module Γ(secondScheme, baseOpen) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj moduleSheaf, openSubset) :=
      Module.compHom _ ((pullback.snd gY gZ).appLE baseOpen openSubset (hUle.trans inf_le_right)).hom
    Module.Flat Γ(secondScheme, baseOpen) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj moduleSheaf, openSubset) := by
  set firstProjection := pullback.fst gY gZ
  set structureMap := pullback.snd gY gZ
  set productOpen := firstProjection ⁻¹ᵁ sourceOpen ⊓ structureMap ⁻¹ᵁ baseOpen
  have hΩ : IsAffineOpen productOpen := isAffineOpen_preimage_inf_preimage_pullback gY gZ hW hV
  have hUV : openSubset ≤ structureMap ⁻¹ᵁ baseOpen := hUle.trans inf_le_right
  have hUW' : openSubset ≤ firstProjection ⁻¹ᵁ sourceOpen := hUle.trans inf_le_left
  let : Algebra Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) := (gY.appLE ⊤ sourceOpen le_top).hom.toAlgebra
  let : Algebra Γ(affineBase, ⊤) Γ(secondScheme, baseOpen) := (gZ.appLE ⊤ baseOpen le_top).hom.toAlgebra
  let : Algebra Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen) := (firstProjection.appLE sourceOpen productOpen inf_le_left).hom.toAlgebra
  let : Algebra Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) := (structureMap.appLE baseOpen productOpen inf_le_right).hom.toAlgebra
  let : Algebra Γ(affineBase, ⊤) Γ(Limits.pullback gY gZ, productOpen) :=
    (gY.appLE ⊤ sourceOpen le_top ≫ firstProjection.appLE sourceOpen productOpen inf_le_left).hom.toAlgebra
  let : Algebra Γ(Limits.pullback gY gZ, productOpen) Γ(Limits.pullback gY gZ, openSubset) :=
    ((Limits.pullback gY gZ).presheaf.map (homOfLE hUle).op).hom.toAlgebra
  let : Algebra Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, openSubset) := (structureMap.appLE baseOpen openSubset hUV).hom.toAlgebra
  let : Algebra Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, openSubset) := (firstProjection.appLE sourceOpen openSubset hUW').hom.toAlgebra
  have : IsScalarTower Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(affineBase, ⊤) Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) := by
    refine IsScalarTower.of_algebraMap_eq fun element ↦ ?_
    change (gY.appLE ⊤ sourceOpen le_top ≫ firstProjection.appLE sourceOpen productOpen inf_le_left) element =
      (gZ.appLE ⊤ baseOpen le_top ≫ structureMap.appLE baseOpen productOpen inf_le_right) element
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [pullback.condition, firstProjection, structureMap]
  have : IsScalarTower Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) Γ(Limits.pullback gY gZ, openSubset) := by
    refine IsScalarTower.of_algebraMap_eq fun element ↦ ?_
    change (structureMap.appLE baseOpen openSubset hUV) element = (structureMap.appLE baseOpen productOpen inf_le_right ≫
      (Limits.pullback gY gZ).presheaf.map (homOfLE hUle).op) element
    rw [Scheme.Hom.appLE_map]
  have : IsScalarTower Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen) Γ(Limits.pullback gY gZ, openSubset) := by
    refine IsScalarTower.of_algebraMap_eq fun element ↦ ?_
    change (firstProjection.appLE sourceOpen openSubset hUW') element = (firstProjection.appLE sourceOpen productOpen inf_le_left ≫
      (Limits.pullback gY gZ).presheaf.map (homOfLE hUle).op) element
    rw [Scheme.Hom.appLE_map]
  have hpush : Algebra.IsPushout Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) := by
    have hiso := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback gY gZ)
      (le_top : baseOpen ≤ gZ ⁻¹ᵁ ⊤) (le_top : sourceOpen ≤ gY ⁻¹ᵁ ⊤) (UY := productOpen) rfl (isAffineOpen_top _) hV hW
    exact CommRingCat.isPushout_iff_isPushout.mp ((isIso_pushoutSection_iff ..).mp hiso)
  have hpush' := hpush.symm
  obtain ⟨inclusion, -⟩ := exists_linearEquiv_pullback_sections firstProjection moduleSheaf hW hU hUW'
  let : Module Γ(affineBase, ⊤) Γ(moduleSheaf, sourceOpen) := Module.compHom _ (algebraMap Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen))
  have : IsScalarTower Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) Γ(moduleSheaf, sourceOpen) := ⟨fun coefficient scalar moduleElement ↦ mul_smul _ _ _⟩
  have hN : Module.Flat Γ(secondScheme, baseOpen) (Γ(Limits.pullback gY gZ, productOpen) ⊗[Γ(firstScheme, sourceOpen)] Γ(moduleSheaf, sourceOpen)) :=
    @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat (Algebra.IsPushout.cancelBaseChange Γ(affineBase, ⊤)
      Γ(secondScheme, baseOpen) Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen) Γ(moduleSheaf, sourceOpen))
  have hΩU : Module.Flat Γ(Limits.pullback gY gZ, productOpen) Γ(Limits.pullback gY gZ, openSubset) :=
    Scheme.Hom.flat_appLE (𝟙 (Limits.pullback gY gZ)) hΩ hU hUle
  have := Module.Flat.tensorProduct_of_flat Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen)
    Γ(Limits.pullback gY gZ, openSubset) (Γ(Limits.pullback gY gZ, productOpen) ⊗[Γ(firstScheme, sourceOpen)] Γ(moduleSheaf, sourceOpen))
  let : Module Γ(secondScheme, baseOpen) Γ((Modules.pullback firstProjection).obj moduleSheaf, openSubset) :=
    Module.compHom _ (structureMap.appLE baseOpen openSubset hUV).hom
  have : IsScalarTower Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, openSubset) Γ((Modules.pullback firstProjection).obj moduleSheaf, openSubset) :=
    ⟨fun coefficient scalar moduleElement ↦ mul_smul _ _ _⟩
  exact Module.Flat.of_linearEquiv (((AlgebraTensorModule.cancelBaseChange Γ(firstScheme, sourceOpen)
    Γ(Limits.pullback gY gZ, productOpen) Γ(Limits.pullback gY gZ, openSubset) Γ(Limits.pullback gY gZ, openSubset)
    Γ(moduleSheaf, sourceOpen)).trans inclusion).restrictScalars Γ(secondScheme, baseOpen)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Flatness of sections of the pulled-back module on a product of affine
opens implies flatness of the corresponding scalar-extended module. -/
theorem flat_baseChange_of_flat_sections_pullback_fst
    (hW : IsAffineOpen sourceOpen) (hV : IsAffineOpen baseOpen)
    (hflat : letI : Module Γ(secondScheme, baseOpen) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj moduleSheaf,
        pullback.fst gY gZ ⁻¹ᵁ sourceOpen ⊓ pullback.snd gY gZ ⁻¹ᵁ baseOpen) :=
      Module.compHom _ ((pullback.snd gY gZ).appLE baseOpen
        (pullback.fst gY gZ ⁻¹ᵁ sourceOpen ⊓ pullback.snd gY gZ ⁻¹ᵁ baseOpen) inf_le_right).hom
      Module.Flat Γ(secondScheme, baseOpen) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj moduleSheaf,
        pullback.fst gY gZ ⁻¹ᵁ sourceOpen ⊓ pullback.snd gY gZ ⁻¹ᵁ baseOpen)) :
    letI := (gZ.appLE ⊤ baseOpen le_top).hom.toAlgebra
    letI : Module Γ(affineBase, ⊤) Γ(moduleSheaf, sourceOpen) := Module.compHom _ (gY.appLE ⊤ sourceOpen le_top).hom
    Module.Flat Γ(secondScheme, baseOpen) (Γ(secondScheme, baseOpen) ⊗[Γ(affineBase, ⊤)] Γ(moduleSheaf, sourceOpen)) := by
  set firstProjection := pullback.fst gY gZ
  set structureMap := pullback.snd gY gZ
  set productOpen := firstProjection ⁻¹ᵁ sourceOpen ⊓ structureMap ⁻¹ᵁ baseOpen
  have hΩ : IsAffineOpen productOpen := isAffineOpen_preimage_inf_preimage_pullback gY gZ hW hV
  let : Algebra Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) := (gY.appLE ⊤ sourceOpen le_top).hom.toAlgebra
  let : Algebra Γ(affineBase, ⊤) Γ(secondScheme, baseOpen) := (gZ.appLE ⊤ baseOpen le_top).hom.toAlgebra
  let : Algebra Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen) := (firstProjection.appLE sourceOpen productOpen inf_le_left).hom.toAlgebra
  let : Algebra Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) := (structureMap.appLE baseOpen productOpen inf_le_right).hom.toAlgebra
  let : Algebra Γ(affineBase, ⊤) Γ(Limits.pullback gY gZ, productOpen) :=
    (gY.appLE ⊤ sourceOpen le_top ≫ firstProjection.appLE sourceOpen productOpen inf_le_left).hom.toAlgebra
  have : IsScalarTower Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(affineBase, ⊤) Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) := by
    refine IsScalarTower.of_algebraMap_eq fun element ↦ ?_
    change (gY.appLE ⊤ sourceOpen le_top ≫ firstProjection.appLE sourceOpen productOpen inf_le_left) element =
      (gZ.appLE ⊤ baseOpen le_top ≫ structureMap.appLE baseOpen productOpen inf_le_right) element
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [pullback.condition, firstProjection, structureMap]
  have hpush : Algebra.IsPushout Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) := by
    have hiso := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback gY gZ)
      (le_top : baseOpen ≤ gZ ⁻¹ᵁ ⊤) (le_top : sourceOpen ≤ gY ⁻¹ᵁ ⊤) (UY := productOpen) rfl (isAffineOpen_top _) hV hW
    exact CommRingCat.isPushout_iff_isPushout.mp ((isIso_pushoutSection_iff ..).mp hiso)
  have hpush' := hpush.symm
  obtain ⟨inclusion, -⟩ := exists_linearEquiv_pullback_sections firstProjection moduleSheaf hW hΩ inf_le_left
  let : Module Γ(affineBase, ⊤) Γ(moduleSheaf, sourceOpen) := Module.compHom _ (algebraMap Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen))
  have : IsScalarTower Γ(affineBase, ⊤) Γ(firstScheme, sourceOpen) Γ(moduleSheaf, sourceOpen) := ⟨fun coefficient scalar moduleElement ↦ mul_smul _ _ _⟩
  let : Module Γ(secondScheme, baseOpen) Γ((Modules.pullback firstProjection).obj moduleSheaf, productOpen) :=
    Module.compHom _ (structureMap.appLE baseOpen productOpen inf_le_right).hom
  have : IsScalarTower Γ(secondScheme, baseOpen) Γ(Limits.pullback gY gZ, productOpen) Γ((Modules.pullback firstProjection).obj moduleSheaf, productOpen) :=
    ⟨fun coefficient scalar moduleElement ↦ mul_smul _ _ _⟩
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat
    ((Algebra.IsPushout.cancelBaseChange Γ(affineBase, ⊤) Γ(secondScheme, baseOpen) Γ(firstScheme, sourceOpen) Γ(Limits.pullback gY gZ, productOpen)
      Γ(moduleSheaf, sourceOpen)).symm.trans (inclusion.restrictScalars Γ(secondScheme, baseOpen)))

end PullbackFst

end AlgebraicGeometry.Scheme.Modules

end
