import Jacobian.Algebra.Category.Ring.Subalgebras
import Jacobian.AlgebraicGeometry.Modules.Flat.Local
import Jacobian.RingTheory.Flat.Approximation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Eventual relative flatness over finitely generated subrings

Let an affine base be exhausted by its finitely generated integer subalgebras.
A finitely presented module on a quasi-compact finitely presented stage scheme
whose pullback is relatively flat becomes relatively flat at every sufficiently
large stage. The stage and the required finite coefficient set are constructed
from a finite affine cover, not supplied as flatness data.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TensorProduct

namespace Module

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Cancelling the algebra factor in a tensor product preserves flatness
over the extension ring. -/
theorem flat_baseChange_tensorProduct_iff {R₀ S₀ M₀ extensionRing : Type*} [CommRing R₀] [CommRing S₀]
    [CommRing extensionRing] [Algebra R₀ S₀] [Algebra R₀ extensionRing] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀]
    [IsScalarTower R₀ S₀ M₀] :
    Flat extensionRing ((extensionRing ⊗[R₀] S₀) ⊗[S₀] M₀) ↔ Flat extensionRing (extensionRing ⊗[R₀] M₀) :=
  Flat.equiv_iff (Algebra.IsPushout.cancelBaseChange R₀ extensionRing S₀ (extensionRing ⊗[R₀] S₀) M₀)

/-- Flatness of a scalar extension is preserved by a further map of
base algebras. -/
theorem Flat.baseChange_of_algHom {baseRing extensionRing extensionRing' moduleType : Type*} [CommRing baseRing] [CommRing extensionRing] [CommRing extensionRing']
    [Algebra baseRing extensionRing] [Algebra baseRing extensionRing'] [AddCommGroup moduleType] [Module baseRing moduleType] (algebraMap : extensionRing →ₐ[baseRing] extensionRing')
    (h : Flat extensionRing (extensionRing ⊗[baseRing] moduleType)) : Flat extensionRing' (extensionRing' ⊗[baseRing] moduleType) := by
  let := algebraMap.toRingHom.toAlgebra
  have : IsScalarTower baseRing extensionRing extensionRing' := IsScalarTower.of_algebraMap_eq fun r ↦ (algebraMap.commutes r).symm
  exact Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange baseRing extensionRing extensionRing' extensionRing' moduleType).symm

end Module

namespace AlgebraicGeometry

/-- On global sections the canonical projection to a finitely generated
subring is the inclusion after the global-sections isomorphism of a spectrum. -/
private lemma affineSubalgebraProjection_appTop_apply (baseScheme : Scheme.{u}) [IsAffine baseScheme]
    (laterStage : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ) (point : Γ(Spec (.of laterStage.unop.1), ⊤)) :
    ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom laterStage.unop.1.val.toRingHom))).appTop point = ((Scheme.ΓSpecIso (.of laterStage.unop.1)).hom point).1 := by
  simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]

/-- For an affine open of a finitely presented coefficient sheaf, a finite
set of base coefficients suffices to make all later scalar-extended sections
flat on every affine open of the later base. -/
theorem Scheme.Modules.exists_finset_forall_flat_baseChange_sections (baseScheme : Scheme.{u}) [IsAffine baseScheme]
    {initialStage : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ} {sourceScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ (Spec (CommRingCat.of initialStage.unop.1)))
    [LocallyOfFiniteType sourceMap] (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
    (h𝒢 : ((Modules.pullback (pullback.fst sourceMap ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))))).obj moduleSheaf).IsFlatOver
      (pullback.snd sourceMap ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))))) (sourceOpen : sourceScheme.affineOpens) :
    ∃ coefficients : Finset Γ(baseScheme, ⊤), ∀ (laterStage : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ) (furtherTransition : laterStage ⟶ initialStage),
      (coefficients : Set Γ(baseScheme, ⊤)) ⊆ laterStage.unop.1 → ∀ baseOpen : ((Spec (CommRingCat.of laterStage.unop.1))).affineOpens,
        letI := (((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))).appLE ⊤ baseOpen.1 le_top).hom.toAlgebra
        letI : Module Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ(moduleSheaf, sourceOpen.1) :=
          Module.compHom _ (sourceMap.appLE ⊤ sourceOpen.1 le_top).hom
        Module.Flat Γ((Spec (CommRingCat.of laterStage.unop.1)), baseOpen.1)
          (Γ((Spec (CommRingCat.of laterStage.unop.1)), baseOpen.1) ⊗[Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤)] Γ(moduleSheaf, sourceOpen.1)) := by
  have : IsAffine ((Spec (CommRingCat.of initialStage.unop.1))) := inferInstanceAs (IsAffine (Spec _))
  have : IsNoetherianRing Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) := by
    have : Algebra.FiniteType ℤ initialStage.unop.1 := (Subalgebra.fg_iff_finiteType _).mp initialStage.unop.2
    have : IsNoetherianRing initialStage.unop.1 := Algebra.FiniteType.isNoetherianRing ℤ _
    exact isNoetherianRing_of_ringEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of initialStage.unop.1)).commRingCatIsoToRingEquiv.symm
  let : Algebra Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ(sourceScheme, sourceOpen.1) := (sourceMap.appLE ⊤ sourceOpen.1 le_top).hom.toAlgebra
  let : Module Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ(moduleSheaf, sourceOpen.1) := Module.compHom _ (sourceMap.appLE ⊤ sourceOpen.1 le_top).hom
  have : IsScalarTower Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ(sourceScheme, sourceOpen.1) Γ(moduleSheaf, sourceOpen.1) :=
    ⟨fun element scalar moduleElement ↦ mul_smul _ _ _⟩
  have : Algebra.FiniteType Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ(sourceScheme, sourceOpen.1) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType sourceMap ‹_› ⟨⊤, isAffineOpen_top _⟩ sourceOpen le_top
  have := finitePresentation_sections_of_isFinitePresentation moduleSheaf sourceOpen.2
  let : Algebra Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ(baseScheme, ⊤) :=
    (((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  have flatSections : Module.Flat Γ(baseScheme, ⊤)
      (Γ(baseScheme, ⊤) ⊗[Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤)]
        Γ(moduleSheaf, sourceOpen.1)) :=
    flat_baseChange_of_flat_sections_pullback_fst.{u}
      (affineBase := Spec (CommRingCat.of initialStage.unop.1))
      (firstScheme := sourceScheme) (secondScheme := baseScheme)
      sourceMap (baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom)) moduleSheaf sourceOpen.2
      (isAffineOpen_top baseScheme)
      (h𝒢 ⟨⊤, isAffineOpen_top baseScheme⟩ ⟨_, isAffineOpen_preimage_inf_preimage_pullback sourceMap
        ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))) sourceOpen.2 (isAffineOpen_top baseScheme)⟩ inf_le_right)
  have flatTensor :=
    (Module.flat_baseChange_tensorProduct_iff
      (R₀ := Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤))
      (S₀ := Γ(sourceScheme, sourceOpen.1)) (M₀ := Γ(moduleSheaf, sourceOpen.1))
      (extensionRing := Γ(baseScheme, ⊤))).mpr flatSections
  have approximation := Module.exists_fg_forall_flat_baseChange
    (R₀ := Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤))
    (S₀ := Γ(sourceScheme, sourceOpen.1)) (M₀ := Γ(moduleSheaf, sourceOpen.1))
    (ambientRing := Γ(baseScheme, ⊤)) flatTensor
  let stageSubalgebra := Classical.choose approximation
  have finiteGeneration : stageSubalgebra.FG := (Classical.choose_spec approximation).1
  have stageFlatness := (Classical.choose_spec approximation).2
  let coefficients := Classical.choose finiteGeneration
  have generatedStage := Classical.choose_spec finiteGeneration
  refine ⟨coefficients, fun laterStage furtherTransition ht baseOpen ↦ ?_⟩
  let : Algebra Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ((Spec (CommRingCat.of laterStage.unop.1)), ⊤) :=
    (((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Algebra Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) Γ((Spec (CommRingCat.of laterStage.unop.1)), baseOpen.1) :=
    (((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))).appLE ⊤ baseOpen.1 le_top).hom.toAlgebra
  have hw : (baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom laterStage.unop.1.val.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom)) = (baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom)) := by
    rw [Category.assoc, ← Spec.map_comp]
    rfl
  let inclusionMap : Γ((Spec (CommRingCat.of laterStage.unop.1)), ⊤) →ₐ[Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤)] Γ(baseScheme, ⊤) :=
    { ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom laterStage.unop.1.val.toRingHom))).appTop.hom with
      commutes' coefficient := by
        change ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom laterStage.unop.1.val.toRingHom))).appTop (((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))).appLE ⊤ ⊤ le_top coefficient) =
          ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))).appLE ⊤ ⊤ le_top coefficient
        have sectionEquation := congrArg Scheme.Hom.appTop hw
        rw [Scheme.Hom.comp_appTop] at sectionEquation
        have pointEquation := congrArg
          (fun ringMap : Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤) ⟶ Γ(baseScheme, ⊤) ↦
            ringMap coefficient) sectionEquation
        have transitionTop :
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom)).appLE ⊤ ⊤ le_top =
              (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom)).appTop :=
          Scheme.Hom.appLE_eq_app _
        have initialTop :
            (baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom)).appLE ⊤ ⊤ le_top =
              (baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom)).appTop :=
          Scheme.Hom.appLE_eq_app _
        have transitionPoint := congrArg
          (fun ringMap : Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤) ⟶
              Γ(Spec (CommRingCat.of laterStage.unop.1), ⊤) ↦
            ringMap coefficient) transitionTop
        have initialPoint := congrArg
          (fun ringMap : Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤) ⟶ Γ(baseScheme, ⊤) ↦
            ringMap coefficient) initialTop
        exact (congrArg
          (fun value : Γ(Spec (CommRingCat.of laterStage.unop.1), ⊤) ↦
            (baseScheme.isoSpec.hom ≫
              Spec.map (CommRingCat.ofHom laterStage.unop.1.val.toRingHom)).appTop value)
          transitionPoint).trans (pointEquation.trans initialPoint.symm) }
  have hρ (point : Γ((Spec (CommRingCat.of laterStage.unop.1)), ⊤)) : inclusionMap point = ((Scheme.ΓSpecIso (.of laterStage.unop.1)).hom point).1 :=
    affineSubalgebraProjection_appTop_apply baseScheme laterStage point
  have hinj : Function.Injective inclusionMap := fun point otherPoint hxy ↦ by
    rw [hρ, hρ] at hxy
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of laterStage.unop.1)).hom).1
      (Subtype.ext hxy)
  have hle : Algebra.adjoin Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤) (coefficients : Set Γ(baseScheme, ⊤)) ≤ inclusionMap.range := by
    refine Algebra.adjoin_le fun element ha ↦ ⟨(Scheme.ΓSpecIso (.of laterStage.unop.1)).inv ⟨element, ht ha⟩, ?_⟩
    change inclusionMap ((Scheme.ΓSpecIso (.of laterStage.unop.1)).inv ⟨element, ht ha⟩) = element
    rw [hρ]
    exact congrArg (fun value : laterStage.unop.1 ↦ value.1)
      ((Scheme.ΓSpecIso (.of laterStage.unop.1)).commRingCatIsoToRingEquiv.apply_symm_apply
        ⟨element, ht ha⟩)
  have stageLe : stageSubalgebra ≤ inclusionMap.range := by
    rw [← generatedStage]
    exact hle
  let res : Γ((Spec (CommRingCat.of laterStage.unop.1)), ⊤) →ₐ[Γ((Spec (CommRingCat.of initialStage.unop.1)), ⊤)]
      Γ((Spec (CommRingCat.of laterStage.unop.1)), baseOpen.1) :=
    { (((Spec (CommRingCat.of laterStage.unop.1))).presheaf.map (homOfLE le_top).op).hom with
      commutes' coefficient := by
        change (((Spec (CommRingCat.of laterStage.unop.1))).presheaf.map (homOfLE le_top).op)
            (((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))).appLE ⊤ ⊤ le_top coefficient) =
          ((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))).appLE ⊤ baseOpen.1 le_top coefficient
        have restrictionEquation := Scheme.Hom.appLE_map
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom furtherTransition.unop)).toRingHom))
          (U := ⊤) (V := ⊤) (V' := baseOpen.1) le_top
          (homOfLE (le_top : baseOpen.1 ≤ ⊤)).op
        exact congrArg
          (fun ringMap : Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤) ⟶
              Γ(Spec (CommRingCat.of laterStage.unop.1), baseOpen.1) ↦
            ringMap coefficient) restrictionEquation }
  have stageFlat : Module.Flat inclusionMap.range
      (inclusionMap.range ⊗[Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤)]
        Γ(moduleSheaf, sourceOpen.1)) :=
    (Module.flat_baseChange_tensorProduct_iff
      (R₀ := Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤))
      (S₀ := Γ(sourceScheme, sourceOpen.1)) (M₀ := Γ(moduleSheaf, sourceOpen.1))
      (extensionRing := inclusionMap.range)).mp (stageFlatness inclusionMap.range stageLe)
  exact Module.Flat.baseChange_of_algHom
    (baseRing := Γ(Spec (CommRingCat.of initialStage.unop.1), ⊤))
    (extensionRing := inclusionMap.range)
    (extensionRing' := Γ(Spec (CommRingCat.of laterStage.unop.1), baseOpen.1))
    (moduleType := Γ(moduleSheaf, sourceOpen.1))
    (res.comp ((AlgEquiv.ofInjective inclusionMap hinj).symm.toAlgHom))
    stageFlat

/-- A finitely presented sheaf on a quasi-compact finitely presented stage
scheme whose pullback to an affine base is relatively flat is relatively flat
over every sufficiently large finitely generated integer subring of that base. -/
theorem Scheme.Modules.exists_isFlatOver_pullback_of_fgSubalgebra (baseScheme : Scheme.{u}) [IsAffine baseScheme]
    {initialStage : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ} {sourceScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ (Spec (CommRingCat.of initialStage.unop.1)))
    [LocallyOfFinitePresentation sourceMap] [QuasiCompact sourceMap] [QuasiSeparated sourceMap] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsFinitePresentation]
    (h𝒢 : ((Modules.pullback (pullback.fst sourceMap ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))))).obj moduleSheaf).IsFlatOver
      (pullback.snd sourceMap ((baseScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom initialStage.unop.1.val.toRingHom))))) :
    ∃ (stage : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ) (transition : stage ⟶ initialStage), ∀ (laterStage : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ) (furtherTransition : laterStage ⟶ stage),
      ((Modules.pullback (pullback.fst sourceMap ((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom (furtherTransition ≫ transition).unop)).toRingHom))))).obj moduleSheaf).IsFlatOver
        (pullback.snd sourceMap ((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom (furtherTransition ≫ transition).unop)).toRingHom)))) := by
  classical
  have : IsAffine ((Spec (CommRingCat.of initialStage.unop.1))) := inferInstanceAs (IsAffine (Spec _))
  haveI : CompactSpace (Spec (CommRingCat.of initialStage.unop.1)) :=
    Scheme.compactSpace_of_isAffine (Spec (CommRingCat.of initialStage.unop.1))
  have : CompactSpace sourceScheme := QuasiCompact.compactSpace_of_compactSpace sourceMap
  obtain ⟨affineOpens, hs, hY⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : sourceScheme.Opens))).mp
    (by simpa using isCompact_univ)
  choose coefficients ht using exists_finset_forall_flat_baseChange_sections.{u}
    (initialStage := initialStage) (sourceScheme := sourceScheme)
    baseScheme sourceMap moduleSheaf h𝒢
  obtain ⟨tᵢ, htᵢ⟩ := initialStage.unop.2
  let requiredCoefficients : Finset Γ(baseScheme, ⊤) := tᵢ ∪ hs.toFinset.biUnion coefficients
  have hij : initialStage.unop.1 ≤ Algebra.adjoin ℤ (requiredCoefficients : Set Γ(baseScheme, ⊤)) := by
    rw [← htᵢ]
    exact Algebra.adjoin_mono (by simp [requiredCoefficients])
  let transition : (Opposite.op ⟨_, Subalgebra.fg_adjoin_finset requiredCoefficients⟩ : ({subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG})ᵒᵖ) ⟶ initialStage :=
    (homOfLE (Subtype.coe_le_coe.mp hij : initialStage.unop ≤ ⟨_, Subalgebra.fg_adjoin_finset requiredCoefficients⟩)).op
  refine ⟨_, transition, fun laterStage furtherTransition ↦ ?_⟩
  have hjk : Algebra.adjoin ℤ (requiredCoefficients : Set Γ(baseScheme, ⊤)) ≤ laterStage.unop.1 := leOfHom furtherTransition.unop
  let stageMap : Spec (CommRingCat.of laterStage.unop.1) ⟶
      Spec (CommRingCat.of initialStage.unop.1) :=
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (leOfHom (furtherTransition ≫ transition).unop)).toRingHom)
  refine isFlatOver_of_forall_exists_nhds.{u}
    (sourceScheme := Limits.pullback sourceMap stageMap)
    (baseScheme := Spec (CommRingCat.of laterStage.unop.1))
    (pullback.snd sourceMap stageMap)
    ((Modules.pullback (pullback.fst sourceMap stageMap)).obj moduleSheaf)
    fun baseOpen point _ ↦ ?_
  have hx : pullback.fst sourceMap ((Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom (furtherTransition ≫ transition).unop)).toRingHom))) point ∈ ⨆ sourceOpen ∈ affineOpens, (sourceOpen : sourceScheme.Opens) := hY ▸ trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨sourceOpen, hW, hxW⟩ := hx
  refine ⟨_, hxW, fun openSubset inclusion hUN ↦ flat_sections_pullback_fst_of_flat_baseChange.{u}
    (affineBase := Spec (CommRingCat.of initialStage.unop.1))
    (firstScheme := sourceScheme) (secondScheme := Spec (CommRingCat.of laterStage.unop.1))
    sourceMap stageMap moduleSheaf sourceOpen.2 baseOpen.2
    openSubset.2 (le_inf hUN inclusion)
    (ht sourceOpen laterStage (furtherTransition ≫ transition)
      (fun element ha ↦ hjk (Algebra.subset_adjoin ?_)) baseOpen)⟩
  simp only [requiredCoefficients, Finset.coe_union, Finset.coe_biUnion, Set.Finite.coe_toFinset, Set.mem_union,
    Set.mem_iUnion, Finset.mem_coe]
  exact Or.inr ⟨sourceOpen, hW, ha⟩

end AlgebraicGeometry
