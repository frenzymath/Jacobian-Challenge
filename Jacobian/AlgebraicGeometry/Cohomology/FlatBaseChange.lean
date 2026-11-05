import Jacobian.Algebra.Homology.DerivedCategory.Ext.BaseChange
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Pushforward
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Jacobian.AlgebraicGeometry.Modules.AffinePushforward
import Jacobian.AlgebraicGeometry.Modules.BaseChange
import Jacobian.Topology.Sheaves.MayerVietoris
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Flat base change for quasi-coherent sheaf cohomology
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

section
universe schemeUniverse

open CategoryTheory Limits TopologicalSpace TensorProduct Opposite

namespace AlgebraicGeometry

/-- **Induction on quasi-compact opens of a quasi-separated scheme.** A property of the opens
of a quasi-separated scheme which holds for the affine opens, and holds for `U ⊔ V` whenever it
holds for `U`, `V` and `U ⊓ V`, holds for every quasi-compact open. -/
theorem Scheme.induction_isCompact_of_quasiSeparatedSpace {scheme : Scheme.{schemeUniverse}}
    [QuasiSeparatedSpace scheme] (testSheaf : scheme.Opens → Prop) (h_aff : ∀ firstOpen, IsAffineOpen firstOpen → testSheaf firstOpen)
    (h_sup : ∀ firstOpen baseOpen, testSheaf firstOpen → testSheaf baseOpen → testSheaf (firstOpen ⊓ baseOpen) → testSheaf (firstOpen ⊔ baseOpen)) (baseScheme : scheme.Opens)
    (hS : IsCompact (baseScheme : Set scheme)) : testSheaf baseScheme := by
  classical

  have hinf : ∀ firstOpen, IsAffineOpen firstOpen → ∀ V₁ ≤ firstOpen, ∀ V₂ ≤ firstOpen, IsAffineOpen V₁ → IsAffineOpen V₂ →
      IsAffineOpen (V₁ ⊓ V₂) := fun firstOpen hU V₁ h₁ V₂ h₂ ↦ by
    refine isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal (𝟙 scheme)))
      firstOpen hU V₁ ?_ V₂ ?_ <;> simpa

  have hfin : ∀ firstOpen, IsAffineOpen firstOpen → ∀ (degree : ℕ) (openFamily : Finset scheme.Opens), openFamily.card ≤ degree →
      (∀ baseOpen ∈ openFamily, IsAffineOpen baseOpen ∧ baseOpen ≤ firstOpen) → testSheaf (openFamily.sup id) := by
    intro firstOpen hU degree
    induction degree with
    | zero =>
      intro openFamily hs _
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs), Finset.sup_empty]
      exact h_aff _ (isAffineOpen_bot scheme)
    | succ degree ih =>
      intro openFamily hs hsU
      induction openFamily using Finset.induction_on with
      | empty => exact h_aff _ (isAffineOpen_bot scheme)
      | insert baseOpen openFamily hV _ =>
        rw [Finset.card_insert_of_notMem hV] at hs
        have hsU' : ∀ openSubset ∈ openFamily, IsAffineOpen openSubset ∧ openSubset ≤ firstOpen := fun openSubset hW ↦
          hsU openSubset (Finset.mem_insert_of_mem hW)
        have hVU := hsU baseOpen (Finset.mem_insert_self baseOpen openFamily)
        rw [Finset.sup_insert]
        refine h_sup _ _ (h_aff _ hVU.1) (ih openFamily (by omega) hsU') ?_
        have hs_img : baseOpen ⊓ openFamily.sup id = (openFamily.image (baseOpen ⊓ ·)).sup id := by
          rw [Finset.sup_inf_distrib_left, Finset.sup_image]; rfl
        rw [id_eq, hs_img]
        refine ih _ (Finset.card_image_le.trans (by omega)) fun openSubset hW ↦ ?_
        obtain ⟨openSubset', hW', rfl⟩ := Finset.mem_image.mp hW
        exact ⟨hinf firstOpen hU baseOpen hVU.2 openSubset' (hsU' openSubset' hW').2 hVU.1 (hsU' openSubset' hW').1,
          inf_le_left.trans hVU.2⟩

  have hcpt : ∀ firstOpen, IsAffineOpen firstOpen → ∀ openSubset ≤ firstOpen, IsCompact (openSubset : Set scheme) → testSheaf openSubset := by
    intro firstOpen hU openSubset hWU hW
    obtain ⟨openFamily, hs, hsW⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
    have hsW' : ∀ index ∈ openFamily, (index : scheme.Opens) ≤ openSubset := fun index hi ↦
      hsW ▸ le_iSup₂ (f := fun (index : scheme.affineOpens) (_ : index ∈ openFamily) ↦ (index : scheme.Opens)) index hi
    have ht : (hs.toFinset.image Subtype.val).sup id = openSubset := by
      apply le_antisymm
      · simp only [Finset.sup_le_iff, Finset.mem_image, Set.Finite.mem_toFinset, id_eq,
          forall_exists_index, and_imp]
        rintro _ index hi rfl
        exact hsW' index hi
      · rw [hsW]
        exact iSup₂_le fun index hi ↦
          Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (hs.mem_toFinset.mpr hi))
    rw [← ht]
    refine hfin firstOpen hU _ _ le_rfl fun baseOpen hV ↦ ?_
    obtain ⟨index, hi, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨index.2, (hsW' index (hs.mem_toFinset.mp hi)).trans hWU⟩
  refine compact_open_induction_on baseScheme hS (h_aff _ (isAffineOpen_bot scheme)) ?_
  intro baseScheme hS firstOpen hP
  refine h_sup _ _ hP (h_aff _ firstOpen.2) (hcpt firstOpen firstOpen.2 _ inf_le_right ?_)
  exact QuasiSeparatedSpace.inter_isCompact _ _ baseScheme.2 hS firstOpen.1.2 firstOpen.2.isCompact

end AlgebraicGeometry

namespace TopCat.Sheaf

open CategoryTheory.Abelian

variable {scheme : TopCat.{schemeUniverse}}

lemma homFreeSheafEquiv_eq (firstOpen : Opens scheme)
    {targetSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{schemeUniverse}}
    (coefficientMap : freeSheaf firstOpen ⟶ targetSheaf) :
    homFreeSheafEquiv firstOpen targetSheaf coefficientMap =
      coefficientMap.hom.app (op firstOpen) (homFreeSheafEquiv firstOpen (freeSheaf firstOpen) (𝟙 (freeSheaf firstOpen))) := by
  rw [← homFreeSheafEquiv_comp, Category.id_comp]

/-- The cohomology in degree `0` of an abelian sheaf `G` on an open `U` is `G(U)`:
`Ext⁰(ℤ_U, G) ≅ Hom(ℤ_U, G) ≅ G(U)`. -/
noncomputable def extFreeSheafZeroAddEquiv (firstOpen : Opens scheme)
    (targetSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{schemeUniverse}) :
    Ext (freeSheaf firstOpen) targetSheaf 0 ≃+ targetSheaf.obj.obj (op firstOpen) where
  toEquiv := Ext.addEquiv₀.toEquiv.trans (homFreeSheafEquiv firstOpen targetSheaf)
  map_add' element otherElement := by
    change homFreeSheafEquiv firstOpen targetSheaf (Ext.addEquiv₀ (element + otherElement)) =
      homFreeSheafEquiv firstOpen targetSheaf (Ext.addEquiv₀ element) + homFreeSheafEquiv firstOpen targetSheaf (Ext.addEquiv₀ otherElement)
    rw [map_add]
    rw [homFreeSheafEquiv_eq, homFreeSheafEquiv_eq firstOpen (Ext.addEquiv₀ element),
      homFreeSheafEquiv_eq firstOpen (Ext.addEquiv₀ otherElement)]
    rfl

lemma extFreeSheafZeroAddEquiv_comp_mk₀ (firstOpen : Opens scheme)
    {targetSheaf targetSheaf' : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{schemeUniverse}}
    (element : Ext (freeSheaf firstOpen) targetSheaf 0)
    (coefficientMap : targetSheaf ⟶ targetSheaf') :
    extFreeSheafZeroAddEquiv firstOpen targetSheaf' (element.comp (Ext.mk₀ coefficientMap) (add_zero 0)) =
      coefficientMap.hom.app (op firstOpen) (extFreeSheafZeroAddEquiv firstOpen targetSheaf element) := by
  change homFreeSheafEquiv firstOpen targetSheaf' (Ext.addEquiv₀ _) = _
  rw [Ext.addEquiv₀_comp_mk₀, homFreeSheafEquiv_comp]
  rfl

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {scheme : Scheme.{schemeUniverse}}

/-- Multiplication by global functions on the underlying abelian sheaf of a sheaf of modules, as
a ring homomorphism to its endomorphisms. -/
noncomputable def smulRingHom (moduleSheaf : scheme.Modules) :
    Γ(scheme, ⊤) →+* End ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj moduleSheaf) where
  toFun baseScalar := (SheafOfModules.toSheaf scheme.ringCatSheaf).map (moduleSheaf.smulHom baseScalar)
  map_one' := by rw [smulHom_one, CategoryTheory.Functor.map_id]; rfl
  map_mul' baseScalar extensionScalar := by rw [smulHom_mul, CategoryTheory.Functor.map_comp, End.mul_def]
  map_zero' := by rw [smulHom_zero, CategoryTheory.Functor.map_zero]
  map_add' baseScalar extensionScalar := by rw [smulHom_add, CategoryTheory.Functor.map_add]

/-- Multiplication by global functions of `Y` on the underlying abelian sheaf of the pushforward
`g_* N` of a sheaf of modules along `g : Y ⟶ X`, as a ring homomorphism to its endomorphisms. -/
noncomputable def pushforwardSmulRingHom {pulledScheme : Scheme.{schemeUniverse}} (baseChangeMap : pulledScheme ⟶ scheme) (otherModule : pulledScheme.Modules) :
    Γ(pulledScheme, ⊤) →+* End ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj ((pushforward baseChangeMap).obj otherModule)) where
  toFun extensionScalar := (SheafOfModules.toSheaf scheme.ringCatSheaf).map ((pushforward baseChangeMap).map (otherModule.smulHom extensionScalar))
  map_one' := by
    rw [smulHom_one, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]; rfl
  map_mul' baseScalar extensionScalar := by
    rw [smulHom_mul, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, End.mul_def]
  map_zero' := by
    rw [smulHom_zero, CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]
  map_add' baseScalar extensionScalar := by
    rw [smulHom_add, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]

section BaseChange

variable {pulledScheme baseScheme extensionScheme : Scheme.{schemeUniverse}} {structureMap : scheme ⟶ baseScheme} {structureMap' : pulledScheme ⟶ extensionScheme} {baseChangeMap : extensionScheme ⟶ baseScheme} {baseChangeMap' : pulledScheme ⟶ scheme}
  (cartesian : IsPullback baseChangeMap' structureMap' structureMap baseChangeMap) (coherentSheaf : scheme.Modules)
  [Algebra Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] (hg : algebraMap Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) = baseChangeMap.appTop.hom)

variable (structureMap) in
/-- The action of `A = Γ(S, ⊤)` on the underlying abelian sheaf of `ℱ`, through `f^♯`. -/
noncomputable abbrev baseAction : Γ(baseScheme, ⊤) →+* End ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj coherentSheaf) :=
  (smulRingHom coherentSheaf).comp structureMap.appTop.hom

variable (structureMap' baseChangeMap') in
/-- The action of `B = Γ(T, ⊤)` on the underlying abelian sheaf of `g'_* g'^* ℱ`, through
`f'^♯`. -/
noncomputable abbrev pushforwardPullbackAction :
    Γ(extensionScheme, ⊤) →+* End ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj
      ((pushforward baseChangeMap').obj ((pullback baseChangeMap').obj coherentSheaf))) :=
  (pushforwardSmulRingHom baseChangeMap' ((pullback baseChangeMap').obj coherentSheaf)).comp structureMap'.appTop.hom

variable (baseChangeMap') in
/-- The unit `ℱ ⟶ g'_* g'^* ℱ`, on the underlying abelian sheaves. -/
noncomputable abbrev toSheafUnit :
    (SheafOfModules.toSheaf scheme.ringCatSheaf).obj coherentSheaf ⟶
      (SheafOfModules.toSheaf scheme.ringCatSheaf).obj ((pushforward baseChangeMap').obj ((pullback baseChangeMap').obj coherentSheaf)) :=
  (SheafOfModules.toSheaf scheme.ringCatSheaf).map ((pullbackPushforwardAdjunction baseChangeMap').unit.app coherentSheaf)

include cartesian in
omit [Algebra Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] in
lemma appTop_appTop_of_isPullback (baseScalar : Γ(baseScheme, ⊤)) :
    baseChangeMap'.appTop (structureMap.appTop baseScalar) = structureMap'.appTop (baseChangeMap.appTop baseScalar) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, cartesian.w]

include cartesian hg in
/-- The unit `ℱ ⟶ g'_* g'^* ℱ` intertwines the actions of `A` and `B`. -/
lemma baseAction_comp_toSheafUnit (baseScalar : Γ(baseScheme, ⊤)) :
    baseAction structureMap coherentSheaf baseScalar ≫ toSheafUnit baseChangeMap' coherentSheaf =
      toSheafUnit baseChangeMap' coherentSheaf ≫ pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf (algebraMap Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) baseScalar) := by
  have key : coherentSheaf.smulHom (structureMap.appTop baseScalar) ≫ (pullbackPushforwardAdjunction baseChangeMap').unit.app coherentSheaf =
      (pullbackPushforwardAdjunction baseChangeMap').unit.app coherentSheaf ≫
        (pushforward baseChangeMap').map (((pullback baseChangeMap').obj coherentSheaf).smulHom (structureMap'.appTop (algebraMap _ _ baseScalar))) := by
    rw [smulHom_naturality, hg, ← appTop_appTop_of_isPullback cartesian, pushforward_map_smulHom]
    rfl
  have compatibility := congrArg (SheafOfModules.toSheaf scheme.ringCatSheaf).map key
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at compatibility
  exact compatibility

/-- The base change map `B ⊗_A H^n(W, ℱ) ⟶ H^n(W, g'_* g'^* ℱ)`, `b ⊗ x ↦ b • η_* x`, for an open
`W` of `X` (with `H^n(W, -) = Ext^n(ℤ_W, -)`), or more generally with `ℤ_W` replaced by any
abelian sheaf `P`. -/
noncomputable abbrev cohomologyBaseChange (testSheaf : Sheaf (Opens.grothendieckTopology scheme)
    AddCommGrpCat.{schemeUniverse}) (degree : ℕ) :=
  WithAction.baseChange (baseAction structureMap coherentSheaf) (pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf) (toSheafUnit baseChangeMap' coherentSheaf)
    (baseAction_comp_toSheafUnit cartesian coherentSheaf hg) testSheaf degree

section Affine

variable [IsAffine baseScheme] [IsAffine extensionScheme] [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) coherentSheaf]

/-- `H⁰(W, ℱ) ≅ Γ(W, ℱ)` as `Γ(S, ⊤)`-modules. -/
noncomputable def sectionsLinearEquiv (openSubset : scheme.Opens) :
    WithAction (baseAction structureMap coherentSheaf) (TopCat.Sheaf.freeSheaf openSubset) 0 ≃ₗ[Γ(baseScheme, ⊤)]
      sectionsModule structureMap coherentSheaf openSubset where
  __ := (WithAction.toExt _).trans (TopCat.Sheaf.extFreeSheafZeroAddEquiv openSubset _)
  map_smul' baseScalar element := by
    change TopCat.Sheaf.extFreeSheafZeroAddEquiv openSubset _
      ((WithAction.toExt _ element).comp (mk₀ (baseAction structureMap coherentSheaf baseScalar)) (add_zero 0)) = _
    rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀]
    rfl

variable (structureMap' baseChangeMap') in
/-- `H⁰(W, g'_* g'^* ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`. -/
noncomputable def pushforwardSectionsAddEquiv (openSubset : scheme.Opens) :
    WithAction (pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf) (TopCat.Sheaf.freeSheaf openSubset) 0 ≃+
      sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset) :=
  (WithAction.toExt _).trans (TopCat.Sheaf.extFreeSheafZeroAddEquiv openSubset _)

include cartesian hg in
/-- In degree `0` the base change map on an affine open `W` is the base change of sections
`B ⊗_A Γ(W, ℱ) ≅ Γ(g'⁻¹ W, g'^* ℱ)`, hence bijective. -/
lemma bijective_cohomologyBaseChange_zero_of_isAffineOpen {openSubset : scheme.Opens} (hW : IsAffineOpen openSubset) :
    Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf openSubset) 0) := by
  have key : ⇑(pushforwardSectionsAddEquiv structureMap' baseChangeMap' coherentSheaf openSubset) ∘
      ⇑(cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf openSubset) 0) =
      ⇑(sectionsModuleBaseChange cartesian coherentSheaf hg openSubset) ∘ ⇑((sectionsLinearEquiv coherentSheaf openSubset).lTensor Γ(extensionScheme, ⊤)) := by
    funext tensorElement
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | add tensorElement tensorElement' hz hz' =>
      simp only [Function.comp_apply, map_add] at hz hz' ⊢
      rw [hz, hz']
    | tmul extensionScalar element =>
      change TopCat.Sheaf.extFreeSheafZeroAddEquiv openSubset _ ((WithAction.toExt _ element).comp
          (mk₀ (toSheafUnit baseChangeMap' coherentSheaf ≫ pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf extensionScalar)) (add_zero 0)) =
        sectionsModuleBaseChange cartesian coherentSheaf hg openSubset (extensionScalar ⊗ₜ sectionsLinearEquiv coherentSheaf openSubset element)
      rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀, sectionsModuleBaseChange_tmul]
      rfl
  refine (Function.Bijective.of_comp_iff' (pushforwardSectionsAddEquiv structureMap' baseChangeMap' coherentSheaf openSubset).bijective
    _).mp ?_
  rw [key]
  exact (bijective_sectionsModuleBaseChange cartesian coherentSheaf hg hW).comp (LinearEquiv.bijective _)

include cartesian in
omit [Algebra Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) coherentSheaf] in
lemma isAffineHom_of_isPullback : IsAffineHom baseChangeMap' :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) cartesian.flip inferInstance

include cartesian in
/-- In positive degrees, both sides of the base change map vanish on an affine open `W`. -/
lemma bijective_cohomologyBaseChange_succ_of_isAffineOpen {openSubset : scheme.Opens} (hW : IsAffineOpen openSubset)
    (degree : ℕ) :
    Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf openSubset) (degree + 1)) := by
  have := isAffineHom_of_isPullback cartesian
  have := isQuasicoherent_pushforward_of_isAffineHom baseChangeMap' ((pullback baseChangeMap').obj coherentSheaf)
  have : Subsingleton (WithAction (baseAction structureMap coherentSheaf) (TopCat.Sheaf.freeSheaf openSubset) (degree + 1)) :=
    subsingleton_H'_succ_of_isAffineOpen _ (cechAcyclicOnAffines_of_isQuasicoherent coherentSheaf) hW degree
  have : Subsingleton (WithAction (pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf)
      (TopCat.Sheaf.freeSheaf openSubset) (degree + 1)) :=
    subsingleton_H'_succ_of_isAffineOpen _ (cechAcyclicOnAffines_of_isQuasicoherent _) hW degree
  have : Subsingleton (Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, ⊤)]
      WithAction (baseAction structureMap coherentSheaf) (TopCat.Sheaf.freeSheaf openSubset) (degree + 1)) := inferInstance
  exact ⟨fun element otherElement _ ↦ Subsingleton.elim element otherElement, fun otherElement ↦ ⟨0, Subsingleton.elim _ _⟩⟩

include cartesian hg in
/-- The base change map is bijective on affine opens. -/
lemma bijective_cohomologyBaseChange_of_isAffineOpen {openSubset : scheme.Opens} (hW : IsAffineOpen openSubset)
    (degree : ℕ) : Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf openSubset) degree) := by
  cases degree with
  | zero => exact bijective_cohomologyBaseChange_zero_of_isAffineOpen cartesian coherentSheaf hg hW
  | succ degree => exact bijective_cohomologyBaseChange_succ_of_isAffineOpen cartesian coherentSheaf hg hW degree

end Affine

include hg in
lemma moduleFlat_of_flat [IsAffine baseScheme] [IsAffine extensionScheme] [Flat baseChangeMap] : Module.Flat Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) := by
  have compatibility := baseChangeMap.flat_appTop
  rw [← hg, RingHom.flat_algebraMap_iff] at compatibility
  exact compatibility

/-- **Mayer–Vietoris step.** If the base change maps are bijective on `U`, `V` and `U ⊓ V`, then
they are bijective on `U ⊔ V`. -/
lemma bijective_cohomologyBaseChange_sup [Module.Flat Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] {firstOpen baseOpen : scheme.Opens}
    (hU : ∀ degree, Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf firstOpen) degree))
    (hV : ∀ degree, Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf baseOpen) degree))
    (hUV : ∀ degree,
      Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf (firstOpen ⊓ baseOpen)) degree))
    (degree : ℕ) :
    Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf (firstOpen ⊔ baseOpen)) degree) :=
  WithAction.bijective_baseChange_of_shortExact _ _ _ _
    (Opens.mayerVietorisSquare firstOpen baseOpen).shortComplex_shortExact hUV
    (fun degree ↦ WithAction.bijective_baseChange_biprod _ _ _ _ (hU degree) (hV degree)) degree

variable [IsAffine baseScheme] [IsAffine extensionScheme] [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) coherentSheaf]
  [Flat baseChangeMap] [QuasiSeparated structureMap]

include hg in
/-- **Flat base change on quasi-compact opens.** For a quasi-compact open `W` of `X`, the base
change map `B ⊗_A H^n(W, ℱ) ⟶ H^n(W, g'_* g'^* ℱ)` is bijective. -/
theorem bijective_cohomologyBaseChange_of_isCompact {openSubset : scheme.Opens} (hW : IsCompact (openSubset : Set scheme))
    (degree : ℕ) : Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf openSubset) degree) := by
  have := moduleFlat_of_flat hg
  have : QuasiSeparatedSpace scheme := quasiSeparatedSpace_of_quasiSeparated structureMap
  revert degree
  refine Scheme.induction_isCompact_of_quasiSeparatedSpace
    (fun openSubset ↦ ∀ degree, Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg (TopCat.Sheaf.freeSheaf openSubset) degree))
    (fun firstOpen hU ↦ bijective_cohomologyBaseChange_of_isAffineOpen cartesian coherentSheaf hg hU)
    (fun firstOpen baseOpen hU hV hUV ↦ bijective_cohomologyBaseChange_sup cartesian coherentSheaf hg hU hV hUV) openSubset hW

variable [QuasiCompact structureMap]

include hg in
/-- **Flat base change of cohomology, on `X`.** The base change map
`B ⊗_A H^n(X, ℱ) ⟶ H^n(X, g'_* g'^* ℱ)` is bijective. -/
theorem bijective_cohomologyBaseChange (degree : ℕ) :
    Function.Bijective (cohomologyBaseChange cartesian coherentSheaf hg
      ((constantSheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{schemeUniverse}).obj
        (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))) degree) := by
  have : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  have compatibility := bijective_cohomologyBaseChange_of_isCompact cartesian coherentSheaf hg (openSubset := ⊤)
    (by rw [Opens.coe_top]; exact isCompact_univ) degree
  exact WithAction.bijective_baseChange_of_iso (baseAction structureMap coherentSheaf)
    (pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf) (toSheafUnit baseChangeMap' coherentSheaf) (baseAction_comp_toSheafUnit cartesian coherentSheaf hg)
    (TopCat.Sheaf.freeSheafTopIso (X := scheme)) compatibility

variable (structureMap' baseChangeMap') in
/-- The action of `B = Γ(T, ⊤)` on the underlying abelian sheaf of `g'^* ℱ`, through `f'^♯`. -/
noncomputable abbrev pullbackAction :
    Γ(extensionScheme, ⊤) →+* End ((SheafOfModules.toSheaf pulledScheme.ringCatSheaf).obj ((pullback baseChangeMap').obj coherentSheaf)) :=
  (smulRingHom ((pullback baseChangeMap').obj coherentSheaf)).comp structureMap'.appTop.hom

include cartesian in
omit [Algebra Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] [Flat baseChangeMap] [QuasiSeparated structureMap] [QuasiCompact structureMap] in
/-- `H^n(Y, g'^* ℱ) ≅ H^n(X, g'_* g'^* ℱ)` as `B`-modules, since `g'` is affine. -/
theorem nonempty_H_linearEquiv_pushforward (degree : ℕ) :
    Nonempty (WithAction (pullbackAction structureMap' baseChangeMap' coherentSheaf) ((constantSheaf (Opens.grothendieckTopology pulledScheme)
        AddCommGrpCat.{schemeUniverse}).obj (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))) degree ≃ₗ[Γ(extensionScheme, ⊤)]
      WithAction (pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf) ((constantSheaf
        (Opens.grothendieckTopology scheme) AddCommGrpCat.{schemeUniverse}).obj
          (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))) degree) := by
  have := isAffineHom_of_isPullback cartesian
  obtain ⟨comparison⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom baseChangeMap' degree
  let targetSheaf := (pullback baseChangeMap').obj coherentSheaf
  let abelianSheaf : (cechAcyclicOnAffines pulledScheme).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf pulledScheme.ringCatSheaf).obj targetSheaf, cechAcyclicOnAffines_of_isQuasicoherent targetSheaf⟩
  let sectionEquiv : WithAction (pullbackAction structureMap' baseChangeMap' coherentSheaf) ((constantSheaf (Opens.grothendieckTopology pulledScheme)
        AddCommGrpCat.{schemeUniverse}).obj (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))) degree ≃+
      WithAction (pushforwardPullbackAction structureMap' baseChangeMap' coherentSheaf) ((constantSheaf
        (Opens.grothendieckTopology scheme) AddCommGrpCat.{schemeUniverse}).obj
          (AddCommGrpCat.of (ULift.{schemeUniverse} ℤ))) degree :=
    (comparison.app abelianSheaf).addCommGroupIsoToAddEquiv
  refine ⟨{ sectionEquiv with map_smul' := fun extensionScalar element ↦ ?_ }⟩
  have compatibility := NatTrans.naturality_apply comparison.hom (ObjectProperty.homMk
    ((SheafOfModules.toSheaf pulledScheme.ringCatSheaf).map (targetSheaf.smulHom (structureMap'.appTop extensionScalar))) : abelianSheaf ⟶ abelianSheaf) element
  exact compatibility

include cartesian hg in
/-- **Cohomology and flat base change** (Stacks 02KH). Consider a cartesian square
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `B ⊗_A H^n(X, ℱ) ≅ H^n(Y, g'^* ℱ)` as
`B`-modules, where `A` acts on `H^n(X, ℱ)` through `f^♯` and `B` on `H^n(Y, g'^* ℱ)` through
`f'^♯`. It is the composite of the canonical base change map
`B ⊗_A H^n(X, ℱ) ⟶ H^n(X, g'_* g'^* ℱ)` (bijective by `bijective_cohomologyBaseChange`) and the
identification `H^n(X, g'_* g'^* ℱ) ≅ H^n(Y, g'^* ℱ)` for the affine morphism `g'`.
 -/
@[stacks 02KH]
theorem nonempty_H_baseChange_linearEquiv (degree : ℕ) :
    letI : Module Γ(baseScheme, ⊤) (coherentSheaf.H degree) :=
      Module.compHom (coherentSheaf.H degree) structureMap.appTop.hom
    letI : Module Γ(extensionScheme, ⊤) (((pullback baseChangeMap').obj coherentSheaf).H degree) :=
      Module.compHom (((pullback baseChangeMap').obj coherentSheaf).H degree) structureMap'.appTop.hom
    Nonempty (Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, ⊤)] coherentSheaf.H degree ≃ₗ[Γ(extensionScheme, ⊤)]
      ((pullback baseChangeMap').obj coherentSheaf).H degree) := by
  letI : Module Γ(baseScheme, ⊤) (coherentSheaf.H degree) :=
    Module.compHom (coherentSheaf.H degree) structureMap.appTop.hom
  letI : Module Γ(extensionScheme, ⊤)
      (((pullback baseChangeMap').obj coherentSheaf).H degree) :=
    Module.compHom (((pullback baseChangeMap').obj coherentSheaf).H degree)
      structureMap'.appTop.hom
  obtain ⟨comparison⟩ := nonempty_H_linearEquiv_pushforward cartesian coherentSheaf degree
  let tensorComparison := (LinearEquiv.ofBijective _
    (bijective_cohomologyBaseChange cartesian coherentSheaf hg degree)).trans comparison.symm
  exact ⟨{ toFun := tensorComparison
           invFun := tensorComparison.symm
           left_inv := tensorComparison.left_inv
           right_inv := tensorComparison.right_inv
           map_add' := tensorComparison.map_add
           map_smul' := tensorComparison.map_smul }⟩

end BaseChange

end AlgebraicGeometry.Scheme.Modules
