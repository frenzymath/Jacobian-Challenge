import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Localization and finite basic-open covers

Functions on an affine basic open are localization fractions. An affine
scheme mapping to any scheme has a finite basic-open cover subordinate to
affine opens of the target.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u coefficientUniverse

open CategoryTheory

namespace AlgebraicGeometry

/-- The basic open of a finite product of sections is the intersection of the basic opens. -/
lemma Scheme.basicOpen_prod {scheme : Scheme.{coefficientUniverse}} {openSubset : scheme.Opens} {indexType : Type*} (sectionValue : Finset indexType)
    (sectionFamily : indexType → Γ(scheme, openSubset)) : scheme.basicOpen (∏ index ∈ sectionValue, sectionFamily index) = openSubset ⊓ ⨅ index ∈ sectionValue, scheme.basicOpen (sectionFamily index) := by
  classical
  induction sectionValue using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_one]
  | insert scalar sectionValue ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.iInf_insert, inf_left_comm,
      inf_eq_right.2 ((inf_le_left).trans (scheme.basicOpen_le _))]

/-- A nonempty finite intersection of basic opens is the basic open of the product. -/
lemma Scheme.iInf_basicOpen_eq_basicOpen_prod {scheme : Scheme.{coefficientUniverse}} {openSubset : scheme.Opens} {indexType : Type*}
    [Fintype indexType] [Nonempty indexType] (sectionFamily : indexType → Γ(scheme, openSubset)) :
    ⨅ index, scheme.basicOpen (sectionFamily index) = scheme.basicOpen (∏ index, sectionFamily index) := by
  rw [Scheme.basicOpen_prod]
  simp only [Finset.mem_univ, iInf_pos]
  exact (inf_eq_right.2 ((iInf_le _ (Classical.arbitrary indexType)).trans (scheme.basicOpen_le _))).symm

/-- Composition of restriction maps of the structure sheaf, elementwise. -/
lemma Scheme.presheaf_map_homOfLE_map_homOfLE_apply {scheme : Scheme.{coefficientUniverse}} {cover openSubset smallerOpen : scheme.Opens}
    (h₁ : cover ≤ openSubset) (h₂ : openSubset ≤ smallerOpen) (scalar : Γ(scheme, smallerOpen)) :
    scheme.presheaf.map (homOfLE h₁).op (scheme.presheaf.map (homOfLE h₂).op scalar) =
      scheme.presheaf.map (homOfLE (h₁.trans h₂)).op scalar := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- A global section which is invertible in every stalk is a unit. -/
lemma Scheme.isUnit_of_basicOpen_eq_top {scheme : Scheme.{u}}
    (sectionValue : Γ(scheme, ⊤)) (nonvanishing : scheme.basicOpen sectionValue = ⊤) :
    IsUnit sectionValue := by
  refine scheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ sectionValue fun point _ ↦ ?_
  exact (scheme.mem_basicOpen_top sectionValue point).mp (nonvanishing.ge trivial)

section BasicOpen

variable (scheme : Scheme.{u})

/-- The denominator becomes invertible on its basic open. -/
lemma Scheme.isUnit_ι_appTop_basicOpen (denominator : Γ(scheme, ⊤)) :
    IsUnit ((scheme.basicOpen denominator).ι.appTop denominator) := by
  refine Scheme.isUnit_of_basicOpen_eq_top _ ?_
  rw [← Scheme.preimage_basicOpen_top, Scheme.Opens.ι_preimage_self]

/-- The quotient of two global functions, defined where the denominator is invertible. -/
def Scheme.divBasicOpen (numerator denominator : Γ(scheme, ⊤)) :
    Γ((scheme.basicOpen denominator : Scheme.{u}), ⊤) :=
  Ring.inverse ((scheme.basicOpen denominator).ι.appTop denominator) *
    (scheme.basicOpen denominator).ι.appTop numerator

@[simp]
lemma Scheme.divBasicOpen_mul_self (numerator denominator : Γ(scheme, ⊤)) :
    scheme.divBasicOpen numerator denominator * (scheme.basicOpen denominator).ι.appTop denominator =
      (scheme.basicOpen denominator).ι.appTop numerator := by
  rw [Scheme.divBasicOpen, mul_right_comm,
    Ring.inverse_mul_cancel _ (scheme.isUnit_ι_appTop_basicOpen denominator), one_mul]

/-- A quotient is determined by its product with its invertible denominator. -/
lemma Scheme.eq_divBasicOpen {numerator denominator : Γ(scheme, ⊤)}
    {sectionValue : Γ((scheme.basicOpen denominator : Scheme.{u}), ⊤)}
    (multiplication : sectionValue * (scheme.basicOpen denominator).ι.appTop denominator =
      (scheme.basicOpen denominator).ι.appTop numerator) :
    sectionValue = scheme.divBasicOpen numerator denominator :=
  (scheme.isUnit_ι_appTop_basicOpen denominator).mul_right_cancel
    (multiplication.trans (scheme.divBasicOpen_mul_self numerator denominator).symm)

end BasicOpen

section Away

variable (sourceScheme : Scheme.{u}) (sectionValue : Γ(sourceScheme, ⊤))

noncomputable def Scheme.toSpecAway :
    (sourceScheme.basicOpen sectionValue : Scheme.{u}) ⟶ Spec (.of <| Localization.Away sectionValue) :=
  sourceScheme.toSpecΓ.resLE _ (sourceScheme.basicOpen sectionValue) (sourceScheme.toSpecΓ_preimage_basicOpen sectionValue).ge ≫
    (basicOpenIsoSpecAway sectionValue).hom

@[reassoc]
lemma Scheme.toSpecAway_SpecMap_algebraMap :
    sourceScheme.toSpecAway sectionValue ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away sectionValue))) =
      (sourceScheme.basicOpen sectionValue).ι ≫ sourceScheme.toSpecΓ := by
  rw [Scheme.toSpecAway, Category.assoc]
  rw [basicOpenIsoSpecAway_hom_SpecMap, Scheme.Hom.resLE_comp_ι]

noncomputable def Scheme.awayToBasicOpen :
    CommRingCat.of (Localization.Away sectionValue) ⟶ Γ((sourceScheme.basicOpen sectionValue : Scheme.{u}), ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (sourceScheme.toSpecAway sectionValue).appTop

lemma Scheme.awayToBasicOpen_apply (y : Localization.Away sectionValue) :
    sourceScheme.awayToBasicOpen sectionValue y = (sourceScheme.toSpecAway sectionValue).appTop ((Scheme.ΓSpecIso _).inv y) :=
  rfl

lemma Scheme.algebraMap_comp_awayToBasicOpen :
    CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away sectionValue)) ≫ sourceScheme.awayToBasicOpen sectionValue =
      (sourceScheme.basicOpen sectionValue).ι.appTop := by
  rw [Scheme.awayToBasicOpen, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecAway_SpecMap_algebraMap, Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.toSpecΓ_appTop]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (Γ(sourceScheme, ⊤) : Type u))).inv ≫
    (Scheme.ΓSpecIso Γ(sourceScheme, ⊤)).hom = 𝟙 _ from Iso.inv_hom_id _, Category.id_comp]

@[simp]
lemma Scheme.awayToBasicOpen_algebraMap (numerator : Γ(sourceScheme, ⊤)) :
    sourceScheme.awayToBasicOpen sectionValue (algebraMap Γ(sourceScheme, ⊤) (Localization.Away sectionValue) numerator) =
      (sourceScheme.basicOpen sectionValue).ι.appTop numerator := by
  conv_rhs => rw [← Scheme.algebraMap_comp_awayToBasicOpen sourceScheme sectionValue]
  rfl

@[simp]
lemma Scheme.awayToBasicOpen_mk' (numerator : Γ(sourceScheme, ⊤)) (membership : sectionValue ∈ Submonoid.powers sectionValue) :
    sourceScheme.awayToBasicOpen sectionValue (IsLocalization.mk' (Localization.Away sectionValue) numerator ⟨sectionValue, membership⟩) =
      sourceScheme.divBasicOpen numerator sectionValue := by
  refine sourceScheme.eq_divBasicOpen ?_
  rw [← sourceScheme.awayToBasicOpen_algebraMap sectionValue sectionValue, ← sourceScheme.awayToBasicOpen_algebraMap sectionValue numerator, ← map_mul,
    IsLocalization.mk'_spec]

lemma mk'_eq_divBasicOpen_pow [IsAffine sourceScheme] (numerator : Γ(sourceScheme, ⊤)) (exponent : ℕ)
    (membership : sectionValue ^ exponent ∈ Submonoid.powers sectionValue) :
    IsLocalization.mk' Γ((sourceScheme.basicOpen sectionValue : Scheme.{u}), ⊤) numerator ⟨sectionValue ^ exponent, membership⟩ =
      sourceScheme.divBasicOpen 1 sectionValue ^ exponent * sourceScheme.divBasicOpen (numerator * sectionValue) sectionValue := by
  have e₁ : sourceScheme.divBasicOpen (numerator * sectionValue) sectionValue = (sourceScheme.basicOpen sectionValue).ι.appTop numerator :=
    (sourceScheme.isUnit_ι_appTop_basicOpen sectionValue).mul_right_cancel
      ((sourceScheme.divBasicOpen_mul_self _ _).trans (map_mul _ _ _))
  have e₂ : sourceScheme.divBasicOpen 1 sectionValue * (sourceScheme.basicOpen sectionValue).ι.appTop sectionValue = 1 :=
    (sourceScheme.divBasicOpen_mul_self _ _).trans (map_one _)
  refine (IsLocalization.eq_mk'_iff_mul_eq.mpr ?_).symm
  change _ * (sourceScheme.basicOpen sectionValue).ι.appTop (sectionValue ^ exponent) = (sourceScheme.basicOpen sectionValue).ι.appTop numerator
  rw [map_pow, e₁, mul_right_comm, ← mul_pow, e₂, one_pow, one_mul]

end Away

theorem exists_finite_basicOpen_cover_le_preimage_isAffineOpen
    {affineScheme baseScheme : Scheme.{u}} [IsAffine affineScheme] (structureMap : affineScheme ⟶ baseScheme) :
    ∃ (coverIndex : Type u) (_ : Finite coverIndex) (sections : coverIndex → Γ(affineScheme, ⊤)) (affineOpen : coverIndex → baseScheme.Opens),
      (∀ coverMember, IsAffineOpen (affineOpen coverMember)) ∧
      (∀ coverMember, affineScheme.basicOpen (sections coverMember) ≤ structureMap ⁻¹ᵁ affineOpen coverMember) ∧
      ⨆ coverMember, affineScheme.basicOpen (sections coverMember) = ⊤ := by
  set allowedSections : Set Γ(affineScheme, ⊤) := {sections | ∃ affineOpen : baseScheme.Opens, IsAffineOpen affineOpen ∧ affineScheme.basicOpen sections ≤ structureMap ⁻¹ᵁ affineOpen}
  have hcov : (Set.univ : Set affineScheme) ⊆ ⋃ sections ∈ allowedSections, (affineScheme.basicOpen sections : Set affineScheme) := by
    intro point _
    obtain ⟨affineOpen, hW, hvW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens baseScheme) (U := ⊤) (x := structureMap.base point) trivial
    obtain ⟨-, ⟨sections, rfl⟩, hvb, hbW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (isBasis_basicOpen affineScheme) (U := structureMap ⁻¹ᵁ affineOpen) (x := point) hvW
    exact Set.mem_biUnion (show sections ∈ allowedSections from ⟨affineOpen, hW, hbW⟩) hvb
  obtain ⟨finiteCover, htT, htfin, htcov⟩ :=
    isCompact_univ.elim_finite_subcover_image (fun sections _ ↦ (affineScheme.basicOpen sections).isOpen) hcov
  have membership : ∀ coverMember : finiteCover, ∃ affineOpen : baseScheme.Opens, IsAffineOpen affineOpen ∧ affineScheme.basicOpen (coverMember : Γ(affineScheme, ⊤)) ≤ structureMap ⁻¹ᵁ affineOpen :=
    fun coverMember ↦ htT coverMember.2
  choose affineOpen hW hWle using membership
  refine ⟨finiteCover, htfin.to_subtype, Subtype.val, affineOpen, hW, hWle, eq_top_iff.mpr fun point _ ↦ ?_⟩
  obtain ⟨sections, hb, hv⟩ := Set.mem_iUnion₂.mp (htcov (Set.mem_univ point))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨sections, hb⟩, hv⟩

end AlgebraicGeometry
