import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local
import Jacobian.AlgebraicGeometry.Modules.Tensor
import Jacobian.CategoryTheory.Monoidal.Braided.Adjunction
import Jacobian.LinearAlgebra.TensorProduct.FreeGenerator

/-!
# Tensor products of local sections

Elementary tensors of sections map to the sheaf tensor product through its
sheafification map. The structural maps act on these elementary tensors as the
usual unitors, associator, and symmetry. Tensoring with a free generator gives a
bijection on sections over every smaller open subset.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}} {moduleSheaf otherSheaf : scheme.Modules}

variable (moduleSheaf otherSheaf) in
/-- The unit `M ⊗ₚ N ⟶ a(M ⊗ₚ N)` of the sheafification of the tensor product of the
underlying presheaves of modules. -/
noncomputable abbrev toSheafifyTensor :=
  (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 scheme.ringCatSheaf.obj)).unit.app
    (moduleSheaf.val ⊗ otherSheaf.val)

variable (moduleSheaf otherSheaf) in
/-- The sheafification of the tensor product of the underlying presheaves of modules. -/
noncomputable abbrev sheafifyTensor : scheme.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 scheme.ringCatSheaf.obj)).obj (moduleSheaf.val ⊗ otherSheaf.val)

/-- The tensor product `s ⊗ t ∈ Γ(M ⊗ N, U)` of sections `s ∈ Γ(M, U)` and `t ∈ Γ(N, U)`. -/
noncomputable def tmulSection {openSubset : scheme.Opens} (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) : Γ(moduleSheaf ⊗ otherSheaf, openSubset) :=
  Hom.app (SheafOfModules.tensorObjIsoSheafification moduleSheaf otherSheaf).inv openSubset
    ((toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset) (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection))

lemma toSheafifyTensor_map {openSubset smallerOpen : scheme.Opens} (index : smallerOpen ⟶ openSubset) (tensorValue : (moduleSheaf.val ⊗ otherSheaf.val).obj (op openSubset)) :
    (sheafifyTensor moduleSheaf otherSheaf).presheaf.map index.op ((toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset) tensorValue) =
      (toSheafifyTensor moduleSheaf otherSheaf).app (op smallerOpen) ((moduleSheaf.val ⊗ otherSheaf.val).map index.op tensorValue) :=
  (PresheafOfModules.naturality_apply (toSheafifyTensor moduleSheaf otherSheaf) index.op tensorValue).symm

lemma toSheafifyTensor_smul {openSubset : scheme.Opens} (scalar : Γ(scheme, openSubset)) (tensorValue : (moduleSheaf.val ⊗ otherSheaf.val).obj (op openSubset)) :
    (toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset) (scalar • tensorValue) = scalar • (toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset) tensorValue :=
  ((toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset)).hom.map_smul scalar tensorValue

lemma isFreeGenerator_toSheafifyTensor {openSubset : scheme.Opens} {sectionValue : Γ(moduleSheaf, openSubset)} {otherSection : Γ(otherSheaf, openSubset)}
    (hs : IsFreeGenerator sectionValue) (ht : IsFreeGenerator otherSection) :
    IsFreeGenerator (M := sheafifyTensor moduleSheaf otherSheaf)
      ((toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset) (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection)) := by
  have hP (smallestOpen : scheme.Opens) (hW : smallestOpen ≤ openSubset) : Function.Bijective fun scalar : Γ(scheme, smallestOpen) ↦
      scalar • (moduleSheaf.val ⊗ otherSheaf.val).map (homOfLE hW).op (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection) :=
    TensorProduct.bijective_smul_tmul (hs smallestOpen hW) (ht smallestOpen hW)
  have hPmap {smallerOpen smallestOpen : scheme.Opens} (hV : smallerOpen ≤ openSubset) (index : smallestOpen ⟶ smallerOpen) :
      (moduleSheaf.val ⊗ otherSheaf.val).map index.op ((moduleSheaf.val ⊗ otherSheaf.val).map (homOfLE hV).op (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection)) =
        (moduleSheaf.val ⊗ otherSheaf.val).map (homOfLE ((leOfHom index).trans hV)).op (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection) := by
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology scheme)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor moduleSheaf otherSheaf)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallyInjective
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology scheme)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor moduleSheaf otherSheaf)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  have hinj (smallerOpen : scheme.Opens) (compatibility : smallerOpen ≤ openSubset) : Function.Injective fun scalar : Γ(scheme, smallerOpen) ↦
      scalar • (sheafifyTensor moduleSheaf otherSheaf).presheaf.map (homOfLE compatibility).op
        ((toSheafifyTensor moduleSheaf otherSheaf).app (op openSubset) (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection)) := by
    intro scalar otherScalar hrr'
    dsimp only at hrr'
    rw [toSheafifyTensor_map, ← toSheafifyTensor_smul, ← toSheafifyTensor_smul] at hrr'
    have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology scheme)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor moduleSheaf otherSheaf)) (X := op smallerOpen) _ _ hrr'
    have hO := ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ scheme.presheaf
        (CategoryTheory.forget CommRingCat)).mp scheme.sheaf.property)) _ hS
    refine hO.isSeparatedFor.ext fun auxiliaryScheme lastIndex hl ↦ (hP auxiliaryScheme ((leOfHom lastIndex).trans compatibility)).1 ?_
    have : (moduleSheaf.val ⊗ otherSheaf.val).map lastIndex.op (scalar • (moduleSheaf.val ⊗ otherSheaf.val).map (homOfLE compatibility).op
        (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection)) = (moduleSheaf.val ⊗ otherSheaf.val).map lastIndex.op (otherScalar • (moduleSheaf.val ⊗ otherSheaf.val).map (homOfLE compatibility).op
        (sectionValue ⊗ₜ[Γ(scheme, openSubset)] otherSection)) := hl
    rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul, hPmap] at this
    exact this
  refine isFreeGenerator_of_locally _ hinj fun smallerOpen compatibility otherDegree ↦ ?_
  refine ⟨_, Presheaf.imageSieve_mem (Opens.grothendieckTopology scheme)
    ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor moduleSheaf otherSheaf)) (U := op smallerOpen) otherDegree,
    fun smallestOpen index hi ↦ ?_⟩
  obtain ⟨tensorValue, hx⟩ := hi
  obtain ⟨firstElement, rfl⟩ := (hP smallestOpen ((leOfHom index).trans compatibility)).2 tensorValue
  refine ⟨firstElement, ?_⟩
  refine hx.symm.trans ?_
  change (toSheafifyTensor moduleSheaf otherSheaf).app (op smallestOpen) (firstElement • _) = _
  rw [toSheafifyTensor_smul, toSheafifyTensor_map]

/-- **The tensor product of free generators is a free generator.** -/
lemma IsFreeGenerator.tmulSection {openSubset : scheme.Opens} {sectionValue : Γ(moduleSheaf, openSubset)} {otherSection : Γ(otherSheaf, openSubset)}
    (hs : IsFreeGenerator sectionValue) (ht : IsFreeGenerator otherSection) : IsFreeGenerator (tmulSection sectionValue otherSection) :=
  (isFreeGenerator_toSheafifyTensor hs ht).app_hom
    (SheafOfModules.tensorObjIsoSheafification moduleSheaf otherSheaf).symm

lemma tmulSection_map {openSubset smallerOpen : scheme.Opens} (compatibility : smallerOpen ≤ openSubset) (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    (moduleSheaf ⊗ otherSheaf).presheaf.map (homOfLE compatibility).op (tmulSection sectionValue otherSection) =
      tmulSection (moduleSheaf.presheaf.map (homOfLE compatibility).op sectionValue) (otherSheaf.presheaf.map (homOfLE compatibility).op otherSection) := by
  rw [tmulSection]
  refine (Hom.app_presheaf_map (SheafOfModules.tensorObjIsoSheafification moduleSheaf otherSheaf).inv
    (homOfLE compatibility) _).symm.trans ?_
  rw [toSheafifyTensor_map]
  rfl

lemma smul_tmulSection {openSubset : scheme.Opens} (scalar : Γ(scheme, openSubset)) (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    tmulSection (scalar • sectionValue) otherSection = scalar • tmulSection sectionValue otherSection := by
  rw [tmulSection, tmulSection, ← Hom.app_smul, ← toSheafifyTensor_smul]
  rfl

lemma tmulSection_smul {openSubset : scheme.Opens} (scalar : Γ(scheme, openSubset)) (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    tmulSection sectionValue (scalar • otherSection) = scalar • tmulSection sectionValue otherSection := by
  rw [tmulSection, tmulSection, ← Hom.app_smul, ← toSheafifyTensor_smul]
  congr 2
  exact TensorProduct.tmul_smul scalar sectionValue otherSection

section Monoidal

open TensorProduct

/-! ### The tensor product of sections as the tensorator of a lax monoidal functor -/

variable (scheme) in
/-- The braided structure on the sheafification functor of `X`. -/
@[instance_reducible]
noncomputable def sheafificationBraided :
    (sheafification scheme).Braided :=
  SheafOfModules.sheafificationBraided scheme.sheaf

attribute [local instance] sheafificationMonoidal sheafificationBraided

variable (scheme) in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules, in the form which is
right adjoint to `sheafification X`. -/
noncomputable abbrev forgetToPresheafOfModules :
    scheme.Modules ⥤ _root_.PresheafOfModules.{u} scheme.ringCatSheaf.obj :=
  SheafOfModules.forget _ ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 _)

variable (scheme) in
/-- The sheafification adjunction for presheaves of modules over the structure sheaf of `X`. -/
noncomputable abbrev sheafificationAdjunction :
    sheafification scheme ⊣ forgetToPresheafOfModules scheme :=
  _root_.PresheafOfModules.sheafificationAdjunction.{u} (𝟙 scheme.ringCatSheaf.obj)

variable (scheme) in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules is lax monoidal, being
right adjoint to the monoidal sheafification functor. -/
@[instance_reducible]
noncomputable def forgetToPresheafOfModulesLaxMonoidal :
    (forgetToPresheafOfModules scheme).LaxMonoidal :=
  (sheafificationAdjunction scheme).rightAdjointLaxMonoidal

attribute [local instance] forgetToPresheafOfModulesLaxMonoidal

variable {thirdSheaf targetSheaf otherTargetSheaf : scheme.Modules} {openSubset : scheme.Opens}

/-- The tensorator of the lax monoidal functor `forgetToPresheafOfModules X` at `M` and `N`. -/
local notation "μ[" moduleSheaf ", " otherSheaf "]" => Functor.LaxMonoidal.μ (forgetToPresheafOfModules _) moduleSheaf otherSheaf

variable (moduleSheaf otherSheaf openSubset) in
/-- The `Γ(X, U)`-linear map `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)`, the component at `U`
of the tensorator of the lax monoidal functor `forgetToPresheafOfModules X`, i.e. of the
canonical map from the presheaf tensor product to its sheafification `M ⊗ N`. -/
noncomputable def tensorSectionsMap :
    Γ(moduleSheaf, openSubset) ⊗[Γ(scheme, openSubset)] Γ(otherSheaf, openSubset) →ₗ[Γ(scheme, openSubset)] Γ(moduleSheaf ⊗ otherSheaf, openSubset) :=
  (μ[moduleSheaf, otherSheaf].app (op openSubset)).hom

/-- The tensorator of `forgetToPresheafOfModules X` sends `s ⊗ₜ t` to `tmulSection s t`. -/
lemma tensorSectionsMap_tmul (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    tensorSectionsMap moduleSheaf otherSheaf openSubset (sectionValue ⊗ₜ otherSection) = tmulSection sectionValue otherSection :=
  rfl

lemma add_tmulSection (sectionValue otherSectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    tmulSection (sectionValue + otherSectionValue) otherSection = tmulSection sectionValue otherSection + tmulSection otherSectionValue otherSection := by
  rw [← tensorSectionsMap_tmul, TensorProduct.add_tmul, map_add, tensorSectionsMap_tmul,
    tensorSectionsMap_tmul]

lemma tmulSection_add (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection otherOtherSection : Γ(otherSheaf, openSubset)) :
    tmulSection sectionValue (otherSection + otherOtherSection) = tmulSection sectionValue otherSection + tmulSection sectionValue otherOtherSection := by
  rw [← tensorSectionsMap_tmul, TensorProduct.tmul_add, map_add, tensorSectionsMap_tmul,
    tensorSectionsMap_tmul]

@[simp]
lemma zero_tmulSection (otherSection : Γ(otherSheaf, openSubset)) : tmulSection (0 : Γ(moduleSheaf, openSubset)) otherSection = 0 := by
  rw [← tensorSectionsMap_tmul, TensorProduct.zero_tmul, map_zero]

@[simp]
lemma tmulSection_zero (sectionValue : Γ(moduleSheaf, openSubset)) : tmulSection sectionValue (0 : Γ(otherSheaf, openSubset)) = 0 := by
  rw [← tensorSectionsMap_tmul, TensorProduct.tmul_zero, map_zero]

/-- Naturality of the tensor product of sections. -/
lemma tensorHom_app_tmulSection (morphism : moduleSheaf ⟶ targetSheaf) (otherMorphism : otherSheaf ⟶ otherTargetSheaf) (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    (morphism ⊗ₘ otherMorphism).app openSubset (tmulSection sectionValue otherSection) = tmulSection (morphism.app openSubset sectionValue) (otherMorphism.app openSubset otherSection) :=
  (congr_arg (fun φ ↦ φ.app (op openSubset) (sectionValue ⊗ₜ otherSection))
    (Functor.LaxMonoidal.μ_natural (forgetToPresheafOfModules scheme) morphism otherMorphism)).symm

lemma whiskerLeft_app_tmulSection (otherMorphism : otherSheaf ⟶ otherTargetSheaf) (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    (moduleSheaf ◁ otherMorphism).app openSubset (tmulSection sectionValue otherSection) = tmulSection sectionValue (otherMorphism.app openSubset otherSection) :=
  (congr_arg (fun φ ↦ φ.app (op openSubset) (sectionValue ⊗ₜ otherSection))
    (Functor.LaxMonoidal.μ_natural_right (forgetToPresheafOfModules scheme) moduleSheaf otherMorphism)).symm

lemma whiskerRight_app_tmulSection (morphism : moduleSheaf ⟶ targetSheaf) (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    (morphism ▷ otherSheaf).app openSubset (tmulSection sectionValue otherSection) = tmulSection (morphism.app openSubset sectionValue) otherSection :=
  (congr_arg (fun φ ↦ φ.app (op openSubset) (sectionValue ⊗ₜ otherSection))
    (Functor.LaxMonoidal.μ_natural_left (forgetToPresheafOfModules scheme) morphism otherSheaf)).symm

variable (openSubset) in
/-- The sections of the unit `𝟙_ X.Modules = 𝒪_X` over `U` are the functions `Γ(X, U)`. -/
noncomputable def unitSectionsEquiv : Γ(scheme, openSubset) ≃ₗ[Γ(scheme, openSubset)] Γ(𝟙_ scheme.Modules, openSubset) :=
  LinearEquiv.refl _ _

/-- A section of the unit is a multiple of the section `1`. -/
lemma unitSectionsEquiv_eq_smul_one (scalar : Γ(scheme, openSubset)) :
    unitSectionsEquiv openSubset scalar = scalar • unitSectionsEquiv openSubset 1 := by
  rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]

/-- Restriction of sections of the unit is restriction of functions. -/
lemma presheaf_map_unitSectionsEquiv {smallerOpen : scheme.Opens} (index : smallerOpen ⟶ openSubset) (scalar : Γ(scheme, openSubset)) :
    (𝟙_ scheme.Modules).presheaf.map index.op (unitSectionsEquiv openSubset scalar) =
      unitSectionsEquiv smallerOpen (scheme.presheaf.map index.op scalar) :=
  rfl

/-- The unit of the lax monoidal functor `forgetToPresheafOfModules X` is the identity. -/
lemma ε_forgetToPresheafOfModules_app (scalar : Γ(scheme, openSubset)) :
    (Functor.LaxMonoidal.ε (forgetToPresheafOfModules scheme)).app (op openSubset) scalar =
      unitSectionsEquiv openSubset scalar :=
  congr_arg (fun φ ↦ φ.app (op openSubset) scalar)
    ((sheafificationAdjunction scheme).right_triangle_components (SheafOfModules.unit _))

/-- The left unitor on elementary tensors: `1 ⊗ s ↦ s`. -/
lemma leftUnitor_hom_app_tmulSection (scalar : Γ(scheme, openSubset)) (sectionValue : Γ(moduleSheaf, openSubset)) :
    (λ_ moduleSheaf).hom.app openSubset (tmulSection (unitSectionsEquiv openSubset scalar) sectionValue) = scalar • sectionValue := by
  rw [← ε_forgetToPresheafOfModules_app]
  exact (congr_arg (fun φ ↦ φ.app (op openSubset) (scalar ⊗ₜ sectionValue))
    (Functor.LaxMonoidal.left_unitality (forgetToPresheafOfModules scheme) moduleSheaf)).symm

/-- The right unitor on elementary tensors: `s ⊗ 1 ↦ s`. -/
lemma rightUnitor_hom_app_tmulSection (scalar : Γ(scheme, openSubset)) (sectionValue : Γ(moduleSheaf, openSubset)) :
    (ρ_ moduleSheaf).hom.app openSubset (tmulSection sectionValue (unitSectionsEquiv openSubset scalar)) = scalar • sectionValue := by
  rw [← ε_forgetToPresheafOfModules_app]
  exact (congr_arg (fun φ ↦ φ.app (op openSubset) (sectionValue ⊗ₜ scalar))
    (Functor.LaxMonoidal.right_unitality (forgetToPresheafOfModules scheme) moduleSheaf)).symm

/-- The left unitor on elementary tensors, for an arbitrary section of the unit. -/
lemma leftUnitor_hom_app_tmulSection' (firstElement : Γ(𝟙_ scheme.Modules, openSubset)) (sectionValue : Γ(moduleSheaf, openSubset)) :
    (λ_ moduleSheaf).hom.app openSubset (tmulSection firstElement sectionValue) = (unitSectionsEquiv openSubset).symm firstElement • sectionValue := by
  rw [← leftUnitor_hom_app_tmulSection, LinearEquiv.apply_symm_apply]

/-- The right unitor on elementary tensors, for an arbitrary section of the unit. -/
lemma rightUnitor_hom_app_tmulSection' (sectionValue : Γ(moduleSheaf, openSubset)) (firstElement : Γ(𝟙_ scheme.Modules, openSubset)) :
    (ρ_ moduleSheaf).hom.app openSubset (tmulSection sectionValue firstElement) = (unitSectionsEquiv openSubset).symm firstElement • sectionValue := by
  rw [← rightUnitor_hom_app_tmulSection, LinearEquiv.apply_symm_apply]

/-- The associator on elementary tensors: `(s ⊗ t) ⊗ w ↦ s ⊗ (t ⊗ w)`. -/
lemma associator_hom_app_tmulSection (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) (thirdSection : Γ(thirdSheaf, openSubset)) :
    (α_ moduleSheaf otherSheaf thirdSheaf).hom.app openSubset (tmulSection (tmulSection sectionValue otherSection) thirdSection) =
      tmulSection sectionValue (tmulSection otherSection thirdSection) :=
  congr_arg (fun φ ↦ φ.app (op openSubset) ((sectionValue ⊗ₜ otherSection) ⊗ₜ thirdSection))
    (Functor.LaxMonoidal.associativity (forgetToPresheafOfModules scheme) moduleSheaf otherSheaf thirdSheaf)

/-- The braiding on elementary tensors: `s ⊗ t ↦ t ⊗ s`. -/
lemma braiding_hom_app_tmulSection (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) :
    (β_ moduleSheaf otherSheaf).hom.app openSubset (tmulSection sectionValue otherSection) = tmulSection otherSection sectionValue :=
  congr_arg (fun φ ↦ φ.app (op openSubset) (sectionValue ⊗ₜ otherSection))
    ((sheafificationAdjunction scheme).rightAdjointLaxMonoidal_μ_comp_map_braiding moduleSheaf otherSheaf)

/-- The inverse of an isomorphism of modules undoes it on sections. -/
lemma inv_app_hom_app_apply_of_iso (generator : moduleSheaf ≅ otherSheaf) (sectionElement : Γ(moduleSheaf, openSubset)) :
    generator.inv.app openSubset (generator.hom.app openSubset sectionElement) = sectionElement := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, generator.hom_inv_id, Hom.id_app]
  rfl

/-- An isomorphism of modules is bijective on sections. -/
lemma bijective_app_of_iso (generator : moduleSheaf ≅ otherSheaf) (openSubset : scheme.Opens) : Function.Bijective (generator.hom.app openSubset) :=
  ConcreteCategory.bijective_of_isIso (generator.hom.app openSubset)

/-- The inverse of the left unitor: `s ↦ 1 ⊗ s`. -/
lemma leftUnitor_inv_app (sectionValue : Γ(moduleSheaf, openSubset)) :
    (λ_ moduleSheaf).inv.app openSubset sectionValue = tmulSection (unitSectionsEquiv openSubset 1) sectionValue := by
  conv_lhs => rw [← one_smul Γ(scheme, openSubset) sectionValue, ← leftUnitor_hom_app_tmulSection]
  exact inv_app_hom_app_apply_of_iso _ _

/-- The inverse of the right unitor: `s ↦ s ⊗ 1`. -/
lemma rightUnitor_inv_app (sectionValue : Γ(moduleSheaf, openSubset)) :
    (ρ_ moduleSheaf).inv.app openSubset sectionValue = tmulSection sectionValue (unitSectionsEquiv openSubset 1) := by
  conv_lhs => rw [← one_smul Γ(scheme, openSubset) sectionValue, ← rightUnitor_hom_app_tmulSection]
  exact inv_app_hom_app_apply_of_iso _ _

/-- The inverse of the associator: `s ⊗ (t ⊗ w) ↦ (s ⊗ t) ⊗ w`. -/
lemma associator_inv_app_tmulSection (sectionValue : Γ(moduleSheaf, openSubset)) (otherSection : Γ(otherSheaf, openSubset)) (thirdSection : Γ(thirdSheaf, openSubset)) :
    (α_ moduleSheaf otherSheaf thirdSheaf).inv.app openSubset (tmulSection sectionValue (tmulSection otherSection thirdSection)) =
      tmulSection (tmulSection sectionValue otherSection) thirdSection := by
  rw [← associator_hom_app_tmulSection]
  exact inv_app_hom_app_apply_of_iso _ _

variable (moduleSheaf otherSheaf) in
/-- The map from the presheaf tensor product to `M ⊗ N` is the unit of the sheafification
adjunction followed by an isomorphism. -/
lemma toPresheaf_map_μ :
    (_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf] =
      CategoryTheory.toSheafify _ _ ≫ (_root_.PresheafOfModules.toPresheaf _).map
        ((forgetToPresheafOfModules scheme).map (Functor.OplaxMonoidal.δ (sheafification scheme) _ _ ≫
          ((sheafificationAdjunction scheme).counit.app moduleSheaf ⊗ₘ
            (sheafificationAdjunction scheme).counit.app otherSheaf))) := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit, Functor.map_comp]
  exact congr_arg (· ≫ _)
    (_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _)

variable (moduleSheaf otherSheaf) in
/-- The comparison isomorphism `a(M ⊗ₚ N) ≅ M ⊗ N`, seen on underlying presheaves. -/
instance isIso_toPresheaf_map_δ_comp_counit :
    IsIso ((_root_.PresheafOfModules.toPresheaf _).map
        ((forgetToPresheafOfModules scheme).map (Functor.OplaxMonoidal.δ (sheafification scheme) _ _ ≫
          ((sheafificationAdjunction scheme).counit.app moduleSheaf ⊗ₘ
            (sheafificationAdjunction scheme).counit.app otherSheaf)))) := by
  have : IsIso (sheafificationAdjunction scheme).counit :=
    (inferInstance : IsIso (_root_.PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 scheme.ringCatSheaf.obj)).counit)
  infer_instance

variable (moduleSheaf otherSheaf) in
/-- The map from the presheaf tensor product to `M ⊗ N` becomes an isomorphism after
sheafification. -/
lemma W_toPresheaf_map_μ :
    (Opens.grothendieckTopology scheme).W ((_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf]) := by
  rw [toPresheaf_map_μ]
  exact MorphismProperty.comp_mem _ _ _ ((Opens.grothendieckTopology scheme).W_toSheafify _)
    (MorphismProperty.of_isIso _ _)

instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology scheme)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf]) :=
  (W_toPresheaf_map_μ moduleSheaf otherSheaf).isLocallyInjective

instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology scheme)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf]) :=
  (W_toPresheaf_map_μ moduleSheaf otherSheaf).isLocallySurjective

/-- Tensoring with a free generator `e` of `N` on `V` is injective on sections over `W ≤ V`. -/
lemma IsFreeGenerator.injective_tmulSection_right {smallerOpen : scheme.Opens} {generator : Γ(otherSheaf, smallerOpen)}
    (he : IsFreeGenerator generator) {smallestOpen : scheme.Opens} (compatibility : smallestOpen ≤ smallerOpen) :
    Function.Injective fun sectionValue : Γ(moduleSheaf, smallestOpen) ↦
      Modules.tmulSection sectionValue (otherSheaf.presheaf.map (homOfLE compatibility).op generator) := by
  intro sectionValue otherSectionValue hss'
  simp only [← tensorSectionsMap_tmul] at hss'
  have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology scheme)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf]) (X := op smallestOpen)
    (sectionValue ⊗ₜ[Γ(scheme, smallestOpen)] otherSheaf.presheaf.map (homOfLE compatibility).op generator : Γ(moduleSheaf, smallestOpen) ⊗[Γ(scheme, smallestOpen)] Γ(otherSheaf, smallestOpen))
    (otherSectionValue ⊗ₜ[Γ(scheme, smallestOpen)] otherSheaf.presheaf.map (homOfLE compatibility).op generator : Γ(moduleSheaf, smallestOpen) ⊗[Γ(scheme, smallestOpen)] Γ(otherSheaf, smallestOpen)) hss'
  have hM := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ moduleSheaf.presheaf
      (CategoryTheory.forget AddCommGrpCat)).mp moduleSheaf.isSheaf)) _ hS
  refine hM.isSeparatedFor.ext fun otherSmallestOpen morphism hf ↦ ?_
  apply (TensorProduct.bijective_tmul_right_of_bijective_smul
    (firstModule := Γ(moduleSheaf, otherSmallestOpen))
    (he.map ((leOfHom morphism).trans compatibility)).bijective).1
  have hf' : moduleSheaf.presheaf.map morphism.op sectionValue ⊗ₜ[Γ(scheme, otherSmallestOpen)]
        otherSheaf.presheaf.map morphism.op (otherSheaf.presheaf.map (homOfLE compatibility).op generator) =
      moduleSheaf.presheaf.map morphism.op otherSectionValue ⊗ₜ[Γ(scheme, otherSmallestOpen)]
        otherSheaf.presheaf.map morphism.op (otherSheaf.presheaf.map (homOfLE compatibility).op generator) := hf
  rw [presheaf_map_map_apply] at hf'
  exact hf'

/-- Restriction of an elementary tensor with a restriction of a fixed section `e`. -/
lemma presheaf_map_tmulSection_presheaf_map {smallerOpen smallestOpen otherSmallestOpen : scheme.Opens} (generator : Γ(otherSheaf, smallerOpen)) (compatibility : smallestOpen ≤ smallerOpen)
    (otherCompatibility : otherSmallestOpen ≤ smallerOpen) (otherMorphism : otherSmallestOpen ⟶ smallestOpen) (sectionValue : Γ(moduleSheaf, smallestOpen)) :
    (moduleSheaf ⊗ otherSheaf).presheaf.map otherMorphism.op (Modules.tmulSection sectionValue (otherSheaf.presheaf.map (homOfLE compatibility).op generator)) =
      Modules.tmulSection (moduleSheaf.presheaf.map otherMorphism.op sectionValue) (otherSheaf.presheaf.map (homOfLE otherCompatibility).op generator) := by
  refine (tmulSection_map (leOfHom otherMorphism) _ _).trans ?_
  rw [presheaf_map_map_apply]
  rfl

/-- **Local triviality of tensor products.** If `e` is a free generator of `N` on `V`, then
`s ↦ s ⊗ e|_W` is a bijection `Γ(M, W) → Γ(M ⊗ N, W)` for every `W ≤ V`.

The map from the presheaf tensor product to `M ⊗ N` is locally bijective, and on opens
contained in `V` the presheaf tensor product is identified with `M` by `s ↦ s ⊗ e`; one
concludes with the sheaf property of `M` and `M ⊗ N`. -/
lemma IsFreeGenerator.bijective_tmulSection_right {smallerOpen : scheme.Opens} {generator : Γ(otherSheaf, smallerOpen)}
    (he : IsFreeGenerator generator) {smallestOpen : scheme.Opens} (compatibility : smallestOpen ≤ smallerOpen) :
    Function.Bijective fun sectionValue : Γ(moduleSheaf, smallestOpen) ↦
      Modules.tmulSection sectionValue (otherSheaf.presheaf.map (homOfLE compatibility).op generator) := by
  refine ⟨he.injective_tmulSection_right compatibility, fun sectionValue ↦ ?_⟩
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology scheme)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf]) (U := op smallestOpen) sectionValue
  have hb (otherSmallestOpen : scheme.Opens) (morphism : otherSmallestOpen ⟶ smallestOpen) := (TensorProduct.bijective_tmul_right_of_bijective_smul
    (firstModule := Γ(moduleSheaf, otherSmallestOpen))
    (he.map ((leOfHom morphism).trans compatibility)).bijective).2
  let tensorValue : Presieve.FamilyOfElements (moduleSheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (Presheaf.imageSieve ((_root_.PresheafOfModules.toPresheaf _).map μ[moduleSheaf, otherSheaf]) sectionValue).arrows :=
    fun otherSmallestOpen morphism hf ↦ Function.surjInv (hb otherSmallestOpen morphism)
      (Presheaf.localPreimage _ sectionValue morphism hf : Γ(moduleSheaf, otherSmallestOpen) ⊗[Γ(scheme, otherSmallestOpen)] Γ(otherSheaf, otherSmallestOpen))
  have hx {otherSmallestOpen : scheme.Opens} (morphism : otherSmallestOpen ⟶ smallestOpen) (hf) :
      Modules.tmulSection (tensorValue morphism hf) (otherSheaf.presheaf.map (homOfLE ((leOfHom morphism).trans compatibility)).op generator) =
        (moduleSheaf ⊗ otherSheaf).presheaf.map morphism.op sectionValue :=
    (tensorSectionsMap_tmul _ _).symm.trans
      ((congr_arg (tensorSectionsMap moduleSheaf otherSheaf otherSmallestOpen) (Function.surjInv_eq (hb otherSmallestOpen morphism) _)).trans
        (Presheaf.app_localPreimage _ sectionValue morphism hf))
  have hcompat : tensorValue.Compatible := by
    intro Z₁ Z₂ auxiliaryScheme g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    have hZ : auxiliaryScheme ≤ smallerOpen := (leOfHom (g₁ ≫ f₁)).trans compatibility
    have e₁ := presheaf_map_tmulSection_presheaf_map generator ((leOfHom f₁).trans compatibility) hZ g₁ (tensorValue f₁ hf₁)
    have e₂ := presheaf_map_tmulSection_presheaf_map generator ((leOfHom f₂).trans compatibility) hZ g₂ (tensorValue f₂ hf₂)
    rw [hx, presheaf_map_map_apply, hcomm] at e₁
    rw [hx, presheaf_map_map_apply] at e₂
    exact he.injective_tmulSection_right hZ (e₁.symm.trans e₂)
  have hM := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ moduleSheaf.presheaf
      (CategoryTheory.forget AddCommGrpCat)).mp moduleSheaf.isSheaf)) _ hS
  have hMN := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ (moduleSheaf ⊗ otherSheaf).presheaf
      (CategoryTheory.forget AddCommGrpCat)).mp (moduleSheaf ⊗ otherSheaf).isSheaf)) _ hS
  refine ⟨hM.amalgamate tensorValue hcompat,
    hMN.isSeparatedFor.ext fun otherSmallestOpen morphism hf ↦ ?_⟩
  exact (presheaf_map_tmulSection_presheaf_map generator compatibility ((leOfHom morphism).trans compatibility) morphism _).trans
    ((congrArg (Modules.tmulSection · _) (hM.valid_glue hcompat morphism hf)).trans (hx morphism hf))

/-- **Local triviality of tensor products**, with the free generator on the left: if `e` is a
free generator of `M` on `V`, then `t ↦ e|_W ⊗ t` is a bijection `Γ(N, W) → Γ(M ⊗ N, W)` for
every `W ≤ V`. -/
lemma IsFreeGenerator.bijective_tmulSection_left {smallerOpen : scheme.Opens} {generator : Γ(moduleSheaf, smallerOpen)}
    (he : IsFreeGenerator generator) {smallestOpen : scheme.Opens} (compatibility : smallestOpen ≤ smallerOpen) :
    Function.Bijective fun otherSection : Γ(otherSheaf, smallestOpen) ↦
      Modules.tmulSection (moduleSheaf.presheaf.map (homOfLE compatibility).op generator) otherSection := by
  have : (fun otherSection : Γ(otherSheaf, smallestOpen) ↦ Modules.tmulSection (moduleSheaf.presheaf.map (homOfLE compatibility).op generator) otherSection) =
      (β_ otherSheaf moduleSheaf).hom.app smallestOpen ∘
        fun otherSection : Γ(otherSheaf, smallestOpen) ↦ Modules.tmulSection otherSection (moduleSheaf.presheaf.map (homOfLE compatibility).op generator) := by
    ext otherSection
    exact (braiding_hom_app_tmulSection _ _).symm
  rw [this]
  exact (bijective_app_of_iso _ smallestOpen).comp (he.bijective_tmulSection_right compatibility)

end Monoidal

end AlgebraicGeometry.Scheme.Modules
