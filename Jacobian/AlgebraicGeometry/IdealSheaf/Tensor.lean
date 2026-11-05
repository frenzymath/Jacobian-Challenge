import Jacobian.AlgebraicGeometry.IdealSheaf.Colon
import Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor
import Jacobian.AlgebraicGeometry.Picard.Group

/-!
# Tensor products of Cartier ideal sheaves

For invertible ideals `I` and `J`, the inclusion `IJ → I` vanishes along `J`.
Consequently multiplication of Cartier ideals gives tensor multiplication of
their Picard classes.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {scheme : Scheme.{u}}

/-- The ideal of sections on an arbitrary open is monotone in the ideal sheaf. -/
lemma idealOfOpens_mono {first second : scheme.IdealSheafData} (inclusion : first ≤ second)
    (openSubset : scheme.Opens) : first.idealOfOpens openSubset ≤ second.idealOfOpens openSubset := by
  intro scalar membership
  rw [mem_idealOfOpens_iff] at membership ⊢
  have normalize : ∀ morphism : second.subscheme ⟶ scheme,
      morphism = second.subschemeι → morphism.app openSubset scalar = 0 →
        second.subschemeι.app openSubset scalar = 0 := by
    rintro morphism rfl equality
    exact equality
  refine normalize _ (inclusion_subschemeι inclusion) ?_
  have equality : (IdealSheafData.inclusion inclusion).app
      (first.subschemeι ⁻¹ᵁ openSubset) (first.subschemeι.app openSubset scalar) = 0 := by
    rw [membership, map_zero]
  exact equality

/-- Inclusion of ideal sheaves induces inclusion of their module sheaves. -/
def toModulesOfLE {first second : scheme.IdealSheafData} (inclusion : first ≤ second) :
    first.toModules ⟶ second.toModules :=
  kernel.lift _ first.toModulesι <| Modules.hom_ext _ _ fun openSubset ↦ by
    ext element
    exact second.mem_idealOfOpens_iff.mp
      (idealOfOpens_mono inclusion openSubset
        ((first.range_toModulesι_app_eq_idealOfOpens openSubset).subset ⟨element, rfl⟩))

@[reassoc (attr := simp)]
lemma toModulesOfLE_toModulesι {first second : scheme.IdealSheafData}
    (inclusion : first ≤ second) :
    toModulesOfLE inclusion ≫ second.toModulesι = first.toModulesι :=
  kernel.lift_ι _ _ _

/-- A principal equation for a Cartier ideal lifts to a free generator of its module sheaf. -/
lemma IsInvertible.exists_isFreeGenerator {ideal : scheme.IdealSheafData}
    (invertible : ideal.IsInvertible) {affineOpen : scheme.affineOpens}
    {equation : Γ(scheme, affineOpen.1)}
    (principal : ideal.ideal affineOpen = Ideal.span {equation}) :
    ∃ generator : Γ(ideal.toModules, affineOpen.1),
      ideal.toModulesι.app affineOpen.1 generator = equation ∧ Modules.IsFreeGenerator generator := by
  obtain ⟨generator, image⟩ := ideal.exists_toModulesι_app_eq
    (principal ▸ Ideal.mem_span_singleton_self equation)
  refine ⟨generator, image, invertible.isFreeGenerator generator fun smaller inclusion ↦ ?_⟩
  rw [image, ← ideal.map_ideal inclusion, principal, Ideal.map_span, Set.image_singleton]
  rfl

/-- A product of ideal sheaves is contained in its first factor. -/
lemma mul_le_left (first second : scheme.IdealSheafData) : first * second ≤ first := by
  change (first * second).ideal ≤ first.ideal
  intro affineOpen
  exact Ideal.mul_le_left

/-- The zero scheme of the inclusion `IJ → I` is the effective Cartier divisor `J`. -/
theorem IsInvertible.zeroLocus_toModulesOfLE_mul {first second : scheme.IdealSheafData}
    (firstInvertible : first.IsInvertible) (secondInvertible : second.IsInvertible) :
    letI : first.toModules.IsInvertible := firstInvertible.isInvertible_toModules
    letI : (first * second).toModules.IsInvertible :=
      (firstInvertible.mul_effectiveCartier secondInvertible).isInvertible_toModules
    Modules.Hom.zeroLocus (toModulesOfLE (first.mul_le_left second)) = second := by
  have productInvertible := firstInvertible.mul_effectiveCartier secondInvertible
  letI := firstInvertible.isInvertible_toModules
  letI := productInvertible.isInvertible_toModules
  have localEquality (point : scheme) : ∃ affineOpen : scheme.affineOpens,
      point ∈ affineOpen.1 ∧
      (Modules.Hom.zeroLocus (toModulesOfLE (first.mul_le_left second))).ideal affineOpen =
        second.ideal affineOpen := by
    obtain ⟨affineOpen, membership, -, ⟨firstEquation, -, firstPrincipal⟩,
      ⟨secondEquation, -, secondPrincipal⟩⟩ :=
      exists_affineOpens_isRegularPrincipal firstInvertible secondInvertible (O := ⊤) trivial
    have productPrincipal : (first * second).ideal affineOpen =
        Ideal.span {firstEquation * secondEquation} := by
      rw [ideal_mul, Pi.mul_apply, firstPrincipal, secondPrincipal,
        Ideal.span_singleton_mul_span_singleton]
    obtain ⟨productGenerator, productImage, productFree⟩ :=
      productInvertible.exists_isFreeGenerator productPrincipal
    obtain ⟨firstGenerator, firstImage, firstFree⟩ :=
      firstInvertible.exists_isFreeGenerator firstPrincipal
    refine ⟨affineOpen, membership, ?_⟩
    rw [Modules.Hom.ideal_zeroLocus _ affineOpen productFree firstFree
      (b := secondEquation), secondPrincipal]
    apply first.injective_toModulesι_app affineOpen.1
    have image := congr($(toModulesOfLE_toModulesι (first.mul_le_left second)).app
      affineOpen.1 productGenerator)
    rw [Modules.Hom.comp_app, ConcreteCategory.comp_apply] at image
    rw [image, Modules.Hom.app_smul, productImage, firstImage, mul_comm, smul_eq_mul]
  choose affineOpen membership equality using localEquality
  exact ext_of_iSup_eq_top affineOpen
    (eq_top_iff.mpr fun point _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨point, membership point⟩) equality

/-- The line bundle of the divisor `J` identifies `I` with `Jᵛ ⊗ IJ`. -/
theorem IsInvertible.nonempty_toModules_iso_dual_tensorObj_mul
    {first second : scheme.IdealSheafData} (firstInvertible : first.IsInvertible)
    (secondInvertible : second.IsInvertible) :
    Nonempty (first.toModules ≅ second.toModulesᵛ ⊗ (first * second).toModules) := by
  letI := firstInvertible.isInvertible_toModules
  letI := (firstInvertible.mul_effectiveCartier secondInvertible).isInvertible_toModules
  have equality := firstInvertible.zeroLocus_toModulesOfLE_mul secondInvertible
  have invertible :
      (Modules.Hom.zeroLocus (toModulesOfLE (first.mul_le_left second))).IsInvertible := by
    rw [equality]
    exact secondInvertible
  obtain ⟨comparison⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj
    (toModulesOfLE (first.mul_le_left second)) invertible
  exact ⟨comparison ≪≫ eqToIso (by rw [equality])⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Pic

variable {scheme : Scheme.{u}}

/-- The Picard class of a product of Cartier ideals is the product of their classes. -/
lemma mk_toModules_mul {first second : scheme.IdealSheafData}
    (firstInvertible : first.IsInvertible) (secondInvertible : second.IsInvertible) :
    letI := firstInvertible.isInvertible_toModules
    letI := secondInvertible.isInvertible_toModules
    letI := (firstInvertible.mul_effectiveCartier secondInvertible).isInvertible_toModules
    mk (first * second).toModules = mk first.toModules * mk second.toModules := by
  letI := firstInvertible.isInvertible_toModules
  letI := secondInvertible.isInvertible_toModules
  letI := (firstInvertible.mul_effectiveCartier secondInvertible).isInvertible_toModules
  obtain ⟨comparison⟩ := firstInvertible.nonempty_toModules_iso_dual_tensorObj_mul
    secondInvertible
  have equality : mk first.toModules = mk (second.toModulesᵛ ⊗ (first * second).toModules) :=
    (mk_eq_mk_iff _ _).2 ⟨comparison⟩
  rw [mk_tensorObj, mk_dual] at equality
  rw [equality, mul_right_comm, inv_mul_cancel, one_mul]

/-- The unit ideal has trivial Picard class. -/
@[simp]
lemma mk_toModules_top :
    letI := (IdealSheafData.isInvertible_top (X := scheme)).isInvertible_toModules
    mk (⊤ : scheme.IdealSheafData).toModules = 1 := by
  have invertible := IdealSheafData.isInvertible_top (X := scheme)
  letI := invertible.isInvertible_toModules
  obtain ⟨comparison⟩ := invertible.nonempty_toModules_iso_dual_tensorObj_mul invertible
  have equality : mk (⊤ : scheme.IdealSheafData).toModules =
      mk ((⊤ : scheme.IdealSheafData).toModulesᵛ ⊗ (⊤ : scheme.IdealSheafData).toModules) :=
    (mk_eq_mk_iff _ _).2
    ⟨comparison ≪≫ whiskerLeftIso _ (eqToIso (by rw [IdealSheafData.top_mul]))⟩
  rw [mk_tensorObj, mk_dual, inv_mul_cancel] at equality
  exact equality

end AlgebraicGeometry.Scheme.Pic
