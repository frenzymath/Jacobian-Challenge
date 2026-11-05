import Jacobian.Algebra.Category.ModuleCat.Dual
import Jacobian.AlgebraicGeometry.Cohomology.DualityPairing
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveLine
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwistPresentation
import Jacobian.AlgebraicGeometry.Modules.Coherent
import Jacobian.AlgebraicGeometry.Modules.TensorHom
import Jacobian.AlgebraicGeometry.ProjectiveLine.Differentials
import Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import Jacobian.AlgebraicGeometry.ProjectiveLine.Koszul
import Jacobian.AlgebraicGeometry.ProjectiveLine.TwistCohomology
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Tensor

/-!
# Degree-one Serre duality on the projective line

A nonzero linear form on `H¹(Ω¹)` gives a perfect pairing between morphisms
into `Ω¹` and first cohomology. For twists, the degree-minus-two calculation
and descending induction along the coordinate Koszul sequences prove
surjectivity, and the dimension calculation proves injectivity. Finite twist
presentations extend the pairing to every finitely presented module sheaf.
The resulting linear isomorphisms are natural in the coefficient sheaf.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type u) [Field baseField]

local notation "lineGrading" => MvPolynomial.homogeneousSubmodule (Fin 2) baseField
local notation "𝒪(" twistDegree ")" => Proj.twist lineGrading twistDegree
local notation "ω" => Scheme.Hom.relativeDifferentials (projectiveLineToSpec baseField)

local instance : (Proj lineGrading).Over (Spec (.of baseField)) :=
  overSpec baseField

private theorem nonempty_dual_twist_iso (twistDegree : ℤ) :
    Nonempty ((𝒪(twistDegree))ᵛ ≅ 𝒪(-twistDegree)) := by
  obtain ⟨productIso⟩ := Proj.nonempty_tensorObj_twist_iso lineGrading
    (Proj.exists_mem_basicOpen_homogeneousSubmodule (Fin 2) baseField)
    (-twistDegree) twistDegree
  let inverseIso : 𝒪(-twistDegree) ⊗ 𝒪(twistDegree) ≅ 𝟙_ _ :=
    productIso ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫
      (Proj.unitIsoTwistZero (𝒜 := lineGrading)).symm
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso inverseIso.symm _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (tensorObjDualIsoUnit (𝒪(twistDegree))) ≪≫ ρ_ _⟩

/-- The internal hom from a twist to the cotangent sheaf is the complementary twist. -/
theorem nonempty_homObj_twist_iso (twistDegree : ℤ) :
    Nonempty (homObj (𝒪(twistDegree)) ω ≅ 𝒪(-twistDegree + -2)) := by
  let differentialIso := relativeDifferentialsIsoTwist baseField
  letI : (ω).IsInvertible := Scheme.Hom.isInvertible_relativeDifferentials (projectiveLineToSpec baseField)
  obtain ⟨dualIso⟩ := nonempty_dual_twist_iso baseField twistDegree
  obtain ⟨tensorIso⟩ := Proj.nonempty_tensorObj_twist_iso lineGrading
    (Proj.exists_mem_basicOpen_homogeneousSubmodule (Fin 2) baseField) (-twistDegree) (-2)
  exact ⟨(asIso (dualTensorHom _ _)).symm ≪≫ (dualIso ⊗ᵢ differentialIso) ≪≫ tensorIso⟩

/-- The internal-hom twist comparison induces a linear equivalence on global cohomology. -/
def homObjTwistHZeroLinearEquiv (twistDegree : ℤ) :
    H (homObj (𝒪(twistDegree)) ω) 0 ≃ₗ[baseField] (𝒪(-twistDegree + -2)).H 0 :=
  ((cohomologyFunctor baseField 0).mapIso
    (nonempty_homObj_twist_iso baseField twistDegree).some).toLinearEquiv

/-- The two sides of the twist duality pairing have equal dimension. -/
theorem finrank_H_zero_homObj_twist (twistDegree : ℤ) :
    Module.finrank baseField (H (homObj (𝒪(twistDegree)) ω) 0) =
      Module.finrank baseField (Module.Dual baseField ((𝒪(twistDegree)).H 1)) := by
  rw [(homObjTwistHZeroLinearEquiv baseField twistDegree).finrank_eq]
  rw [← sub_eq_add_neg (-twistDegree) 2]
  exact finrank_H_zero_twist_eq_dual_H_one_twist baseField twistDegree

private theorem bijective_dualPairing_twist_of_surjective
    (traceForm : Module.Dual baseField ((ω).H 1)) (twistDegree : ℤ)
    (surjectivePairing : Function.Surjective (dualPairing traceForm (𝒪(twistDegree)))) :
    Function.Bijective (dualPairing traceForm (𝒪(twistDegree))) := by
  rw [← bijective_dualPairingH_iff]
  have surjectiveLinearPairing :
      Function.Surjective (dualPairingH traceForm (𝒪(twistDegree))) := by
    intro value
    obtain ⟨morphism, rfl⟩ := surjectivePairing value
    exact ⟨(homObjHZeroAddEquiv _ _).symm morphism, by
      rw [dualPairingH_apply, AddEquiv.apply_symm_apply]⟩
  letI := finiteDimensional_H_one_twist baseField twistDegree
  letI : FiniteDimensional baseField (H (homObj (𝒪(twistDegree)) ω) 0) := by
    letI := finiteDimensional_H_zero_twist baseField (-twistDegree + -2)
    exact (homObjTwistHZeroLinearEquiv baseField twistDegree).symm.finiteDimensional
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_H_zero_homObj_twist baseField twistDegree)).2 surjectiveLinearPairing,
    surjectiveLinearPairing⟩

/-- First cohomology of the cotangent sheaf admits a nonzero linear form. -/
theorem exists_dual_H_one_relativeDifferentials_ne_zero :
    ∃ traceForm : Module.Dual baseField ((ω).H 1), traceForm ≠ 0 := by
  let differentialIso := relativeDifferentialsIsoTwist baseField
  let comparison : (ω).H 1 ≃ₗ[baseField] (𝒪(-2)).H 1 :=
    ((cohomologyFunctor baseField 1).mapIso differentialIso).toLinearEquiv
  letI := finiteDimensional_H_one_twist baseField (-2)
  letI : FiniteDimensional baseField ((ω).H 1) := comparison.symm.finiteDimensional
  have dimension : Module.finrank baseField (Module.Dual baseField ((ω).H 1)) = 1 := by
    rw [Subspace.dual_finrank_eq, comparison.finrank_eq, ← Subspace.dual_finrank_eq]
    exact finrank_dual_H_one_twist_neg_two baseField
  letI := Module.nontrivial_of_finrank_eq_succ dimension
  exact exists_ne 0

private theorem surjective_dualPairing_twist_neg_two
    (traceForm : Module.Dual baseField ((ω).H 1)) (traceNonzero : traceForm ≠ 0) :
    Function.Surjective (dualPairing traceForm (𝒪(-2))) := by
  let differentialIso := relativeDifferentialsIsoTwist baseField
  obtain ⟨classValue, nonzeroValue⟩ : ∃ classValue, traceForm classValue ≠ 0 := by
    by_contra! vanishes
    exact traceNonzero (LinearMap.ext vanishes)
  have nonzeroPairing :
      dualPairingH traceForm (𝒪(-2))
        ((homObjHZeroAddEquiv _ _).symm differentialIso.inv) ≠ 0 := by
    rw [dualPairingH_apply, AddEquiv.apply_symm_apply]
    intro zeroPairing
    refine nonzeroValue ?_
    have evaluation := LinearMap.congr_fun zeroPairing (H.map differentialIso.hom 1 classValue)
    rwa [dualPairing_apply, ← H.map_comp_apply, differentialIso.hom_inv_id,
      H.map_id_apply] at evaluation
  have dimension := finrank_dual_H_one_twist_neg_two baseField
  letI := finiteDimensional_H_one_twist baseField (-2)
  have fullRange : LinearMap.range (dualPairingH traceForm (𝒪(-2))) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    refine le_antisymm (Submodule.finrank_le _) ?_
    rw [dimension, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    have rangeMembership := LinearMap.mem_range_self (dualPairingH traceForm (𝒪(-2)))
      ((homObjHZeroAddEquiv _ _).symm differentialIso.inv)
    exact fun zeroRange ↦ nonzeroPairing (by
      rw [zeroRange] at rangeMembership
      exact (Submodule.mem_bot baseField).1 rangeMembership)
  intro value
  obtain ⟨sectionValue, rfl⟩ := LinearMap.range_eq_top.1 fullRange value
  exact ⟨_, rfl⟩

/-- A nonzero trace gives perfect degree-one duality for every twist. -/
theorem bijective_dualPairing_twist
    (traceForm : Module.Dual baseField ((ω).H 1)) (traceNonzero : traceForm ≠ 0)
    (twistDegree : ℤ) : Function.Bijective (dualPairing traceForm (𝒪(twistDegree))) := by
  refine bijective_dualPairing_twist_of_surjective baseField traceForm twistDegree ?_
  rcases le_or_gt (-1) twistDegree with nonnegative | negative
  · letI := subsingleton_H_one_twist baseField twistDegree nonnegative
    intro value
    refine ⟨0, LinearMap.ext fun classValue ↦ ?_⟩
    rw [Subsingleton.elim classValue 0, map_zero, map_zero]
  · obtain ⟨depth, rfl⟩ : ∃ depth : ℕ, twistDegree = -2 - depth :=
      ⟨(-2 - twistDegree).toNat, by omega⟩
    clear negative
    induction depth with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      exact surjective_dualPairing_twist_neg_two baseField traceForm traceNonzero
    | succ depth inductionHypothesis =>
      have nextPairing :=
        bijective_dualPairing_twist_of_surjective baseField traceForm _ inductionHypothesis
      have nextDegree : -2 - ((depth + 1 : ℕ) : ℤ) + 1 = -2 - depth := by
        push_cast
        ring
      rw [← nextDegree] at nextPairing
      let degree : ℤ := -2 - ((depth + 1 : ℕ) : ℤ)
      letI : Subsingleton ((Proj.koszul baseField degree).X₃.H 0) := by
        change Subsingleton ((𝒪(degree + 1 + 1)).H 0)
        exact subsingleton_H_zero_twist_of_neg baseField _ (by dsimp only [degree]; omega)
      exact surjective_dualPairing_of_injective traceForm (Proj.koszulLeft baseField degree)
        (H.injective_map_f_one (shortComplex := Proj.koszul baseField degree)
          (Proj.koszul_shortExact baseField degree))
        (bijective_dualPairing_biprod traceForm _ _ nextPairing nextPairing).2

/-- Degree-one duality is perfect for every finitely presented module sheaf. -/
theorem bijective_dualPairing_of_isFinitePresentation
    (traceForm : Module.Dual baseField ((ω).H 1)) (traceNonzero : traceForm ≠ 0)
    (coefficient : (projectiveLine baseField).Modules) [coefficient.IsFinitePresentation] :
    Function.Bijective (dualPairing traceForm coefficient) := by
  have sumPairing (indexType : Type u) [Finite indexType] (generatorDegree : indexType → ℕ) :=
    bijective_dualPairing_sigma traceForm _ fun index ↦
      bijective_dualPairing_twist baseField traceForm traceNonzero (-(generatorDegree index : ℤ))
  obtain ⟨generatorIndex, generatorFinite, generatorDegree, presentationMap,
      presentationEpi, kernelQuasicoherent, kernelFinitePresentation⟩ :=
    Proj.exists_epi_sigma_twist.{u, 0} (Fin 2) baseField coefficient
  letI := generatorFinite
  letI := presentationEpi
  letI := kernelQuasicoherent
  letI := kernelFinitePresentation
  obtain ⟨relationIndex, relationFinite, relationDegree, relationMap, relationEpi, _, _⟩ :=
    Proj.exists_epi_sigma_twist.{u, 0} (Fin 2) baseField (kernel presentationMap)
  letI := relationFinite
  letI := relationEpi
  let kernelSequence :=
    ShortComplex.mk (kernel.ι presentationMap) presentationMap (kernel.condition presentationMap)
  have shortExact : kernelSequence.ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel presentationMap))
      inferInstance presentationEpi
  letI : Subsingleton ((kernel presentationMap).H (1 + 1)) :=
    subsingleton_H_of_affine_hom_projectiveLine (𝟙 (projectiveLine baseField))
      (kernel presentationMap) (1 + 1) le_rfl
  exact bijective_dualPairing_of_epi traceForm presentationMap relationMap
    (sumPairing generatorIndex generatorDegree) (sumPairing relationIndex relationDegree).1
    (H.surjective_map_g (shortComplex := kernelSequence) shortExact 1)

/-- Serre duality in degree one, naturally in finitely presented coefficient sheaves. -/
theorem nonempty_dual_H_one_iso :
    let finitePresentation : ObjectProperty (projectiveLine baseField).Modules :=
      fun coefficient ↦ coefficient.IsFinitePresentation
    Nonempty (finitePresentation.ι.op ⋙ (cohomologyFunctor baseField 1).op ⋙
        ModuleCat.dualFunctor baseField ≅
      finitePresentation.ι.op ⋙
        (SheafOfModules.homFunctor (projectiveLine baseField).sheaf).flip.obj ω ⋙
        cohomologyFunctor baseField 0) := by
  let finitePresentation : ObjectProperty (projectiveLine baseField).Modules :=
    fun coefficient ↦ coefficient.IsFinitePresentation
  obtain ⟨traceForm, traceNonzero⟩ := exists_dual_H_one_relativeDifferentials_ne_zero baseField
  let comparison : finitePresentation.ι.op ⋙
        (SheafOfModules.homFunctor (projectiveLine baseField).sheaf).flip.obj ω ⋙
        cohomologyFunctor baseField 0 ⟶
      finitePresentation.ι.op ⋙ (cohomologyFunctor baseField 1).op ⋙
        ModuleCat.dualFunctor baseField :=
    { app coefficient := ModuleCat.ofHom (dualPairingH traceForm coefficient.unop.obj)
      naturality source target morphism := by
        ext sectionValue : 2
        refine LinearMap.ext fun classValue ↦ ?_
        change dualPairing traceForm _ (homObjHZeroAddEquiv _ _ (H.map
            (SheafOfModules.homObjMap (R := (projectiveLine baseField).sheaf)
              morphism.unop.hom (𝟙 _)) 0 sectionValue)) classValue =
          dualPairing traceForm _ (homObjHZeroAddEquiv _ _ sectionValue)
            (H.map morphism.unop.hom 1 classValue)
        rw [homObjHZeroAddEquiv_map, dualPairing_comp]
        rfl }
  have (coefficient : finitePresentation.FullSubcategoryᵒᵖ) :
      IsIso (comparison.app coefficient) := by
    letI : coefficient.unop.obj.IsFinitePresentation := coefficient.unop.property
    exact (ConcreteCategory.isIso_iff_bijective _).2
      ((bijective_dualPairingH_iff traceForm coefficient.unop.obj).2
        (bijective_dualPairing_of_isFinitePresentation baseField traceForm traceNonzero
          coefficient.unop.obj))
  have := NatIso.isIso_of_isIso_app comparison
  exact ⟨(asIso comparison).symm⟩

end AlgebraicGeometry.ProjectiveLine
