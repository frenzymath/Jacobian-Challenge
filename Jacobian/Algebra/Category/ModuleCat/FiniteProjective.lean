import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Finite projective modules as finite summands

A finite projective module is a direct summand of a finite free module.
The splitting is expressed as a finite sum of rank-one endomorphisms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory

/-- A finite projective module `moduleObject` is a direct summand of a free module of finite rank: there are
`ξⱼ : moduleObject ⟶ baseRing` and `mⱼ : baseRing ⟶ moduleObject` with `∑ⱼ ξⱼ ≫ mⱼ = 𝟙`. -/
lemma ModuleCat.exists_sum_comp_eq_id_of_projective {baseRing : Type u} [CommRing baseRing]
    (moduleObject : ModuleCat.{u} baseRing) [Module.Finite baseRing moduleObject]
    [Module.Projective baseRing moduleObject] :
    ∃ (rank : ℕ) (coordinates : Fin rank → (moduleObject ⟶ ModuleCat.of baseRing baseRing))
      (generators : Fin rank → (ModuleCat.of baseRing baseRing ⟶ moduleObject)),
      ∑ index, coordinates index ≫ generators index = 𝟙 moduleObject := by
  obtain ⟨rank, projection, inclusion, -, -, splitting⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective baseRing moduleObject
  refine ⟨rank, fun index ↦ ModuleCat.ofHom (LinearMap.proj index ∘ₗ inclusion),
    fun index ↦ ModuleCat.ofHom (projection ∘ₗ LinearMap.single baseRing (fun _ ↦ baseRing) index), ?_⟩
  ext element
  have reconstruct : ∑ index, LinearMap.single baseRing (fun _ ↦ baseRing) index
      (inclusion element index) = inclusion element := by
    ext coordinate
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  exact (map_sum projection _ _).symm.trans
    ((congrArg projection reconstruct).trans congr($splitting element))
