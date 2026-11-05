import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Jacobian.AlgebraicGeometry.Modules.AffineQuasicoherent
import Jacobian.AlgebraicGeometry.Modules.Localization

/-!
# Quasi-coherence of affine pushforward
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme targetObject : Scheme.{schemeUniverse}}

/-- **The pushforward along an affine morphism is quasi-coherent.** For `f : X ⟶ T` affine and
`ℱ` quasi-coherent, `f_* ℱ` is quasi-coherent: for an affine open `V` of `T` and `g ∈ Γ(T, V)`,
the preimage `f ⁻¹ᵁ V` is affine with `f ⁻¹ᵁ D(g) = D(f^♯ g)`, so `Γ(D(g), f_* ℱ)` is the
localization of `Γ(V, f_* ℱ) = Γ(f ⁻¹ᵁ V, ℱ)` at `g`
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_forall_isAffineOpen`).
 -/
theorem isQuasicoherent_pushforward_of_isAffineHom (morphism : scheme ⟶ targetObject) [IsAffineHom morphism] (coherentSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) coherentSheaf] :
    ((pushforward morphism).obj coherentSheaf).IsQuasicoherent := by
  refine isQuasicoherent_of_forall_isAffineOpen _ (fun largerOpen hW secondMorphism s ↦ ?_) (fun largerOpen hW secondMorphism tensorElement ht ↦ ?_)
  · obtain ⟨degree, tensorElement, ht⟩ := exists_map_eq_pow_smul_of_basicOpen_eq coherentSheaf (hW.preimage morphism) (morphism.app largerOpen secondMorphism)
      (morphism.preimage_basicOpen secondMorphism).symm (morphism.preimage_mono (targetObject.basicOpen_le secondMorphism)) s
    refine ⟨degree, tensorElement, ht.trans ?_⟩
    have compatibility : morphism.app (targetObject.basicOpen secondMorphism) (targetObject.presheaf.map (homOfLE (targetObject.basicOpen_le secondMorphism)).op secondMorphism) =
        scheme.presheaf.map (homOfLE (morphism.preimage_mono (targetObject.basicOpen_le secondMorphism))).op (morphism.app largerOpen secondMorphism) := by
      rw [← ConcreteCategory.comp_apply, morphism.naturality]
      rfl
    rw [← compatibility, ← map_pow]
    rfl
  · obtain ⟨degree, hn⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq coherentSheaf (hW.preimage morphism) (morphism.app largerOpen secondMorphism)
      (morphism.preimage_basicOpen secondMorphism).symm (morphism.preimage_mono (targetObject.basicOpen_le secondMorphism)) tensorElement ht
    rw [← map_pow] at hn
    exact ⟨degree, hn⟩

end AlgebraicGeometry.Scheme.Modules
