import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing

/-!
# Maps prescribed on local free generators

A map out of a line module is determined by its values on local free generators.
The map glued from compatible generator images has the prescribed values.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} {U : ι → X.Opens} {e : ∀ i, Γ(M, U i)}

lemma isGlueValue_app (φ : M ⟶ N) {V : X.Opens} (m : Γ(M, V)) :
    IsGlueValue e (fun i ↦ φ.app (U i) (e i)) m (φ.app V m) := by
  intro i W hW hWi a ha
  rw [← Hom.app_presheaf_map, ← ha, Hom.app_smul, Hom.app_presheaf_map]

/-- Two morphisms out of a module with free generators `e i` over an open cover agree if they
agree on the generators. -/
lemma hom_ext_of_isFreeGenerator (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
    {φ ψ : M ⟶ N} (h : ∀ i, φ.app (U i) (e i) = ψ.app (U i) (e i)) : φ = ψ := by
  refine hom_ext _ _ fun V ↦ ?_
  ext m
  have hψ := isGlueValue_app (e := e) ψ m
  simp only [← h] at hψ
  exact (isGlueValue_app φ m).unique hU he hψ

lemma glueHom_app_self {f : ∀ i, Γ(N, U i)} (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
    (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
      a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) →
        a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j))
    (i : ι) : (glueHom hU he hc).app (U i) (e i) = f i := by
  have := isGlueValue_glueHom_app hU he hc (e i) i (U i) le_rfl le_rfl 1
    (by rw [one_smul])
  rwa [presheaf_map_id_apply, presheaf_map_id_apply, one_smul] at this

end AlgebraicGeometry.Scheme.Modules
