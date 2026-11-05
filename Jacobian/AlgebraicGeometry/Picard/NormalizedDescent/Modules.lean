import Jacobian.AlgebraicGeometry.Modules.Endomorphism
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import Jacobian.AlgebraicGeometry.Picard.NormalizedDescent.Basic
import Jacobian.AlgebraicGeometry.Modules.Invertible

/-!
# Rigidity and normalization of module transition maps

Scalar correction normalizes invertible module isomorphisms. Surjectivity on global functions makes normalized maps unique.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme

section NormalizationModules

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom}
  {T : Over S} {ι : Type*} {T' : ι → Over S} {g : ∀ i, T' i ⟶ T}
  {N : modulesPseudofunctor.obj (.mk (op T.left))}
  {L : ∀ i, modulesPseudofunctor.obj (.mk (op (pullback f (T' i).hom)))}
  {α : ∀ i, (modulesPseudofunctor.map (s (T' i)).op.toLoc).toFunctor.obj
    (L i) ≅ (modulesPseudofunctor.map (g i).left.op.toLoc).toFunctor.obj N}

/-- **Rigidity of normalized morphisms.** If `Γ(Y, 𝒪_Y) ⟶ Γ(X_Y, 𝒪_{X_Y})` is surjective, a
normalized morphism between pullbacks of invertible modules is determined by its normalization:
two normalized morphisms, one of them an isomorphism, are equal. -/
lemma IsSectionNormalized.eq {Y : Over S} (hs : s Y ≫ pullback.snd f Y.hom = 𝟙 _)
    (hY : Function.Surjective (pullback.snd f Y.hom).appTop) {i j : ι}
    [hL : (L i).IsInvertible]
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ ψ : (modulesPseudofunctor.map v₁.op.toLoc).toFunctor.obj (L i) ⟶
      (modulesPseudofunctor.map v₂.op.toLoc).toFunctor.obj (L j)} [IsIso ψ]
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ)
    (hψ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ ψ) :
    φ = ψ := by
  have : ((Modules.pullback v₁).obj (L i)).IsInvertible := inferInstance
  exact Modules.eq_of_pullback_map_eq (moduleSheaf := (Modules.pullback v₁).obj (L i))
    (pullback.snd f Y.hom) (s Y) hs hY φ ψ
    (hφ.map_eq hψ)

/-- Pulling back multiplication by a global function along `b` gives multiplication by its
pullback. -/
lemma pullHom_smulHom {Y Y' Z : Scheme.{u}} (M : modulesPseudofunctor.obj (.mk (op Z)))
    (f₁ : Y ⟶ Z) (b : Y' ⟶ Y) (bf : Y' ⟶ Z) (h : b ≫ f₁ = bf) (u : Γ(Y, ⊤)) :
    pullHom (F := modulesPseudofunctor)
      (Modules.smulHom ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj M) u) b bf bf h h =
      Modules.smulHom ((modulesPseudofunctor.map bf.op.toLoc).toFunctor.obj M) (b.appTop u) := by
  dsimp only [pullHom]
  erw [Modules.pullback_map_smulHom, ← Modules.smulHom_naturality_assoc]
  rw [Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  rfl

/-- **Normalizing an isomorphism.** Any isomorphism between pullbacks of invertible modules can be
rescaled by a unit to a normalized isomorphism. -/
lemma exists_isSectionNormalized {Y : Over S} (hs : s Y ≫ pullback.snd f Y.hom = 𝟙 _) {i j : ι}
    [hL : (L i).IsInvertible]
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    (h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)) (h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j))
    (hq₁ : t₁ ≫ (g i).left = q) (hq₂ : t₂ ≫ (g j).left = q)
    (e : (modulesPseudofunctor.map v₁.op.toLoc).toFunctor.obj (L i) ≅
      (modulesPseudofunctor.map v₂.op.toLoc).toFunctor.obj (L j)) :
    ∃ φ, IsIso φ ∧ IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ := by
  let Pi := pullHom (F := modulesPseudofunctor) (α i).hom t₁ (t₁ ≫ s (T' i)) q rfl hq₁
  let Pj := pullHom (F := modulesPseudofunctor) (α j).hom t₂ (t₂ ≫ s (T' j)) q rfl hq₂
  let E := pullHom (F := modulesPseudofunctor) e.hom (s Y) (t₁ ≫ s (T' i)) (t₂ ≫ s (T' j)) h₁ h₂
  have : IsIso Pi := isIso_pullHom _ _ _ _ _ _
  have : IsIso Pj := isIso_pullHom _ _ _ _ _ _
  have : IsIso E := isIso_pullHom _ _ _ _ _ _
  let A : Y.left.Modules :=
    (modulesPseudofunctor.map (t₁ ≫ s (T' i)).op.toLoc).toFunctor.obj (L i)
  have : A.IsInvertible := inferInstanceAs ((Modules.pullback _).obj (L i)).IsInvertible
  let δ : A ⟶ A := E ≫ Pj ≫ inv Pi
  have : IsIso δ := by dsimp only [δ]; infer_instance
  obtain ⟨c, hc⟩ := Modules.exists_eq_smulHom A (inv δ)
  obtain ⟨c', hc'⟩ := Modules.exists_eq_smulHom A δ
  have hcc : c * c' = 1 := by
    refine Modules.eq_of_smulHom_eq A ?_
    rw [Modules.smulHom_mul, Modules.smulHom_one, ← hc, ← hc', IsIso.hom_inv_id]
  have hcc' : c' * c = 1 := by rw [mul_comm, hcc]
  let B : (pullback f Y.hom).Modules :=
    (modulesPseudofunctor.map v₁.op.toLoc).toFunctor.obj (L i)
  let u := (pullback.snd f Y.hom).appTop c
  let u' := (pullback.snd f Y.hom).appTop c'
  have hsu : (s Y).appTop u = c := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hs]
    rfl
  have : IsIso (B.smulHom u) := ⟨B.smulHom u', by
    rw [← Modules.smulHom_mul, ← map_mul, hcc', map_one, Modules.smulHom_one], by
    rw [← Modules.smulHom_mul, ← map_mul, hcc, map_one, Modules.smulHom_one]⟩
  refine ⟨B.smulHom u ≫ e.hom, inferInstance, ?_⟩
  unfold IsSectionNormalized
  rw [pullHom_comp (F := modulesPseudofunctor) _ _ _ _ (t₁ ≫ s (T' i)) _ h₁ h₁ h₂,
    pullHom_smulHom, hsu, ← hc, Category.assoc]
  change inv δ ≫ E ≫ Pj = Pi
  simp [δ]

end NormalizationModules

end AlgebraicGeometry
