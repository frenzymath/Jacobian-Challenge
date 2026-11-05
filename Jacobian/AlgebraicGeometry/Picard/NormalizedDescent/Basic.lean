import Mathlib.AlgebraicGeometry.Pullbacks
import Jacobian.CategoryTheory.Sites.Descent.PullHom

/-!
# Section-normalized morphisms

Chosen section trivializations define normalized morphisms compatible with composition and pullback.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme

section Normalization

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} {X S : Scheme.{u}}
  {f : X ⟶ S} (s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom) {T : Over S}
  {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T) {N : F.obj (.mk (op T.left))}
  {L : ∀ i, F.obj (.mk (op (pullback f (T' i).hom)))}
  (α : ∀ i, (F.map (s (T' i)).op.toLoc).toFunctor.obj
    (L i) ≅ (F.map (g i).left.op.toLoc).toFunctor.obj N)

/-- A morphism `φ : v₁^* L i ⟶ v₂^* L j` over `X_Y` is *normalized* if its pullback along the
section `s Y` is compatible with the trivialisations `α i` and `α j`. -/
def IsSectionNormalized {Y : Over S} {i j : ι} {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    (h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)) (h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j))
    (hq₁ : t₁ ≫ (g i).left = q) (hq₂ : t₂ ≫ (g j).left = q)
    (φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶
      (F.map v₂.op.toLoc).toFunctor.obj (L j)) : Prop :=
  pullHom φ (s Y) (t₁ ≫ s (T' i)) (t₂ ≫ s (T' j)) h₁ h₂ ≫
    pullHom (α j).hom t₂ (t₂ ≫ s (T' j)) q rfl hq₂ =
  pullHom (α i).hom t₁ (t₁ ≫ s (T' i)) q rfl hq₁

variable {s g α}

/-- Normalized morphisms are stable under composition. -/
lemma IsSectionNormalized.comp {Y : Over S} {i j k : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom}
    {v₃ : pullback f Y.hom ⟶ pullback f (T' k).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {t₃ : Y.left ⟶ (T' k).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {h₃ : s Y ≫ v₃ = t₃ ≫ s (T' k)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q} {hq₃ : t₃ ≫ (g k).left = q}
    {φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶
      (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    {ψ : (F.map v₂.op.toLoc).toFunctor.obj (L j) ⟶
      (F.map v₃.op.toLoc).toFunctor.obj (L k)}
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ)
    (hψ : IsSectionNormalized s g α h₂ h₃ hq₂ hq₃ ψ) :
    IsSectionNormalized s g α h₁ h₃ hq₁ hq₃ (φ ≫ ψ) := by
  unfold IsSectionNormalized at hφ hψ ⊢
  rw [pullHom_comp  φ ψ _ _ (t₂ ≫ s (T' j)) _ h₁ h₂ h₃,
    Category.assoc, hψ, hφ]

/-- Identities are normalized. -/
lemma isSectionNormalized_id {Y : Over S} {i : ι} {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {t₁ : Y.left ⟶ (T' i).left} {q : Y.left ⟶ T.left} {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)}
    {hq₁ : t₁ ≫ (g i).left = q} :
    IsSectionNormalized s g α h₁ h₁ hq₁ hq₁
      (𝟙 ((F.map v₁.op.toLoc).toFunctor.obj (L i))) := by
  unfold IsSectionNormalized
  rw [pullHom_id_eq_id, Category.id_comp]

/-- Normalized morphisms are stable under pullback along a morphism `b : X_{Y'} ⟶ X_Y`
compatible with the sections, for instance `b = baseChangeMap f w`. -/
lemma IsSectionNormalized.pullHom {Y Y' : Over S} (w : Y' ⟶ Y) {i j : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ) (b : pullback f Y'.hom ⟶ pullback f Y.hom)
    (hb : s Y' ≫ b = w.left ≫ s Y) {v₁' : pullback f Y'.hom ⟶ pullback f (T' i).hom}
    {v₂' : pullback f Y'.hom ⟶ pullback f (T' j).hom} (hv₁ : b ≫ v₁ = v₁') (hv₂ : b ≫ v₂ = v₂')
    (h₁' : s Y' ≫ v₁' = (w.left ≫ t₁) ≫ s (T' i))
    (h₂' : s Y' ≫ v₂' = (w.left ≫ t₂) ≫ s (T' j))
    (hq₁' : (w.left ≫ t₁) ≫ (g i).left = w.left ≫ q)
    (hq₂' : (w.left ≫ t₂) ≫ (g j).left = w.left ≫ q) :
    IsSectionNormalized s g α h₁' h₂' hq₁' hq₂' (pullHom φ b v₁' v₂' hv₁ hv₂) := by
  unfold IsSectionNormalized at hφ ⊢
  rw [pullHom_pullHom, pullHom_congr_left φ hb,
    ← pullHom_pullHom φ (s Y) (t₁ ≫ s (T' i)) (t₂ ≫ s (T' j)) w.left _ _ h₁ h₂,
    ← pullHom_pullHom (α j).hom t₂ (t₂ ≫ s (T' j)) q w.left _ (w.left ≫ q) rfl hq₂,
    ← pullHom_comp, hφ, pullHom_pullHom]

/-- Being normalized only depends on the equality classes of the auxiliary morphisms `t₁`, `t₂`
and `q`. -/
lemma IsSectionNormalized.congr {Y : Over S} {i j : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ t₁' : Y.left ⟶ (T' i).left}
    {t₂ t₂' : Y.left ⟶ (T' j).left} {q q' : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {h₁' : s Y ≫ v₁ = t₁' ≫ s (T' i)} {h₂' : s Y ≫ v₂ = t₂' ≫ s (T' j)}
    {hq₁' : t₁' ≫ (g i).left = q'} {hq₂' : t₂' ≫ (g j).left = q'}
    {φ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    (ht₁ : t₁ = t₁') (ht₂ : t₂ = t₂') (hq : q = q')
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ) :
    IsSectionNormalized s g α h₁' h₂' hq₁' hq₂' φ := by
  subst ht₁ ht₂ hq
  exact hφ

/-- Two normalized morphisms have the same pullback along the section. -/
lemma IsSectionNormalized.map_eq {Y : Over S} {i j : ι}
    {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ ψ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)}
    (hφ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ)
    (hψ : IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ ψ) :
    (F.map (s Y).op.toLoc).toFunctor.map φ = (F.map (s Y).op.toLoc).toFunctor.map ψ := by
  unfold IsSectionNormalized at hφ hψ
  rw [← hψ, cancel_mono] at hφ
  rw [map_eq_pullHom φ (s Y) _ _ h₁ h₂, map_eq_pullHom ψ (s Y) _ _ h₁ h₂, hφ]

end Normalization

end AlgebraicGeometry
