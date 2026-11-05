import Jacobian.AlgebraicGeometry.Picard.Pullback
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The relative Picard presheaf

The Picard presheaf of a morphism `X ⟶ S` assigns to a scheme `T` over `S`
the Picard classes on `X ×[S] T`. Restriction maps are pullbacks of module sheaves.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

/-- The map between base changes induced by a morphism over the base. -/
abbrev baseChangeMap (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) :
    pullback f T'.hom ⟶ pullback f T.hom :=
  pullback.lift (pullback.fst f T'.hom) (pullback.snd f T'.hom ≫ φ.left) (by
    rw [Category.assoc, Over.w, pullback.condition])

@[simp]
lemma baseChangeMap_id (f : X ⟶ S) (T : Over S) : baseChangeMap f (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [baseChangeMap]

@[simp]
lemma baseChangeMap_comp (f : X ⟶ S) {T T' T'' : Over S} (φ : T'' ⟶ T') (ψ : T' ⟶ T) :
    baseChangeMap f (φ ≫ ψ) = baseChangeMap f φ ≫ baseChangeMap f ψ := by
  apply pullback.hom_ext <;> simp [baseChangeMap, Category.assoc]

/-- Changing the parameter scheme gives a cartesian square of families. -/
lemma isPullback_baseChangeMap (f : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    IsPullback (baseChangeMap f g) (pullback.snd f T'.hom) (pullback.snd f T.hom)
      g.left := by
  refine IsPullback.of_right ?_ (by exact pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f T.hom)
  rw [Over.w g]
  rw [show baseChangeMap f g ≫ pullback.fst f T.hom = pullback.fst f T'.hom from
    pullback.lift_fst _ _ _]
  exact IsPullback.of_hasPullback f T'.hom

/-- Cartesian squares of parameter schemes remain cartesian after base change. -/
lemma isPullback_baseChangeMap_of_isPullback (f : X ⟶ S) {T₁ T₂ T₃ T₄ : Over S}
    {i : T₁ ⟶ T₂} {j : T₁ ⟶ T₃} {k : T₂ ⟶ T₄} {l : T₃ ⟶ T₄}
    (h : IsPullback i.left j.left k.left l.left) :
    IsPullback (baseChangeMap f i) (baseChangeMap f j) (baseChangeMap f k)
      (baseChangeMap f l) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_baseChangeMap f k).flip
  · rw [pullback.lift_snd, pullback.lift_snd]
    exact (isPullback_baseChangeMap f j).flip.paste_horiz h
  · rw [← baseChangeMap_comp, ← baseChangeMap_comp]
    congr 1
    exact Over.OverMorphism.ext h.w

/-- The relative Picard presheaf, before quotienting by fppf descent. -/
def picardPresheaf (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := (pullback f T.unop.hom).Pic
  map φ := TypeCat.ofHom (Pic.map (baseChangeMap f φ.unop))
  map_id T := by
    simp only [unop_id, baseChangeMap_id]
    exact congrArg TypeCat.ofHom (funext Pic.map_id)
  map_comp φ ψ := by
    simp only [unop_comp, baseChangeMap_comp]
    exact congrArg TypeCat.ofHom (funext fun L ↦ Pic.map_comp _ _ L)

end AlgebraicGeometry
