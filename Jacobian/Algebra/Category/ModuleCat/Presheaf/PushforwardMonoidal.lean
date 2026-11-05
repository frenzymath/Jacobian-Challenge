import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Jacobian.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# The pushforward of presheaves of modules is lax monoidal

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ CommRingCat` and `S : Cᵒᵖ ⥤ CommRingCat` presheaves
of commutative rings, and `φ : S ⋙ forget₂ _ _ ⟶ (F.op ⋙ R) ⋙ forget₂ _ _` a morphism of the
underlying presheaves of rings. We show that `PresheafOfModules.pushforward φ` is lax monoidal:
it is the composition of the (strong) monoidal functor
`PresheafOfModules.pushforward₀OfCommRingCat F R` with the lax monoidal functor
`PresheafOfModules.restrictScalars φ`.

## Main declarations

* `PresheafOfModules.pushforwardLaxMonoidal`: `pushforward φ` is lax monoidal;
* `PresheafOfModules.pushforward_ε_app`, `PresheafOfModules.pushforward_μ_app` and
  `PresheafOfModules.pushforward_μ_app_tmul` identify the structure maps objectwise.

## Implementation notes

The presheaf of rings `(F.op ⋙ R) ⋙ forget₂ _ _` appearing in the type of `φ` is only
definitionally equal to the presheaf `F.op ⋙ (R ⋙ forget₂ _ _)` that `pushforward`
expects, so the arguments `F`, `R` and `S` of `pushforward` have to be provided explicitly.
The type of `φ` is chosen so that it is the one obtained by whiskering a morphism
`S ⟶ F.op ⋙ R` of presheaves of commutative rings with `forget₂ CommRingCat RingCat`.

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)

/-- The pushforward of presheaves of modules along `φ` is lax monoidal, being the composition
of the (strong) monoidal functor `pushforward₀OfCommRingCat F R` with the lax monoidal functor
`restrictScalars φ`. -/
noncomputable instance pushforwardLaxMonoidal :
    (pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal :=
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙ restrictScalars φ).LaxMonoidal)

@[simp]
lemma pushforward_ε_app (X : Cᵒᵖ) :
    (ε (pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
        (S := S ⋙ forget₂ CommRingCat RingCat) φ)).app X =
      ε (ModuleCat.restrictScalars (φ.app X).hom) :=
  rfl

@[simp]
lemma pushforward_μ_app (M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (X : Cᵒᵖ) :
    (μ (pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
        (S := S ⋙ forget₂ CommRingCat RingCat) φ) M₁ M₂).app X =
      μ (ModuleCat.restrictScalars (φ.app X).hom)
        (M₁.obj (F.op.obj X)) (M₂.obj (F.op.obj X)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pushforward_μ_app_tmul (M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (X : Cᵒᵖ) (m₁ : M₁.obj (F.op.obj X)) (m₂ : M₂.obj (F.op.obj X)) :
    (μ (pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
        (S := S ⋙ forget₂ CommRingCat RingCat) φ) M₁ M₂).app X (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂ := by
  rw [pushforward_μ_app]
  erw [ModuleCat.restrictScalars_μ_tmul (R := S.obj X) (S := R.obj (F.op.obj X))]

end PresheafOfModules
