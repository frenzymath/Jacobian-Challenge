import Jacobian.AlgebraicGeometry.Cohomology.InjectiveFlasque
import Jacobian.AlgebraicGeometry.Cohomology.LongExact
import Jacobian.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Flasque modules and direct images

Flasqueness is preserved by restriction, pushforward and suitable cokernels. Flasque modules are acyclic for pushforward.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Flasque sheaves of modules

We say that an `𝒪_X`-module is flasque if its underlying abelian presheaf is
(`TopCat.Presheaf.IsFlasque`). Injective `𝒪_X`-modules are flasque, the direct image and the
restriction to an open subscheme of a flasque module are flasque, and in a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` flasque the sections of `M₂` surject onto those of `M₃`.
Dimension shifting then shows that flasque modules are acyclic for every left exact additive
functor which sends such short exact sequences to epimorphisms, in particular for every direct
image functor `f_*`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.epi_app_of_shortExact_of_isFlasque`: surjectivity on
  sections in a short exact sequence with flasque kernel.
- `AlgebraicGeometry.Scheme.Modules.rightAcyclic_of_isFlasque`: flasque modules are acyclic for
  a left exact functor which is epimorphic on such short exact sequences.
- `AlgebraicGeometry.Scheme.Modules.rightAcyclic_pushforward_of_isFlasque`: flasque modules are
  acyclic for the direct image functors.
-/

section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance : Functor.PreservesZeroMorphisms (C := X.Modules)
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` flasque, the
sections of `M₂` over any open surject onto those of `M₃`. -/
theorem epi_app_of_shortExact_of_isFlasque {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : TopCat.Presheaf.IsFlasque S.X₁.presheaf) (U : X.Opens) : Epi (S.g.app U) := by
  have hS' := shortExact_map_toSheaf hS
  have : TopCat.Sheaf.IsFlasque (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).X₁ := h₁
  exact TopCat.Sheaf.IsFlasque.epi_of_shortExact hS' (U := U)

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` and `M₂`
flasque, `M₃` is flasque. -/
theorem isFlasque_X₃_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : TopCat.Presheaf.IsFlasque S.X₁.presheaf) (h₂ : TopCat.Presheaf.IsFlasque S.X₂.presheaf) :
    TopCat.Presheaf.IsFlasque S.X₃.presheaf := by
  have hS' := shortExact_map_toSheaf hS
  have : TopCat.Sheaf.IsFlasque (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).X₁ := h₁
  have : TopCat.Sheaf.IsFlasque (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).X₂ := h₂
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS'

/-- A morphism of `𝒪_X`-modules which is surjective on the sections over every open is an
epimorphism. -/
theorem epi_of_epi_app {M N : X.Modules} (φ : M ⟶ N) (h : ∀ U, Epi (φ.app U)) : Epi φ := by
  have : ∀ U, Epi (((toPresheaf X).map φ).app U) := fun U ↦ h U.unop
  have : Epi ((toPresheaf X).map φ) := NatTrans.epi_of_epi_app _
  exact (toPresheaf X).epi_of_epi_map this

/-- The direct image of a flasque module is flasque. -/
theorem isFlasque_pushforward (f : X ⟶ Y) (M : X.Modules)
    (h : TopCat.Presheaf.IsFlasque M.presheaf) :
    TopCat.Presheaf.IsFlasque ((pushforward f).obj M).presheaf where
  epi {U V} i := by
    rw [show i = i.unop.op from rfl, pushforward_obj_presheaf_map]
    exact h.epi _

/-- The restriction of a flasque module to an open subscheme is flasque. -/
theorem isFlasque_restrict (g : Y ⟶ X) [IsOpenImmersion g] (M : X.Modules)
    (h : TopCat.Presheaf.IsFlasque M.presheaf) :
    TopCat.Presheaf.IsFlasque (M.restrict g).presheaf where
  epi {U V} i := by
    rw [show i = i.unop.op from rfl, restrict_map]
    exact h.epi _

variable [HasInjectiveResolutions X.Modules]

/-- **Flasque modules are acyclic** for every left exact additive functor `F` on `𝒪_X`-modules
which sends a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` flasque to an
epimorphism `F M₂ ⟶ F M₃`. -/
theorem rightAcyclic_of_isFlasque {D : Type*} [Category* D] [Abelian D] (F : X.Modules ⥤ D)
    [F.Additive] [PreservesFiniteLimits F]
    (hF : ∀ S : ShortComplex X.Modules, S.ShortExact →
      TopCat.Presheaf.IsFlasque S.X₁.presheaf → Epi (F.map S.g))
    (M : X.Modules) (hM : TopCat.Presheaf.IsFlasque M.presheaf) : F.rightAcyclic M :=
  F.rightAcyclic_of_epi_map_g (fun M ↦ TopCat.Presheaf.IsFlasque M.presheaf)
    (fun I _ ↦ isFlasque_of_injective I)
    (fun _ hS h₁ h₂ ↦ isFlasque_X₃_of_shortExact hS h₁ h₂) hF hM

/-- **Flasque modules are acyclic for direct images**: `R^q f_* M = 0` for `q > 0` if `M` is
flasque. -/
theorem rightAcyclic_pushforward_of_isFlasque (f : X ⟶ Y) (M : X.Modules)
    (hM : TopCat.Presheaf.IsFlasque M.presheaf) : (pushforward f).rightAcyclic M :=
  rightAcyclic_of_isFlasque _ (fun _ hS h₁ ↦ epi_of_epi_app _ fun V ↦
    epi_app_of_shortExact_of_isFlasque hS h₁ (f ⁻¹ᵁ V)) M hM

end AlgebraicGeometry.Scheme.Modules
