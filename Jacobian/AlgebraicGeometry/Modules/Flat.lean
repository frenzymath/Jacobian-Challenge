import Jacobian.AlgebraicGeometry.Modules.LocallyFreeAffine
import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.AlgebraicGeometry.Modules.PullbackSections
import Jacobian.RingTheory.Flat.Transport
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Relative flatness of module sheaves

A module sheaf is flat over a scheme morphism when its sections on affine opens
are flat over every affine open of the base containing their image. Finite
locally free sheaves satisfy this criterion over a flat morphism. Flatness over
the identity is preserved by restriction to an open subscheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- Affine sections are flat over affine opens of the base, with the scalar
action induced by the given scheme morphism. -/
def IsFlatOver (M : X.Modules) (f : X ⟶ T) : Prop :=
  ∀ (V : T.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
    letI : Module Γ(T, V.1) Γ(M, U.1) := Module.compHom _ (f.appLE V.1 U.1 hUV).hom
    Module.Flat Γ(T, V.1) Γ(M, U.1)

/-- Affine sections of a finite locally free sheaf are flat over their coordinate ring. -/
theorem flat_sections_of_isFiniteLocallyFree (M : X.Modules) [M.IsFiniteLocallyFree]
    {U : X.Opens} (hU : IsAffineOpen U) : Module.Flat Γ(X, U) Γ(M, U) := by
  have := (finitePresentation_projective_sections M hU).2
  infer_instance

/-- A finite locally free module sheaf is relatively flat over a flat morphism. -/
theorem isFlatOver_of_isFiniteLocallyFree (f : X ⟶ T) [Flat f]
    (M : X.Modules) [M.IsFiniteLocallyFree] : M.IsFlatOver f := by
  intro V U hUV
  letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have : Module.Flat Γ(T, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat f inferInstance V U hUV
  have := flat_sections_of_isFiniteLocallyFree M U.2
  letI : Module Γ(T, V.1) Γ(M, U.1) := Module.compHom _ (f.appLE V.1 U.1 hUV).hom
  have : IsScalarTower Γ(T, V.1) Γ(X, U.1) Γ(M, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(T, V.1) Γ(X, U.1) Γ(M, U.1)

/-- An invertible module sheaf is relatively flat over a flat morphism. -/
theorem isFlatOver_of_isInvertible (f : X ⟶ T) [Flat f]
    (M : X.Modules) [M.IsInvertible] : M.IsFlatOver f := by
  letI : M.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree M
  exact isFlatOver_of_isFiniteLocallyFree f M

/-- Flatness over the identity gives flat affine sections with their canonical scalar action. -/
theorem flat_sections_of_isFlatOver_identity (M : X.Modules)
    (hM : M.IsFlatOver (𝟙 X)) (U : X.affineOpens) :
    Module.Flat Γ(X, U.1) Γ(M, U.1) := by
  have h := hM U U (by simp)
  have hid : ((𝟙 X : X ⟶ X).appLE U.1 U.1 (by simp)).hom =
      RingHom.id Γ(X, U.1) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact congrArg CommRingCat.Hom.hom (X.presheaf.map_id (Opposite.op U.1))
  change @Module.Flat Γ(X, U.1) Γ(M, U.1) _ _
    (Module.compHom _ ((𝟙 X : X ⟶ X).appLE U.1 U.1 (by simp)).hom) at h
  rw [hid] at h
  exact h

/-- Restriction to an open subscheme preserves flatness over the identity. -/
theorem isFlatOver_identity_pullback_of_isOpenImmersion {Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (hM : M.IsFlatOver (𝟙 Y)) : ((Modules.pullback f).obj M).IsFlatOver (𝟙 X) := by
  have hrest (U : X.affineOpens) : Module.Flat Γ(X, U.1) Γ(M.restrict f, U.1) := by
    let A := Γ(X, U.1)
    let B := Γ(Y, f ''ᵁ U.1)
    letI : Algebra A B := (f.appIso U.1).inv.hom.toAlgebra
    have : Module.Flat A B :=
      RingHom.Flat.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (f.appIso U.1).inv).mp inferInstance)
    have : Module.Flat B Γ(M, f ''ᵁ U.1) :=
      flat_sections_of_isFlatOver_identity M hM
        ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
    letI : Module A Γ(M, f ''ᵁ U.1) := Module.compHom _ (f.appIso U.1).inv.hom
    have : IsScalarTower A B Γ(M, f ''ᵁ U.1) := ⟨fun a b m ↦ mul_smul _ _ _⟩
    exact Module.Flat.trans A B Γ(M, f ''ᵁ U.1)
  intro V U hUV
  letI := ((𝟙 X : X ⟶ X).appLE V.1 U.1 hUV).hom.toAlgebra
  have : Module.Flat Γ(X, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat (𝟙 X) inferInstance V U hUV
  have := hrest U
  have : Module.Flat Γ(X, U.1) Γ(((Modules.pullback f).obj M), U.1) :=
    Module.Flat.of_linearEquiv
      (appLinearEquivOfIso ((restrictFunctorIsoPullback f).app M) U.1).symm
  letI : Module Γ(X, V.1) Γ(((Modules.pullback f).obj M), U.1) :=
    Module.compHom _ ((𝟙 X : X ⟶ X).appLE V.1 U.1 hUV).hom
  have : IsScalarTower Γ(X, V.1) Γ(X, U.1) Γ(((Modules.pullback f).obj M), U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(X, V.1) Γ(X, U.1) Γ(((Modules.pullback f).obj M), U.1)

variable {X' T' : Scheme.{u}}

/-- Flatness over the base is invariant under isomorphisms of modules. -/
theorem IsFlatOver.of_iso {ℱ ℱ' : X.Modules} (e : ℱ ≅ ℱ') {f : X ⟶ T} (h : ℱ.IsFlatOver f) :
    ℱ'.IsFlatOver f := by
  intro V U hUV
  exact Module.Flat.of_bijective_compHom (f.appLE V.1 U.1 hUV).hom (f.appLE V.1 U.1 hUV).hom
    (RingHom.id _) Function.bijective_id (e.hom.app U.1).hom
    (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)) (fun _ _ ↦ Hom.app_smul _ _ _)
    (h V U hUV)

/-- Flatness over the base passes to the pullback along an open immersion into the source. -/
theorem IsFlatOver.pullback_of_isOpenImmersion {ℱ : X.Modules} {f : X ⟶ T} (h : ℱ.IsFlatOver f)
    (j : X' ⟶ X) [IsOpenImmersion j] : ((Modules.pullback j).obj ℱ).IsFlatOver (j ≫ f) := by
  rintro V ⟨U', hU'⟩ hUV
  obtain ⟨W, hW, hWr, hWV, rfl⟩ : ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ j.opensRange ∧
      W ≤ f ⁻¹ᵁ V.1 ∧ j ⁻¹ᵁ W = U' :=
    ⟨j ''ᵁ U', hU'.image_of_isOpenImmersion j, Set.image_subset_range _ _,
      fun _ ⟨_, hy, hx⟩ ↦ hx ▸ hUV hy, j.preimage_image_eq U'⟩
  refine Module.Flat.of_bijective_compHom (f.appLE V.1 W hWV).hom
    ((j ≫ f).appLE V.1 (j ⁻¹ᵁ W) hUV).hom (RingHom.id _) Function.bijective_id
    (pullbackUnitApp j ℱ W).hom (bijective_pullbackUnit_app_of_isOpenImmersion j ℱ hWr)
    (fun r m ↦ ?_) (h V ⟨W, hW⟩ hWV)
  rw [RingHom.id_apply, ← Scheme.Hom.appLE_comp_appLE j f V.1 W (j ⁻¹ᵁ W) hWV le_rfl,
    Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply]
  exact Hom.app_smul _ _ _

/-- Flatness over the base can be checked after composing with an open immersion of the base. -/
theorem IsFlatOver.of_comp_isOpenImmersion {ℱ : X.Modules} {f : X ⟶ T} (ι : T ⟶ T')
    [IsOpenImmersion ι] (h : ℱ.IsFlatOver (f ≫ ι)) : ℱ.IsFlatOver f := by
  intro V U hUV
  have hUV' : U.1 ≤ (f ≫ ι) ⁻¹ᵁ (ι ''ᵁ V.1) := by
    intro x hx
    exact ⟨f x, hUV hx, rfl⟩
  refine Module.Flat.of_bijective_compHom ((f ≫ ι).appLE _ U.1 hUV').hom
    (f.appLE V.1 U.1 hUV).hom (ι.appIso V.1).hom.hom
    (ConcreteCategory.bijective_of_isIso (ι.appIso V.1).hom) (AddMonoidHom.id _)
    Function.bijective_id (fun r m ↦ ?_) (h ⟨_, V.2.image_of_isOpenImmersion ι⟩ U hUV')
  rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, Scheme.Hom.appIso_hom',
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end AlgebraicGeometry.Scheme.Modules
