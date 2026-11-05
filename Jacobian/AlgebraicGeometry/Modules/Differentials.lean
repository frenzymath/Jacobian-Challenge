import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import Jacobian.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Jacobian.Algebra.Module.LocalizedModule.Derivation
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeRank
import Jacobian.AlgebraicGeometry.Modules.Invertible
import Jacobian.AlgebraicGeometry.Modules.BaseChange
import Jacobian.RingTheory.Smooth.Differentials
import Jacobian.AlgebraicGeometry.Differentials.Presheaf

/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf `Ω¹_{X/S}` of relative Kähler differentials is
the sheafification of the presheaf of `𝒪_X`-modules `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`. Here
`f⁻¹𝒪_S` is the presheaf inverse image `AlgebraicGeometry.Scheme.Hom.pullbackPresheaf`, not its
sheafification.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`: the sheaf `Ω¹_{X/S}`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsDerivation`: the derivation
  `d : 𝒪_X → Ω¹_{X/S}`, relative to `f⁻¹𝒪_S ⟶ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsHomEquiv`: the universal property of `d`:
  for a sheaf of `𝒪_X`-modules `M`, morphisms `Ω¹_{X/S} ⟶ M` are the same as
  `f⁻¹𝒪_S`-linear derivations `𝒪_X → M`.
- `AlgebraicGeometry.relativeDifferentialsSpecTildeHom`: for a ring map `φ : R ⟶ S`, the
  canonical morphism `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}`, adjoint to the map
  `relativeDifferentialsSpecΓHom : Ω_{S/R} → Γ(Spec S, Ω¹)` sending `D b` to `d b`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsRestrictIso`: for an open immersion
  `j : U ⟶ X`, the isomorphism `Ω¹_{X/S}|_U ≅ Ω¹_{U/S}`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsCompIso`: for an open immersion
  `i : V ⟶ S` and `g : X ⟶ V`, the isomorphism `Ω¹_{X/S} ≅ Ω¹_{X/V}`.
- `AlgebraicGeometry.tildeDerivation`: the derivation `𝒪_{Spec S} → M^~` induced by a
  derivation `S → M`, given on stalks by the quotient rule.
- `AlgebraicGeometry.relativeDifferentialsSpecIso`: the isomorphism
  `Ω¹_{Spec S / Spec R} ≅ Ω_{S/R}^~`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsRestrictFromSpecIso`: for affine opens
  `V = Spec B ⊆ X` and `U = Spec A ⊆ S` with `f(V) ⊆ U`, the isomorphism `Ω¹_{X/S}|_V ≅ Ω_{B/A}^~`.
- `AlgebraicGeometry.relativeDifferentialsSpecΓIso`: the isomorphism
  `Γ(Spec S, Ω¹_{Spec S / Spec R}) ≅ Ω_{S/R}` of `S`-modules, compatible with `d` and `D`.

For an `A`-algebra `B`, apply these to `φ = CommRingCat.ofHom (algebraMap A B)`; then
`CommRingCat.KaehlerDifferential φ` is `Ω[B⁄A]` for the algebra structure `φ.hom.toAlgebra`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials`: `Ω¹_{X/S} = 0` for an open
  immersion `f`; in particular `Ω¹_{X/X} = 0` (`isZero_relativeDifferentials_id`).
- `AlgebraicGeometry.Scheme.Hom.isInvertible_relativeDifferentials`: `Ω¹_{X/S}` is invertible
  for `f` smooth of relative dimension one.
- `AlgebraicGeometry.isIso_relativeDifferentialsSpecTildeHom`: the canonical morphism
  `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}` is an isomorphism. Its inverse comes from
  `tildeDerivation`; that the two composites are the identity uses that derivations into a sheaf
  on an affine scheme are determined by their global sections
  (`AlgebraicGeometry.Scheme.Modules.derivation_ext_of_isAffine`).

-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite TopologicalSpace PresheafOfModules
  PresheafOfModules.DifferentialsConstruction

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The sheaf of relative Kähler differentials `Ω¹_{X/S}` of a morphism of schemes `f : X ⟶ S`:
the sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`.

For a smooth curve `C` over a field `k`, `Ω¹_{C/k}` is the sheaf of Kähler differentials and
`ω_C = Ω¹_{C/k}` the canonical sheaf. On an affine open `Spec B ⊆ C` it is `Ω_{B/k}^~`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsRestrictFromSpecIso`).
-/
@[stacks 01UM]
noncomputable def relativeDifferentials : X.Modules :=
  (sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentials' f.pullbackPresheafToPresheaf)

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/S}`, relative to `f⁻¹𝒪_S ⟶ 𝒪_X`: the universal
derivation into the presheaf of differentials, composed with the sheafification unit. -/
noncomputable def relativeDifferentialsDerivation :
    f.relativeDifferentials.val.Derivation' f.pullbackPresheafToPresheaf :=
  (derivation' f.pullbackPresheafToPresheaf).postcomp
    ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _)

/-- The universal property of `d : 𝒪_X → Ω¹_{X/S}`: for a sheaf of `𝒪_X`-modules `M`,
composing with `d` identifies morphisms `Ω¹_{X/S} ⟶ M` with `f⁻¹𝒪_S`-linear derivations
`𝒪_X → M`. -/
noncomputable def relativeDifferentialsHomEquiv (M : X.Modules) :
    (f.relativeDifferentials ⟶ M) ≃ M.val.Derivation' f.pullbackPresheafToPresheaf where
  toFun g := f.relativeDifferentialsDerivation.postcomp g.val
  invFun D := ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    ((isUniversal' f.pullbackPresheafToPresheaf).desc D)
  left_inv g := by
    apply ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply (isUniversal' f.pullbackPresheafToPresheaf).postcomp_injective
    rw [Derivation.Universal.fac]
    rfl
  right_inv D := by
    change (derivation' f.pullbackPresheafToPresheaf).postcomp
      (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _)
        (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm _)) = D
    rw [Equiv.apply_symm_apply, Derivation.Universal.fac]

@[simp]
lemma relativeDifferentialsHomEquiv_apply {M : X.Modules} (g : f.relativeDifferentials ⟶ M) :
    f.relativeDifferentialsHomEquiv M g = f.relativeDifferentialsDerivation.postcomp g.val :=
  rfl

/-- If `f⁻¹𝒪_S ⟶ 𝒪_X` is surjective on sections, then `Ω¹_{X/S} = 0`. -/
lemma isZero_relativeDifferentials_of_surjective
    (h : ∀ U, Function.Surjective (f.pullbackPresheafToPresheaf.app U)) :
    IsZero f.relativeDifferentials := by
  rw [IsZero.iff_id_eq_zero]
  apply (f.relativeDifferentialsHomEquiv _).injective
  ext U x
  obtain ⟨a, rfl⟩ := h U x
  simp only [relativeDifferentialsHomEquiv_apply, Derivation.postcomp_d_apply]
  erw [Derivation'.d_app]
  simp

/-- The sheaf of relative differentials of an open immersion vanishes. -/
lemma isZero_relativeDifferentials [IsOpenImmersion f] : IsZero f.relativeDifferentials := by
  refine f.isZero_relativeDifferentials_of_surjective fun U y ↦ ?_
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.appIso U.unop).hom).2 y
  rw [appIso_hom', appLE_eq_pullbackPresheafToPresheaf_app]
  exact ⟨_, rfl⟩

variable (X) in
/-- The sheaf of relative differentials of the identity morphism vanishes: `Ω¹_{X/X} = 0`. -/
lemma isZero_relativeDifferentials_id : IsZero (𝟙 X : X ⟶ X).relativeDifferentials :=
  isZero_relativeDifferentials _

/-- Every section of `f⁻¹𝒪_S` over `W` comes, in `𝒪_X(W)`, from a section of `𝒪_S` over some
open `V` with `W ⊆ f⁻¹ V`: the colimit defining `f⁻¹𝒪_S` is filtered. -/
lemma exists_appLE_eq_pullbackPresheafToPresheaf_app (W : X.Opens)
    (x : f.pullbackPresheaf.obj (op W)) :
    ∃ (V : S.Opens) (e : W ≤ f ⁻¹ᵁ V) (a : Γ(S, V)),
      f.pullbackPresheafToPresheaf.app (op W) x = f.appLE V W e a := by
  have : IsFiltered (CostructuredArrow (Opens.map f.base).op (op W)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _)
  obtain ⟨g, a, rfl⟩ := Concrete.isColimit_exists_rep _
    ((Opens.map f.base).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit S.presheaf (op W)) x
  refine ⟨g.left.unop, leOfHom g.hom.unop, a, ?_⟩
  rw [appLE_eq_pullbackPresheafToPresheaf_app]
  have : ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
      S.presheaf).app g.left ≫ f.pullbackPresheaf.map (homOfLE (leOfHom g.hom.unop)).op =
      ((Functor.LeftExtension.mk _ ((Opens.map f.base).op.leftKanExtensionUnit
        S.presheaf)).coconeAt (op W)).ι.app g := by
    rw [TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    rfl
  rw [← Category.assoc, this]
  rfl

lemma app_eq_pullbackPresheafToPresheaf_app (V : S.Opens) (a : Γ(S, V)) :
    ∃ x, f.pullbackPresheafToPresheaf.app (op (f ⁻¹ᵁ V)) x = f.app V a := by
  rw [app_eq_appLE, appLE_eq_pullbackPresheafToPresheaf_app]
  exact ⟨_, rfl⟩

variable {f} in
/-- A derivation relative to `f⁻¹𝒪_S ⟶ 𝒪_X` vanishes on the image of `f.app`. -/
lemma _root_.PresheafOfModules.Derivation'.d_app_app
    {M : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ _ _)}
    (D : M.Derivation' f.pullbackPresheafToPresheaf) (V : S.Opens) (a : Γ(S, V)) :
    D.d (X := op (f ⁻¹ᵁ V)) (f.app V a) = 0 := by
  obtain ⟨x, hx⟩ := f.app_eq_pullbackPresheafToPresheaf_app V a
  rw [← hx]
  exact D.d_app x

/-- Constructor for derivations relative to `f⁻¹𝒪_S ⟶ 𝒪_X`: a family of derivations compatible
with restrictions is relative to `f⁻¹𝒪_S` as soon as it vanishes on the image of `f.app`. -/
noncomputable def derivationMk {M : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ _ _)}
    (d : ∀ {U : X.Opensᵒᵖ}, X.presheaf.obj U →+ M.obj U)
    (d_mul : ∀ {U : X.Opensᵒᵖ} (a b : X.presheaf.obj U), d (a * b) = a • d b + b • d a)
    (d_map : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : X.presheaf.obj U),
      d (X.presheaf.map i x) = M.map i (d x))
    (d_app : ∀ (V : S.Opens) (a : Γ(S, V)), d (U := op (f ⁻¹ᵁ V)) (f.app V a) = 0) :
    M.Derivation' f.pullbackPresheafToPresheaf where
  d := d
  d_mul := d_mul
  d_map := d_map
  d_app {W} x := by
    obtain ⟨V, e, a, hx⟩ := f.exists_appLE_eq_pullbackPresheafToPresheaf_app W.unop x
    change d (f.pullbackPresheafToPresheaf.app (op W.unop) x) = 0
    rw [hx]
    change d (X.presheaf.map (homOfLE e).op (f.app V a)) = 0
    rw [d_map, d_app]
    exact map_zero _


/-- On sections, `(relativeDifferentialsHomEquiv M).symm D` sends `d x` to `D x`. -/
lemma relativeDifferentialsHomEquiv_symm_app_d {M : X.Modules}
    (D : M.val.Derivation' f.pullbackPresheafToPresheaf) {U : X.Opensᵒᵖ} (x : X.presheaf.obj U) :
    ((f.relativeDifferentialsHomEquiv M).symm D).val.app U
      (f.relativeDifferentialsDerivation.d x) = D.d x :=
  congr($((f.relativeDifferentialsHomEquiv M).apply_symm_apply D).d x)

/-- Equal morphisms have isomorphic sheaves of relative differentials. -/
noncomputable def relativeDifferentialsCongr {g : X ⟶ S} (h : f = g) :
    f.relativeDifferentials ≅ g.relativeDifferentials :=
  eqToIso (by rw [h])

/-- Two morphisms `f₁ : X ⟶ S₁` and `f₂ : X ⟶ S₂` with the same derivations have isomorphic
sheaves of relative differentials. -/
noncomputable def relativeDifferentialsIsoOfDerivation {S₁ S₂ : Scheme.{u}} (f₁ : X ⟶ S₁)
    (f₂ : X ⟶ S₂)
    (h₁ : ∀ (M : X.Modules) (D : M.val.Derivation' f₁.pullbackPresheafToPresheaf) (V : S₂.Opens)
      (a : Γ(S₂, V)), D.d (X := op (f₂ ⁻¹ᵁ V)) (f₂.app V a) = 0)
    (h₂ : ∀ (M : X.Modules) (D : M.val.Derivation' f₂.pullbackPresheafToPresheaf) (V : S₁.Opens)
      (a : Γ(S₁, V)), D.d (X := op (f₁ ⁻¹ᵁ V)) (f₁.app V a) = 0) :
    f₁.relativeDifferentials ≅ f₂.relativeDifferentials where
  hom := (f₁.relativeDifferentialsHomEquiv _).symm
    (f₁.derivationMk f₂.relativeDifferentialsDerivation.d
      f₂.relativeDifferentialsDerivation.d_mul f₂.relativeDifferentialsDerivation.d_map
      (h₂ _ f₂.relativeDifferentialsDerivation))
  inv := (f₂.relativeDifferentialsHomEquiv _).symm
    (f₂.derivationMk f₁.relativeDifferentialsDerivation.d
      f₁.relativeDifferentialsDerivation.d_mul f₁.relativeDifferentialsDerivation.d_map
      (h₁ _ f₁.relativeDifferentialsDerivation))
  hom_inv_id := by
    apply (f₁.relativeDifferentialsHomEquiv _).injective
    ext U x
    simp only [relativeDifferentialsHomEquiv_apply]
    erw [Derivation.postcomp_d_apply, Derivation.postcomp_d_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
      relativeDifferentialsHomEquiv_symm_app_d]
    exact (f₂.relativeDifferentialsHomEquiv_symm_app_d _ _).trans rfl
  inv_hom_id := by
    apply (f₂.relativeDifferentialsHomEquiv _).injective
    ext U x
    simp only [relativeDifferentialsHomEquiv_apply]
    erw [Derivation.postcomp_d_apply, Derivation.postcomp_d_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
      relativeDifferentialsHomEquiv_symm_app_d]
    exact (f₁.relativeDifferentialsHomEquiv_symm_app_d _ _).trans rfl


/-- For an open immersion `i : V ⟶ S` and `g : X ⟶ V`, the sheaves of relative differentials
`Ω¹_{X/S}` (for `g ≫ i`) and `Ω¹_{X/V}` (for `g`) are isomorphic. -/
noncomputable def relativeDifferentialsCompIso {V : Scheme.{u}} (g : X ⟶ V) (i : V ⟶ S)
    [IsOpenImmersion i] : (g ≫ i).relativeDifferentials ≅ g.relativeDifferentials :=
  relativeDifferentialsIsoOfDerivation _ _
    (fun M D W b ↦ by
      obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.appIso W).hom).2 b
      have h : (i.appIso W).hom ≫ g.app W = (g ≫ i).app (i ''ᵁ W) ≫
          X.presheaf.map (homOfLE (show g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (i ⁻¹ᵁ (i ''ᵁ W)) by
            rw [i.preimage_image_eq])).op := by
        rw [appIso_hom, Category.assoc, g.naturality, ← Category.assoc, ← comp_app]
        rfl
      rw [← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]
      erw [D.d_map, D.d_app_app]
      exact map_zero _)
    (fun M D W a ↦ by
      change D.d (g.app _ (i.app W a)) = 0
      exact D.d_app_app _ _)


section Restrict

variable {U : Scheme.{u}} (j : U ⟶ X)

/-- The derivation `𝒪_X → j_* Ω¹_{U/S}`, `s ↦ d (j^♯ s)`. -/
noncomputable def pushforwardDerivation :
    ((Modules.pushforward j).obj (j ≫ f).relativeDifferentials).val.Derivation'
      f.pullbackPresheafToPresheaf :=
  f.derivationMk
    (fun {W} ↦ ((j ≫ f).relativeDifferentialsDerivation.d (X := op (j ⁻¹ᵁ W.unop))).comp
      (j.app W.unop).hom.toAddMonoidHom)
    (fun {W} a b ↦
      (congrArg (j ≫ f).relativeDifferentialsDerivation.d (map_mul (j.app W.unop).hom a b)).trans
        ((j ≫ f).relativeDifferentialsDerivation.d_mul _ _))
    (fun {W₁ W₂} i x ↦ by
      change (j ≫ f).relativeDifferentialsDerivation.d (j.app W₂.unop (X.presheaf.map i x)) =
        (j ≫ f).relativeDifferentials.val.map ((Opens.map j.base).map i.unop).op
          ((j ≫ f).relativeDifferentialsDerivation.d (j.app W₁.unop x))
      rw [← ConcreteCategory.comp_apply, j.naturality, ConcreteCategory.comp_apply]
      exact (j ≫ f).relativeDifferentialsDerivation.d_map _ _)
    (fun V a ↦ (j ≫ f).relativeDifferentialsDerivation.d_app_app V a)

lemma pushforwardDerivation_desc_app_d (W : X.Opens) (s : Γ(X, W)) :
    ((f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation j)).val.app (op W)
      (f.relativeDifferentialsDerivation.d s) =
      (j ≫ f).relativeDifferentialsDerivation.d (X := op (j ⁻¹ᵁ W)) (j.app W s) :=
  (relativeDifferentialsHomEquiv_symm_app_d _ _ _).trans rfl

variable [IsOpenImmersion j]

/-- The derivation `𝒪_U → Ω¹_{X/S}|_U`, `t ↦ d (t)` viewed as a section over `j(W)`. -/
noncomputable def restrictDerivation :
    (f.relativeDifferentials.restrict j).val.Derivation' (j ≫ f).pullbackPresheafToPresheaf :=
  (j ≫ f).derivationMk
    (fun {W} ↦ (f.relativeDifferentialsDerivation.d (X := op (j ''ᵁ W.unop))).comp
      (j.appIso W.unop).inv.hom.toAddMonoidHom)
    (fun {W} a b ↦ by
      exact (congrArg f.relativeDifferentialsDerivation.d
        (map_mul (j.appIso W.unop).inv.hom a b)).trans
          (f.relativeDifferentialsDerivation.d_mul _ _))
    (fun {W₁ W₂} i x ↦ by
      change f.relativeDifferentialsDerivation.d ((j.appIso W₂.unop).inv (U.presheaf.map i x)) =
        f.relativeDifferentials.val.map (j.opensFunctor.op.map i)
          (f.relativeDifferentialsDerivation.d ((j.appIso W₁.unop).inv x))
      rw [← ConcreteCategory.comp_apply, appIso_inv_naturality, ConcreteCategory.comp_apply]
      exact f.relativeDifferentialsDerivation.d_map _ _)
    (fun V a ↦ by
      change f.relativeDifferentialsDerivation.d
        ((j.appIso (j ⁻¹ᵁ (f ⁻¹ᵁ V))).inv (j.app (f ⁻¹ᵁ V) (f.app V a))) = 0
      rw [← ConcreteCategory.comp_apply (j.app _), app_appIso_inv]
      erw [f.relativeDifferentialsDerivation.d_map, f.relativeDifferentialsDerivation.d_app_app]
      exact map_zero _)

/-- The morphism `Ω¹_{X/S}|_U ⟶ Ω¹_{U/S}`. -/
noncomputable def restrictToRelativeDifferentials :
    f.relativeDifferentials.restrict j ⟶ (j ≫ f).relativeDifferentials :=
  ((Modules.restrictAdjunction j).homEquiv _ _).symm
    ((f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation j))

/-- The morphism `Ω¹_{U/S} ⟶ Ω¹_{X/S}|_U`. -/
noncomputable def relativeDifferentialsToRestrict :
    (j ≫ f).relativeDifferentials ⟶ f.relativeDifferentials.restrict j :=
  ((j ≫ f).relativeDifferentialsHomEquiv _).symm (f.restrictDerivation j)

lemma relativeDifferentialsToRestrict_app_d {W : U.Opensᵒᵖ} (t : U.presheaf.obj W) :
    (f.relativeDifferentialsToRestrict j).val.app W ((j ≫ f).relativeDifferentialsDerivation.d t) =
      f.relativeDifferentialsDerivation.d ((j.appIso W.unop).inv t) :=
  relativeDifferentialsHomEquiv_symm_app_d _ _ _

lemma restrictToRelativeDifferentials_app (W : U.Opens) (m : Γ(f.relativeDifferentials, j ''ᵁ W)) :
    (f.restrictToRelativeDifferentials j).app W m =
      (j ≫ f).relativeDifferentials.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op
      (((f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation j)).app (j ''ᵁ W) m) := by
  rw [restrictToRelativeDifferentials, Adjunction.homEquiv_counit]
  rfl

lemma restrictToRelativeDifferentials_app_d (W : U.Opens) (s : Γ(X, j ''ᵁ W)) :
    (f.restrictToRelativeDifferentials j).val.app (op W) (f.relativeDifferentialsDerivation.d s) =
      (j ≫ f).relativeDifferentials.val.map (eqToHom (j.preimage_image_eq W).symm).op
        ((j ≫ f).relativeDifferentialsDerivation.d (X := op (j ⁻¹ᵁ (j ''ᵁ W)))
          (j.app (j ''ᵁ W) s)) := by
  refine (f.restrictToRelativeDifferentials_app j W _).trans ?_
  exact congrArg _ (f.pushforwardDerivation_desc_app_d j _ s)

lemma relativeDifferentialsToRestrict_restrictToRelativeDifferentials :
    f.relativeDifferentialsToRestrict j ≫ f.restrictToRelativeDifferentials j = 𝟙 _ := by
  apply ((j ≫ f).relativeDifferentialsHomEquiv _).injective
  ext W t
  change (f.restrictToRelativeDifferentials j).val.app W
    ((f.relativeDifferentialsToRestrict j).val.app W
      ((j ≫ f).relativeDifferentialsDerivation.d t)) = (j ≫ f).relativeDifferentialsDerivation.d t
  refine (congrArg (fun m ↦ (f.restrictToRelativeDifferentials j).val.app W m)
    (f.relativeDifferentialsToRestrict_app_d j t)).trans ?_
  refine (f.restrictToRelativeDifferentials_app_d j W.unop _).trans ?_
  refine ((j ≫ f).relativeDifferentialsDerivation.d_map _ _).symm.trans ?_
  refine congrArg _ ?_
  exact ConcreteCategory.congr_hom (j.appIso_inv_app_presheafMap W.unop) t

lemma restrictToRelativeDifferentials_relativeDifferentialsToRestrict :
    f.restrictToRelativeDifferentials j ≫ f.relativeDifferentialsToRestrict j = 𝟙 _ := by
  apply ((Modules.restrictAdjunction j).homEquiv _ _).injective
  apply (f.relativeDifferentialsHomEquiv _).injective
  rw [Adjunction.homEquiv_naturality_right, restrictToRelativeDifferentials,
    Equiv.apply_symm_apply, Adjunction.homEquiv_id]
  ext W s
  change (f.relativeDifferentialsToRestrict j).val.app (op (j ⁻¹ᵁ W.unop))
    (((f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation j)).val.app W
      (f.relativeDifferentialsDerivation.d s)) =
    ((Modules.restrictAdjunction j).unit.app f.relativeDifferentials).val.app W
      (f.relativeDifferentialsDerivation.d s)
  refine (congrArg _ (f.pushforwardDerivation_desc_app_d j W.unop s)).trans ?_
  refine (f.relativeDifferentialsToRestrict_app_d j _).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom (j.app_appIso_inv W.unop) s)).trans ?_
  exact f.relativeDifferentialsDerivation.d_map _ _

/-- For an open immersion `j : U ⟶ X`, the restriction of `Ω¹_{X/S}` to `U` is `Ω¹_{U/S}`. -/
noncomputable def relativeDifferentialsRestrictIso :
    f.relativeDifferentials.restrict j ≅ (j ≫ f).relativeDifferentials where
  hom := f.restrictToRelativeDifferentials j
  inv := f.relativeDifferentialsToRestrict j
  hom_inv_id := f.restrictToRelativeDifferentials_relativeDifferentialsToRestrict j
  inv_hom_id := f.relativeDifferentialsToRestrict_restrictToRelativeDifferentials j

end Restrict

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

section Affine

/-- On an affine scheme, a derivation of `𝒪_X` with values in a sheaf of modules is determined
by its values on global sections. -/
lemma Scheme.Modules.derivation_ext_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {R' : X.Opensᵒᵖ ⥤ CommRingCat.{u}} {φ : R' ⟶ X.presheaf} {N : X.Modules}
    {D₁ D₂ : N.val.Derivation' φ} (h : ∀ a : Γ(X, ⊤), D₁.d (X := op ⊤) a = D₂.d a) :
    D₁ = D₂ := by
  ext W s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {r : Γ(X, ⊤) // X.basicOpen r ≤ W.unop} ↦ X.basicOpen i.1) W.unop
    (fun i ↦ homOfLE i.2) ?_ _ _ fun i ↦ ?_
  · intro x hx
    obtain ⟨_, ⟨r, rfl⟩, hxr, hrW⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X)) hx
    exact Opens.mem_iSup.2 ⟨⟨r, hrW⟩, hxr⟩
  · obtain ⟨r, hr⟩ := i
    refine (D₁.d_map (homOfLE hr).op s).symm.trans (Eq.trans ?_ (D₂.d_map (homOfLE hr).op s))
    suffices ∀ y : Γ(X, X.basicOpen r), D₁.d y = D₂.d y from this _
    intro y
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers r) y
    have key (b : Γ(X, ⊤)) : D₁.d (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) b) =
        D₂.d (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) b) :=
      (D₁.d_map (homOfLE (X.basicOpen_le r)).op b).trans
        ((congrArg _ (h b)).trans (D₂.d_map (homOfLE (X.basicOpen_le r)).op b).symm)
    have hu : IsUnit (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) (r ^ n)) :=
      IsLocalization.map_units _ (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
    set u := algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) (r ^ n)
    have e₁ := D₁.d_mul y u
    have e₂ := D₂.d_mul y u
    erw [hy] at e₁ e₂
    rw [← key, e₁, key] at e₂
    have hu' : IsUnit (M := X.ringCatSheaf.obj.obj (op (X.basicOpen r))) u := hu
    exact (hu'.smul_left_cancel).1 (add_left_cancel e₂)

section TildeDerivation

variable {R S : CommRingCat.{u}} {φ : R ⟶ S} {M : ModuleCat.{u} S} (D : M.Derivation φ)

/-- The derivation of the localization `S_𝔭 → M_𝔭` induced by `D`. -/
noncomputable def derivationStalk (x : PrimeSpectrum S) :
    StructureSheaf.Localizations S x → StructureSheaf.Localizations M x :=
  LocalizedModule.derivationLift x.asIdeal.primeCompl (AddMonoidHom.mk' D.d D.d_add) D.d_mul

lemma derivationStalk_add (x : PrimeSpectrum S) (a b : StructureSheaf.Localizations S x) :
    derivationStalk D x (a + b) = derivationStalk D x a + derivationStalk D x b :=
  LocalizedModule.derivationLift_add _ (AddMonoidHom.mk' D.d D.d_add) D.d_mul a b

lemma derivationStalk_mul (x : PrimeSpectrum S) (a b : StructureSheaf.Localizations S x) :
    derivationStalk D x (a * b) = a • derivationStalk D x b + b • derivationStalk D x a :=
  LocalizedModule.derivationLift_mul _ (AddMonoidHom.mk' D.d D.d_add) D.d_mul a b

lemma derivationStalk_localRingHom (x : PrimeSpectrum S)
    (z : Localization.AtPrime (PrimeSpectrum.comap φ.hom x).asIdeal) :
    derivationStalk D x (Localization.localRingHom _ x.asIdeal φ.hom rfl z) = 0 := by
  induction z using Localization.induction_on with | H p
  obtain ⟨r, u⟩ := p
  unfold derivationStalk
  erw [Localization.localRingHom_mk]
  change LocalizedModule.derivationLift _ _ _ (LocalizedModule.mk _ _) = 0
  refine (LocalizedModule.derivationLift_mk _ _ _ _ _).trans ?_
  simp [D.d_map]

lemma isLocallyFraction_derivationStalk (W : (Spec S).Opens) (s : Γ(Spec S, W)) :
    (StructureSheaf.isLocallyFraction S M).pred (fun x : W ↦ derivationStalk D x.1 (s.1 x)) := by
  intro x
  obtain ⟨V, m, i, a, h, w⟩ := s.2 x
  refine ⟨V, m, i, h • D.d a - a • D.d h, h * h, fun y ↦ ?_⟩
  obtain ⟨hy, e⟩ := w y
  refine ⟨fun hh ↦ (y.1.isPrime.mem_or_mem hh).elim hy hy, ?_⟩
  simp only [e, derivationStalk]
  rfl


/-- The derivation `𝒪_{Spec S} → M^~` induced by `D`, on sections over `W`. -/
noncomputable def tildeDerivationApp (W : (Spec S).Opens) :
    Γ(Spec S, W) →+ (tilde M).val.obj (op W) :=
  AddMonoidHom.mk' (fun s ↦ ⟨fun x ↦ derivationStalk D x.1 (s.1 x),
    isLocallyFraction_derivationStalk D W s⟩) (fun s t ↦ Subtype.ext (funext fun x ↦
      derivationStalk_add D x.1 (s.1 x) (t.1 x)))

/-- The derivation `𝒪_{Spec S} → M^~` induced by an `R`-derivation `D : S → M`, relative to
`Spec S ⟶ Spec R`. -/
noncomputable def tildeDerivation :
    (tilde M).val.Derivation' (Spec.map φ).pullbackPresheafToPresheaf :=
  (Spec.map φ).derivationMk (fun {W} ↦ tildeDerivationApp D W.unop)
    (fun {W} a b ↦ Subtype.ext (funext fun x ↦ derivationStalk_mul D x.1 (a.1 x) (b.1 x)))
    (fun {W₁ W₂} i s ↦ Subtype.ext (funext fun x ↦ rfl))
    (fun V a ↦ by
      refine Subtype.ext (funext fun x ↦ ?_)
      change derivationStalk D x.1 ((StructureSheaf.comap φ.hom V _ le_rfl a).1 x) = 0
      erw [StructureSheaf.comap_apply]
      exact derivationStalk_localRingHom D x.1 _)


lemma tildeDerivation_d_top (b : S) :
    (tildeDerivation D).d (X := op ⊤) ((Scheme.ΓSpecIso S).inv b) =
      tilde.toOpen M ⊤ (D.d b) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change derivationStalk D x.1 (LocalizedModule.mk b 1) = LocalizedModule.mk (D.d b) 1
  exact (LocalizedModule.derivationLift_mk_one _ _ _ _)


end TildeDerivation

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- For a ring map `φ : R ⟶ S`, the global sections of `d : 𝒪 → Ω¹_{Spec S / Spec R}` form an
`R`-derivation `S → Γ(Spec S, Ω¹_{Spec S / Spec R})`. -/
noncomputable def relativeDifferentialsSpecΓDerivation :
    ((moduleSpecΓFunctor (R := S)).obj (Spec.map φ).relativeDifferentials).Derivation φ :=
  ModuleCat.Derivation.mk
    (fun b ↦ (Spec.map φ).relativeDifferentialsDerivation.d (X := .op ⊤)
      ((Scheme.ΓSpecIso S).inv b))
    (fun b b' ↦ by simp)
    (fun b b' ↦ by
      rw [map_mul]
      exact (Spec.map φ).relativeDifferentialsDerivation.d_mul _ _)
    (fun a ↦ by
      rw [← Scheme.specMap_appTop_ΓSpecIso_inv, ← Scheme.Hom.appLE_top_top_eq_appTop _ le_top,
        Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app]
      exact PresheafOfModules.Derivation'.d_app _ _)

/-- For a ring map `φ : R ⟶ S`, the `S`-linear map `Ω_{S/R} → Γ(Spec S, Ω¹_{Spec S / Spec R})`
sending `D b` to `d b`, given by the universal property of Kähler differentials. -/
noncomputable def relativeDifferentialsSpecΓHom :
    CommRingCat.KaehlerDifferential φ ⟶
      (moduleSpecΓFunctor (R := S)).obj (Spec.map φ).relativeDifferentials :=
  (relativeDifferentialsSpecΓDerivation φ).desc

/-- The map `Ω_{S/R} → Γ(Spec S, Ω¹_{Spec S / Spec R})` sends `D b` to `d b`. -/
@[simp]
lemma relativeDifferentialsSpecΓHom_d (b : S) :
    relativeDifferentialsSpecΓHom φ (CommRingCat.KaehlerDifferential.d b) =
      (Spec.map φ).relativeDifferentialsDerivation.d (X := .op ⊤) ((Scheme.ΓSpecIso S).inv b) :=
  (relativeDifferentialsSpecΓDerivation φ).desc_d b

/-- For a ring map `φ : R ⟶ S`, the canonical morphism `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}`,
adjoint to `relativeDifferentialsSpecΓHom` under `tilde ⊣ Γ`. -/
noncomputable def relativeDifferentialsSpecTildeHom :
    tilde (CommRingCat.KaehlerDifferential φ) ⟶ (Spec.map φ).relativeDifferentials :=
  (tilde.adjunction.homEquiv _ _).symm (relativeDifferentialsSpecΓHom φ)

/-- On global sections, `relativeDifferentialsSpecTildeHom` is `relativeDifferentialsSpecΓHom`,
after identifying `Γ(Spec S, Ω_{S/R}^~)` with `Ω_{S/R}`. -/
@[reassoc (attr := simp)]
lemma unit_app_comp_map_relativeDifferentialsSpecTildeHom :
    tilde.adjunction.unit.app _ ≫
        (moduleSpecΓFunctor (R := S)).map (relativeDifferentialsSpecTildeHom φ) =
      relativeDifferentialsSpecΓHom φ :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans ((tilde.adjunction.homEquiv _ _).apply_symm_apply _)

/-- The inverse of `relativeDifferentialsSpecTildeHom`. -/
noncomputable def relativeDifferentialsSpecToTilde :
    (Spec.map φ).relativeDifferentials ⟶ tilde (CommRingCat.KaehlerDifferential φ) :=
  ((Spec.map φ).relativeDifferentialsHomEquiv _).symm
    (tildeDerivation (CommRingCat.KaehlerDifferential.D φ))

lemma relativeDifferentialsSpecTildeHom_comp_toTilde :
    relativeDifferentialsSpecTildeHom φ ≫ relativeDifferentialsSpecToTilde φ = 𝟙 _ := by
  apply (tilde.adjunction.homEquiv _ _).injective
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans
    (Eq.trans ?_ (tilde.adjunction.homEquiv_id (CommRingCat.KaehlerDifferential φ)).symm)
  refine (congrArg (· ≫ _) ((tilde.adjunction.homEquiv _ _).apply_symm_apply _)).trans ?_
  ext b
  rw [ConcreteCategory.comp_apply, relativeDifferentialsSpecΓHom_d]
  exact (Scheme.Hom.relativeDifferentialsHomEquiv_symm_app_d _ _ _).trans
    (tildeDerivation_d_top _ b)


lemma relativeDifferentialsSpecToTilde_comp_tildeHom :
    relativeDifferentialsSpecToTilde φ ≫ relativeDifferentialsSpecTildeHom φ = 𝟙 _ := by
  apply ((Spec.map φ).relativeDifferentialsHomEquiv _).injective
  apply Scheme.Modules.derivation_ext_of_isAffine
  intro a
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).2 a
  change (relativeDifferentialsSpecTildeHom φ).val.app (op ⊤)
      ((relativeDifferentialsSpecToTilde φ).val.app (op ⊤)
        ((Spec.map φ).relativeDifferentialsDerivation.d ((Scheme.ΓSpecIso S).inv b))) =
    (Spec.map φ).relativeDifferentialsDerivation.d ((Scheme.ΓSpecIso S).inv b)
  refine (congrArg _ ((Scheme.Hom.relativeDifferentialsHomEquiv_symm_app_d _ _ _).trans
    (tildeDerivation_d_top _ b))).trans ?_
  refine (ConcreteCategory.congr_hom (unit_app_comp_map_relativeDifferentialsSpecTildeHom φ)
    (CommRingCat.KaehlerDifferential.d b)).trans ?_
  exact relativeDifferentialsSpecΓHom_d φ b

/-- The canonical morphism `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}` is an isomorphism. -/
instance isIso_relativeDifferentialsSpecTildeHom :
    IsIso (relativeDifferentialsSpecTildeHom φ) :=
  ⟨relativeDifferentialsSpecToTilde φ, relativeDifferentialsSpecTildeHom_comp_toTilde φ,
    relativeDifferentialsSpecToTilde_comp_tildeHom φ⟩

/-- The map `Ω_{S/R} → Γ(Spec S, Ω¹_{Spec S / Spec R})` is an isomorphism. -/
instance isIso_relativeDifferentialsSpecΓHom : IsIso (relativeDifferentialsSpecΓHom φ) := by
  rw [← unit_app_comp_map_relativeDifferentialsSpecTildeHom]
  exact IsIso.comp_isIso' inferInstance
    (inferInstanceAs (IsIso ((moduleSpecΓFunctor).map (relativeDifferentialsSpecTildeHom φ))))

/-- For a ring map `φ : R ⟶ S`, the sheaf of relative differentials `Ω¹_{Spec S / Spec R}` is
isomorphic to the quasi-coherent sheaf `Ω_{S/R}^~`, via the inverse of
`relativeDifferentialsSpecTildeHom`. -/
noncomputable def relativeDifferentialsSpecIso :
    (Spec.map φ).relativeDifferentials ≅ tilde (CommRingCat.KaehlerDifferential φ) :=
  (asIso (relativeDifferentialsSpecTildeHom φ)).symm

/-- For a ring map `φ : R ⟶ S`, the global sections of `Ω¹_{Spec S / Spec R}` are the `S`-module
`Ω_{S/R}`, compatibly with `d` and `D` (`relativeDifferentialsSpecΓHom_d`). -/
@[stacks 01UT]
noncomputable def relativeDifferentialsSpecΓIso :
    (moduleSpecΓFunctor (R := S)).obj (Spec.map φ).relativeDifferentials ≅
      CommRingCat.KaehlerDifferential φ :=
  (asIso (relativeDifferentialsSpecΓHom φ)).symm

/-- If `Ω_{S/R} ≅ S`, then `Ω¹_{Spec S / Spec R} ≅ 𝒪_{Spec S}`. -/
noncomputable def relativeDifferentialsSpecIsoUnit {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (e : CommRingCat.KaehlerDifferential φ ≅ ModuleCat.of S S) :
    (Spec.map φ).relativeDifferentials ≅ SheafOfModules.unit (Spec S).ringCatSheaf :=
  relativeDifferentialsSpecIso φ ≪≫ (tilde.functor S).mapIso e ≪≫ tildeSelf

end Affine

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The affine description of `Ω¹_{X/S}`.** Let `U ⊆ S` and `V ⊆ X` be affine opens with
`f(V) ⊆ U`, and write `A = Γ(S, U)`, `B = Γ(X, V)`. Then the restriction of `Ω¹_{X/S}` to
`V = Spec B` is the sheaf `Ω_{B/A}^~` associated with the `B`-module of Kähler differentials of
the `A`-algebra `B` (for the algebra structure given by `f.appLE U V e`).

For a curve `C` over a field `k`, with `S = Spec k` and `U = ⊤`, this is the standard affine
description `Ω¹_{C/k}|_{Spec B} = Ω_{B/k}^~` of the sheaf of Kähler differentials of `C`.

-/
noncomputable def relativeDifferentialsRestrictFromSpecIso {U : S.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    f.relativeDifferentials.restrict hV.fromSpec ≅
      tilde (CommRingCat.KaehlerDifferential (f.appLE U V e)) :=
  f.relativeDifferentialsRestrictIso hV.fromSpec ≪≫
    relativeDifferentialsCongr _ (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm ≪≫
    relativeDifferentialsCompIso _ _ ≪≫ relativeDifferentialsSpecIso _

/-- If `f` is smooth of relative dimension one, then every point of `X` has an open
neighbourhood `V` on which `Ω¹_{X/S}` is trivial: on an affine chart where `f` is standard
smooth, `Ω¹_{X/S}|_V ≅ Ω_{𝒪(V)/𝒪(U)}^~ ≅ 𝒪_V`. -/
lemma nonempty_restrict_relativeDifferentials_iso_unit [SmoothOfRelativeDimension 1 f] (x : X) :
    ∃ V : X.Opens, x ∈ V ∧
      Nonempty (f.relativeDifferentials.restrict V.ι ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  obtain ⟨U, hU, V, hV, hx, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(S, U) Γ(X, V) := hsm
  obtain ⟨eΩ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential
      (R := Γ(S, U)) (S := Γ(X, V)) 1
  refine ⟨V, hx, ⟨?_⟩⟩
  let eM : CommRingCat.KaehlerDifferential (f.appLE U V e) ≅ ModuleCat.of Γ(X, V) Γ(X, V) :=
    (eΩ ≪≫ₗ LinearEquiv.funUnique (Fin 1) Γ(X, V) Γ(X, V)).toModuleIso
  let T : f.relativeDifferentials.restrict hV.fromSpec ≅
      SheafOfModules.unit (Spec Γ(X, V)).ringCatSheaf :=
    f.relativeDifferentialsRestrictIso hV.fromSpec ≪≫
      relativeDifferentialsCongr _ (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm ≪≫
      relativeDifferentialsCompIso _ _ ≪≫ relativeDifferentialsSpecIsoUnit _ eM
  exact (Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec.symm).app _ ≪≫
    (Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app _ ≪≫
    (Modules.restrictFunctor hV.isoSpec.hom).mapIso T ≪≫ Modules.restrictUnitIso _

/-- **The canonical sheaf of a smooth curve.** For `f : X ⟶ S` smooth of relative dimension one,
the sheaf `Ω¹_{X/S}` is invertible: Zariski-locally `f` is standard smooth, `X = Spec B` with
`B = R[x₁, …, xₙ₊₁]/(g₁, …, gₙ)`, and `Ω_{B/R}` is free of rank one on the class of `dxᵢ` for
the coordinate `xᵢ` not involved in the invertible Jacobian minor.

-/
theorem isInvertible_relativeDifferentials [SmoothOfRelativeDimension 1 f] :
    SheafOfModules.IsInvertible (ringSheaf := X.ringCatSheaf) f.relativeDifferentials := by
  choose V hxV hV using f.nonempty_restrict_relativeDifferentials_iso_unit
  have hV' (x : X) : Nonempty (f.relativeDifferentials.over (V x) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (V x))) :=
    ⟨Modules.overIsoUnitOfPullbackIotaIso
      (((Modules.restrictFunctorIsoPullback (V x).ι).app _).symm ≪≫ (hV x).some)⟩
  have hcov : (Opens.grothendieckTopology X).CoversTop V := by
    rw [Opens.coversTop_iff]
    exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxV x⟩)
  exact SheafOfModules.isInvertible_of_forall_over_unit (M := f.relativeDifferentials) V hcov
    hV'

/-- **Differentials of a smooth morphism.** If `f` is smooth of relative dimension `d`, then
`Ω¹_{X/S}` is finite locally free of rank `d`: on an affine chart `Spec B ⟶ Spec A` where `f` is
standard smooth, `Ω¹_{X/S}` is `Ω_{B/A}^~`, and `Ω_{B/A} ≅ Bᵈ`. -/
theorem isFiniteLocallyFreeOfRank_relativeDifferentials (d : ℕ)
    [SmoothOfRelativeDimension d f] : f.relativeDifferentials.IsFiniteLocallyFreeOfRank d := by
  choose U hU V hV hx e hsm using fun x ↦
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) x
  refine Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion _ (fun x ↦ (hV x).fromSpec)
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2
      ⟨x, by rw [IsAffineOpen.opensRange_fromSpec]; exact hx x⟩) fun x ↦ ?_
  let φ := f.appLE (U x) (V x) (e x)
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension d Γ(S, U x) Γ(X, V x) := hsm x
  obtain ⟨eΩ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential
      (R := Γ(S, U x)) (S := Γ(X, V x)) d
  let N := (Spec.map φ).relativeDifferentials
  let T : (Modules.pullback (hV x).fromSpec).obj f.relativeDifferentials ≅ N :=
    ((Modules.restrictFunctorIsoPullback _).app _).symm ≪≫
      f.relativeDifferentialsRestrictIso (hV x).fromSpec ≪≫
      relativeDifferentialsCongr _
        (IsAffineOpen.SpecMap_appLE_fromSpec f (hU x) (hV x) (e x)).symm ≪≫
      relativeDifferentialsCompIso _ _
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, V x)).ringCatSheaf).prop_of_iso
      (relativeDifferentialsSpecIso φ).symm
      (inferInstanceAs (tilde (CommRingCat.KaehlerDifferential φ)).IsQuasicoherent)
  let E : Γ(N, ⊤) ≃ₗ[Γ(X, V x)] (Fin d → Γ(X, V x)) :=
    (relativeDifferentialsSpecΓIso φ).toLinearEquiv ≪≫ₗ eΩ
  have : Module.FinitePresentation Γ(X, V x) Γ(N, ⊤) := .of_equiv E.symm
  have : Module.Flat Γ(X, V x) Γ(N, ⊤) := .of_linearEquiv E
  have : N.IsFiniteLocallyFreeOfRank d :=
    Modules.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq N fun p ↦ by
      have := p.nontrivial
      rw [congr_fun (Module.rankAtStalk_eq_of_equiv E) p, Module.rankAtStalk_eq_finrank_of_free]
      simp
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso T.symm

end Scheme.Hom

end AlgebraicGeometry
