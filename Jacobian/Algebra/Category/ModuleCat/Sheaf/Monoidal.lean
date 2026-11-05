import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Jacobian.Algebra.Category.ModuleCat.Presheaf.InternalHom
import Jacobian.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# The monoidal category of sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. The sheafification functor
`PresheafOfModules.sheafification (𝟙 _)` from presheaves of modules over `R` to sheaves of
modules over `R` is a localization functor with respect to the class `W` of morphisms that become
isomorphisms after sheafification (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization`).
If `W` is stable under tensoring with a presheaf of modules (`W.IsMonoidal`), the monoidal
structure of `PresheafOfModules.Monoidal` descends to sheaves of modules
(`Mathlib.CategoryTheory.Localization.Monoidal`). The tensor product `M ⊗ N` of two sheaves of
modules is then the sheafification of the tensor product of the underlying presheaves of
modules, and the associator, unitors, braiding and all coherences come from the localization.

This is the module-coefficient analogue of `CategoryTheory.Sheaf.monoidalCategory`. As there,
the monoidal structure is not an instance.

The key input is that `W` is monoidal: if `g : P₁ ⟶ P₂` becomes an isomorphism after
sheafification, so does `F ◁ g` for every presheaf of modules `F`. We prove it when the
site is in the universe of the coefficients, by testing against sheaves `N` and using the
internal hom `PresheafOfModules.homObj F N`, which is a sheaf when `N` is.

## Main definitions and results

- `SheafOfModules.isMonoidal_W`: the class `W` is monoidal.
- `SheafOfModules.monoidalCategory`: the monoidal category structure on sheaves of modules.
- `SheafOfModules.symmetricCategory`: it is symmetric.
- `SheafOfModules.tensorObjIsoSheafification`: `M ⊗ N` is the sheafification of the tensor
  product of the underlying presheaves of modules.
- `SheafOfModules.sheafificationMonoidal`, `SheafOfModules.sheafificationBraided`: the
  sheafification functor is monoidal and braided, as named definitions.

The sheafification functor is a braided monoidal functor for these structures.
-/


universe v' u' u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)

-- The class of morphisms of presheaves of modules over `R` that become isomorphisms after
-- sheafification.
set_option hygiene false in
local notation "𝓦" =>
  J.W.inverseImage (PresheafOfModules.toPresheaf.{u} (𝓡).obj)

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})

/-- The monoidal category structure on presheaves of modules over the underlying presheaf of
rings of `R`, from `PresheafOfModules.monoidalCategory`. -/
noncomputable instance : MonoidalCategory (PresheafOfModules.{u} (𝓡).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- The symmetric monoidal category structure on presheaves of modules over the underlying
presheaf of rings of `R`, from `PresheafOfModules.symmetricCategory`. -/
noncomputable instance : SymmetricCategory (PresheafOfModules.{u} (𝓡).obj) :=
  inferInstanceAs (SymmetricCategory (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)))

end

section IsMonoidal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- A morphism `h` of presheaves of modules becomes an isomorphism after sheafification if and
only if precomposition with `h` is bijective on morphisms to the underlying presheaf of modules
of every sheaf of modules. -/
lemma W_iff_bijective_comp {P₁ P₂ : PresheafOfModules.{u} (𝓡).obj} (h : P₁ ⟶ P₂) :
    𝓦 h ↔ ∀ N : SheafOfModules.{u} 𝓡, Function.Bijective (fun φ : P₂ ⟶ N.val ↦ h ≫ φ) := by
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 _),
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun N ↦ ?_
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)
  have : (fun φ : P₂ ⟶ N.val ↦ h ≫ φ) = adj.homEquiv P₁ N ∘
      (fun x ↦ (𝓢).map h ≫ x) ∘
      (adj.homEquiv P₂ N).symm := by
    funext φ
    exact ((adj.homEquiv_naturality_left h _).trans
      (congrArg (h ≫ ·) ((adj.homEquiv P₂ N).apply_symm_apply φ))).symm
  rw [this]
  exact ((Equiv.bijective_comp _ _).trans (Equiv.comp_bijective _ _)).symm

/-- If `g : P₁ ⟶ P₂` becomes an isomorphism after sheafification, then so does `F ◁ g`. -/
lemma W_whiskerLeft (F : PresheafOfModules.{u} (𝓡).obj)
    {P₁ P₂ : PresheafOfModules.{u} (𝓡).obj} {g : P₁ ⟶ P₂}
    (hg : 𝓦 g) : 𝓦 (F ◁ g) := by
  rw [W_iff_bijective_comp] at hg ⊢
  intro N
  have : (fun φ : F ⊗ P₂ ⟶ N.val ↦ F ◁ g ≫ φ) =
      (PresheafOfModules.homObjEquiv (R := R.obj) F P₁ N.val).symm ∘ (fun ψ ↦ g ≫ ψ) ∘
      PresheafOfModules.homObjEquiv (R := R.obj) F P₂ N.val := by
    funext φ
    exact (Equiv.eq_symm_apply _).2 (PresheafOfModules.homObjEquiv_whiskerLeft_comp g φ)
  rw [this]
  exact ((Equiv.bijective_comp _ _).trans (Equiv.comp_bijective _ _)).2 <|
    hg ⟨PresheafOfModules.homObj (R := R.obj) F N.val,
      PresheafOfModules.isSheaf_homObj N.isSheaf⟩

/-- The class of morphisms of presheaves of modules that become isomorphisms after
sheafification is stable under tensor products. -/
instance isMonoidal_W : (𝓦).IsMonoidal where
  whiskerLeft F _ _ _ hg := W_whiskerLeft R F hg
  whiskerRight {P₁ P₂} f hf G := ((𝓦).arrow_mk_iso_iff
    (Arrow.isoMk (β_ P₁ G) (β_ P₂ G))).2 (W_whiskerLeft R G hf)

end IsMonoidal

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The sheafification of the unit presheaf of modules is the unit sheaf of modules: this is
the counit of the sheafification adjunction at `SheafOfModules.unit`. -/
noncomputable def sheafificationObjUnitIso :
    (𝓢).obj
        (𝟙_ (PresheafOfModules.{u} (𝓡).obj)) ≅ unit 𝓡 :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).counit).app (unit 𝓡)

variable [(𝓦).IsMonoidal]

/-- The monoidal category structure on sheaves of modules over `R`, obtained by localizing the
monoidal category structure on presheaves of modules. -/
@[instance_reducible]
noncomputable def monoidalCategory : MonoidalCategory (SheafOfModules.{u} 𝓡) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (L := 𝓢)
    (W := 𝓦) (sheafificationObjUnitIso R)))

/-- The monoidal category structure `SheafOfModules.monoidalCategory` is symmetric. -/
@[instance_reducible]
noncomputable def symmetricCategory :
    letI := monoidalCategory R
    SymmetricCategory (SheafOfModules.{u} 𝓡) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (L := 𝓢)
    (W := 𝓦) (sheafificationObjUnitIso R)))

attribute [local instance] monoidalCategory symmetricCategory

noncomputable instance :
    (𝓢).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := 𝓢)
    (W := 𝓦) (sheafificationObjUnitIso R)).Monoidal

noncomputable instance :
    (𝓢).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := 𝓢)
    (W := 𝓦) (sheafificationObjUnitIso R)).Braided

variable {R} in
/-- The tensor product `M ⊗ N` of two sheaves of modules is the sheafification `a` of the tensor
product of the underlying presheaves of modules. Writing `ε` for the counit of the
sheafification adjunction and `μ` for the tensorator of the monoidal functor `a`:
```
  M ⊗ N ──ε⁻¹ ⊗ ε⁻¹──▶ a(M.val) ⊗ a(N.val) ──μ──▶ a(M.val ⊗ N.val)
```
-/
noncomputable def tensorObjIsoSheafification (M N : SheafOfModules.{u} 𝓡) :
    M ⊗ N ≅ (𝓢).obj
      (M.val ⊗ N.val : PresheafOfModules.{u} (𝓡).obj) :=
  ((asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).counit).app M ⊗ᵢ
      (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)).counit).app N).symm ≪≫
    Functor.Monoidal.μIso 𝓢
      M.val N.val

end

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] monoidalCategory symmetricCategory

/-- The sheafification functor from presheaves of modules over `R` to sheaves of modules is
monoidal for `SheafOfModules.monoidalCategory`. This names the instance above, which instance
search does not find for the structure sheaf of a scheme. -/
@[instance_reducible]
noncomputable def sheafificationMonoidal :
    (PresheafOfModules.sheafification.{u}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).Monoidal :=
  inferInstance

/-- The sheafification functor from presheaves of modules over `R` to sheaves of modules is
braided for `SheafOfModules.symmetricCategory`. -/
@[instance_reducible]
noncomputable def sheafificationBraided :
    letI := sheafificationMonoidal R
    (PresheafOfModules.sheafification.{u}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).Braided :=
  inferInstance

end

end SheafOfModules
