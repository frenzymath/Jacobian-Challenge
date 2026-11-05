import Jacobian.AlgebraicGeometry.Modules.Invertible
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Twisting sheaves on a projective spectrum

The twisting sheaf `𝒪(m)` consists of locally homogeneous fractions of degree `m`.
Its zeroth twist is the structure sheaf. Multiplication by a homogeneous element
is an isomorphism over its standard open. If degree-one standard opens cover the
projective spectrum, every twist is an invertible sheaf.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace ProjectiveSpectrum.Twist

variable {𝒜}

section Zero

/-- The canonical morphism of presheaves of abelian groups from the structure sheaf of `Proj 𝒜`
to the twisting presheaf `𝒪(0)`, given by `HomogeneousLocalization.degreePart.zeroEquiv` at
every point. -/
def unitToPresheafInAbZero :
    (PresheafOfModules.unit (Proj 𝒜).ringCatSheaf.obj).presheaf ⟶ presheafInAb 𝒜 0 where
  app _ := AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_zeroEquiv s⟩
      map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }
  naturality _ _ _ := rfl

/-- The map `𝒪 ⟶ 𝒪(0)` is `HomogeneousLocalization.degreePart.zeroEquiv` at every point. -/
@[simp]
theorem unitToPresheafInAbZero_app_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) (x : U.unop) :
    (unitToPresheafInAbZero.app U s).1 x = degreePart.zeroEquiv (s.1 x) :=
  rfl

/-- The inverse of the canonical map from the sections of the structure sheaf to those
of `𝒪(0)`, given by the inverse of `HomogeneousLocalization.degreePart.zeroEquiv` at every
point. -/
def sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (t : sections 𝒜 0 U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  ⟨fun x ↦ degreePart.zeroEquiv.symm (t.1 x), by
    intro x
    obtain ⟨V, hxV, e, i, j, hij, ⟨a, ha⟩, ⟨b, hb⟩, hw, w⟩ := t.2 x
    obtain rfl : i = j := by omega
    refine ⟨V, hxV, e, i, ⟨a, ha⟩, ⟨b, hb⟩, hw, fun y ↦ ?_⟩
    refine (LinearEquiv.symm_apply_eq _).mpr ((w y).trans ?_)
    ext
    simp [val_mk]⟩

/-- `sectionsZeroInv` is a right inverse of `HomogeneousLocalization.degreePart.zeroEquiv`
at every point. -/
@[simp]
theorem zeroEquiv_sectionsZeroInv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (t : sections 𝒜 0 U) (x : U.unop) :
    degreePart.zeroEquiv ((sectionsZeroInv t).1 x) = t.1 x :=
  LinearEquiv.apply_symm_apply _ _

end Zero

section Mul

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

include hf

/-- Multiplication by a homogeneous element `f` of degree `d`, as a morphism of presheaves of
abelian groups from `𝒪(m)` to `𝒪(m + d)`. -/
def mulPresheafHom : presheafInAb 𝒜 m ⟶ presheafInAb 𝒜 (m + d) where
  app U := AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_mul rfl s.2
        (isLocallyFraction_mk (by simp) ⟨f, hf⟩ ⟨1, SetLike.one_mem_graded 𝒜⟩
          fun x ↦ (Ideal.ne_top_iff_one _).mp x.1.isPrime.ne_top)⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext (zero_mul _))
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (add_mul _ _ _)) }
  naturality _ _ _ := rfl

/-- The map `𝒪(m) ⟶ 𝒪(m + d)` multiplies every value by `f`. -/
@[simp]
theorem val_mulPresheafHom_app_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (presheafInAb 𝒜 m).obj U) (x : U.unop) :
    (((mulPresheafHom m hf).app U s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk f 1 :=
  rfl

/-- On an open set `U` contained in `D₊(f)`, division by the homogeneous element `f` of
degree `d` maps the sections of `𝒪(m + d)` to those of `𝒪(m)`. -/
def divPresheafHomApp {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (presheafInAb 𝒜 (m + d)).obj U ⟶ (presheafInAb 𝒜 m).obj U :=
  AddCommGrpCat.ofHom
    { toFun s := ⟨_, isLocallyFraction_mul (add_neg_cancel_right m d) s.2
        (isLocallyFraction_mk (by simp) ⟨1, SetLike.one_mem_graded 𝒜⟩ ⟨f, hf⟩
          fun x ↦ hU x.2)⟩
      map_zero' := Subtype.ext (funext fun _ ↦ Subtype.ext (zero_mul _))
      map_add' _ _ := Subtype.ext (funext fun _ ↦ Subtype.ext (add_mul _ _ _)) }

/-- The map `𝒪(m + d) ⟶ 𝒪(m)` on `U ≤ D₊(f)` divides every value by `f`. -/
@[simp]
theorem val_divPresheafHomApp_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (s : (presheafInAb 𝒜 (m + d)).obj U)
    (x : U.unop) :
    ((divPresheafHomApp m hf hU s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  rfl

/-- On an open set `U` contained in `D₊(f)`, multiplication by `f` is a bijection from the
sections of `𝒪(m)` to those of `𝒪(m + d)`. -/
theorem isIso_mulPresheafHom_app {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) : IsIso ((mulPresheafHom m hf).app U) := by
  have key (x : U.unop) :
      Localization.mk f 1 *
          Localization.mk 1 (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
        (1 : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) := by
    rw [Localization.mk_mul, one_mul, mul_one]
    exact Localization.mk_self (⟨f, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have key' (x : U.unop) := (mul_comm _ _).trans (key x)
  refine ⟨divPresheafHomApp m hf hU, ?_, ?_⟩ <;>
  · ext s : 2
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    simp [mul_assoc, key, key']

end Mul

end ProjectiveSpectrum.Twist

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace Proj

open ProjectiveSpectrum.Twist

/-- **The twisting sheaf `𝒪(m)` on `Proj 𝒜`**, for `m : ℤ`: its sections over `U` are the
dependent functions `x ↦ s x ∈ (A_x)ₘ` which are locally fractions `a / b` of homogeneous
elements with `deg a = deg b + m`. -/
def twist : (Proj 𝒜).Modules :=
  ⟨presheafOfModules 𝒜 m, isSheaf_presheafInAb 𝒜 m⟩

variable {𝒜}

/-- The canonical morphism `𝒪 ⟶ 𝒪(0)` from the structure sheaf of `Proj 𝒜` to its zeroth
twisting sheaf. -/
def unitToTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ⟶ twist 𝒜 0 :=
  ⟨PresheafOfModules.homMk unitToPresheafInAbZero fun _ _ _ ↦
    Subtype.ext (funext fun _ ↦ Subtype.ext (val_mul _ _))⟩

/-- The morphism `𝒪 ⟶ 𝒪(0)` sends a section `s` of the structure sheaf to the section
`x ↦ s x` of `𝒪(0)`. -/
@[simp]
theorem val_unitToTwistZero_app_apply (U : (Proj 𝒜).Opens)
    (s : Γ((SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules), U)) (x : U) :
    ((Scheme.Modules.Hom.app unitToTwistZero U) s).1 x = degreePart.zeroEquiv (s.1 x) :=
  rfl

/-- The morphism `𝒪 ⟶ 𝒪(0)` is an isomorphism. -/
instance : IsIso (unitToTwistZero (𝒜 := 𝒜)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun s t h ↦ ?_, fun t ↦ ⟨sectionsZeroInv t, ?_⟩⟩
    · refine Subtype.ext (funext fun x ↦ degreePart.zeroEquiv.injective ?_)
      simpa using congr($(h).1 x)
    · exact Subtype.ext (funext fun x ↦ (val_unitToTwistZero_app_apply _ _ _).trans
        (zeroEquiv_sectionsZeroInv t x))

/-- **`𝒪(0)` is the structure sheaf**: the zeroth twisting sheaf of `Proj 𝒜` is isomorphic to
the structure sheaf. -/
def unitIsoTwistZero :
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf : (Proj 𝒜).Modules) ≅ twist 𝒜 0 :=
  asIso unitToTwistZero

variable {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

/-- Multiplication by a homogeneous element `f` of degree `d` is a morphism of `𝒪`-modules
`𝒪(m) ⟶ 𝒪(m + d)` on `Proj 𝒜`. -/
def twistMul : twist 𝒜 m ⟶ twist 𝒜 (m + d) :=
  ⟨PresheafOfModules.homMk (mulPresheafHom m hf) fun _ _ _ ↦
    Subtype.ext (funext fun _ ↦ Subtype.ext (mul_assoc _ _ _))⟩

/-- On the basic open set `D₊(f)`, multiplication by `f` is an isomorphism `𝒪(m) ≅ 𝒪(m + d)`. -/
instance isIso_restrict_twistMul :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistMul m hf)) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V ↦
    isIso_mulPresheafHom_app m hf ((Proj.basicOpen 𝒜 f).ι_image_le V)

/-- **`𝒪(m)` is locally trivial**: on the basic open set `D₊(f)` of a homogeneous element `f`
of degree `d`, multiplication by `f` is an isomorphism `𝒪(m)|_{D₊(f)} ≅ 𝒪(m + d)|_{D₊(f)}`. -/
def twistRestrictIso :
    (twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twist 𝒜 (m + d)).restrict (Proj.basicOpen 𝒜 f).ι :=
  asIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι).map (twistMul m hf))

/-- Multiplications by two homogeneous elements of the same degree commute. -/
lemma twistMul_comp_twistMul {g : A} (hg : g ∈ 𝒜 d) :
    twistMul m hf ≫ twistMul (m + d) hg = twistMul m hg ≫ twistMul (m + d) hf := by
  ext U s : 3
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact mul_right_comm _ _ _

/-- **`𝒪(m)` is trivial on `D₊(f)`** for a homogeneous element `f` of degree `1`: composing
`twistRestrictIso` `|m|` times gives `𝒪(m)|_{D₊(f)} ≅ 𝒪(0)|_{D₊(f)}`, and `𝒪(0) ≅ 𝒪`. -/
lemma nonempty_restrict_twist_iso_unit (hf : f ∈ 𝒜 1) :
    Nonempty ((twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅ SheafOfModules.unit _) := by
  have key (m : ℤ) : Nonempty ((twist 𝒜 m).restrict (Proj.basicOpen 𝒜 f).ι ≅
      (twist 𝒜 0).restrict (Proj.basicOpen 𝒜 f).ι) := by
    induction m using Int.induction_on with
    | zero => exact ⟨Iso.refl _⟩
    | succ k ih => exact ⟨(twistRestrictIso k hf).symm ≪≫ ih.some⟩
    | pred k ih =>
      have e := twistRestrictIso (-(k : ℤ) - 1) hf
      rw [show -(k : ℤ) - 1 + ((1 : ℕ) : ℤ) = -k by omega] at e
      exact ⟨e ≪≫ ih.some⟩
  exact ⟨(key m).some ≪≫ (Scheme.Modules.restrictFunctor _).mapIso unitIsoTwistZero.symm ≪≫
    Scheme.Modules.restrictUnitIso _⟩

variable (𝒜) in
/-- **`𝒪(m)` is invertible** on `Proj 𝒜` when the basic open sets `D₊(f)` of the homogeneous
elements `f` of degree `1` cover `Proj 𝒜`, e.g. when `𝒜` is generated in degree `1`. -/
lemma isInvertible_twist (h : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ Proj.basicOpen 𝒜 f) :
    (twist 𝒜 m).IsInvertible := by
  refine (Scheme.Modules.isInvertible_iff_forall_exists_pullback_unit _).mpr ?_
  intro x
  obtain ⟨f, hf, hx⟩ := h x
  obtain ⟨e⟩ := nonempty_restrict_twist_iso_unit m hf
  exact ⟨_, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback _).symm.app _ ≪≫ e⟩⟩

end Proj

end AlgebraicGeometry
