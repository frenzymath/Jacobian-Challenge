import Jacobian.AlgebraicGeometry.Modules.FreeGenerator
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist

/-!
# Free generators of twisting sheaves

A section of `𝒪(m)` with a pointwise inverse in `𝒪(-m)` freely generates the
twisting sheaf on its domain. Restrictions and scalar actions are pointwise.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace Proj

open ProjectiveSpectrum.Twist

section FreeGenerator

variable {𝒜 m}

/-- Sections of `𝒪(m)` restrict pointwise. -/
lemma twist_presheaf_map_apply {U V : (Proj 𝒜).Opens} (h : V ≤ U) (s : Γ(twist 𝒜 m, U))
    (x : V) : ((twist 𝒜 m).presheaf.map (homOfLE h).op s).1 x = s.1 ⟨x.1, h x.2⟩ :=
  rfl

/-- Sections of the structure sheaf act on sections of `𝒪(m)` by pointwise multiplication. -/
lemma coe_twist_smul_apply {U : (Proj 𝒜).Opens} (r : Γ(Proj 𝒜, U)) (s : Γ(twist 𝒜 m, U))
    (x : U) : ((r • s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (r.1 x).val * (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) :=
  rfl

/-- **A section of `𝒪(m)` with a pointwise inverse is a free generator**: if `ε` is a section of
`𝒪(m)` over `U` and `ε'` a section of `𝒪(-m)` over `U` with `ε ε' = 1` at every point, then every
section of `𝒪(m)` over an open `V ⊆ U` is uniquely `r • ε|_V`. -/
lemma isFreeGenerator_twist_of_mul_eq_one {U : (Proj 𝒜).Opens} (ε : Γ(twist 𝒜 m, U))
    (ε' : Γ(twist 𝒜 (-m), U))
    (h : ∀ x : U, (ε.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * ε'.1 x = 1) :
    Scheme.Modules.IsFreeGenerator ε := by
  intro V hV
  constructor
  · intro r r' hrr
    refine Subtype.ext (funext fun x ↦ val_injective _ ?_)
    have hx := congrArg (fun s : Γ(twist 𝒜 m, V) ↦
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hrr
    dsimp only at hx
    rw [coe_twist_smul_apply, coe_twist_smul_apply, twist_presheaf_map_apply] at hx
    have hx' := congrArg (· * (ε'.1 ⟨x.1, hV x.2⟩ :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hx
    dsimp only at hx'
    rwa [mul_assoc, mul_assoc, h, mul_one, mul_one] at hx'
  · intro t
    let ε'V := (twist 𝒜 (-m)).presheaf.map (homOfLE hV).op ε'
    refine ⟨sectionsZeroInv ⟨fun x ↦ ⟨t.1 x * ε'V.1 x, add_neg_cancel m ▸
      mul_mem_degreePart (t.1 x).2 (ε'V.1 x).2⟩, isLocallyFraction_mul (add_neg_cancel m) t.2
        ε'V.2⟩, ?_⟩
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    rw [coe_twist_smul_apply, twist_presheaf_map_apply]
    have := zeroEquiv_sectionsZeroInv (U := Opposite.op V) ⟨fun x ↦ ⟨t.1 x * ε'V.1 x,
      add_neg_cancel m ▸ mul_mem_degreePart (t.1 x).2 (ε'V.1 x).2⟩,
        isLocallyFraction_mul (add_neg_cancel m) t.2 ε'V.2⟩ x
    have hv := congrArg Subtype.val this
    rw [degreePart.coe_zeroEquiv_apply] at hv
    rw [hv]
    change (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      (ε'.1 ⟨x.1, hV x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      (ε.1 ⟨x.1, hV x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    have hx := h ⟨x.1, hV x.2⟩
    rw [mul_comm] at hx
    rw [mul_assoc, hx, mul_one]

end FreeGenerator

end Proj

end AlgebraicGeometry
