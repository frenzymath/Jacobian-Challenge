import Jacobian.AlgebraicGeometry.Modules.Limits
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Ideal sheaves as module sheaves

For an ideal sheaf described on affine opens, the kernel of the restriction to its closed
subscheme gives the corresponding module sheaf. Its sections recover the given affine ideals.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- The comparison morphism `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` of `𝒪_X`-modules attached to the closed
immersion `J.subschemeι` of the closed subscheme cut out by `J`. Its kernel is the ideal
sheaf; see `AlgebraicGeometry.Scheme.IdealSheafData.toModules`. -/
noncomputable def toPushforwardSubscheme :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit _

@[simp]
lemma map_toPushforwardSubscheme (U : X.Opens)
    (x : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map J.toPushforwardSubscheme x =
      J.subschemeι.app U x :=
  rfl

/-- **The ideal sheaf attached to a `Scheme.IdealSheafData`**, as a sheaf of `𝒪_X`-modules:
the kernel of `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}`.

Over an affine open `U` its sections are `J.ideal U`
(`AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app`). -/
noncomputable def toModules : X.Modules := kernel J.toPushforwardSubscheme

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
noncomputable def toModulesι :
    J.toModules ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  kernel.ι _

lemma map_kernelι_eq_toModulesι_app (U : X.Opens) (x : Γ(J.toModules, U)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι J.toPushforwardSubscheme) x =
      J.toModulesι.app U x :=
  rfl

/-- The ideal cut out by `J` on an **arbitrary** open subset, not just an affine one: the
kernel of the restriction map to the closed subscheme.

`Scheme.IdealSheafData` itself only records ideals on affine opens, so this is the extension
of `J.ideal` to all of `X.Opens`, and `idealOfOpens_eq_ideal` says the extension is
compatible. -/
noncomputable def idealOfOpens (U : X.Opens) : Ideal Γ(X, U) :=
  RingHom.ker (J.subschemeι.app U).hom

@[simp]
lemma idealOfOpens_eq_ideal (U : X.affineOpens) : J.idealOfOpens U.1 = J.ideal U :=
  J.ker_subschemeι_app U

lemma mem_idealOfOpens_iff {U : X.Opens} {x : Γ(X, U)} :
    x ∈ J.idealOfOpens U ↔ J.subschemeι.app U x = 0 :=
  RingHom.mem_ker

/-- Over any open subset, the sections of the ideal sheaf are exactly the sections of `𝒪_X`
killed by the restriction to the closed subscheme cut out by `J`. -/
lemma range_toModulesι_app_eq (U : X.Opens) :
    Set.range (J.toModulesι.app U) = { x | J.subschemeι.app U x = 0 } :=
  Modules.range_kernelι_app J.toPushforwardSubscheme U

lemma range_toModulesι_app_eq_idealOfOpens (U : X.Opens) :
    Set.range (J.toModulesι.app U) = (J.idealOfOpens U : Set Γ(X, U)) :=
  J.range_toModulesι_app_eq U

/-- **Over an affine open the sections of the ideal sheaf are the given ideal.** This is what
identifies `J.toModules` with the ideal sheaf that `J` is intended to describe: `J` only
records `J.ideal U` for affine `U`, and that is exactly what `J.toModules` gives back. -/
lemma range_toModulesι_app (U : X.affineOpens) :
    Set.range (J.toModulesι.app U.1) = (J.ideal U : Set Γ(X, U.1)) := by
  rw [range_toModulesι_app_eq_idealOfOpens, idealOfOpens_eq_ideal]

instance : Mono J.toModulesι := by
  unfold toModulesι
  infer_instance

/-- The ideal sheaf really is a subsheaf of `𝒪_X`: the inclusion is injective on sections
over every open subset, not merely a categorical monomorphism. -/
lemma injective_toModulesι_app (U : X.Opens) : Function.Injective (J.toModulesι.app U) :=
  Modules.injective_kernelι_app J.toPushforwardSubscheme U


/-- If the global sections are mapped injectively to the closed subscheme cut out by `J`, then
`J` has no nonzero global sections. -/
lemma subsingleton_sections_toModules_of_injective
    (h : Function.Injective (J.subschemeι.app ⊤)) : Subsingleton Γ(J.toModules, ⊤) := by
  refine ⟨fun a b ↦ J.injective_toModulesι_app ⊤ ?_⟩
  have ha : J.subschemeι.app ⊤ (J.toModulesι.app ⊤ a) = 0 :=
    (J.range_toModulesι_app_eq ⊤).subset ⟨a, rfl⟩
  have hb : J.subschemeι.app ⊤ (J.toModulesι.app ⊤ b) = 0 :=
    (J.range_toModulesι_app_eq ⊤).subset ⟨b, rfl⟩
  exact h (ha.trans hb.symm)

/-- If `Γ(X, 𝒪_X)` is a field (for instance if `X` is proper and geometrically integral over a
field), and the closed subscheme cut out by `J` is nonempty, then `J` has no nonzero global
sections. -/
lemma subsingleton_sections_toModules_of_isField (hX : IsField Γ(X, ⊤)) [Nonempty J.subscheme] :
    Subsingleton Γ(J.toModules, ⊤) := by
  let := hX.toField
  have : Nonempty ↥(J.subschemeι ⁻¹ᵁ ⊤) := ⟨⟨Classical.arbitrary J.subscheme, trivial⟩⟩
  exact J.subsingleton_sections_toModules_of_injective (J.subschemeι.app ⊤).hom.injective
end AlgebraicGeometry.Scheme.IdealSheafData
