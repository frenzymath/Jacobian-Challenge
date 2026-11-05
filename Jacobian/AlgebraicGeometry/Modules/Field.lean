import Jacobian.AlgebraicGeometry.Modules.Localization
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Module sheaves over a field

Every module sheaf on the spectrum of a field is quasi-coherent. Global sections give an additive equivalence with modules over the field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite

private lemma fieldSections_bijective_map_of_eq {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat}
    (F : TopCat.Presheaf C X) {U V : TopologicalSpace.Opens X}
    (i : op U ⟶ op V) (h : U = V) : Function.Bijective (F.map i) := by
  have : IsIso i := ⟨⟨(homOfLE h.le).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact ConcreteCategory.bijective_of_isIso _

namespace AlgebraicGeometry
variable {R : CommRingCat.{u}}

/-- Over a field `R`, every sheaf of `R`-modules on `Spec R` coming from an `𝒪_{Spec R}`-module is
localizing: a basic open `D(f)` is empty for `f = 0` and everything for `f ≠ 0`. -/
theorem isLocalizing_of_isField (hR : IsField R) (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) := by
  let := hR.toField
  intro f
  by_cases hf : f = 0
  · subst hf
    have : Subsingleton ((modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen 0))) :=
      ModuleCat.subsingleton_of_isZero (IsTerminal.isZero
        ((modulesSpecToSheaf.obj M).isTerminalOfEqEmpty PrimeSpectrum.basicOpen_zero))
    exact
      { map_units _ := isUnit_of_subsingleton _
        surj _ := ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
        exists_of_eq {x₁ x₂} _ := ⟨⟨0, 1, pow_one _⟩, by
          change (0 : R) • x₁ = (0 : R) • x₂
          simp⟩ }
  · have hf' : IsUnit f := Ne.isUnit hf
    have hU : ⊤ ≤ PrimeSpectrum.basicOpen f := fun x _ ↦ (PrimeSpectrum.mem_basicOpen _ _).2
      fun h ↦ x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hf')
    have hb := fieldSections_bijective_map_of_eq (modulesSpecToSheaf.obj M).obj
      (PrimeSpectrum.basicOpen f).leTop.op (hU.antisymm le_top)
    exact
      { map_units x := by
          obtain ⟨_, n, rfl⟩ := x
          exact (hf'.pow n).map _
        surj y := by
          obtain ⟨x, rfl⟩ := hb.2 y
          exact ⟨⟨x, 1⟩, by simp⟩
        exists_of_eq h := ⟨1, by simpa using hb.1 h⟩ }

/-- Over a field `R`, every `𝒪_{Spec R}`-module is quasi-coherent: it is `Γ(M)^~`. -/
theorem Scheme.Modules.isIso_fromTildeΓ_of_isField (hR : IsField R) (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing M).2 (isLocalizing_of_isField hR M)

instance moduleSpecΓFunctorIsRightAdjoint : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint

instance moduleSpecΓFunctorAdditive : (moduleSpecΓFunctor (R := R)).Additive :=
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryProducts (moduleSpecΓFunctor (R := R))
  Functor.additive_of_preservesBinaryBiproducts _

/-- Over a field `R`, the global sections functor `(Spec R).Modules ⥤ ModuleCat R` is an
equivalence, with inverse `M ↦ M^~`. In particular it is exact. -/
theorem isEquivalence_moduleSpecΓFunctor (hR : IsField R) :
    (moduleSpecΓFunctor (R := R)).IsEquivalence := by
  have (M : (Spec R).Modules) : IsIso ((tilde.adjunction (R := R)).counit.app M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isField hR M
  have (M : ModuleCat R) : IsIso ((tilde.adjunction (R := R)).unit.app M) :=
    inferInstanceAs (IsIso ((tilde.toTildeΓNatIso (R := R)).hom.app M))
  exact (tilde.adjunction (R := R)).toEquivalence.isEquivalence_inverse


namespace Scheme.Modules

private lemma fieldSections_smul_top_eq (M : (Spec R).Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = (Scheme.ΓSpecIso R).inv r • x := by
  rw [smul_Spec_def]
  congr 1

theorem finrank_eq_of_coe_eq (M : (Spec R).Modules) (p : Submodule R Γ(M, ⊤))
    (p' : Submodule Γ(Spec R, ⊤) Γ(M, ⊤)) (h : (p : Set Γ(M, ⊤)) = p') :
    Module.finrank R p = Module.finrank Γ(Spec R, ⊤) p' := by
  let j : p ≃+ p' := { Set.equivOfEq h with map_add' _ _ := rfl }
  have hi : Function.Bijective (Scheme.ΓSpecIso R).inv :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv
  exact congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv _ j hi fun r x ↦ Subtype.ext (fieldSections_smul_top_eq M r x))


end Scheme.Modules
end AlgebraicGeometry
