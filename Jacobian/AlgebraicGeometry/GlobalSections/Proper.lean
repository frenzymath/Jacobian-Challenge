import Jacobian.Algebra.Category.Ring.Pushout
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Global functions on proper geometrically integral schemes

The global sections of a proper geometrically integral scheme over a field
are the base field. Properness makes the section algebra a finite field
extension; flat base change along that field and a pushout argument show
that the structure map is an epimorphism, hence surjective.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Bundled-field form of the global-sections field theorem for an integral,
universally closed scheme. -/
theorem isField_of_universallyClosed_of_isField {R : CommRingCat.{u}}
    (hR : IsField R) {X : Scheme.{u}} (f : X ⟶ Spec R)
    [IsIntegral X] [UniversallyClosed f] : IsField Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' hR

/-- The structure morphism induces a bijection on global sections. -/
theorem bijective_appTop_of_isProper_of_geometricallyIntegral
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [GeometricallyIntegral f] : Function.Bijective f.appTop := by
  have hX : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  have hA : IsField Γ(X, ⊤) := isField_of_universallyClosed K f
  letI : Field Γ(X, ⊤) := hA.toField
  letI : Field Γ(Spec (CommRingCat.of K), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  refine ⟨f.appTop.hom.injective, ?_⟩
  suffices h : Epi f.appTop from
    RingHom.surjective_of_epi_of_finite f.appTop (finite_appTop_of_universallyClosed K f)
  set q : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of K) :=
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop) with hq
  have hsub : Subsingleton ↥(Spec Γ(X, ⊤)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Γ(X, ⊤)))
  have hYint : IsIntegral (pullback f q) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f q)
  letI : IsProper (pullback.snd f q) :=
    IsProper.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f q) inferInstance
  have hD : IsField Γ(pullback f q, ⊤) :=
    isField_of_universallyClosed_of_isField hA (pullback.snd f q)
  have hUST : (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ q ⁻¹ᵁ ⊤ :=
    (Scheme.Hom.preimage_top q).ge
  have hUSX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top f).ge
  have hUY : (⊤ : (pullback f q).Opens) =
      pullback.fst f q ⁻¹ᵁ ⊤ ⊓ pullback.snd f q ⁻¹ᵁ ⊤ := by simp
  have hCS : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hQS : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f q) hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _)
    (by simpa using CompactSpace.isCompact_univ)
    (by simpa using isQuasiSeparated_univ)
  have hpo := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f q) hUST hUSX hUY).mp hiso
  have hcompat : q.appLE ⊤ ⊤ hUST ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom =
      f.appLE ⊤ ⊤ hUSX := by
    have h₁ : q.appLE ⊤ ⊤ hUST = q.appTop := Scheme.Hom.appLE_eq_app q
    have h₂ : f.appLE ⊤ ⊤ hUSX = f.appTop := Scheme.Hom.appLE_eq_app f
    rw [h₁, h₂, hq, Scheme.ΓSpecIso_naturality, Iso.hom_inv_id_assoc]
  have hepi : Epi (f.appLE ⊤ ⊤ hUSX) :=
    CommRingCat.epi_of_isPushout_of_isField hpo hD (Scheme.ΓSpecIso Γ(X, ⊤)) hcompat
  rwa [show f.appLE ⊤ ⊤ hUSX = f.appTop from Scheme.Hom.appLE_eq_app f] at hepi

end AlgebraicGeometry
