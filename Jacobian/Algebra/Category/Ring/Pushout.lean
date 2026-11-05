import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pushouts of commutative rings

Pushouts are tensor products, and a field pushout with two isomorphic input legs forces
the input morphism to be an epimorphism.
-/

universe u

open CategoryTheory Limits

namespace CommRingCat

/-- A pushout of commutative rings whose two legs become isomorphic, and whose
pushout is a field, makes either structure map an epimorphism. -/
lemma epi_of_isPushout_of_isField {A B C D : CommRingCat.{u}}
    {φ : A ⟶ B} {ψ : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D}
    (H : IsPushout φ ψ inl inr) (hD : IsField D) [Nontrivial B]
    (e : C ≅ B) (he : ψ ≫ e.hom = φ) : Epi φ := by
  letI : Field D := hD.toField
  let μ : D ⟶ B := H.desc (𝟙 B) e.hom (by rw [Category.comp_id, he])
  have hμinl : inl ≫ μ = 𝟙 B := H.inl_desc _ _ _
  have hμinr : inr ≫ μ = e.hom := H.inr_desc _ _ _
  have hμiso : IsIso μ := by
    refine (ConcreteCategory.isIso_iff_bijective μ).mpr
      ⟨μ.hom.injective, fun b ↦ ⟨inl b, ?_⟩⟩
    simpa using congr($(hμinl) b)
  letI := hμiso
  have hlegs : e.inv ≫ inr = inl := by
    rw [← cancel_mono μ, Category.assoc, hμinr, hμinl, Iso.inv_hom_id]
  refine ⟨fun {W} a b hab ↦ ?_⟩
  have hab' : φ ≫ a = ψ ≫ (e.hom ≫ b) := by
    rw [← Category.assoc, he]
    exact hab
  calc
    a = inl ≫ H.desc a (e.hom ≫ b) hab' := (H.inl_desc _ _ _).symm
    _ = e.inv ≫ inr ≫ H.desc a (e.hom ≫ b) hab' := by rw [← Category.assoc, hlegs]
    _ = e.inv ≫ e.hom ≫ b := by rw [H.inr_desc]
    _ = b := by rw [Iso.inv_hom_id_assoc]

end CommRingCat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse

open TensorProduct

variable {baseRing baseAlgebra' extensionAlgebra pushoutRing : CommRingCat.{schemeUniverse}} {coefficientMap : baseRing ⟶ extensionAlgebra} {algebraStructure : baseRing ⟶ baseAlgebra'} {i₁ : extensionAlgebra ⟶ pushoutRing} {i₂ : baseAlgebra' ⟶ pushoutRing}
  [Algebra baseRing baseAlgebra'] [Algebra baseRing extensionAlgebra]

/-- A pushout square of rings identifies `Q` with the tensor product `A' ⊗[R] E`, given that the
algebra structures are the ones induced by the span. -/
noncomputable def _root_.CategoryTheory.IsPushout.tensorEquiv (compatibility : IsPushout coefficientMap algebraStructure i₁ i₂)
    (hα : CommRingCat.ofHom (algebraMap baseRing baseAlgebra') = algebraStructure) (hφ : CommRingCat.ofHom (algebraMap baseRing extensionAlgebra) = coefficientMap) :
    baseAlgebra' ⊗[baseRing] extensionAlgebra ≃+* pushoutRing := by
  have compatibility' : IsPushout algebraStructure coefficientMap
      (CommRingCat.ofHom (S := baseAlgebra' ⊗[baseRing] extensionAlgebra) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := baseAlgebra' ⊗[baseRing] extensionAlgebra) Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← hα, ← hφ]
    exact CommRingCat.isPushout_tensorProduct baseRing baseAlgebra' extensionAlgebra
  exact (compatibility'.isoIsPushout _ _ compatibility.flip).commRingCatIsoToRingEquiv

lemma _root_.CategoryTheory.IsPushout.tensorEquiv_tmul (compatibility : IsPushout coefficientMap algebraStructure i₁ i₂)
    (hα : CommRingCat.ofHom (algebraMap baseRing baseAlgebra') = algebraStructure) (hφ : CommRingCat.ofHom (algebraMap baseRing extensionAlgebra) = coefficientMap)
    (baseScalar : baseAlgebra') (element : extensionAlgebra) : compatibility.tensorEquiv hα hφ (baseScalar ⊗ₜ element) = i₂ baseScalar * i₁ element := by
  have compatibility' : IsPushout algebraStructure coefficientMap
      (CommRingCat.ofHom (S := baseAlgebra' ⊗[baseRing] extensionAlgebra) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := baseAlgebra' ⊗[baseRing] extensionAlgebra) Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← hα, ← hφ]
    exact CommRingCat.isPushout_tensorProduct baseRing baseAlgebra' extensionAlgebra
  have e₁ := compatibility'.inl_isoIsPushout_hom _ _ compatibility.flip
  have e₂ := compatibility'.inr_isoIsPushout_hom _ _ compatibility.flip
  have : (baseScalar ⊗ₜ[baseRing] element : baseAlgebra' ⊗[baseRing] extensionAlgebra) = Algebra.TensorProduct.includeLeftRingHom baseScalar *
      Algebra.TensorProduct.includeRight element := by simp
  rw [IsPushout.tensorEquiv]
  change (compatibility'.isoIsPushout _ _ compatibility.flip).hom (baseScalar ⊗ₜ element) = _
  rw [this, map_mul]
  congr 1
  · exact congr($(e₁) baseScalar)
  · exact congr($(e₂) element)
