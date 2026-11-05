import Jacobian.AlgebraicGeometry.GlobalSections.Rank
import Mathlib.Algebra.Algebra.Pi
import Mathlib.AlgebraicGeometry.Limits

/-!
# Splitting affine schemes by rational sections

Evaluation of global functions along rational sections gives algebra maps.
When joint evaluation is bijective, these sections exhibit the affine scheme
as a coproduct of copies of the base field and detect equality of morphisms.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section RationalPoints

variable {K : Type u} [Field K] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of K))

/-- Pull back global functions along an rational section. -/
def rationalPointEvaluation (t : Spec (.of K) ⟶ Z) (ht : t ≫ q = 𝟙 _) :
    letI := q.ΓAlgebra
    Γ(Z, ⊤) →ₐ[K] K := by
  letI := q.ΓAlgebra
  refine { (t.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom with commutes' := ?_ }
  intro r
  change (((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ t.appTop ≫
    (Scheme.ΓSpecIso (.of K)).hom).hom r) = r
  have hm : (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ t.appTop ≫
      (Scheme.ΓSpecIso (.of K)).hom = 𝟙 (CommRingCat.of K) := by
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, Category.id_comp,
      Category.assoc, Iso.inv_hom_id] using congrArg
        (fun v : Spec (.of K) ⟶ Spec (.of K) =>
          (Scheme.ΓSpecIso (.of K)).inv ≫ v.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom) ht
  exact congrArg (fun v : CommRingCat.of K ⟶ CommRingCat.of K => v r) hm

/-- On an affine scheme, distinct rational sections give distinct algebra maps. -/
theorem rationalPointEvaluation_injective {ι : Type u} [IsAffine Z]
    (t : ι → (Spec (.of K) ⟶ Z)) (ht : ∀ i, t i ≫ q = 𝟙 _)
    (hinj : Function.Injective t) :
    Function.Injective (fun i => rationalPointEvaluation q (t i) (ht i)) := by
  letI := q.ΓAlgebra
  intro i j h
  apply hinj
  apply ext_of_isAffine
  have hh := congrArg (fun a : Γ(Z, ⊤) →ₐ[K] K => CommRingCat.ofHom a.toRingHom) h
  change (t i).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom =
    (t j).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom at hh
  exact (cancel_mono (Scheme.ΓSpecIso (.of K)).hom).mp hh

/-- Bijective evaluation identifies the scheme with the coproduct of its rational sections. -/
theorem isIso_sigmaDesc_of_bijective_evaluation {ι : Type u} [Finite ι] [IsAffine Z]
    (t : ι → (Spec (.of K) ⟶ Z)) (ht : ∀ i, t i ≫ q = 𝟙 _)
    (heval : letI := q.ΓAlgebra
      Function.Bijective (AlgHom.pi (fun i => rationalPointEvaluation q (t i) (ht i)))) :
    IsIso (Sigma.desc t) := by
  letI := q.ΓAlgebra
  let a : Γ(Z, ⊤) ⟶ CommRingCat.of (ι → K) :=
    CommRingCat.ofHom (AlgHom.pi (fun i => rationalPointEvaluation q (t i) (ht i))).toRingHom
  letI : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr heval
  have hd : Sigma.desc t = sigmaSpec (fun _ : ι => CommRingCat.of K) ≫
      Spec.map a ≫ Z.isoSpec.inv := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp_assoc]
    change t i = Spec.map ((t i).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom) ≫ Z.isoSpec.inv
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom]
    simp only [Category.assoc, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hd]
  infer_instance

/-- A full family of rational sections detects morphism equality to
an arbitrary target. The affine product decomposition supplies the cover. -/
theorem hom_ext_of_bijective_evaluation {ι : Type u} [Finite ι] [IsAffine Z]
    (t : ι → (Spec (.of K) ⟶ Z)) (ht : ∀ i, t i ≫ q = 𝟙 _)
    (heval : letI := q.ΓAlgebra
      Function.Bijective (AlgHom.pi (fun i => rationalPointEvaluation q (t i) (ht i))))
    {W : Scheme.{u}} {a b : Z ⟶ W} (h : ∀ i, t i ≫ a = t i ≫ b) : a = b := by
  letI := isIso_sigmaDesc_of_bijective_evaluation q t ht heval
  apply (cancel_epi (Sigma.desc t)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [Sigma.ι_desc_assoc] using h i

end RationalPoints

end AlgebraicGeometry
