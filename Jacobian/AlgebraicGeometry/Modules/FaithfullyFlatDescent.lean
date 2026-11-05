import Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.PullbackTilde
import Jacobian.AlgebraicGeometry.Modules.Localization
import Jacobian.RingTheory.FaithfullyFlat.FamilyDescent

/-!
# Faithfully flat descent of affine module morphisms

Faithfully flat descent of modules identifies affine module-sheaf morphisms with compatible morphisms after base change.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TensorProduct CategoryTheory.Bicategory

namespace AlgebraicGeometry.Scheme.Modules

section

variable {R : CommRingCat.{u}}

/-- Morphisms out of a quasi-coherent module on an affine scheme are determined by their effect
on global sections. -/
lemma hom_ext_of_isQuasicoherent_Spec {M Q : (Spec R).Modules} [M.IsQuasicoherent]
    {α β : M ⟶ Q} (h : ∀ m : Γ(M, ⊤), α.app ⊤ m = β.app ⊤ m) : α = β := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  rw [← cancel_epi M.fromTildeΓ]
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  ext m
  change α.app ⊤ (M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m)) =
    β.app ⊤ (M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m))
  have e := fromTildeΓ_app_toOpen M m
  exact (congrArg (α.app ⊤) e).trans ((h m).trans (congrArg (β.app ⊤) e).symm)

/-- A linear map between the global sections of quasi-coherent modules on an affine scheme comes
from a morphism of modules. -/
lemma exists_hom_app_top_eq {M N : (Spec R).Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (χ : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = χ m := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  refine ⟨inv M.fromTildeΓ ≫ tilde.map χ ≫ N.fromTildeΓ, fun m ↦ ?_⟩
  have hm : (inv M.fromTildeΓ).app ⊤ m = tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m := by
    have k : ∀ x, (inv M.fromTildeΓ).app ⊤ (M.fromTildeΓ.app ⊤ x) = x := fun x ↦
      congr($(IsIso.hom_inv_id M.fromTildeΓ).app ⊤ x)
    exact (congrArg ((inv M.fromTildeΓ).app ⊤) (fromTildeΓ_app_toOpen M m)).symm.trans (k _)
  change N.fromTildeΓ.app ⊤ ((tilde.map χ).app ⊤ ((inv M.fromTildeΓ).app ⊤ m)) = χ m
  rw [hm]
  have h₂ : (tilde.map χ).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) =
      tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ (χ m) :=
    congr($(tilde.toOpen_map_app χ ⊤) m)
  rw [h₂]
  exact fromTildeΓ_app_toOpen N (χ m)

/-- A function between the global sections of quasi-coherent modules on an affine scheme which
is additive and linear for `R` comes from a morphism of modules. -/
lemma exists_hom_app_top_eq' {M N : (Spec R).Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (g : Γ(M, ⊤) →+ Γ(N, ⊤))
    (hsmul : ∀ (a : R) (m : Γ(M, ⊤)),
      g (((ΓSpecIso R).inv ≫ (Spec R).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op).hom a • m) =
        ((ΓSpecIso R).inv ≫ (Spec R).presheaf.map
          (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op).hom a • g m) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = g m := by
  let X := moduleSpecΓFunctor.obj M
  let Y := moduleSpecΓFunctor.obj N
  exact exists_hom_app_top_eq (@ModuleCat.ofHom R _ X Y _ X.isModule _ Y.isModule
    { toFun := g
      map_add' := g.map_add
      map_smul' a m := hsmul a m })

end

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Morphisms out of the pullback of a quasi-coherent module along `Spec B ⟶ Spec A` are
determined by their values on the images of global sections under the unit. -/
lemma pullback_hom_ext_Spec {M : (Spec (.of A)).Modules} [M.IsQuasicoherent]
    {Q : (Spec (.of B)).Modules}
    {α β : (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M ⟶ Q}
    (h : ∀ m : Γ(M, ⊤),
      α.app ⊤ (pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) M m) =
        β.app ⊤ (pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) M m)) :
    α = β := by
  apply hom_ext_of_isQuasicoherent_Spec (R := .of B)
  intro y
  obtain ⟨e, he⟩ := exists_linearEquiv_pullback_Spec (extensionAlgebra := B) M
  obtain ⟨t, rfl⟩ := e.surjective y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b m =>
    have : e (b ⊗ₜ m) = b • e (1 ⊗ₜ m) := by
      rw [← LinearEquiv.map_smul, smul_tmul', smul_eq_mul, mul_one]
    rw [this, he]
    exact (Hom.app_smul_of α ⊤ b _).trans
      ((congrArg (b • ·) (h m)).trans (Hom.app_smul_of β ⊤ b _).symm)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The two morphisms `Spec (B ⊗[A] B) ⟶ Spec B`. -/
noncomputable abbrev specTensorFst (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The two morphisms `Spec (B ⊗[A] B) ⟶ Spec B`. -/
noncomputable abbrev specTensorSnd (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)

lemma specTensorFst_comp :
    specTensorFst A B ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) := by
  rw [← Spec.map_comp]
  congr 1

lemma specTensorSnd_comp :
    specTensorSnd A B ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

/-- On global sections over `Spec B`, the unit of the adjunction for `Spec C ⟶ Spec B` is
semilinear along the ring map. -/
lemma pullbackΓ_smul_ringHom {C : Type u} [CommRing C] (ι : B →+* C)
    (P : (Spec (.of B)).Modules) (b : B) (x : Γ(P, ⊤)) :
    pullbackΓ (Spec.map (CommRingCat.ofHom ι)) P (b • x) =
      ι b • pullbackΓ (Spec.map (CommRingCat.ofHom ι)) P x :=
  letI := ι.toAlgebra
  pullbackΓ_smul (baseAlgebra := B) (extensionAlgebra := C) P b x

/-- Base change identifications transform the unit along `p : Spec C ⟶ Spec B` into `ι ⊗ 𝟙`
(stated for an abstract `p`, semilinear along `ι`). -/
lemma pullbackCompOfEq_hom_app_top_linearEquiv {C : Type u} [CommRing C] [Algebra A C]
    (ι : B →ₐ[A] C) (N : (Spec (.of A)).Modules) {fB : Spec (.of B) ⟶ Spec (.of A)}
    {fC : Spec (.of C) ⟶ Spec (.of A)} {p : Spec (.of C) ⟶ Spec (.of B)} (h : p ≫ fB = fC)
    (hp : ∀ (P : (Spec (.of B)).Modules) (b : B) (x : Γ(P, ⊤)),
      pullbackΓ p P (b • x) = ι b • pullbackΓ p P x)
    (eB : B ⊗[A] Γ(N, ⊤) ≃ₗ[B] Γ((pullback fB).obj N, ⊤))
    (heB : ∀ n, eB (1 ⊗ₜ n) = pullbackΓ fB N n)
    (eC : C ⊗[A] Γ(N, ⊤) ≃ₗ[C] Γ((pullback fC).obj N, ⊤))
    (heC : ∀ n, eC (1 ⊗ₜ n) = pullbackΓ fC N n) (t : B ⊗[A] Γ(N, ⊤)) :
    ((pullbackCompOfEq p fB fC h N).hom).app ⊤ (pullbackΓ p _ (eB t)) =
      eC (ι.toLinearMap.rTensor _ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b n =>
    have hb : eB (b ⊗ₜ n) = b • eB (1 ⊗ₜ n) := by
      rw [← LinearEquiv.map_smul, smul_tmul', smul_eq_mul, mul_one]
    have hc : eC (ι b ⊗ₜ n) = ι b • eC (1 ⊗ₜ n) := by
      rw [← LinearEquiv.map_smul, smul_tmul', smul_eq_mul, mul_one]
    rw [hb, heB, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hc, heC, hp,
      Hom.app_smul_of, pullbackCompOfEq_hom_app_pullbackΓ]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Morphisms out of `f^* M` agree if they agree on the images of global sections, when global
sections of `f^* M` are the base change of those of `M` (abstract version). -/
lemma pullback_hom_ext_of {f : Spec (.of B) ⟶ Spec (.of A)} {M : (Spec (.of A)).Modules}
    [((pullback f).obj M).IsQuasicoherent]
    (e : B ⊗[A] Γ(M, ⊤) ≃ₗ[B] Γ((pullback f).obj M, ⊤))
    (he : ∀ m, e (1 ⊗ₜ m) = pullbackΓ f M m) {Q : (Spec (.of B)).Modules}
    {α β : (pullback f).obj M ⟶ Q}
    (h : ∀ m : Γ(M, ⊤), α.app ⊤ (pullbackΓ f M m) = β.app ⊤ (pullbackΓ f M m)) : α = β := by
  apply hom_ext_of_isQuasicoherent_Spec (R := .of B)
  intro y
  obtain ⟨t, rfl⟩ := e.surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    have : e (b ⊗ₜ m) = b • e (1 ⊗ₜ m) := by
      rw [← LinearEquiv.map_smul, smul_tmul', smul_eq_mul, mul_one]
    rw [this, he, Hom.app_smul_of, Hom.app_smul_of, h]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1000000 in
open Pseudofunctor in
/-- **Descent of morphisms along a faithfully flat map of affine schemes** (abstract version):
for `f : Spec B ⟶ Spec A` with `A → B` faithfully flat, `f^*` is fully faithful on
quasi-coherent modules relative to descent data. -/
theorem bijective_toDescentData_map_of [Module.FaithfullyFlat A B]
    {f : Spec (.of B) ⟶ Spec (.of A)} {p₁ p₂ : Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B)}
    {q : Spec (.of (B ⊗[A] B)) ⟶ Spec (.of A)} (h₁ : p₁ ≫ f = q) (h₂ : p₂ ≫ f = q)
    (hf : ∀ (P : (Spec (.of A)).Modules) (a : A) (x : Γ(P, ⊤)),
      pullbackΓ f P (a • x) = algebraMap A B a • pullbackΓ f P x)
    (hp₁ : ∀ (P : (Spec (.of B)).Modules) (b : B) (x : Γ(P, ⊤)),
      pullbackΓ p₁ P (b • x) =
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) b • pullbackΓ p₁ P x)
    (hp₂ : ∀ (P : (Spec (.of B)).Modules) (b : B) (x : Γ(P, ⊤)),
      pullbackΓ p₂ P (b • x) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom b • pullbackΓ p₂ P x)
    (M N : (Spec (.of A)).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [((pullback f).obj M).IsQuasicoherent]
    (eM : B ⊗[A] Γ(M, ⊤) ≃ₗ[B] Γ((pullback f).obj M, ⊤))
    (heM : ∀ m, eM (1 ⊗ₜ m) = pullbackΓ f M m)
    (eN : B ⊗[A] Γ(N, ⊤) ≃ₗ[B] Γ((pullback f).obj N, ⊤))
    (heN : ∀ n, eN (1 ⊗ₜ n) = pullbackΓ f N n)
    (eq : (B ⊗[A] B) ⊗[A] Γ(N, ⊤) ≃ₗ[B ⊗[A] B] Γ((pullback q).obj N, ⊤))
    (heq : ∀ n, eq (1 ⊗ₜ n) = pullbackΓ q N n) :
    Function.Bijective ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ f)).map :
      (M ⟶ N) → _) := by
  have hinj : ∀ n n' : Γ(N, ⊤), pullbackΓ f N n = pullbackΓ f N n' → n = n' := by
    intro n n' hnn
    rw [← heN, ← heN] at hnn
    have h0 : (1 : B) ⊗ₜ[A] (n - n') = 0 := by
      rw [tmul_sub, eN.injective hnn, sub_self]
    exact sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := A) (A := B)
      (M := Γ(N, ⊤)) _).mp h0)
  constructor
  · intro α β hαβ
    have h0 : (pullback f).map α = (pullback f).map β :=
      congr_arg (fun φ ↦ DescentData.Hom.hom φ ()) hαβ
    apply hom_ext_of_isQuasicoherent_Spec (R := .of A)
    intro m
    apply hinj
    rw [← pullbackΓ_naturality f α m, ← pullbackΓ_naturality f β m, h0]
  · intro ψ
    obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : (pullback f).obj M ⟶ (pullback f).obj N, ψ.hom () = ψ₀ :=
      ⟨ψ.hom (), rfl⟩
    have hc := ψ.comm q (i₁ := ()) (i₂ := ()) p₁ p₂ h₁ h₂
    rw [hψ₀] at hc
    have hD : ∀ P : (Spec (.of A)).Modules,
        ((modulesPseudofunctor.toDescentData fun _ : Unit ↦ f).obj P).hom q (i₁ := ()) (i₂ := ())
          p₁ p₂ h₁ h₂ =
          (pullbackCompOfEq p₁ f q h₁ P).hom ≫ (pullbackCompOfEq p₂ f q h₂ P).inv := by
      intro P
      rw [← modulesPseudofunctor_mapComp'_inv_app_eq f p₁ q h₁,
        ← modulesPseudofunctor_mapComp'_hom_app_eq f p₂ q h₂]
      rfl
    rw [hD, hD] at hc
    have hc' : (pullback p₁).map ψ₀ ≫ (pullbackCompOfEq p₁ f q h₁ N).hom ≫
        (pullbackCompOfEq p₂ f q h₂ N).inv = ((pullbackCompOfEq p₁ f q h₁ M).hom ≫
          (pullbackCompOfEq p₂ f q h₂ M).inv) ≫ (pullback p₂).map ψ₀ := hc
    have hx : ∀ m : Γ(M, ⊤), ∃ n : Γ(N, ⊤), ψ₀.app ⊤ (pullbackΓ f M m) = pullbackΓ f N n := by
      intro m
      have e1 := congr(Hom.app $hc' ⊤ (pullbackΓ p₁ _ (pullbackΓ f M m)))
      simp only [Hom.comp_app, ConcreteCategory.comp_apply, pullbackΓ_naturality,
        pullbackCompOfEq_hom_app_pullbackΓ, pullbackCompOfEq_inv_app_pullbackΓ] at e1
      have e2 := congrArg (Hom.app (pullbackCompOfEq p₂ f q h₂ N).hom ⊤) e1
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app,
        ConcreteCategory.id_apply] at e2
      generalize ψ₀.app ⊤ (pullbackΓ f M m) = x at e2 ⊢
      obtain ⟨t, rfl⟩ := eN.surjective x

      rw [pullbackCompOfEq_hom_app_top_linearEquiv
          (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) N h₁ hp₁ eN heN eq heq,
        pullbackCompOfEq_hom_app_top_linearEquiv
          (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) N h₂ hp₂ eN heN eq heq] at e2
      obtain ⟨n, rfl⟩ := Module.FaithfullyFlat.exists_eq_one_tmul_of_rTensor_eq t
        (eq.injective e2)
      exact ⟨n, heN n⟩
    have hinj' : Function.Injective (pullbackΓ f N).hom := fun n n' h ↦ hinj n n' h
    let e := AddMonoidHom.ofInjective hinj'
    let g : Γ(M, ⊤) →+ Γ(N, ⊤) := e.symm.toAddMonoidHom.comp
      (((ψ₀.app ⊤).hom.comp (pullbackΓ f M).hom).codRestrict (pullbackΓ f N).hom.range fun m ↦ by
        obtain ⟨n, hn⟩ := hx m
        exact ⟨n, hn.symm⟩)
    have hg : ∀ m, ψ₀.app ⊤ (pullbackΓ f M m) = pullbackΓ f N (g m) := by
      intro m
      have := congrArg Subtype.val (e.apply_symm_apply ⟨_, (hx m).elim fun n hn ↦ ⟨n, hn.symm⟩⟩)
      exact this.symm
    obtain ⟨χ, hχ⟩ := exists_hom_app_top_eq' (R := .of A) g (fun a m ↦ by
      apply hinj
      have h1 := hf M a m
      have h2 := hf N a (g m)
      rw [smul_of_def] at h1 h2
      exact (hg _).symm.trans ((congrArg (ψ₀.app ⊤) h1).trans
        ((Hom.app_smul_of ψ₀ ⊤ _ _).trans ((congrArg _ (hg m)).trans h2.symm))))
    refine ⟨χ, ?_⟩
    ext ⟨⟩
    rw [hψ₀]
    change (pullback f).map χ = ψ₀
    refine pullback_hom_ext_of eM heM fun m ↦ ?_
    rw [pullbackΓ_naturality, hχ, hg]

set_option maxHeartbeats 1000000 in
/-- **Descent of morphisms along a faithfully flat map of affine schemes**: for `A → B`
faithfully flat, pulling back along `Spec B ⟶ Spec A` is fully faithful on quasi-coherent
modules relative to descent data. -/
theorem bijective_toDescentData_map_Spec [Module.FaithfullyFlat A B]
    (M N : (Spec (.of A)).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((modulesPseudofunctor.toDescentData
      (fun _ : Unit ↦ Spec.map (CommRingCat.ofHom (algebraMap A B)))).map : (M ⟶ N) → _) := by
  obtain ⟨eM, heM⟩ := exists_linearEquiv_pullback_Spec (extensionAlgebra := B) M
  obtain ⟨eN, heN⟩ := exists_linearEquiv_pullback_Spec (extensionAlgebra := B) N
  obtain ⟨eq, heq⟩ := exists_linearEquiv_pullback_Spec (extensionAlgebra := B ⊗[A] B) N
  refine bijective_toDescentData_map_of (f := Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (p₁ := specTensorFst A B) (p₂ := specTensorSnd A B)
    (q := Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))))
    specTensorFst_comp specTensorSnd_comp ?_ ?_ ?_ M N eM heM eN heN eq heq
  · exact fun P a x ↦ pullbackΓ_smul P a x
  · exact fun P b x ↦ pullbackΓ_smul_ringHom
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) P b x
  · exact fun P b x ↦ pullbackΓ_smul_ringHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom P b x

end Algebra

end AlgebraicGeometry.Scheme.Modules
