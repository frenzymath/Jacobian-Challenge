import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Jacobian.AlgebraicGeometry.Sites.Representability
import Jacobian.AlgebraicGeometry.Sites.OpenImmersion

/-!
# Representability of group presheaves by open charts

A small-valued Zariski sheaf of groups over a field is represented by a group
scheme if a representable open subfunctor has translates covering all
field-valued points. The same translates give open charts through every point
of any representing scheme. The field-valued coverage hypothesis is explicit;
these results do not construct the open subfunctor for a particular moduli problem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k]

/-- A representable open subfunctor whose translates cover field-valued points
represents a small-valued Zariski sheaf of groups by a group scheme. -/
theorem isRepresentable_of_representable_open_subfunctor
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1})
    (F : Subfunctor (G ⋙ forget GrpCat.{u + 1}))
    (hsmall : ∀ T, Small.{u} ((G ⋙ forget GrpCat.{u + 1}).obj T))
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (.of k)))
      (G ⋙ forget GrpCat.{u + 1}))
    (hFrep : F.toFunctor.IsRepresentable)
    (hFopen : (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} F.ι)
    (hgen : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
      ∃ g' : G.obj (.op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A),
      Nonempty ((G ⋙ forget GrpCat.{u + 1}).RepresentableBy A) := by
  let P := G ⋙ forget GrpCat.{u + 1}
  have : ∀ T, Small.{u} (P.obj T) := hsmall
  obtain ⟨A, ⟨eF⟩⟩ := hFrep.has_representation
  let r (T : Over (Spec (.of k))) (g : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
      G.obj (op T) :=
    (G.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom g
  have hr {T W : Over (Spec (.of k))} (a : W ⟶ T) (g) : (G.map a.op).hom (r T g) = r W g := by
    simp only [r, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp]
    congr 4
    ext
    simp
  have hP {T W : Over (Spec (.of k))} (a : W ⟶ T) (x : G.obj (op T)) :
      (G ⋙ forget GrpCat.{u + 1}).map a.op x = (G.map a.op).hom x := rfl
  let ξ₀ : G.obj (op A) := (eF.homEquiv (𝟙 A)).1
  have he {W : Over (Spec (.of k))} (b : W ⟶ A) : (eF.homEquiv b).1 = (G.map b.op).hom ξ₀ := by
    rw [← Category.comp_id b, eF.homEquiv_comp]
    rfl
  have hsymm {W : Over (Spec (.of k))} (z : P.obj (op W)) (hz : z ∈ F.obj (op W)) :
      (G.map (eF.homEquiv.symm (⟨z, hz⟩ : F.toFunctor.obj (op W))).op).hom ξ₀ = z := by
    rw [← he]
    exact congr_arg Subtype.val (eF.homEquiv.apply_symm_apply _)
  have : Small.{u} (G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) := hsmall _
  let ι := Shrink.{u} (G.obj (op (Over.mk (𝟙 (Spec (.of k))))))
  let g (i : ι) : G.obj (op (Over.mk (𝟙 (Spec (.of k))))) := (equivShrink _).symm i
  let ξ (i : ι) : P.obj (op A) := (r A (g i))⁻¹ * ξ₀
  have hξ {W : Over (Spec (.of k))} (i : ι) (b : W ⟶ A) :
      (G.map b.op).hom (ξ i) = (r W (g i))⁻¹ * (G.map b.op).hom ξ₀ := by
    rw [map_mul, map_inv, hr]
  have hinj (i : ι) {T : Over (Spec (.of k))} (a b : T ⟶ A)
      (h : P.map a.op (ξ i) = P.map b.op (ξ i)) : a = b := by
    simp only [P, hP] at h
    rw [hξ, hξ, mul_right_inj, ← he, ← he] at h
    exact eF.homEquiv.injective (Subtype.ext h)
  have hopen (i : ι) (T : Over (Spec (.of k))) (x : G.obj (op T)) : ∃ U : T.left.Opens,
      ∀ (W : Over (Spec (.of k))) (a : W ⟶ T),
        (∃ b : W ⟶ A, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U := by
    obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion hFopen T (r T (g i) * x)
    refine ⟨U, fun W a ↦ ?_⟩
    rw [← hU]
    simp only [P, hP, map_mul, hr]
    constructor
    · rintro ⟨b, hb⟩
      rw [hb, hξ, mul_inv_cancel_left, ← he]
      exact (eF.homEquiv b).2
    · intro h
      refine ⟨eF.homEquiv.symm (⟨_, h⟩ : F.toFunctor.obj (op W)), ?_⟩
      rw [hξ, hsymm, inv_mul_cancel_left]
  have hcov (T : Over (Spec (.of k))) (x : G.obj (op T)) (t : T.left) :
      ∃ (i : ι) (W : Over (Spec (.of k))) (a : W ⟶ T) (b : W ⟶ A),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i) := by
    let K := T.left.residueField t
    let φ : CommRingCat.of k ⟶ K := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
    let : Algebra k K := φ.hom.toAlgebra
    have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        T.left.fromSpecResidueField t ≫ T.hom := by
      rw [← Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)]
      rfl
    let a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T :=
      Over.homMk (T.left.fromSpecResidueField t) hK.symm
    obtain ⟨g', hg'⟩ := hgen K (P.map a.op x)
    refine ⟨equivShrink _ g', _, a, eF.homEquiv.symm (⟨_, hg'⟩ : F.toFunctor.obj _), ?_, ?_⟩
    · have h := Scheme.range_fromSpecResidueField t
      exact h.symm ▸ Set.mem_singleton t
    · simp only [P, hP]
      rw [hξ, hsymm]
      simp [g, r]
  obtain ⟨A', ⟨e⟩⟩ := (Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over P hG
    (fun _ : ι ↦ A) ξ hinj hopen hcov).has_representation
  exact ⟨A', GrpObj.ofRepresentableBy A' G e, ⟨e⟩⟩

/-- Every point of a representing scheme has an open chart isomorphic to the
scheme representing the open subfunctor, obtained by translation. -/
theorem exists_isOpenImmersion_of_representable_open_subfunctor
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1})
    (F : Subfunctor (G ⋙ forget GrpCat.{u + 1})) {A : Over (Spec (.of k))}
    (eF : F.toFunctor.RepresentableBy A)
    (hFopen : (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} F.ι)
    (hgen : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
      ∃ g' : G.obj (.op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))))
    {A' : Over (Spec (.of k))} (e' : (G ⋙ forget GrpCat.{u + 1}).RepresentableBy A')
    (a : A'.left) :
    ∃ ψ : A ⟶ A', IsOpenImmersion ψ.left ∧ a ∈ Set.range ψ.left.base := by
  let P := G ⋙ forget GrpCat.{u + 1}
  let r (T : Over (Spec (.of k))) (g : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
      G.obj (op T) :=
    (G.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom g
  have hr {T W : Over (Spec (.of k))} (c : W ⟶ T) (g) : (G.map c.op).hom (r T g) = r W g := by
    simp only [r, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp]
    congr 4
    ext
    simp
  have hP {T W : Over (Spec (.of k))} (c : W ⟶ T) (y : G.obj (op T)) :
      P.map c.op y = (G.map c.op).hom y := rfl
  let ξ₀ : G.obj (op A) := (eF.homEquiv (𝟙 A)).1
  have he {W : Over (Spec (.of k))} (b : W ⟶ A) : (eF.homEquiv b).1 = (G.map b.op).hom ξ₀ := by
    rw [← Category.comp_id b, eF.homEquiv_comp]
    rfl
  let x : G.obj (op A') := e'.homEquiv (𝟙 A')
  have he' {W : Over (Spec (.of k))} (c : W ⟶ A') : e'.homEquiv c = (G.map c.op).hom x := by
    rw [← Category.comp_id c, e'.homEquiv_comp]
    rfl
  let K := A'.left.residueField a
  let φ : CommRingCat.of k ⟶ K := Spec.preimage (A'.left.fromSpecResidueField a ≫ A'.hom)
  let : Algebra k K := φ.hom.toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      A'.left.fromSpecResidueField a ≫ A'.hom := by
    rw [← Spec.map_preimage (A'.left.fromSpecResidueField a ≫ A'.hom)]
    rfl
  let pa : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A' :=
    Over.homMk (A'.left.fromSpecResidueField a) hK.symm
  obtain ⟨g', hg'⟩ := hgen K (P.map pa.op x)
  obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion hFopen A' (r A' g' * x)
  have hUiff {W : Over (Spec (.of k))} (c : W ⟶ A') :
      r W g' * (G.map c.op).hom x ∈ F.obj (op W) ↔ Set.range c.left ⊆ U := by
    rw [← hU]
    simp only [P, hP, map_mul, hr]
  let ξ : G.obj (op A) := (r A g')⁻¹ * ξ₀
  let ψ : A ⟶ A' := e'.homEquiv.symm ξ
  have hψ : (G.map ψ.op).hom x = ξ := by
    rw [← he']
    exact e'.homEquiv.apply_symm_apply ξ
  have hξ {W : Over (Spec (.of k))} (b : W ⟶ A) :
      (G.map b.op).hom ξ = (r W g')⁻¹ * (G.map b.op).hom ξ₀ := by
    rw [map_mul, map_inv, hr]
  have hmono {W : Over (Spec (.of k))} (b₁ b₂ : W ⟶ A) (h : b₁ ≫ ψ = b₂ ≫ ψ) : b₁ = b₂ := by
    have h' := congrArg e'.homEquiv h
    rw [he', he', op_comp, op_comp, Functor.map_comp, Functor.map_comp, GrpCat.comp_apply,
      GrpCat.comp_apply, hψ, hξ, hξ, mul_right_inj, ← he, ← he] at h'
    exact eF.homEquiv.injective (Subtype.ext h')
  have hψU : Set.range ψ.left ⊆ U := by
    rw [← hUiff, hψ, mul_inv_cancel_left]
    exact (eF.homEquiv (𝟙 A)).2
  let Uo : Over (Spec (.of k)) := Over.mk (U.ι ≫ A'.hom)
  let ιU : Uo ⟶ A' := Over.homMk U.ι rfl
  have hιU : r Uo g' * (G.map ιU.op).hom x ∈ F.obj (op Uo) := by
    rw [hUiff]
    change Set.range U.ι ⊆ U
    rw [U.range_ι]
  let b : Uo ⟶ A := eF.homEquiv.symm ⟨_, hιU⟩
  have hb : b ≫ ψ = ιU := by
    refine e'.homEquiv.injective ?_
    rw [he', he', op_comp, Functor.map_comp, GrpCat.comp_apply, hψ, hξ, ← he,
      eF.homEquiv.apply_symm_apply]
    exact inv_mul_cancel_left _ _
  have hψU' : Set.range ψ.left ⊆ Set.range U.ι := by
    rw [U.range_ι]
    exact hψU
  let ψ' : A ⟶ Uo := Over.homMk (IsOpenImmersion.lift U.ι ψ.left hψU') (by
    simp only [Uo, Over.mk_hom]
    rw [IsOpenImmersion.lift_fac_assoc, Over.w])
  have hψ' : ψ' ≫ ιU = ψ := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  have h₁ : ψ' ≫ b = 𝟙 A := hmono _ _ (by rw [Category.assoc, hb, hψ', Category.id_comp])
  have h₂ : b ≫ ψ' = 𝟙 Uo := by
    ext1
    rw [← cancel_mono U.ι]
    change (b ≫ ψ' ≫ ιU).left = (𝟙 Uo ≫ ιU).left
    rw [hψ', hb, Category.id_comp]
  have : IsIso ψ' := ⟨b, h₁, h₂⟩
  have : IsIso ψ'.left := (Over.forget _).map_isIso ψ'
  refine ⟨ψ, ?_, ?_⟩
  · rw [← hψ', Over.comp_left]
    change IsOpenImmersion (ψ'.left ≫ U.ι)
    infer_instance
  · -- `a` lies in `U`, the image of `ψ`
    have ha : Set.range pa.left ⊆ U := by
      rw [← hUiff]
      exact hg'
    have : a ∈ Set.range pa.left := by
      have h := Scheme.range_fromSpecResidueField a
      exact h.symm ▸ Set.mem_singleton a
    have haU : a ∈ Set.range U.ι := by
      rw [U.range_ι]
      exact ha this
    obtain ⟨u, hu⟩ := haU
    refine ⟨b.left u, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb]
    exact hu

end AlgebraicGeometry
