import Jacobian.AlgebraicGeometry.Cohomology.Affine.Pushforward
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Jacobian.AlgebraicGeometry.Cohomology.LongExact
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness and dévissage for scheme cohomology

Cohomology over `Spec A` is regarded as an `A`-module through the structure morphism.
Finite generation is invariant under isomorphism and affine pushforward, is preserved by
finite coproducts, and satisfies short exact sequence and kernel-cokernel dévissage.
For a finite morphism, finite presentation of the coefficient sheaf already gives finite
cohomology, by the affine vanishing theorem.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {A : Type u} [CommRing A]

/-- The action on cohomology induced by a structure morphism to `Spec A`. -/
abbrev moduleHOfSpec (p : X ⟶ Spec (.of A)) (M : X.Modules) (q : ℕ) : Module A (M.H q) :=
  Module.compHom (M.H q) ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop).hom

/-- Finite generation in every degree over the affine base of a scheme. -/
def HasFiniteH (p : X ⟶ Spec (.of A)) (M : X.Modules) : Prop :=
  ∀ q : ℕ, letI := moduleHOfSpec p M q; Module.Finite A (M.H q)

variable {p : X ⟶ Spec (.of A)}

/-- All cohomology groups of a zero sheaf vanish. -/
lemma subsingleton_H_of_isZero {M : X.Modules} (zeroSheaf : IsZero M) (q : ℕ) :
    Subsingleton (M.H q) :=
  subsingleton_of_forall_eq 0 fun cohomologyClass ↦ by
    simpa only [H.map_id_apply, H.map_zero_apply] using
      congrArg (fun coefficientMap : M ⟶ M ↦ H.map coefficientMap q cohomologyClass)
        (zeroSheaf.eq_of_src (𝟙 M) 0)

/-- A zero sheaf has finite cohomology over every affine base. -/
lemma HasFiniteH.of_isZero {M : X.Modules} (zeroSheaf : IsZero M) : HasFiniteH p M := by
  intro q
  letI := moduleHOfSpec p M q
  letI := subsingleton_H_of_isZero zeroSheaf q
  infer_instance

/-- An isomorphism of coefficient sheaves preserves finite generation in each degree. -/
lemma finite_H_of_iso {M N : X.Modules} (comparison : M ≅ N) (degree : ℕ)
    (finiteSource : letI := moduleHOfSpec p M degree; Module.Finite A (M.H degree)) :
    letI := moduleHOfSpec p N degree; Module.Finite A (N.H degree) := by
  letI := moduleHOfSpec p M degree
  letI := moduleHOfSpec p N degree
  letI := finiteSource
  let linearComparison : M.H degree ≃ₗ[A] N.H degree :=
    { (H.mapLinearEquiv comparison degree).toAddEquiv with
      map_smul' := fun scalar cohomologyClass ↦
        (H.mapLinearEquiv comparison degree).map_smul _ cohomologyClass }
  exact Module.Finite.equiv linearComparison

/-- An isomorphism of coefficient sheaves preserves finite generation of cohomology. -/
lemma HasFiniteH.of_iso {M N : X.Modules} (e : M ≅ N) (h : HasFiniteH p M) :
    HasFiniteH p N := fun degree ↦ finite_H_of_iso (p := p) e degree (h degree)

/-- The map on cohomology is linear over the affine base. -/
abbrev H.mapOfSpec {M N : X.Modules} (φ : M ⟶ N) (q : ℕ) :
    letI := moduleHOfSpec p M q
    letI := moduleHOfSpec p N q
    M.H q →ₗ[A] N.H q :=
  letI := moduleHOfSpec p M q
  letI := moduleHOfSpec p N q
  { toFun := H.map φ q
    map_add' := (H.map φ q).map_add
    map_smul' := fun _ x ↦ H.map_smul φ q _ x }

/-- Finite coproducts of coefficient sheaves preserve finite generation in each degree. -/
lemma finite_H_sigma {indexType : Type u} [Finite indexType]
    (modules : indexType → X.Modules) (degree : ℕ)
    (finiteCohomology : ∀ index, letI := moduleHOfSpec p (modules index) degree;
      Module.Finite A ((modules index).H degree)) :
    letI := moduleHOfSpec p (∐ modules) degree;
      Module.Finite A ((∐ modules).H degree) := by
  obtain ⟨count, ⟨indexEquiv⟩⟩ := Finite.exists_equiv_fin indexType
  suffices finiteIndexed : ∀ reindexedModules : Fin count → X.Modules,
      (∀ index, letI := moduleHOfSpec p (reindexedModules index) degree;
        Module.Finite A ((reindexedModules index).H degree)) →
      letI := moduleHOfSpec p (∐ reindexedModules) degree;
        Module.Finite A ((∐ reindexedModules).H degree) from
    finite_H_of_iso (p := p) (Sigma.reindex indexEquiv.symm modules) degree
      (finiteIndexed (modules ∘ indexEquiv.symm) fun index ↦
        finiteCohomology (indexEquiv.symm index))
  intro reindexedModules finiteReindexed
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  refine finite_H_of_iso (p := p) (biproduct.isoCoproduct reindexedModules) degree ?_
  letI := moduleHOfSpec p (⨁ reindexedModules) degree
  letI scalarActions (index : Fin count) :=
    moduleHOfSpec p (reindexedModules index) degree
  let inclusions (index : Fin count) :
      (reindexedModules index).H degree →ₗ[A] (⨁ reindexedModules).H degree :=
    H.mapOfSpec (p := p) (biproduct.ι reindexedModules index) degree
  have generated : ⨆ index, Submodule.map (inclusions index) ⊤ = ⊤ := by
    refine eq_top_iff.2 fun cohomologyClass _ ↦ ?_
    have decomposition : H.map (∑ index,
        biproduct.π reindexedModules index ≫ biproduct.ι reindexedModules index)
        degree cohomologyClass = cohomologyClass := by
      rw [biproduct.total]
      exact H.map_id_apply _ _ cohomologyClass
    rw [← decomposition, H.map_sum_apply]
    exact Submodule.sum_mem _ fun index _ ↦ Submodule.mem_iSup_of_mem index
      ⟨H.map (biproduct.π reindexedModules index) degree cohomologyClass,
        trivial, (H.map_comp_apply _ _ degree cohomologyClass).symm⟩
  exact ⟨generated ▸ Submodule.fg_iSup _ fun index ↦
    (finiteReindexed index).fg_top.map (inclusions index)⟩

/-- Finite generation of the outer cohomology groups implies that of the middle group. -/
lemma finite_H_X₂_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₁ : letI := moduleHOfSpec p S.X₁ q; Module.Finite A (S.X₁.H q))
    (h₃ : letI := moduleHOfSpec p S.X₃ q; Module.Finite A (S.X₃.H q)) :
    letI := moduleHOfSpec p S.X₂ q; Module.Finite A (S.X₂.H q) := by
  letI := moduleHOfSpec p S.X₁ q
  letI := moduleHOfSpec p S.X₂ q
  letI := moduleHOfSpec p S.X₃ q
  letI := h₁
  letI := h₃
  let f : S.X₁.H q →ₗ[A] S.X₂.H q := H.mapOfSpec (p := p) S.f q
  let g : S.X₂.H q →ₗ[A] S.X₃.H q := H.mapOfSpec (p := p) S.g q
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    exact SetLike.ext_iff.1 (H.ker_map_g_eq_range_map_f hS q) x
  haveI : _root_.IsNoetherian A (S.X₃.H q) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, hker, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

/-- Finite generation of the second and preceding third cohomology groups implies that
of the first group; in degree zero only the second group is needed. -/
lemma finite_H_X₁_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : letI := moduleHOfSpec p S.X₂ q; Module.Finite A (S.X₂.H q))
    (h₃ : ∀ q' : ℕ, q' + 1 = q →
      letI := moduleHOfSpec p S.X₃ q'; Module.Finite A (S.X₃.H q')) :
    letI := moduleHOfSpec p S.X₁ q; Module.Finite A (S.X₁.H q) := by
  letI := moduleHOfSpec p S.X₁ q
  letI := moduleHOfSpec p S.X₂ q
  letI := h₂
  let f : S.X₁.H q →ₗ[A] S.X₂.H q := H.mapOfSpec (p := p) S.f q
  haveI : _root_.IsNoetherian A (S.X₂.H q) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq]
  cases q with
  | zero =>
    have hinj : LinearMap.ker f = ⊥ :=
      LinearMap.ker_eq_bot.2 (H.injective_map_zero_of_shortExact hS)
    rw [hinj]
    exact Submodule.fg_bot
  | succ q =>
    letI := moduleHOfSpec p S.X₃ q
    haveI := h₃ q rfl
    let δ : S.X₃.H q →ₗ[A] S.X₁.H (q + 1) :=
      { toFun := H.δ hS q
        map_add' := (H.δ hS q).map_add
        map_smul' := fun _ x ↦ H.δ_smul hS q _ x }
    have hker : LinearMap.ker f = LinearMap.range δ := by
      ext x
      exact SetLike.ext_iff.1 (H.ker_map_f_eq_range_δ hS q) x
    rw [hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map δ

/-- Finite generation of the second and next first cohomology groups implies that
of the third group. -/
lemma finite_H_X₃_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : letI := moduleHOfSpec p S.X₂ q; Module.Finite A (S.X₂.H q))
    (h₁ : letI := moduleHOfSpec p S.X₁ (q + 1); Module.Finite A (S.X₁.H (q + 1))) :
    letI := moduleHOfSpec p S.X₃ q; Module.Finite A (S.X₃.H q) := by
  letI := moduleHOfSpec p S.X₁ (q + 1)
  letI := moduleHOfSpec p S.X₂ q
  letI := moduleHOfSpec p S.X₃ q
  letI := h₂
  letI := h₁
  let g : S.X₂.H q →ₗ[A] S.X₃.H q := H.mapOfSpec (p := p) S.g q
  let δ : S.X₃.H q →ₗ[A] S.X₁.H (q + 1) :=
    { toFun := H.δ hS q
      map_add' := (H.δ hS q).map_add
      map_smul' := fun _ x ↦ H.δ_smul hS q _ x }
  have hker : LinearMap.ker δ = LinearMap.range g := by
    ext x
    exact SetLike.ext_iff.1 (H.ker_δ_eq_range_map_g hS q) x
  haveI : _root_.IsNoetherian A (S.X₁.H (q + 1)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, hker, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map g

/-- In a short exact sequence, finite cohomology of any two sheaves implies finite
cohomology of the third. -/
lemma hasFiniteH_of_shortExact [IsNoetherianRing A] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) :
    (HasFiniteH p S.X₁ ∧ HasFiniteH p S.X₃ → HasFiniteH p S.X₂) ∧
      (HasFiniteH p S.X₂ ∧ HasFiniteH p S.X₃ → HasFiniteH p S.X₁) ∧
      (HasFiniteH p S.X₁ ∧ HasFiniteH p S.X₂ → HasFiniteH p S.X₃) := by
  refine ⟨fun h q ↦ finite_H_X₂_of_shortExact (p := p) hS q (h.1 q) (h.2 q),
    (fun h q ↦ finite_H_X₁_of_shortExact (p := p) hS q (h.1 q) fun q' _ ↦ h.2 q'),
    fun h q ↦ finite_H_X₃_of_shortExact (p := p) hS q (h.2 q) (h.1 (q + 1))⟩

/-- Dévissage through the image of a morphism: finite cohomology of the kernel,
cokernel and target implies finite cohomology of the source. -/
lemma HasFiniteH.of_hom [IsNoetherianRing A] {M N : X.Modules} (φ : M ⟶ N)
    (hK : HasFiniteH p (kernel φ)) (hC : HasFiniteH p (cokernel φ))
    (hN : HasFiniteH p N) : HasFiniteH p M := by
  have hS₂ : (ShortComplex.cokernelSequence (image.ι φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
      (inferInstanceAs (Mono (image.ι φ))) (inferInstanceAs (Epi (cokernel.π (image.ι φ))))
  have hS₁ : (ShortComplex.kernelSequence (factorThruImage φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
      (inferInstanceAs (Mono (kernel.ι (factorThruImage φ))))
      (inferInstanceAs (Epi (factorThruImage φ)))
  have hC' : HasFiniteH p (cokernel (image.ι φ)) := hC.of_iso (cokernelImageι φ).symm
  have hK' : HasFiniteH p (kernel (factorThruImage φ)) :=
    hK.of_iso (kernelFactorThruImage φ).symm
  have hI : HasFiniteH p (image φ) := fun q ↦
    finite_H_X₁_of_shortExact (p := p) hS₂ q (hN q) fun q' _ ↦ hC' q'
  exact fun q ↦ finite_H_X₂_of_shortExact (p := p) hS₁ q (hK' q) (hI q)

set_option maxHeartbeats 800000 in
/-- Finiteness of cohomology is invariant under affine pushforward of quasi-coherent sheaves. -/
lemma hasFiniteH_pushforward_iff {Y : Scheme.{u}} (g : X ⟶ Y) [IsAffineHom g]
    (p : Y ⟶ Spec (.of A)) (M : X.Modules) [M.IsQuasicoherent] :
    HasFiniteH p ((pushforward g).obj M) ↔ HasFiniteH (g ≫ p) M := by
  have comparison (q : ℕ) :
      letI := moduleHOfSpec (g ≫ p) M q
      letI := moduleHOfSpec p ((pushforward g).obj M) q
      Nonempty (M.H q ≃ₗ[A] ((pushforward g).obj M).H q) := by
    letI := moduleHOfSpec (g ≫ p) M q
    letI := moduleHOfSpec p ((pushforward g).obj M) q
    obtain ⟨e⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom g q
    let abelianSheaf : (cechAcyclicOnAffines X).FullSubcategory :=
      ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj M,
        cechAcyclicOnAffines_of_isQuasicoherent M⟩
    let additiveComparison : M.H q ≃+ ((pushforward g).obj M).H q :=
      (e.app abelianSheaf).addCommGroupIsoToAddEquiv
    refine ⟨{ additiveComparison with
      map_smul' := fun a x ↦ ?_ }⟩
    let r : Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop) a
    let scalarMap : abelianSheaf ⟶ abelianSheaf :=
      ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (M.smulHom (g.appTop r)))
    have scalarNaturality := NatTrans.naturality_apply e.hom scalarMap x
    have hr : ((Scheme.ΓSpecIso (.of A)).inv ≫ (g ≫ p).appTop) a = g.appTop r := by
      rw [Scheme.Hom.comp_appTop]
      rfl
    change e.hom.app abelianSheaf
        (H.map (M.smulHom (((Scheme.ΓSpecIso (.of A)).inv ≫ (g ≫ p).appTop) a)) q x) =
      H.map (((pushforward g).obj M).smulHom r) q (e.hom.app abelianSheaf x)
    rw [hr, ← pushforward_map_smulHom]
    exact scalarNaturality
  refine ⟨fun h q ↦ ?_, fun h q ↦ ?_⟩
  · letI := moduleHOfSpec (g ≫ p) M q
    letI := moduleHOfSpec p ((pushforward g).obj M) q
    haveI := h q
    exact Module.Finite.equiv (comparison q).some.symm
  · letI := moduleHOfSpec (g ≫ p) M q
    letI := moduleHOfSpec p ((pushforward g).obj M) q
    haveI := h q
    exact Module.Finite.equiv (comparison q).some

/-- A finitely presented quasi-coherent sheaf on a scheme finite over `Spec A` has
finite cohomology over `A`. -/
theorem hasFiniteH_of_isFinite (p : X ⟶ Spec (.of A)) [IsFinite p]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFinitePresentation] : HasFiniteH p M := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  let σ : A →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop).hom
  letI : Algebra A Γ(X, ⊤) := σ.toAlgebra
  have hσ : σ.Finite := p.finite_appTop.comp
    (RingHom.Finite.of_surjective (Scheme.ΓSpecIso (.of A)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)
  letI : Module.Finite A Γ(X, ⊤) := hσ
  letI : Module.FinitePresentation Γ(X, ⊤) Γ(M, ⊤) :=
    finitePresentation_sections_of_isFinitePresentation M (isAffineOpen_top X)
  letI : Module A Γ(M, ⊤) := Module.compHom Γ(M, ⊤) σ
  letI : IsScalarTower A Γ(X, ⊤) Γ(M, ⊤) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Finite A Γ(M, ⊤) := Module.Finite.trans Γ(X, ⊤) Γ(M, ⊤)
  intro q
  letI := moduleHOfSpec p M q
  cases q with
  | zero =>
    let e : M.H 0 ≃ₗ[A] Γ(M, ⊤) :=
      { (H.zeroLinearEquiv M).toAddEquiv with
        map_smul' := fun a x ↦ (H.zeroLinearEquiv M).map_smul (σ a) x }
    exact Module.Finite.equiv e.symm
  | succ q =>
    haveI := subsingleton_H_succ_of_isAffine M q
    infer_instance

end AlgebraicGeometry.Scheme.Modules
