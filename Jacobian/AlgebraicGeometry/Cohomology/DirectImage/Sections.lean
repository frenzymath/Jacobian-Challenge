import Jacobian.AlgebraicGeometry.Cohomology.AcyclicResolution
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.LocalizedFreeRestriction
import Jacobian.CategoryTheory.Abelian.Injective.Cycles

/-!
# Sections of higher direct images over an affine base

For a quasi-compact separated morphism and a quasi-coherent module, global
sections of the higher direct images over an affine base compute the source
cohomology. The comparison is natural in the module and semilinear along
the map on global functions. In particular it respects the vector-space
structures for a scheme over a field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Comparison

/-- Global sections along an isomorphism of `𝒪_X`-modules. -/
noncomputable def appTopAddEquiv {M N : X.Modules} (e : M ≅ N) : Γ(M, ⊤) ≃+ Γ(N, ⊤) :=
  ((Modules.toPresheaf X).mapIso e).app (Opposite.op ⊤) |>.addCommGroupIsoToAddEquiv

/-- The pushforward of an injective `𝒪_X`-module is acyclic, being flasque. -/
lemma subsingleton_H_pushforward_of_injective (I : X.Modules) [Injective I] (m : ℕ) :
    Subsingleton (((pushforward f).obj I).H (m + 1)) :=
  have := isFlasque_of_injective I
  have : TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf.{u} T.ringCatSheaf).obj ((pushforward f).obj I)).obj :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque
      (f.base _* ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj I).obj))
  TopCat.Sheaf.IsFlasque.subsingleton_H m
    ((SheafOfModules.toSheaf.{u} T.ringCatSheaf).obj ((pushforward f).obj I))

variable [IsAffine T] [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- The cohomology sheaves of `f_* I`, for an injective resolution `I` of `ℱ`, are the higher
direct images of `ℱ`; over the affine `T` they are acyclic, being quasi-coherent. -/
lemma subsingleton_H_homology_pushforward (I : InjectiveResolution ℱ) (q m : ℕ) :
    Subsingleton ((HomologicalComplex.homology
      (((pushforward f).mapHomologicalComplex _).obj I.cocomplex) q).H (m + 1)) :=
  have := isQuasicoherent_higherDirectImage f ℱ q
  have : Subsingleton ((((pushforward f).rightDerived q).obj ℱ).H (m + 1)) :=
    subsingleton_H_succ_of_isAffine ((higherDirectImage f q).obj ℱ) m
  (H.mapLinearEquiv (I.isoRightDerivedObj (pushforward f) q).symm (m + 1)).injective.subsingleton

/-- **`Γ(T, R^{n+1} f_* ℱ) ≅ H^{n+1}(X, ℱ)`** computed with an injective resolution `I` of `ℱ`:
`Γ(T, Hⁿ⁺¹(f_* I)) = Hⁿ⁺¹(Γ(X, I)) = Hⁿ⁺¹(X, ℱ)`, the first identification because the terms
and the cohomology sheaves of `f_* I` are acyclic on the affine `T`, the second because the terms
of `I` are acyclic. -/
noncomputable def sectionsHigherDirectImageSuccAddEquiv (I : InjectiveResolution ℱ) (n : ℕ) :
    Γ((higherDirectImage f (n + 1)).obj ℱ, ⊤) ≃+ ℱ.H (n + 1) :=
  let L := ((pushforward f).mapHomologicalComplex _).obj I.cocomplex
  have hL : ∀ j m, Subsingleton ((L.X j).H (m + 1)) := fun j m ↦
    subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m
  (appTopAddEquiv (I.isoRightDerivedObj (pushforward f) (n + 1))).trans <|
  (homologySectionsAddEquiv L hL (subsingleton_H_homology_pushforward f ℱ I) n).trans <|
  (cyclesQuotientAddEquiv L n).trans <|
  (AddEquiv.refl (sectionsCycles I.cocomplex n ⧸ sectionsBoundaries I.cocomplex n)).trans <|
  (cyclesQuotientAddEquiv I.cocomplex n).symm.trans <|
  (H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
    (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm.trans <|
  H.mapAddEquiv I.isoCyclesZero.symm (n + 1)

lemma sectionsHigherDirectImageSuccAddEquiv_apply (I : InjectiveResolution ℱ) (n : ℕ)
    (x : Γ((higherDirectImage f (n + 1)).obj ℱ, ⊤)) :
    sectionsHigherDirectImageSuccAddEquiv f ℱ I n x =
      H.map I.isoCyclesZero.inv (n + 1) ((H.cyclesZeroSuccAddEquiv I.cocomplex
        I.cocomplex_exactAt_succ (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm
        ((cyclesQuotientAddEquiv I.cocomplex n).symm
          (cyclesQuotientAddEquiv (((pushforward f).mapHomologicalComplex _).obj I.cocomplex) n
            (homologySectionsAddEquiv (((pushforward f).mapHomologicalComplex _).obj I.cocomplex)
              (fun j m ↦ subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m)
              (subsingleton_H_homology_pushforward f ℱ I) n
              (((I.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤) x))))) :=
  rfl

set_option maxHeartbeats 1600000 in
-- identifying sections of `f_* Iⁿ` and of `Iⁿ` over `⊤` unfolds `f ⁻¹ᵁ ⊤`
/-- The comparison `Γ(T, R^{n+1} f_* ℱ) ≅ H^{n+1}(X, ℱ)` is natural in `ℱ`. -/
lemma sectionsHigherDirectImageSuccAddEquiv_naturality (𝒢 : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
    (I : InjectiveResolution ℱ) (J : InjectiveResolution 𝒢) (n : ℕ)
    (x : Γ((higherDirectImage f (n + 1)).obj ℱ, ⊤)) :
    sectionsHigherDirectImageSuccAddEquiv f 𝒢 J n
        (((higherDirectImage f (n + 1)).map φ).app ⊤ x) =
      H.map φ (n + 1) (sectionsHigherDirectImageSuccAddEquiv f ℱ I n x) := by
  let ψ := InjectiveResolution.desc φ J I
  let χ := ((pushforward f).mapHomologicalComplex _).map ψ
  have hK := I.cocomplex_exactAt_succ
  have hK' := J.cocomplex_exactAt_succ
  have hacyc : ∀ j m, Subsingleton ((I.cocomplex.X j).H (m + 1)) :=
    fun _ m ↦ subsingleton_H_of_injective _ m
  have hacyc' : ∀ j m, Subsingleton ((J.cocomplex.X j).H (m + 1)) :=
    fun _ m ↦ subsingleton_H_of_injective _ m
  have hL : ∀ j m, Subsingleton
      (((((pushforward f).mapHomologicalComplex _).obj I.cocomplex).X j).H (m + 1)) :=
    fun j m ↦ subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m
  have hL' : ∀ j m, Subsingleton
      (((((pushforward f).mapHomologicalComplex _).obj J.cocomplex).X j).H (m + 1)) :=
    fun j m ↦ subsingleton_H_pushforward_of_injective f (J.cocomplex.X j) m
  -- the derived functor side
  have h1 : ((J.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤)
      (((higherDirectImage f (n + 1)).map φ).app ⊤ x) =
      ((HomologicalComplex.homologyMap χ (n + 1)).app ⊤)
        (((I.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤) x) := by
    change ((((pushforward f).rightDerived (n + 1)).map φ ≫
      (J.isoRightDerivedObj (pushforward f) (n + 1)).hom).app ⊤) x = _
    rw [InjectiveResolution.isoRightDerivedObj_hom_naturality φ I J ψ
      (InjectiveResolution.desc_commutes_zero φ J I)]
    rfl
  let LI := ((pushforward f).mapHomologicalComplex _).obj I.cocomplex
  let a := homologySectionsAddEquiv LI hL (subsingleton_H_homology_pushforward f ℱ I) n
    (((I.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤) x)
  let b : sectionsCycles I.cocomplex n ⧸ sectionsBoundaries I.cocomplex n :=
    cyclesQuotientAddEquiv LI n a
  let c := (cyclesQuotientAddEquiv I.cocomplex n).symm b
  let w := (H.cyclesZeroSuccAddEquiv I.cocomplex hK hacyc n).symm c
  have hc : (cyclesQuotientAddEquiv J.cocomplex n).symm
      (QuotientAddGroup.map _ _ (sectionsCyclesMap ψ n) (sectionsBoundaries_le_comap ψ n) b) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) c := by
    rw [AddEquiv.symm_apply_eq, cyclesQuotientAddEquiv_naturality, AddEquiv.apply_symm_apply]
  have hw : (H.cyclesZeroSuccAddEquiv J.cocomplex hK' hacyc' n).symm
      (QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) c) =
      H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1) w := by
    rw [AddEquiv.symm_apply_eq, H.cyclesZeroSuccAddEquiv_naturality ψ hK hacyc hK' hacyc',
      AddEquiv.apply_symm_apply]
  have hc' : (cyclesQuotientAddEquiv J.cocomplex n).symm
      (QuotientAddGroup.map _ _ (sectionsCyclesMap χ n) (sectionsBoundaries_le_comap χ n)
        (cyclesQuotientAddEquiv LI n a)) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) c := hc
  have key : (H.cyclesZeroSuccAddEquiv J.cocomplex hK' hacyc' n).symm
      ((cyclesQuotientAddEquiv J.cocomplex n).symm
        (QuotientAddGroup.map _ _ (sectionsCyclesMap χ n) (sectionsBoundaries_le_comap χ n)
          (cyclesQuotientAddEquiv LI n a))) =
      H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1) w := by
    rw [hc', hw]
  rw [sectionsHigherDirectImageSuccAddEquiv_apply, sectionsHigherDirectImageSuccAddEquiv_apply, h1,
    homologySectionsAddEquiv_naturality χ hL (subsingleton_H_homology_pushforward f ℱ I) hL'
      (subsingleton_H_homology_pushforward f 𝒢 J), cyclesQuotientAddEquiv_naturality χ, key,
    ← H.map_comp_apply, ← H.map_comp_apply, InjectiveResolution.isoCyclesZero_inv_naturality]


/-- **`Γ(T, R⁰ f_* ℱ) ≅ H⁰(X, ℱ)`**: both are the global sections of `ℱ`. -/
noncomputable def sectionsHigherDirectImageZeroAddEquiv :
    Γ((higherDirectImage f 0).obj ℱ, ⊤) ≃+ ℱ.H 0 :=
  (appTopAddEquiv ((pushforward f).rightDerivedZeroIsoSelf.app ℱ)).trans
    (H.zeroLinearEquiv ℱ).symm.toAddEquiv

omit [IsAffine T] [QuasiCompact f] [IsSeparated f]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] in
lemma sectionsHigherDirectImageZeroAddEquiv_naturality (𝒢 : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
    (x : Γ((higherDirectImage f 0).obj ℱ, ⊤)) :
    sectionsHigherDirectImageZeroAddEquiv f 𝒢 (((higherDirectImage f 0).map φ).app ⊤ x) =
      H.map φ 0 (sectionsHigherDirectImageZeroAddEquiv f ℱ x) := by
  have h : (((pushforward f).rightDerivedZeroIsoSelf.app 𝒢).hom.app ⊤)
      (((higherDirectImage f 0).map φ).app ⊤ x) =
      (((pushforward f).map φ).app ⊤)
        (((pushforward f).rightDerivedZeroIsoSelf.app ℱ).hom.app ⊤ x) := by
    change ((((pushforward f).rightDerived 0).map φ ≫
      ((pushforward f).rightDerivedZeroIsoSelf.app 𝒢).hom).app ⊤) x = _
    rw [Iso.app_hom, (pushforward f).rightDerivedZeroIsoSelf.hom.naturality φ]
    rfl
  change (H.zeroLinearEquiv 𝒢).symm (((pushforward f).rightDerivedZeroIsoSelf.app 𝒢).hom.app ⊤
      (((higherDirectImage f 0).map φ).app ⊤ x)) =
    H.map φ 0 ((H.zeroLinearEquiv ℱ).symm
      (((pushforward f).rightDerivedZeroIsoSelf.app ℱ).hom.app ⊤ x))
  rw [h, LinearEquiv.symm_apply_eq, H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply]
  rfl

end Comparison

theorem exists_addEquiv_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] (q : ℕ) :
    ∃ e : ∀ (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ],
        Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q,
      ∀ (ℱ 𝒢 : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
        [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
        (x : Γ((higherDirectImage f q).obj ℱ, ⊤)),
        e 𝒢 (((higherDirectImage f q).map φ).app ⊤ x) = H.map φ q (e ℱ x) := by
  cases q with
  | zero =>
    exact ⟨fun ℱ _ ↦ sectionsHigherDirectImageZeroAddEquiv f ℱ,
      fun ℱ 𝒢 _ _ φ x ↦ sectionsHigherDirectImageZeroAddEquiv_naturality f ℱ 𝒢 φ x⟩
  | succ n =>
    exact ⟨fun ℱ _ ↦ sectionsHigherDirectImageSuccAddEquiv f ℱ (injectiveResolution ℱ) n,
      fun ℱ 𝒢 _ _ φ x ↦ sectionsHigherDirectImageSuccAddEquiv_naturality f ℱ 𝒢 φ _ _ n x⟩

/-- Over an affine base, the sections of a higher direct image are the cohomology
of the source, semilinearly along the map on global functions. Naturality of
the additive comparison implies compatibility with scalar endomorphisms. -/
theorem exists_bijective_semilinearMap_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ∃ e : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₛₗ[f.appTop.hom] ℱ.H q, Function.Bijective e := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_higherDirectImage_H f q
  refine ⟨{ toFun := e ℱ, map_add' := map_add _, map_smul' := fun a x ↦ ?_ }, (e ℱ).bijective⟩
  have h : a • x = ((higherDirectImage f q).map (ℱ.smulHom (f.appTop a))).app ⊤ x := by
    rw [higherDirectImage_map_smulHom, smulHom_app_apply]
    congr 1
    exact (congrArg (fun φ ↦ φ a) (T.presheaf.map_id _)).symm
  rw [h, he]
  rfl

/-- Over a field, sections of a higher direct image identify with source
cohomology as vector spaces over that field. -/
theorem nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] [IsSeparated (X ↘ Spec (.of K))]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty ((moduleSpecΓFunctor (R := .of K)).obj
      ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ) ≃ₗ[K] ℱ.H q) := by
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (X ↘ Spec (.of K)) ℱ q
  let M := (moduleSpecΓFunctor (R := .of K)).obj ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ)
  refine ⟨LinearEquiv.ofBijective (M := M)
    { toFun := e, map_add' := e.map_add, map_smul' := fun c x ↦ ?_ } he⟩
  let y : Γ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ, ⊤) := x
  have h : (c • x : M) = (Scheme.ΓSpecIso (.of K)).inv c • y := smul_top_eq (R := .of K) _ c y
  exact (congrArg e h).trans ((e.map_smulₛₗ _ y).trans
    (smul_H_eq_globalSectionsRingHom_smul K ℱ q c (e y)).symm)

end AlgebraicGeometry.Scheme.Modules
