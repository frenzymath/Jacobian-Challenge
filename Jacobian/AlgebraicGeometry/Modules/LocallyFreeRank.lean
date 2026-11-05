import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeAffine
import Jacobian.AlgebraicGeometry.Modules.LocalizedFreeRestriction

/-!
# Rank of finite locally free modules

Fixed local rank is preserved by pullback and can be read from the ranks of affine sections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The pullback of a finite locally free module of rank `r` is finite locally free of rank `r`. -/
instance isFiniteLocallyFreeOfRank_pullback (g : Y ⟶ X) (M : X.Modules) {r : ℕ}
    [M.IsFiniteLocallyFreeOfRank r] : ((pullback g).obj M).IsFiniteLocallyFreeOfRank r := by
  obtain ⟨ι, U, hU, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  refine isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun i ↦ (g ⁻¹ᵁ U i).ι) ?_ fun i ↦
    ⟨(restrictFunctorIsoPullback (g ⁻¹ᵁ U i).ι).app ((pullback g).obj M) ≪≫
      (pullbackComp (g ⁻¹ᵁ U i).ι g).app M ≪≫
      (pullbackCongr (morphismRestrict_ι g (U i)).symm).app M ≪≫
      (pullbackComp (g ∣_ U i) (U i).ι).symm.app M ≪≫
      (pullback (g ∣_ U i)).mapIso ((restrictFunctorIsoPullback (U i).ι).symm.app M ≪≫
        (e i).some) ≪≫
      pullbackFreeIso _ _⟩
  simp only [Scheme.Opens.opensRange_ι]
  rw [← Scheme.Hom.preimage_iSup, hU]
  rfl

/-- **Finite local freeness of rank `r` is local** for a family of open immersions covering `X`:
if the pullbacks of `M` along them are finite locally free of rank `r`, so is `M`. -/
theorem isFiniteLocallyFreeOfRank_of_isOpenImmersion (M : X.Modules) {r : ℕ} {ι : Type u}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, ((pullback (f i)).obj M).IsFiniteLocallyFreeOfRank r) :
    M.IsFiniteLocallyFreeOfRank r := by
  choose κ W hW e using fun i ↦
    have := h i
    IsFiniteLocallyFreeOfRank.exists_restrict_iso_free ((pullback (f i)).obj M) (r := r)
  refine isFiniteLocallyFreeOfRank_of_restrict_iso_free M
    (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ f j.1) ?_ fun j ↦
      ⟨(restrictFunctorComp (W j.1 j.2).ι (f j.1)).app M ≪≫
        (restrictFunctor (W j.1 j.2).ι).mapIso ((restrictFunctorIsoPullback (f j.1)).app M) ≪≫
        (e j.1 j.2).some⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hf.ge (Set.mem_univ x) : x ∈ ⨆ i, (f i).opensRange)
  obtain ⟨y, rfl⟩ := hi
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
    (by rw [hW i]; trivial : y ∈ ⨆ k, W i k)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, ⟨⟨y, hk⟩, rfl⟩⟩

/-- A quasi-coherent module on `Spec R` whose global sections are finitely presented, flat and of
rank `r` at every prime is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_rankAtStalk_eq {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] {r : ℕ} [Module.FinitePresentation R Γ(M, ⊤)] [Module.Flat R Γ(M, ⊤)]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk Γ(M, ⊤) p = r) :
    M.IsFiniteLocallyFreeOfRank r := by
  have hfree (p : PrimeSpectrum R) : ∃ a ∉ p.asIdeal,
      Nonempty (M.restrict (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))) ≅
        SheafOfModules.free (ULift.{u} (Fin r))) := by
    obtain ⟨a, ha, _⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant Γ(M, ⊤)
      p.asIdeal fun m _ ↦ (h _).trans (h p).symm
    obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact ha
    have : Nontrivial (Localization.Away a) := q.nontrivial
    have hrank : Module.finrank (Localization.Away a) (LocalizedModule.Away a Γ(M, ⊤)) = r := by
      have h₁ := congr_fun (Module.rankAtStalk_eq_finrank_of_free (R := Localization.Away a)
        (M := LocalizedModule.Away a Γ(M, ⊤))) q
      rw [Module.rankAtStalk_isBaseChange (IsLocalizedModule.isBaseChange (.powers a)
        (Localization.Away a) (LocalizedModule.mkLinearMap (.powers a) Γ(M, ⊤))) q, hq, h p] at h₁
      simpa using h₁.symm
    exact ⟨a, ha, nonempty_restrict_iso_free_of_localizedModule M a
      ((Module.finBasisOfFinrankEq _ _ hrank).repr ≪≫ₗ
        Finsupp.domLCongr Equiv.ulift.symm)⟩
  choose a ha e using hfree
  refine isFiniteLocallyFreeOfRank_of_restrict_iso_free M
    (fun p ↦ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a p))))) ?_ e
  refine eq_top_iff.2 fun p _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨p, ?_⟩
  rw [Hom.opensRange_localizationAway]
  exact ha p

/-- The sections of a finite locally free module of rank `r` over an affine open `U` have rank
`r` at every prime of `Γ(X, U)`: near every prime they localize to a free module of rank `r`. -/
theorem rankAtStalk_sections_eq (M : X.Modules) {r : ℕ} [M.IsFiniteLocallyFreeOfRank r]
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    Module.rankAtStalk Γ(M, U) p = r := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree M r
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree M
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  obtain ⟨_, _⟩ := finitePresentation_projective_sections M hU
  obtain ⟨ι, V, hV, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  have hxU : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨i, hxV⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hV.ge (Set.mem_univ (hU.fromSpec p)) : hU.fromSpec p ∈ ⨆ i, V i)
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨_, hxV⟩ hxU
  have hp : p ∈ PrimeSpectrum.basicOpen g := by
    rw [← hU.fromSpec_preimage_basicOpen]
    exact hxg
  let _ : Module Γ(X, U) Γ(M, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  have := isLocalizedModule_basicOpen M hU g
  have := hU.isLocalization_basicOpen g
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(M, X.basicOpen g) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  obtain ⟨q, rfl⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hp
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le g)).op
      map_add' := map_add _
      map_smul' := map_smul M _ }
  rw [← Module.rankAtStalk_isBaseChange (IsLocalizedModule.isBaseChange (.powers g) _ φ)]
  classical
  have : Nontrivial Γ(X, X.basicOpen g) := q.nontrivial
  rw [Module.rankAtStalk_eq_of_equiv (sectionsLinearEquivOfOverIsoFree
    ((overIsoFreeEquiv M _ _).symm (e i).some) hgV), Module.rankAtStalk_eq_finrank_of_free]
  simp

end AlgebraicGeometry.Scheme.Modules

namespace Module

/-- Finite presentation, flatness and the rank at stalks can be transported along a ring
isomorphism `e : R ≃+* R'` compatible with the actions of `R` and `R'` on `M`. -/
theorem finitePresentation_flat_rankAtStalk_of_ringEquiv {R R' M : Type*} [CommRing R]
    [CommRing R'] [AddCommGroup M] [Module R M] [Module R' M] (e : R ≃+* R')
    (he : ∀ (a : R) (m : M), a • m = e a • m) [Module.FinitePresentation R' M]
    [Module.Flat R' M] :
    Module.FinitePresentation R M ∧ Module.Flat R M ∧
      ∀ p : PrimeSpectrum R,
        rankAtStalk M p = rankAtStalk (R := R') M (p.comap e.symm.toRingHom) := by
  let := e.toRingHom.toAlgebra
  have : IsScalarTower R R' M := ⟨fun a b m ↦ by
    rw [Algebra.smul_def, mul_smul, he]
    rfl⟩
  let h : R ≃ₐ[R] R' := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  have : Module.FinitePresentation R R' := .of_equiv h.toLinearEquiv
  have : Module.Flat R R' := .of_linearEquiv h.toLinearEquiv.symm
  have : IsLocalization (⊥ : Submonoid R) R :=
    IsLocalization.self bot_le
  have : IsLocalization (⊥ : Submonoid R) R' := IsLocalization.isLocalization_of_algEquiv ⊥ h
  have := isLocalizedModule_id (⊥ : Submonoid R) M R'
  have hb : IsBaseChange R' (LinearMap.id : M →ₗ[R] M) :=
    IsLocalizedModule.isBaseChange ⊥ R' _
  have : Module.FinitePresentation R M := .trans R M R'
  have : Module.Flat R M := .trans R R' M
  refine ⟨inferInstance, inferInstance, fun p ↦ ?_⟩
  rw [rankAtStalk_isBaseChange hb]
  congr 1
  ext x
  simp [RingHom.algebraMap_toAlgebra]

end Module

namespace AlgebraicGeometry.Scheme.Modules

/-- The global sections of a finite locally free module of rank `r` on `Spec R` are finitely
presented, flat and of rank `r` at every prime. -/
theorem rankAtStalk_eq_of_isFiniteLocallyFreeOfRank {R : CommRingCat.{u}} (M : (Spec R).Modules)
    {r : ℕ} [M.IsFiniteLocallyFreeOfRank r] :
    Module.FinitePresentation R Γ(M, ⊤) ∧ Module.Flat R Γ(M, ⊤) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk Γ(M, ⊤) p = r := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  obtain ⟨_, _⟩ := finitePresentation_projective_sections M (isAffineOpen_top (Spec R))
  obtain ⟨h₁, h₂, h₃⟩ := Module.finitePresentation_flat_rankAtStalk_of_ringEquiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv (smul_top_eq M)
  refine ⟨h₁, h₂, fun p ↦ ?_⟩
  rw [h₃]
  exact rankAtStalk_sections_eq M (isAffineOpen_top (Spec R)) _

end AlgebraicGeometry.Scheme.Modules
