import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.AlgebraicGeometry.Modules.Free
import Jacobian.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Local trivializations of finite locally free module sheaves

Fixed-rank local freeness is equivalent to freeness on an open covering and is
preserved by restriction to open subschemes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
/-- `M.over U` is free of rank `r` if and only if the restriction of `M` to `U` is. -/
noncomputable def overIsoFreeEquiv (M : X.Modules) (U : X.Opens) (I : Type u) :
    (M.over U ≅ SheafOfModules.free I) ≃ (M.restrict U.ι ≅ SheafOfModules.free I) where
  toFun e := ((overFunctorEquiv U).app M).symm ≪≫ (overEquiv U).functor.mapIso e ≪≫
    (SheafOfModules.mapFreeIso _ I ((overEquivObjUnitIso U).symm)).symm
  invFun e := (overEquiv U).functor.preimageIso (((overFunctorEquiv U).app M) ≪≫ e ≪≫
    SheafOfModules.mapFreeIso _ I ((overEquivObjUnitIso U).symm))
  left_inv e := by ext1; simp
  right_inv e := by ext1; simp

/-- The restriction of a free module along an open immersion is free. -/
noncomputable def restrictFreeIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (I : Type u) :
    restrict (SheafOfModules.free (R := X.ringCatSheaf) I) f ≅ SheafOfModules.free I :=
  (restrictFunctorIsoPullback f).app _ ≪≫ pullbackFreeIso f I

/-- Restricting along a composite of open immersions is restricting twice. -/
noncomputable def restrictCompIso (M : X.Modules) {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] (hh : g ≫ f = h) :
    M.restrict h ≅ (M.restrict f).restrict g :=
  (restrictFunctorCongr hh).symm.app M ≪≫ (restrictFunctorComp g f).app M

/-- An `𝒪_X`-module whose restrictions along a family of open immersions covering `X` are free
of rank `r` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_restrict_iso_free (M : X.Modules) {r : ℕ} {ι : Type u}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, Nonempty (M.restrict (f i) ≅ SheafOfModules.free (ULift.{u} (Fin r)))) :
    M.IsFiniteLocallyFreeOfRank r := by
  refine SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.2
    ⟨ι, fun i ↦ (f i).opensRange, (Opens.coversTop_iff _ _).2 hf, fun i ↦ ⟨?_⟩⟩
  refine (overIsoFreeEquiv M _ _).symm ?_
  exact restrictCompIso M (f i) (f i).isoOpensRange.inv (f i).opensRange.ι
      (f i).isoOpensRange_inv_comp ≪≫
    (restrictFunctor _).mapIso (h i).some ≪≫ restrictFreeIso _ _

/-- An `𝒪_X`-module whose restrictions along a family of open immersions covering `X` are free
of finite rank is finite locally free. -/
theorem isFiniteLocallyFree_of_restrict_iso_free (M : X.Modules) {ι : Type u}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) (κ : ι → Type u) [∀ i, Finite (κ i)]
    (h : ∀ i, Nonempty (M.restrict (f i) ≅ SheafOfModules.free (κ i))) :
    M.IsFiniteLocallyFree := by
  refine SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free.{u, u, u}
    (fun i ↦ (f i).opensRange) ((Opens.coversTop_iff _ _).2 hf) κ fun i ↦ ⟨?_⟩
  refine (overIsoFreeEquiv M _ _).symm ?_
  exact restrictCompIso M (f i) (f i).isoOpensRange.inv (f i).opensRange.ι
      (f i).isoOpensRange_inv_comp ≪≫
    (restrictFunctor _).mapIso (h i).some ≪≫ restrictFreeIso _ _

/-- A finite locally free `𝒪_X`-module of rank `r` is free of rank `r` on the members of an open
cover of `X`. -/
theorem IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (M : X.Modules) {r : ℕ}
    [M.IsFiniteLocallyFreeOfRank r] :
    ∃ (ι : Type u) (U : ι → X.Opens), ⨆ i, U i = ⊤ ∧
      ∀ i, Nonempty (M.restrict (U i).ι ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
  obtain ⟨I, U, hU, h⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      ‹M.IsFiniteLocallyFreeOfRank r›
  exact ⟨I, U, (Opens.coversTop_iff _ _).1 hU, fun i ↦ ⟨overIsoFreeEquiv M _ _ (h i).some⟩⟩

/-- The free module of rank `r` is finite locally free of rank `r`. -/
instance isFiniteLocallyFreeOfRank_free (r : ℕ) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).IsFiniteLocallyFreeOfRank r :=
  isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (ι := PUnit) (fun _ ↦ 𝟙 X)
    (by simpa using (Scheme.Hom.opensRange_of_isIso (𝟙 X))) fun _ ↦ ⟨restrictFreeIso _ _⟩

/-- **Finite local freeness of rank `r` is local.** An `𝒪_X`-module whose restrictions to the
members of an open cover are finite locally free of rank `r` is finite locally free of
rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_iSup_eq_top (M : X.Modules) {r : ℕ} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (M.restrict (U i).ι).IsFiniteLocallyFreeOfRank r) :
    M.IsFiniteLocallyFreeOfRank r := by
  choose κ W hW e using fun i ↦
    have := h i
    IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (M.restrict (U i).ι) (r := r)
  refine isFiniteLocallyFreeOfRank_of_restrict_iso_free M
    (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ (U j.1).ι) ?_ fun j ↦
      ⟨(restrictFunctorComp _ _).app M ≪≫ (e j.1 j.2).some⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.ge (Set.mem_univ x) : x ∈ ⨆ i, U i)
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
    (by rw [hW i]; trivial : (⟨x, hi⟩ : U i) ∈ ⨆ k, W i k)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, ⟨⟨⟨x, hi⟩, hk⟩, rfl⟩⟩

/-- The restriction of a finite locally free module of rank `r` along an open immersion is
finite locally free of rank `r`. -/
instance isFiniteLocallyFreeOfRank_restrict (M : X.Modules) {r : ℕ}
    [M.IsFiniteLocallyFreeOfRank r] {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (M.restrict f).IsFiniteLocallyFreeOfRank r := by
  obtain ⟨ι, U, hU, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  refine isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun i ↦ (f ⁻¹ᵁ U i).ι) ?_ fun i ↦
    ⟨((restrictFunctorComp _ _).app M).symm ≪≫
      restrictCompIso M (U i).ι (f ∣_ U i) ((f ⁻¹ᵁ U i).ι ≫ f)
        (morphismRestrict_ι f (U i)) ≪≫
      (restrictFunctor _).mapIso (e i).some ≪≫ restrictFreeIso _ _⟩
  simp only [Scheme.Opens.opensRange_ι]
  rw [← Scheme.Hom.preimage_iSup, hU]
  rfl
end AlgebraicGeometry.Scheme.Modules
