import Jacobian.AlgebraicGeometry.Modules.Localization
import Jacobian.AlgebraicGeometry.Modules.Quasicoherent

/-!
# A localization criterion for quasi-coherence
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme : Scheme.{schemeUniverse}}

set_option backward.isDefEq.respectTransparency false in
/-- Conversely to `exists_map_eq_pow_smul_of_isAffineOpen` and
`exists_pow_smul_eq_zero_of_isAffineOpen`, let `W` be an affine open such that for every
`f ∈ Γ(X, W)` every section of `M` over `D(f)` becomes the restriction of a section over `W` after
multiplication by a power of `f`, and every section over `W` vanishing on `D(f)` is killed by a
power of `f`. Then the restriction of `M` along `fromSpec` is localizing. -/
lemma isLocalizing_restrict_fromSpec_of_forall (moduleSheaf : scheme.Modules) {largerOpen : scheme.Opens}
    (hW : IsAffineOpen largerOpen)
    (h₁ : ∀ (morphism : Γ(scheme, largerOpen)) (s : Γ(moduleSheaf, scheme.basicOpen morphism)), ∃ (degree : ℕ) (tensorElement : Γ(moduleSheaf, largerOpen)),
      moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op tensorElement =
        scheme.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op morphism ^ degree • s)
    (h₂ : ∀ (morphism : Γ(scheme, largerOpen)) (tensorElement : Γ(moduleSheaf, largerOpen)), moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op tensorElement = 0 →
      ∃ degree : ℕ, morphism ^ degree • tensorElement = 0) :
    IsLocalizing (modulesSpecToSheaf.obj (moduleSheaf.restrict hW.fromSpec)) := by
  intro morphism
  have hW' : largerOpen ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen morphism ≤ scheme.basicOpen morphism :=
    (hW.fromSpec_image_basicOpen morphism).le
  have hD' : scheme.basicOpen morphism ≤ hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen morphism :=
    (hW.fromSpec_image_basicOpen morphism).ge
  have hinj : Function.Injective (moduleSheaf.presheaf.map (homOfLE hD').op) := fun baseScalar extensionScalar hab ↦ by
    have := congr(moduleSheaf.presheaf.map (homOfLE hD).op $hab)
    rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      show (homOfLE hD').op ≫ (homOfLE hD).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
      ConcreteCategory.id_apply] at this
  have hhom (openSubset : (Spec Γ(scheme, largerOpen)).Opens) :
      Function.Injective (moduleSheaf.restrictAppIso hW.fromSpec openSubset).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (isUnit_algebraMap_end_of_le_basicOpen morphism le_rfl) (fun element ↦ ?_) (fun tensorElement ht ↦ ?_)
  · obtain ⟨degree, tensorElement, ht⟩ := h₁ morphism
      (moduleSheaf.presheaf.map (homOfLE hD').op ((moduleSheaf.restrictAppIso hW.fromSpec _).hom element))
    let otherElement := (moduleSheaf.restrictAppIso hW.fromSpec ⊤).inv
      (moduleSheaf.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op tensorElement)
    have key : moduleSheaf.presheaf.map (homOfLE hD').op ((moduleSheaf.restrictAppIso hW.fromSpec _).hom (morphism ^ degree • element)) =
        moduleSheaf.presheaf.map (homOfLE hD').op ((moduleSheaf.restrictAppIso hW.fromSpec _).hom
          ((moduleSheaf.restrict hW.fromSpec).presheaf.map (homOfLE (le_top :
            (PrimeSpectrum.basicOpen morphism : (Spec Γ(scheme, largerOpen)).Opens) ≤ ⊤)).op otherElement)) := by
      rw [restrictAppIso_fromSpec_smul, map_smul, map_restrictAppIso_hom_apply]
      dsimp only [otherElement]
      rw [Iso.inv_hom_id_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, Subsingleton.elim (_ ≫ _ ≫ _) (homOfLE (scheme.basicOpen_le morphism)).op,
        ht, Subsingleton.elim (_ ≫ _) (homOfLE (scheme.basicOpen_le morphism)).op, map_pow]
    exact ⟨degree, otherElement, hhom _ (hinj key)⟩
  · replace ht : (moduleSheaf.restrict hW.fromSpec).presheaf.map (homOfLE (le_top :
        (PrimeSpectrum.basicOpen morphism : (Spec Γ(scheme, largerOpen)).Opens) ≤ ⊤)).op tensorElement = 0 := ht
    let tensorElement' := moduleSheaf.presheaf.map (homOfLE hW').op ((moduleSheaf.restrictAppIso hW.fromSpec ⊤).hom tensorElement)
    have ht' : moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op tensorElement' = 0 := by
      have := congr(moduleSheaf.presheaf.map (homOfLE hD').op ((moduleSheaf.restrictAppIso hW.fromSpec _).hom $ht))
      rw [map_restrictAppIso_hom_apply, map_zero, map_zero, ← Functor.map_comp_apply] at this
      dsimp only [tensorElement']
      rw [← Functor.map_comp_apply]
      exact (congrArg (fun ringMap ↦ moduleSheaf.presheaf.map ringMap _) (Subsingleton.elim _ _)).trans this
    obtain ⟨degree, hn⟩ := h₂ morphism tensorElement' ht'
    refine ⟨degree, hhom _ ?_⟩
    have ht : (moduleSheaf.restrictAppIso hW.fromSpec ⊤).hom tensorElement =
        moduleSheaf.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op tensorElement' := by
      dsimp only [tensorElement']
      rw [← Functor.map_comp_apply, Subsingleton.elim (_ ≫ _) (𝟙 _),
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    rw [restrictAppIso_fromSpec_smul, map_zero, ht, ← map_smul, hn, map_zero]

/-- **A criterion for quasi-coherence.** An `𝒪_X`-module `M` is quasi-coherent as soon as, for
every affine open `W` of `X` and every `f ∈ Γ(X, W)`, every section of `M` over `D(f)` becomes the
restriction of a section over `W` after multiplication by a power of `f`, and every section over
`W` vanishing on `D(f)` is killed by a power of `f` [EGA I, Théorème 1.4.1]. -/
theorem isQuasicoherent_of_forall_isAffineOpen (moduleSheaf : scheme.Modules)
    (h₁ : ∀ (largerOpen : scheme.Opens), IsAffineOpen largerOpen → ∀ (morphism : Γ(scheme, largerOpen)) (s : Γ(moduleSheaf, scheme.basicOpen morphism)),
      ∃ (degree : ℕ) (tensorElement : Γ(moduleSheaf, largerOpen)), moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op tensorElement =
        scheme.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op morphism ^ degree • s)
    (h₂ : ∀ (largerOpen : scheme.Opens), IsAffineOpen largerOpen → ∀ (morphism : Γ(scheme, largerOpen)) (tensorElement : Γ(moduleSheaf, largerOpen)),
      moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op tensorElement = 0 → ∃ degree : ℕ, morphism ^ degree • tensorElement = 0) :
    moduleSheaf.IsQuasicoherent :=
  isQuasicoherent_of_iSup_opensRange_eq_top moduleSheaf
    (fun openSubset : scheme.affineOpens ↦ openSubset.2.fromSpec) (by
      simp only [IsAffineOpen.opensRange_fromSpec]
      exact iSup_affineOpens_eq_top scheme)
    fun openSubset ↦
      have : IsIso (moduleSheaf.restrict openSubset.2.fromSpec).fromTildeΓ :=
        (isIso_fromTildeΓ_iff_isLocalizing _).2
          (isLocalizing_restrict_fromSpec_of_forall moduleSheaf openSubset.2 (h₁ openSubset.1 openSubset.2) (h₂ openSubset.1 openSubset.2))
      presentationOfIsIsoFromTildeΓ _

end AlgebraicGeometry.Scheme.Modules
