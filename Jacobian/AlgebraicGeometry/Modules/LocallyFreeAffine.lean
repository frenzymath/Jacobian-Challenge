import Jacobian.Algebra.Category.ModuleCat.FiniteProjective
import Jacobian.CategoryTheory.Preadditive.FiniteSummand
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Jacobian.Algebra.Category.ModuleCat.Sheaf.FreeSections
import Jacobian.AlgebraicGeometry.Modules.LocallyFree
import Jacobian.AlgebraicGeometry.Modules.Localization

/-!
# Affine sections of finite locally free modules

Sections of a finite locally free sheaf on an affine open form a finitely presented projective module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}

/-- A finite locally free `𝒪_X`-module is free of finite rank on a neighbourhood of every
point. -/
lemma exists_mem_over_iso_free (M : X.Modules) [M.IsFiniteLocallyFree] (x : X) :
    ∃ (Y : X.Opens) (I : Type u) (_ : Fintype I), x ∈ Y ∧
      Nonempty (M.over Y ≅ SheafOfModules.free I) := by
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hx⟩ := q.coversTop ⊤ x trivial
  have := hf.isFiniteType i
  have := hq.isIso i
  exact ⟨q.X i, (q.generators i).I, Fintype.ofFinite _, g.le hx,
    ⟨(asIso (q.generators i).π).symm⟩⟩

/-- A trivialisation `M.over Y ≅ 𝒪_Y^I` of an `𝒪_X`-module over an open `Y` gives, for every open
`W ≤ Y`, a `Γ(X, W)`-linear isomorphism `Γ(M, W) ≃ Γ(X, W)^I`. -/
noncomputable def sectionsLinearEquivOfOverIsoFree {M : X.Modules} {Y : X.Opens} {I : Type u}
    [Fintype I] [DecidableEq I] (e : M.over Y ≅ SheafOfModules.free I) {W : X.Opens}
    (h : W ≤ Y) : Γ(M, W) ≃ₗ[Γ(X, W)] (I → Γ(X, W)) :=
  SheafOfModules.sectionsLinearEquivOfIsoFree e (op (Over.mk (homOfLE h)))

/-- **Sections of finite locally free modules over affine opens.** The sections `Γ(M, U)` of a
finite locally free `𝒪_X`-module over an affine open `U` form a finitely presented projective
`Γ(X, U)`-module: they localize to the free modules `Γ(M, D(g))` over the basic opens `D(g)` on
which `M` is trivial. -/
theorem finitePresentation_projective_sections (M : X.Modules) [M.IsFiniteLocallyFree]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(M, U) ∧ Module.Projective Γ(X, U) Γ(M, U) := by
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree M
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree M
  let s : Set Γ(X, U) := {g | ∃ (Y : X.Opens) (I : Type u) (_ : Fintype I),
    X.basicOpen g ≤ Y ∧ Nonempty (M.over Y ≅ SheafOfModules.free I)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨Y, I, _, hxY, ⟨e⟩⟩ := exists_mem_over_iso_free M x
    obtain ⟨g, hgY, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxY⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, Y, I, inferInstance, hgY, ⟨e⟩⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(M, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen M hU r.1
  have _ (r : s) := hU.isLocalization_basicOpen r.1
  have _ (r : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  have hfree (r : s) : Module.Free Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) ∧
      Module.FinitePresentation Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) := by
    obtain ⟨Y, I, _, hY, ⟨e⟩⟩ := r.2
    classical
    let e' := sectionsLinearEquivOfOverIsoFree e hY
    exact ⟨Module.Free.of_equiv e'.symm, Module.FinitePresentation.of_equiv e'.symm⟩
  let ϕ (r : s) : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen r.1) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
      map_add' := map_add _
      map_smul' := map_smul M _ }
  have hfp : Module.FinitePresentation Γ(X, U) Γ(M, U) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun r ↦ Γ(X, X.basicOpen r.1)) ϕ fun r ↦ (hfree r).2
  have : Module.Flat Γ(X, U) Γ(M, U) :=
    Module.flat_of_isLocalized_span Γ(X, U) Γ(M, U) s hs
      (fun r ↦ Γ(M, X.basicOpen r.1)) ϕ fun r ↦ by
        have := (hfree r).1
        have := IsLocalization.flat Γ(X, X.basicOpen r.1) (.powers r.1)
        exact Module.Flat.trans Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1)
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

variable {scheme : Scheme.{u}}

/-- **Finite locally free modules are summands of free modules on affine opens.** The
restriction of a finite locally free `𝒪_X`-module `moduleSheaf` to the spectrum of an affine open `openSubset` is a
direct summand of a free module of finite rank: there are `ξⱼ : moduleSheaf ⟶ 𝒪` and `mⱼ : 𝒪 ⟶ moduleSheaf` with
`∑ⱼ ξⱼ ≫ mⱼ = 𝟙`. Indeed `moduleSheaf|_U` is `Γ(moduleSheaf, openSubset)^~`, and `Γ(moduleSheaf, openSubset)` is finite projective
(`finitePresentation_projective_sections`). -/
theorem exists_sum_comp_eq_id_restrict_fromSpec (moduleSheaf : scheme.Modules) [moduleSheaf.IsFiniteLocallyFree]
    {openSubset : scheme.Opens} (affine : IsAffineOpen openSubset) :
    ∃ (rank : ℕ) (coordinates : Fin rank → (moduleSheaf.restrict affine.fromSpec ⟶ SheafOfModules.unit _))
      (generators : Fin rank → (SheafOfModules.unit _ ⟶ moduleSheaf.restrict affine.fromSpec)),
      ∑ index, coordinates index ≫ generators index = 𝟙 _ := by
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree moduleSheaf
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree moduleSheaf
  let restriction := moduleSheaf.restrict affine.fromSpec
  have tildeIso : IsIso restriction.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent restriction
  let sectionEquiv := sectionsRestrictFromSpecLinearEquiv moduleSheaf affine
  obtain ⟨finitePresentation, projective⟩ := finitePresentation_projective_sections moduleSheaf affine
  have : Module.Finite Γ(scheme, openSubset) (moduleSpecΓFunctor.obj restriction) := Module.Finite.equiv sectionEquiv.symm
  have : Module.Projective Γ(scheme, openSubset) (moduleSpecΓFunctor.obj restriction) := Module.Projective.of_equiv sectionEquiv.symm
  obtain ⟨rank, ξ₀, m₀, h₀⟩ :=
    ModuleCat.exists_sum_comp_eq_id_of_projective (baseRing := Γ(scheme, openSubset))
    (moduleSpecΓFunctor.obj restriction)
  exact CategoryTheory.Functor.exists_sum_comp_eq_id_of_iso (tilde.functor Γ(scheme, openSubset))
    (@asIso _ _ _ _ restriction.fromTildeΓ tildeIso) tildeSelf ⟨rank, ξ₀, m₀, h₀⟩

/-- **Finite locally free modules are summands of free modules over affine opens.** The
restriction `moduleSheaf.over openSubset` of a finite locally free `𝒪_X`-module to an affine open `openSubset` is a direct
summand of a free module of finite rank: there are `ξⱼ : moduleSheaf|_U ⟶ 𝒪_U` and `mⱼ : 𝒪_U ⟶ moduleSheaf|_U` with
`∑ⱼ ξⱼ ≫ mⱼ = 𝟙`. -/
theorem exists_sum_comp_eq_id_over (moduleSheaf : scheme.Modules) [moduleSheaf.IsFiniteLocallyFree] {openSubset : scheme.Opens}
    (affine : IsAffineOpen openSubset) :
    ∃ (rank : ℕ) (coordinates : Fin rank → (moduleSheaf.over openSubset ⟶ (SheafOfModules.unit scheme.ringCatSheaf).over openSubset))
      (generators : Fin rank → ((SheafOfModules.unit scheme.ringCatSheaf).over openSubset ⟶ moduleSheaf.over openSubset)),
      ∑ index, coordinates index ≫ generators index = 𝟙 _ := by
  have : (restrictFunctor affine.isoSpec.hom).Additive :=
    Functor.additive_of_iso (restrictFunctorIsoPullback _).symm
  have : HasBinaryBiproducts (SheafOfModules.{u} (scheme.ringCatSheaf.over openSubset)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts (overEquiv openSubset).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : (overEquiv openSubset).inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  exact Functor.exists_sum_comp_eq_id_of_iso
    (restrictFunctor affine.isoSpec.hom ⋙ (overEquiv openSubset).inverse)
    ((overEquiv openSubset).inverse.mapIso ((restrictCompIso moduleSheaf affine.fromSpec affine.isoSpec.hom openSubset.ι
      affine.isoSpec_hom_fromSpec).symm ≪≫ ((overFunctorEquiv openSubset).app moduleSheaf).symm) ≪≫
        ((overEquiv openSubset).unitIso.app (moduleSheaf.over openSubset)).symm)
    ((overEquiv openSubset).inverse.mapIso (restrictUnitIso affine.isoSpec.hom ≪≫
      (overEquivObjUnitIso openSubset).symm) ≪≫ ((overEquiv openSubset).unitIso.app _).symm)
    (exists_sum_comp_eq_id_restrict_fromSpec moduleSheaf affine)


end AlgebraicGeometry.Scheme.Modules
