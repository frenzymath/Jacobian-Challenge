import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Fpqc coverings and restriction to a base scheme

Fpqc covering sieves are jointly surjective and admit finite affine flat refinements over affine schemes.
The sheaf condition over a base scheme transfers to any covering whose target
admits a compatible morphism to that base.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A single flat, surjective morphism locally of finite presentation is an fppf cover
in the category of schemes over a base. -/
lemma singleton_mem_over_fppfTopology {base : Scheme.{u}} {source target : Over base}
    (morphism : source ⟶ target) [Flat morphism.left] [Surjective morphism.left]
    [LocallyOfFinitePresentation morphism.left] :
    Sieve.generate (.singleton morphism) ∈ (fppfTopology.over base) target := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv target (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Presieve.ofArrows_pUnit]
  exact morphism.left.singleton_mem_fppfPrecoverage

/-- If a presheaf is an fpqc sheaf after restriction to a new base, it satisfies the
sheaf condition for coverings whose target admits a compatible map to that base. -/
lemma isSheafFor_of_isSheaf_overMap {base extension : Scheme.{u}}
    (baseMap : extension ⟶ base) {presheaf : (Over base)ᵒᵖ ⥤ Type v}
    (sheafCondition : Presheaf.IsSheaf (fpqcTopology.over extension)
      ((Over.map baseMap).op ⋙ presheaf)) {parameter : Over base} (sieve : Sieve parameter)
    (covering : sieve ∈ (fpqcTopology.over base) parameter)
    (lift : parameter.left ⟶ extension) (compatibility : lift ≫ baseMap = parameter.hom) :
    Presieve.IsSheafFor presheaf sieve.arrows := by
  let parameterIso : (Over.map baseMap).obj (Over.mk lift) ≅ parameter :=
    Over.isoMk (Iso.refl _) (by simpa using compatibility.symm)
  let liftedSieve : Sieve (Over.mk lift) :=
    (Sieve.overEquiv (Over.mk lift)).symm (Sieve.overEquiv parameter sieve)
  have liftedCovering : liftedSieve ∈ (fpqcTopology.over extension) (Over.mk lift) :=
    GrothendieckTopology.overEquiv_symm_mem_over _ _ _
      ((GrothendieckTopology.mem_over_iff _ _).mp covering)
  have liftedSheaf := ((isSheaf_iff_isSheaf_of_type _ _).mp sheafCondition)
    liftedSieve liftedCovering
  have transferred := (Presieve.isSheafFor_over_map_op_comp_iff baseMap presheaf
    liftedSieve parameterIso).mp liftedSheaf
  have sieveEquality : Sieve.pullback parameterIso.inv
      (Sieve.functorPushforward (Over.map baseMap) liftedSieve) = sieve := by
    apply (Sieve.overEquiv parameter).injective
    rw [Sieve.overEquiv_pullback]
    dsimp only [liftedSieve]
    rw [Sieve.functorPushforward_over_map, OrderIso.apply_symm_apply]
    change Sieve.pullback (𝟙 parameter.left) (Sieve.overEquiv parameter sieve) = _
    simp only [Sieve.pullback_id]
  rwa [sieveEquality] at transferred

/-- A covering sieve of the fpqc topology on a scheme `X` is jointly surjective: every point of
`X` is in the image of some morphism of the sieve. -/
lemma exists_mem_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X} (hS : S ∈ fpqcTopology X)
    (x : X) : ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x ∈ Set.range g.base := by
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨-, hR, -⟩, hle⟩ := hS
  obtain ⟨_, g, h, hx⟩ := hR x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, hx⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A covering sieve of the fpqc topology on an affine scheme `V` contains a finite family of flat
morphisms from affine schemes which itself generates a covering sieve. -/
lemma exists_finite_affine_flat_of_mem_fpqcTopology {V : Scheme.{u}} [IsAffine V] {S : Sieve V}
    (hS : S ∈ fpqcTopology V) :
    ∃ (κ : Type u) (W : κ → Scheme.{u}) (f : ∀ j, W j ⟶ V), Finite κ ∧ (∀ j, IsAffine (W j)) ∧
      (∀ j, Flat (f j)) ∧ (∀ j, S (f j)) ∧ Sieve.ofArrows W f ∈ fpqcTopology V := by
  have hS' := hS
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS'
  obtain ⟨R, hR, hle⟩ := hS'
  obtain ⟨𝒰, _, rfl⟩ := mem_propQCPrecoverage_iff_exists_quasiCompactCover.mp hR
  obtain ⟨𝒱, φ, _, -⟩ : ∃ (𝒱 : Scheme.AffineCover.{u} @Flat V) (φ : 𝒱.cover ⟶ 𝒰.qculift),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (φ.h₀ j) := QuasiCompactCover.exists_hom _
  have h𝒰 (k : 𝒰.qculift.I₀) : 𝒰.presieve₀ (𝒰.qculift.f k) := by
    rcases k with k | k
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  refine ⟨𝒱.cover.I₀, 𝒱.cover.X, 𝒱.cover.f, inferInstance, fun j ↦ inferInstanceAs
    (IsAffine (Spec _)), fun j ↦ 𝒱.map_prop j, fun j ↦ ?_, Cover.mem_propQCTopology 𝒱.cover⟩
  rw [← φ.w₀ j]
  exact S.downward_closed (hle _ _ (h𝒰 _)) _

/-- A faithfully flat quasi-compact map over a base is an fpqc covering. -/
lemma singleton_mem_over_fpqcTopology {base : Scheme.{u}} {target source : Over base} (morphism : source ⟶ target)
    [Flat morphism.left] [Surjective morphism.left] [QuasiCompact morphism.left] :
    Sieve.generate (.singleton morphism) ∈ (fpqcTopology.over base) target := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv target (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Presieve.ofArrows_pUnit]
  exact morphism.left.singleton_mem_fpqcPrecoverage

/-- An fpqc sheaf after base change satisfies descent for maps factoring through that base. -/
lemma isSheafFor_singleton_of_isSheaf_overMap {base extensionBase : Scheme.{u}} (baseMap : extensionBase ⟶ base)
    {presheaf : (Over base)ᵒᵖ ⥤ Type*} (sheafCondition : Presheaf.IsSheaf (fpqcTopology.over extensionBase) ((Over.map baseMap).op ⋙ presheaf))
    {target source : Over base} (morphism : source ⟶ target) [Flat morphism.left] [Surjective morphism.left] [QuasiCompact morphism.left]
    (factorization : target.left ⟶ extensionBase) (factorizationEquation : factorization ≫ baseMap = target.hom) :
    Presieve.IsSheafFor presheaf (.singleton morphism) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact isSheafFor_of_isSheaf_overMap baseMap sheafCondition _
    (singleton_mem_over_fpqcTopology morphism) factorization factorizationEquation

end AlgebraicGeometry.Scheme
