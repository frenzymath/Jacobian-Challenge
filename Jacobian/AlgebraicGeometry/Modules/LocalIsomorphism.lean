import Jacobian.AlgebraicGeometry.Modules.Sections
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Local criteria for isomorphisms of module sheaves

A morphism which is bijective on sections over sufficiently small opens is an isomorphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}

/-- A morphism of modules which is bijective on sections over all sufficiently small opens is an
isomorphism. -/
lemma Hom.isIso_of_forall_bijective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∀ W ≤ V, Function.Bijective (φ.app W)) :
    IsIso φ := by
  let f := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hinj : Sheaf.IsLocallyInjective f := ⟨fun {U} a b hab p hp ↦ by
    obtain ⟨V, hpV, hV⟩ := h p
    refine ⟨U.unop ⊓ V, homOfLE inf_le_left, (hV _ inf_le_right).1 ?_, hp, hpV⟩
    have := congrArg (N.presheaf.map (homOfLE (inf_le_left : U.unop ⊓ V ≤ U.unop)).op) hab
    exact (Hom.app_presheaf_map φ (homOfLE inf_le_left) a).trans
      (this.trans (Hom.app_presheaf_map φ (homOfLE inf_le_left) b).symm)⟩
  have hsurj : Sheaf.IsLocallySurjective f := ⟨fun {U} s p hp ↦ by
    obtain ⟨V, hpV, hV⟩ := h p
    obtain ⟨t, ht⟩ := (hV (U ⊓ V) inf_le_right).2
      (N.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)
    exact ⟨U ⊓ V, homOfLE inf_le_left, ⟨t, ht⟩, hp, hpV⟩⟩
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨hinj, hsurj⟩
  have : IsIso ((toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map f))
  exact isIso_of_reflects_iso φ (toPresheaf X)

/-- A morphism of module sheaves is an isomorphism if it is bijective on a basis. -/
lemma isIso_of_bijective_app_of_basis {source target : X.Modules}
    {index : Type*} {opens : index → X.Opens}
    (basis : Opens.IsBasis (Set.range opens)) (morphism : source ⟶ target)
    (bijective : ∀ point, Function.Bijective (morphism.app (opens point))) :
    IsIso morphism := by
  let sourceSheaf : TopCat.Sheaf AddCommGrpCat X := ⟨source.presheaf, source.isSheaf⟩
  let targetSheaf : TopCat.Sheaf AddCommGrpCat X := ⟨target.presheaf, target.isSheaf⟩
  let sheafMorphism : sourceSheaf ⟶ targetSheaf :=
    Sheaf.homEquiv.symm ((toPresheaf X).map morphism)
  have sheafIso : IsIso sheafMorphism := TopCat.Sheaf.isIso_iff_isIso_basis basis
    fun point ↦ (ConcreteCategory.isIso_iff_bijective _).2 (bijective point)
  have : IsIso ((toPresheaf X).map morphism) := by
    obtain ⟨inverse, left_inverse, right_inverse⟩ := sheafIso.out
    exact ⟨inverse.hom, congrArg (fun map ↦ map.hom) left_inverse,
      congrArg (fun map ↦ map.hom) right_inverse⟩
  exact isIso_of_reflects_iso morphism (toPresheaf X)

/-- It suffices to test bijectivity on affine opens. -/
lemma isIso_of_bijective_app_of_isAffineOpen {source target : X.Modules}
    (morphism : source ⟶ target)
    (bijective : ∀ openSubset : X.Opens, IsAffineOpen openSubset →
      Function.Bijective (morphism.app openSubset)) : IsIso morphism := by
  have basis : Opens.IsBasis (Set.range (fun openSubset : X.affineOpens ↦
      (openSubset : X.Opens))) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  exact isIso_of_bijective_app_of_basis basis morphism
    fun openSubset ↦ bijective openSubset openSubset.2

end AlgebraicGeometry.Scheme.Modules
