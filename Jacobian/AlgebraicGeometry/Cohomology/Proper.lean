import Jacobian.AlgebraicGeometry.Modules.Vanishing
import Jacobian.AlgebraicGeometry.Modules.RestrictionKernel
import Jacobian.AlgebraicGeometry.Cohomology.Proper.Modification
import Jacobian.AlgebraicGeometry.Cohomology.Proper.Support
import Jacobian.AlgebraicGeometry.Cohomology.Proper.Chow
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.Modules.Annihilator
import Jacobian.AlgebraicGeometry.Modules.Coherent
import Jacobian.AlgebraicGeometry.Modules.Cokernel
import Jacobian.AlgebraicGeometry.Modules.FinitePushforward
import Jacobian.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite coherent cohomology of proper schemes

Local vanishing and noetherian induction reduce coherent-cohomology finiteness
on a proper scheme to generic finite-cohomology approximations on its closed
subschemes. The kernel and cokernel of each approximation vanish on an open
whose direct image strictly enlarges the open used for the induction.
Chow's lemma and relative Serre vanishing supply these approximations, giving
finite cohomology for every coherent module over a Noetherian affine base.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Vanishing on two opens implies vanishing on their union. -/
lemma isZero_restrict_sup {M : X.Modules} {U W : X.Opens}
    (hU : IsZero (M.restrict U.ι)) (hW : IsZero (M.restrict W.ι)) :
    IsZero (M.restrict (U ⊔ W).ι) := by
  rw [isZero_restrict_iff] at hU hW ⊢
  intro V hV
  refine ⟨fun a b ↦ ?_⟩
  let S : Sieve V := Sieve.generate (Presieve.ofArrows (fun i : Bool ↦ V ⊓ cond i U W)
    (fun i ↦ homOfLE inf_le_left))
  have hS : S ∈ Opens.grothendieckTopology X V := by
    intro x hx
    obtain hxU | hxW := (hV hx : x ∈ U ⊔ W)
    · exact ⟨V ⊓ U, homOfLE inf_le_left,
        ⟨_, 𝟙 _, _, Presieve.ofArrows.mk true, Category.id_comp _⟩, ⟨hx, hxU⟩⟩
    · exact ⟨V ⊓ W, homOfLE inf_le_left,
        ⟨_, 𝟙 _, _, Presieve.ofArrows.mk false, Category.id_comp _⟩, ⟨hx, hxW⟩⟩
  let hM : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (Opens.grothendieckTopology X)
        (CategoryTheory.forget AddCommGrpCat.{u})).obj ⟨M.presheaf, M.isSheaf⟩).property
  refine (hM _ hS).isSeparatedFor.ext fun Z l hl ↦ ?_
  have hZ : Z ≤ U ∨ Z ≤ W := by
    obtain ⟨Y, g, f, hf, rfl⟩ := hl
    obtain ⟨i⟩ := hf
    cases i
    · exact Or.inr ((leOfHom g).trans inf_le_right)
    · exact Or.inl ((leOfHom g).trans inf_le_right)
  obtain hZ | hZ := hZ
  · exact (hU Z hZ).elim _ _
  · exact (hW Z hZ).elim _ _

/-- A module whose restriction to the top open vanishes is zero. -/
lemma isZero_of_isZero_restrict_top {M : X.Modules}
    (h : IsZero (M.restrict (⊤ : X.Opens).ι)) : IsZero M :=
  (isZero_iff_forall_subsingleton M).mpr fun V ↦
    (isZero_restrict_iff M ⊤).mp h V le_top

/-- Restricting a zero module to an open remains zero. -/
lemma isZero_restrict_of_isZero {M : X.Modules} (h : IsZero M) (U : X.Opens) :
    IsZero (M.restrict U.ι) :=
  (isZero_restrict_iff M U).mpr fun V _ ↦
    (isZero_iff_forall_subsingleton M).mp h V

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Generic finite-cohomology approximations on closed subschemes imply finite
cohomology. Noetherian induction applies to the larger open on which the kernel
and cokernel of an approximation vanish. -/
theorem hasFiniteH_of_generic_approximation {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G]
    (approximation : ∀ (I : X.IdealSheafData) [Nonempty I.subscheme]
      (M : I.subscheme.Modules) [M.IsQuasicoherent] [M.IsFinitePresentation],
      ∃ (N : I.subscheme.Modules) (_ : N.IsQuasicoherent) (_ : N.IsFinitePresentation)
        (comparison : M ⟶ N) (W : I.subscheme.Opens),
        (W : Set I.subscheme).Nonempty ∧ IsIso ((restrictFunctor W.ι).map comparison) ∧
          HasFiniteH (I.subschemeι ≫ p) N) :
    HasFiniteH p G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  suffices inductionStep : ∀ (U : X.Opens) (M : X.Modules)
      [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
      [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M],
      IsZero (M.restrict U.ι) → HasFiniteH p M by
    have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun point ↦ point.2⟩
    exact inductionStep ⊥ G (isZero_of_isEmpty _)
  intro U
  induction U using WellFoundedGT.induction with
  | _ U inductionHypothesis =>
    intro M _ _ vanishing
    obtain ⟨I, disjointSupport, unitIsIso⟩ :=
      exists_isIso_pullbackUnit_subschemeι M U vanishing
    let inclusion := I.subschemeι
    let restrictedModule := (pullback inclusion).obj M
    refine HasFiniteH.of_iso (asIso (pullbackUnit inclusion M)).symm
      ((hasFiniteH_pushforward_iff inclusion p restrictedModule).2 ?_)
    rcases isEmpty_or_nonempty I.subscheme with emptySupport | nonemptySupport
    · exact HasFiniteH.of_isZero (isZero_of_isEmpty _)
    have : IsLocallyNoetherian I.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (inclusion ≫ p)
    obtain ⟨N, hNQuasicoherent, hNFinitePresentation, comparison, W, nonemptyOpen,
      comparisonIsIso, finiteN⟩ :=
      approximation I restrictedModule
    letI : N.IsQuasicoherent := hNQuasicoherent
    letI : N.IsFinitePresentation := hNFinitePresentation
    have disjoint : Disjoint (U : Set X) (Set.range inclusion) := by
      refine Set.disjoint_left.mpr ?_
      rintro point membership ⟨sourcePoint, rfl⟩
      apply disjointSupport _ membership
      have hsource : inclusion sourcePoint ∈ Set.range inclusion := ⟨sourcePoint, rfl⟩
      have hsupp : inclusion sourcePoint ∈ (I.support : Set X) := by
        change I.subschemeι sourcePoint ∈ (I.support : Set X)
        rw [← I.range_subschemeι]
        exact hsource
      exact hsupp
    obtain ⟨V, strict, containment⟩ :=
      inclusion.exists_open_extension U disjoint W nonemptyOpen
    have finiteOfVanishing (moduleSheaf : I.subscheme.Modules)
        [moduleSheaf.IsQuasicoherent] [moduleSheaf.IsFinitePresentation]
        (zeroRestriction : IsZero (moduleSheaf.restrict W.ι)) :
        HasFiniteH (inclusion ≫ p) moduleSheaf := by
      letI := isQuasicoherent_pushforward_of_isAffineHom inclusion moduleSheaf
      letI := isFinitePresentation_pushforward_of_isFinite inclusion moduleSheaf
      exact (hasFiniteH_pushforward_iff inclusion p moduleSheaf).1
        (inductionHypothesis V strict _
          (isZero_restrict_pushforward_of_preimage_le inclusion moduleSheaf
            containment zeroRestriction))
    letI := comparisonIsIso
    letI : SheafOfModules.IsQuasicoherent
        (R := I.subscheme.ringCatSheaf) (kernel comparison) :=
      isQuasicoherent_kernel comparison
    letI : SheafOfModules.IsFinitePresentation
        (R := I.subscheme.ringCatSheaf) (kernel comparison) :=
      isFinitePresentation_kernel comparison
    letI : SheafOfModules.IsQuasicoherent
        (R := I.subscheme.ringCatSheaf) (cokernel comparison) :=
      isQuasicoherent_cokernel comparison
    letI : SheafOfModules.IsFinitePresentation
        (R := I.subscheme.ringCatSheaf) (cokernel comparison) :=
      isFinitePresentation_cokernel comparison
    exact HasFiniteH.of_hom comparison
      (@finiteOfVanishing (kernel comparison)
        (isQuasicoherent_kernel comparison) (isFinitePresentation_kernel comparison)
        (isZero_restrict_kernel_of_isIso comparison W))
      (@finiteOfVanishing (cokernel comparison)
        (isQuasicoherent_cokernel comparison) (isFinitePresentation_cokernel comparison)
        (isZero_restrict_cokernel_of_isIso comparison W)) finiteN

/-- Coherent modules on proper schemes over a Noetherian ring have finite
cohomology over that ring in every degree. -/
theorem hasFiniteH_of_isProper {X : Scheme.{u}}
    (baseMap : X ⟶ Spec (.of A)) [IsProper baseMap]
    (moduleSheaf : X.Modules) [moduleSheaf.IsFinitePresentation] :
    HasFiniteH baseMap moduleSheaf := by
  letI : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) moduleSheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData moduleSheaf).choose.isQuasicoherent
  apply hasFiniteH_of_generic_approximation baseMap moduleSheaf
  intro ideal _ coefficientSheaf _ _
  exact exists_hasFiniteH_hom_isIso_restrict (ideal.subschemeι ≫ baseMap) coefficientSheaf

end AlgebraicGeometry.Scheme.Modules
