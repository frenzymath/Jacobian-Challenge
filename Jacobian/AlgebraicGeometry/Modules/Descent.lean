import Jacobian.AlgebraicGeometry.Modules.DescentEffective
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeRank
import Jacobian.AlgebraicGeometry.Modules.PullbackTilde
import Jacobian.RingTheory.FaithfullyFlat.FinitePresentation
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Invertible

/-!
# Rank-one fpqc descent

Effective fpqc descent constructs a quasi-coherent module. Finite presentation,
flatness and constant rank descend on affine refinements, so a quasi-coherent
module with invertible descent components is invertible.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory Opposite CategoryTheory.Bicategory CategoryTheory.Limits
namespace AlgebraicGeometry
variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

namespace Scheme.Modules

/-- **Finite local freeness of rank `r` descends along a faithfully flat map of affine schemes**
`Spec.map φ : Spec B ⟶ Spec R`, for quasi-coherent modules: the global sections of the pullback
are `B ⊗[R] Γ(P, ⊤)`, and finite presentation, flatness and rank descend along `R ⟶ B`. -/
theorem isFiniteLocallyFreeOfRank_of_pullback_Spec_map {R B : CommRingCat.{u}} (φ : R ⟶ B)
    [Flat (Spec.map φ)] [Surjective (Spec.map φ)] (P : (Spec R).Modules) [P.IsQuasicoherent]
    {r : ℕ} [((pullback (Spec.map φ)).obj P).IsFiniteLocallyFreeOfRank r] :
    P.IsFiniteLocallyFreeOfRank r := by
  obtain ⟨_, _, hrank⟩ := rankAtStalk_eq_of_isFiniteLocallyFreeOfRank
    ((pullback (Spec.map φ)).obj P) (r := r)
  have hφ : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩
  let e := pullbackSpecΓEquiv φ P
  have hfp : Module.FinitePresentation B
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) := .of_equiv e.symm
  have hfl : Module.Flat B
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) := .of_linearEquiv e
  have hrank' (q : PrimeSpectrum B) : Module.rankAtStalk
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) q = r := by
    rw [Module.rankAtStalk_eq_of_equiv e, hrank]
  algebraize [φ.hom]
  have : Module.FinitePresentation B (TensorProduct R B Γ(P, ⊤)) := by exact hfp
  have : Module.Flat B (TensorProduct R B Γ(P, ⊤)) := by exact hfl
  have : Module.FinitePresentation R Γ(P, ⊤) :=
    .of_finitePresentation_tensorProduct_of_faithfullyFlat (B := B)
  have : Module.Flat R Γ(P, ⊤) := .of_flat_tensorProduct _ _ B
  exact isFiniteLocallyFreeOfRank_of_rankAtStalk_eq P
    (Module.rankAtStalk_eq_of_rankAtStalk_tensorProduct_eq (B := B) hrank')

/-- **Finite local freeness of rank `r` descends along a flat surjective morphism**
`F : W ⟶ Spec R` from an affine scheme, for quasi-coherent modules on `Spec R`. -/
theorem isFiniteLocallyFreeOfRank_of_pullback_of_isAffine {R : CommRingCat.{u}} {W : Scheme.{u}}
    [IsAffine W] (F : W ⟶ Spec R) [Flat F] [Surjective F] (P : (Spec R).Modules)
    [P.IsQuasicoherent] {r : ℕ} [((pullback F).obj P).IsFiniteLocallyFreeOfRank r] :
    P.IsFiniteLocallyFreeOfRank r := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ F)
  have : Flat (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Surjective (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : ((pullback (Spec.map φ)).obj P).IsFiniteLocallyFreeOfRank r :=
    .of_iso (pullbackCompOfEq W.isoSpec.inv F _ hφ.symm P)
  exact isFiniteLocallyFreeOfRank_of_pullback_Spec_map φ P

/-- **Finite local freeness of rank `r` descends along a finite jointly surjective family of
flat morphisms** `f j : W j ⟶ Spec R` from affine schemes, for quasi-coherent modules on
`Spec R`: the morphism `∐ W j ⟶ Spec R` is flat and surjective, with affine source. -/
theorem isFiniteLocallyFreeOfRank_of_pullback_of_iUnion_range_eq_univ {R : CommRingCat.{u}}
    (P : (Spec R).Modules) [P.IsQuasicoherent] {κ : Type u} [Finite κ] {W : κ → Scheme.{u}}
    [∀ j, IsAffine (W j)] (f : ∀ j, W j ⟶ Spec R) [∀ j, Flat (f j)]
    (hf : ⋃ j, Set.range (f j) = Set.univ) {r : ℕ}
    (h : ∀ j, ((pullback (f j)).obj P).IsFiniteLocallyFreeOfRank r) :
    P.IsFiniteLocallyFreeOfRank r := by
  have : Surjective (Sigma.desc f) := .sigmaDesc_of_union_range_eq_univ hf
  have : ((pullback (Sigma.desc f)).obj P).IsFiniteLocallyFreeOfRank r := by
    refine isFiniteLocallyFreeOfRank_of_isOpenImmersion _ (Sigma.ι W)
      (sigmaOpenCover W).iSup_opensRange fun j ↦ ?_
    have := h j
    exact .of_iso (pullbackCompOfEq _ _ _ (Sigma.ι_desc f j) P).symm
  exact isFiniteLocallyFreeOfRank_of_pullback_of_isAffine (Sigma.desc f) P

end Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine-local step of `isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent`:
the pullback of `M` to the spectrum of the ring of sections of an affine open is finite locally
free of rank `r`. The covering is refined over `U` by finitely many flat affine schemes; their
disjoint union is the spectrum of a faithfully flat `Γ(T, U)`-algebra `B`, over which the
global sections of `M` become finite locally free of rank `r`, and finite presentation, flatness
and rank descend along `Γ(T, U) → B`. -/
theorem isFiniteLocallyFreeOfRank_pullback_fromSpec_of_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T))) (hMq : (M : T.Modules).IsQuasicoherent)
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D)) (r : ℕ)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFiniteLocallyFreeOfRank r)
    {U : T.Opens} (hU : IsAffineOpen U) :
    ((Scheme.Modules.pullback hU.fromSpec).obj M).IsFiniteLocallyFreeOfRank r := by
  obtain ⟨e⟩ := hM
  obtain ⟨κ, W, f, _, _, _, hfS, hcov⟩ := Scheme.exists_finite_affine_flat_of_mem_fpqcTopology
    (Scheme.fpqcTopology.pullback_stable hU.fromSpec hg)
  choose i k hk using fun j ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hfS j)
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_pullback_of_iUnion_range_eq_univ _ f ?_
    fun j ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology hcov x
    obtain ⟨j, k', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
    exact Set.mem_iUnion.2 ⟨j, k' y, rfl⟩
  ·
    have := hD (i j)
    let c : (Scheme.Modules.pullback (g (i j))).obj M ≅ D.obj (i j) :=
      ⟨e.hom.hom (i j), e.inv.hom (i j), congrArg (fun φ ↦ φ.hom (i j)) e.hom_inv_id,
        congrArg (fun φ ↦ φ.hom (i j)) e.inv_hom_id⟩
    exact .of_iso ((Scheme.Modules.pullback (k j)).mapIso c.symm ≪≫
      pullbackCompOfEq (k j) (g (i j)) _ rfl M ≪≫
      (pullbackCompOfEq (f j) hU.fromSpec _ (hk j) M).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Finite local freeness of a fixed rank descends along an fpqc covering**, for a
quasi-coherent module. -/
theorem isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T))) (hMq : (M : T.Modules).IsQuasicoherent)
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D)) (r : ℕ)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFiniteLocallyFreeOfRank r) :
    (M : T.Modules).IsFiniteLocallyFreeOfRank r := by
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion (M : T.Modules)
    (fun U : T.affineOpens ↦ U.2.fromSpec) ?_ fun U ↦
      isFiniteLocallyFreeOfRank_pullback_fromSpec_of_toDescentData_iso g hg D M hMq hM r hD U.2
  simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top T

/-- A quasi-coherent module with invertible components in an fpqc descent datum
is invertible. The quasi-coherence witness is supplied by effective descent. -/
theorem isInvertible_of_toDescentData_iso_of_isQuasicoherent
    (covering : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (datum : modulesPseudofunctor.DescentData g)
    (moduleSheaf : modulesPseudofunctor.obj (.mk (op T)))
    (quasicoherent : (moduleSheaf : T.Modules).IsQuasicoherent)
    (comparison : Nonempty ((modulesPseudofunctor.toDescentData g).obj moduleSheaf ≅ datum))
    (invertible : ∀ index, (datum.obj index : (T' index).Modules).IsInvertible) :
    (moduleSheaf : T.Modules).IsInvertible :=
  (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u, u, u}
    (moduleSheaf : T.Modules)).mpr
    (isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent g covering datum
      moduleSheaf quasicoherent comparison 1 fun index ↦
        (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u, u, u}
          (datum.obj index : (T' index).Modules)).mp
          (invertible index))

end AlgebraicGeometry
