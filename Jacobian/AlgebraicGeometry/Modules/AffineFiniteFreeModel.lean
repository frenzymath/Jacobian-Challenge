import Jacobian.Algebra.Homology.DerivedCategory.Perfect.FiniteFree
import Jacobian.Algebra.Homology.DerivedCategory.Perfect.OfFlat
import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplex
import Jacobian.AlgebraicGeometry.Modules.PullbackTilde
import Jacobian.AlgebraicGeometry.Modules.TildeExactness
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Flat.Stability

/-!
# Finite free models on affine schemes

A bounded flat complex with finite cohomology over a Noetherian ring is perfect.
Its finite projective representative becomes finite free on a principal
neighbourhood of any prime. Sheafification gives a complex of finite free
module sheaves with the original bounds. The comparison remains a
quasi-isomorphism after every affine base change, without flatness of that
base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- On associated sheaves, every affine base change preserves a quasi-isomorphism
between bounded-above flat complexes. -/
theorem quasiIso_pullback_tilde_of_boundedAbove_flat
    {baseRing extensionRing : CommRingCat.{u}} (ringMap : baseRing ⟶ extensionRing)
    {source target : CochainComplex (ModuleCat.{u} baseRing) ℤ}
    (comparison : source ⟶ target) (upperBound : ℤ)
    [source.IsStrictlyLE upperBound] [target.IsStrictlyLE upperBound]
    (sourceFlat : ∀ degree, Module.Flat baseRing (source.X degree))
    (targetFlat : ∀ degree, Module.Flat baseRing (target.X degree))
    (quasiIso : QuasiIso comparison) :
    QuasiIso (((pullback (Spec.map ringMap)).mapHomologicalComplex (.up ℤ)).map
      (((tilde.functor baseRing).mapHomologicalComplex (.up ℤ)).map comparison)) := by
  haveI : (ModuleCat.extendScalars ringMap.hom ⋙ tilde.functor extensionRing).Additive :=
    Functor.additive_of_iso (tildePullbackIso ringMap)
  let extension := (ModuleCat.extendScalars ringMap.hom).mapHomologicalComplex (.up ℤ)
  let sourceSheaf := (tilde.functor baseRing).mapHomologicalComplex (.up ℤ)
  let targetSheaf := (tilde.functor extensionRing).mapHomologicalComplex (.up ℤ)
  let inverseImage := (pullback (Spec.map ringMap)).mapHomologicalComplex (.up ℤ)
  let baseChange : sourceSheaf ⋙ inverseImage ≅ extension ⋙ targetSheaf :=
    Functor.mapHomologicalComplexCompIso (tildePullbackIso ringMap) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := ModuleCat.extendScalars ringMap.hom) (G := tilde.functor extensionRing)
        (Iso.refl _) (.up ℤ)).symm
  haveI : QuasiIso (extension.map comparison) :=
    CochainComplex.quasiIso_extendScalars_of_boundedAbove_flat comparison upperBound
      sourceFlat targetFlat quasiIso ringMap.hom
  have sheafQuasiIso : QuasiIso (targetSheaf.map (extension.map comparison)) := inferInstance
  exact (quasiIso_iff_of_arrow_mk_iso
    (inverseImage.map (sourceSheaf.map comparison)) (targetSheaf.map (extension.map comparison))
    (Arrow.isoMk (baseChange.app source) (baseChange.app target)
      (baseChange.hom.naturality comparison).symm)).mpr sheafQuasiIso

private lemma exists_iso_free_tilde (baseRing : CommRingCat.{u})
    (moduleObject : ModuleCat.{u} baseRing) [Module.Free baseRing moduleObject]
    [Module.Finite baseRing moduleObject] :
    ∃ rank : ℕ, Nonempty (tilde moduleObject ≅ SheafOfModules.free
      (R := (Spec baseRing).ringCatSheaf) (ULift.{u} (Fin rank))) := by
  classical
  let indices := Module.Free.ChooseBasisIndex baseRing moduleObject
  let basis := Module.Free.chooseBasis baseRing moduleObject
  let reindex : indices ≃ ULift.{u} (Fin (Fintype.card indices)) :=
    (Fintype.equivFin indices).trans Equiv.ulift.symm
  exact ⟨Fintype.card indices,
    ⟨(tilde.functor baseRing).mapIso (basis.reindex reindex).repr.toModuleIso ≪≫
      tildeFinsupp (ULift.{u} (Fin (Fintype.card indices)))⟩⟩

/-- A bounded flat ring complex with finite cohomology has a finite free sheaf
model near each prime, and its actual comparison survives every affine base change. -/
theorem exists_finiteFree_model_tilde
    (baseRing : CommRingCat.{u}) [IsNoetherianRing baseRing]
    (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (upperBound : ℕ)
    [complex.IsStrictlyGE 0] [complex.IsStrictlyLE (upperBound : ℤ)]
    (flat : ∀ degree, Module.Flat baseRing (complex.X degree))
    (finite : ∀ degree, Module.Finite baseRing (complex.homology degree))
    (prime : Ideal baseRing) [prime.IsPrime] :
    ∃ denominator ∉ prime,
      ∃ model : CochainComplex (Spec (.of (Localization.Away denominator))).Modules ℤ,
        IsFiniteFreeComplex model upperBound ∧
        ∃ comparison : model ⟶
            ((pullback (Spec.map (CommRingCat.ofHom
              (algebraMap baseRing (Localization.Away denominator))))).mapHomologicalComplex
                (.up ℤ)).obj (((tilde.functor baseRing).mapHomologicalComplex (.up ℤ)).obj complex),
          QuasiIso comparison ∧
          ∀ (extensionRing : CommRingCat.{u})
            (ringMap : CommRingCat.of (Localization.Away denominator) ⟶ extensionRing),
            QuasiIso (((pullback (Spec.map ringMap)).mapHomologicalComplex (.up ℤ)).map
              comparison) := by
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} baseRing) :=
    HasDerivedCategory.standard (ModuleCat.{u} baseRing)
  have finiteDerived (degree : ℤ) : Module.Finite baseRing
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} baseRing) degree).obj
        (DerivedCategory.Q.obj complex)) := by
    haveI : Module.Finite baseRing (complex.homology degree) := finite degree
    exact Module.Finite.equiv (R := baseRing) (M := complex.homology degree)
      (N := (DerivedCategory.homologyFunctor (ModuleCat.{u} baseRing) degree).obj
        (DerivedCategory.Q.obj complex))
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} baseRing) degree).app
        complex).toLinearEquiv.symm
  have perfect : (DerivedCategory.Q.obj complex).IsPerfect :=
    DerivedCategory.isPerfect_of_flat_of_finite_homology complex 0 upperBound flat
      (Iso.refl _) finiteDerived
  obtain ⟨denominator, notMem, ringModel, below, above, freeFinite, ringComparison, ringQuasiIso⟩ :=
    DerivedCategory.exists_quasiIso_free_away_of_isPerfect complex 0 upperBound flat perfect prime
  let localRing : CommRingCat.{u} := CommRingCat.of (Localization.Away denominator)
  haveI : (tilde.functor localRing).Additive :=
    { map_add := fun {sourceModule targetModule} {firstMap secondMap} ↦
        tilde.map_add firstMap secondMap }
  haveI : (tilde.functor localRing).PreservesHomology :=
    tilde.preservesHomology.{u} localRing
  let localization : baseRing ⟶ localRing :=
    CommRingCat.ofHom (algebraMap baseRing (Localization.Away denominator))
  haveI : (ModuleCat.extendScalars localization.hom ⋙ tilde.functor localRing).Additive :=
    Functor.additive_of_iso (tildePullbackIso localization)
  let localComplex : CochainComplex (ModuleCat.{u} localRing) ℤ :=
    ((ModuleCat.extendScalars localization.hom).mapHomologicalComplex (.up ℤ)).obj complex
  let sheafification : CochainComplex (ModuleCat.{u} localRing) ℤ ⥤
      CochainComplex (Spec localRing).Modules ℤ :=
    (tilde.functor localRing).mapHomologicalComplex (.up ℤ)
  let model : CochainComplex (Spec localRing).Modules ℤ := sheafification.obj ringModel
  let compatibility :=
    (Functor.mapHomologicalComplexCompIso (tildePullbackIso localization) (.up ℤ)).app complex
  let comparison := sheafification.map ringComparison ≫ compatibility.inv
  haveI : ringModel.IsStrictlyGE 0 := below
  haveI : ringModel.IsStrictlyLE (upperBound : ℤ) := above
  haveI : QuasiIso ringComparison := ringQuasiIso
  haveI : localComplex.IsStrictlyLE (upperBound : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree degreeBound
    exact (ModuleCat.extendScalars localization.hom).map_isZero
      (complex.isZero_of_isStrictlyLE upperBound degree degreeBound)
  have modelBelow : model.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro degree degreeBound
    exact (tilde.functor localRing).map_isZero
      (ringModel.isZero_of_isStrictlyGE 0 degree degreeBound)
  have modelAbove : model.IsStrictlyLE (upperBound : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree degreeBound
    exact (tilde.functor localRing).map_isZero
      (ringModel.isZero_of_isStrictlyLE upperBound degree degreeBound)
  have modelFree (degree : ℤ) : ∃ rank : ℕ,
      Nonempty (model.X degree ≅ SheafOfModules.free
        (R := (Spec localRing).ringCatSheaf) (ULift.{u} (Fin rank))) := by
    obtain ⟨freeTerm, finiteTerm⟩ := freeFinite degree
    letI := freeTerm
    letI := finiteTerm
    exact exists_iso_free_tilde localRing (ringModel.X degree)
  have ringModelFlat (degree : ℤ) : Module.Flat localRing (ringModel.X degree) := by
    haveI := (freeFinite degree).1
    infer_instance
  have localComplexFlat (degree : ℤ) : Module.Flat localRing (localComplex.X degree) := by
    haveI := flat degree
    exact Module.Flat.of_linearEquiv
      (ModuleCat.tensorEquivExtendScalars baseRing (Localization.Away denominator)
        (complex.X degree)).symm
  refine ⟨denominator, notMem, model, ⟨modelBelow, modelAbove, modelFree⟩,
    comparison, ?_, ?_⟩
  · have sheafifiedQuasiIso : QuasiIso (sheafification.map ringComparison) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology ringComparison
        (tilde.functor localRing)
    exact (quasiIso_iff_comp_right (sheafification.map ringComparison) compatibility.inv).mpr
      sheafifiedQuasiIso
  · intro extensionRing ringMap
    haveI := quasiIso_pullback_tilde_of_boundedAbove_flat ringMap ringComparison upperBound
      ringModelFlat localComplexFlat ringQuasiIso
    dsimp only [comparison]
    rw [Functor.map_comp]
    infer_instance

/-- A quasi-coherent affine complex is locally represented by finite free sheaves
as soon as its complex of global sections is bounded flat with finite cohomology.
The comparison is preserved by every affine base change. -/
theorem exists_finiteFree_model_of_finite_homology
    (baseRing : CommRingCat.{u}) [IsNoetherianRing baseRing]
    (complex : CochainComplex (Spec baseRing).Modules ℤ) (upperBound : ℕ)
    [complex.IsStrictlyGE 0] [complex.IsStrictlyLE (upperBound : ℤ)]
    (quasicoherent : ∀ degree, (complex.X degree).IsQuasicoherent)
    (flat : ∀ degree, Module.Flat baseRing ((moduleSpecΓFunctor (R := baseRing)).obj
      (complex.X degree)))
    (finite : ∀ degree, Module.Finite baseRing
      ((((moduleSpecΓFunctor (R := baseRing)).mapHomologicalComplex (.up ℤ)).obj complex).homology
        degree))
    (prime : Ideal baseRing) [prime.IsPrime] :
    ∃ denominator ∉ prime,
      ∃ model : CochainComplex (Spec (.of (Localization.Away denominator))).Modules ℤ,
        IsFiniteFreeComplex model upperBound ∧
        ∃ comparison : model ⟶
            ((pullback (Spec.map (CommRingCat.ofHom
              (algebraMap baseRing (Localization.Away denominator))))).mapHomologicalComplex
                (.up ℤ)).obj complex,
          QuasiIso comparison ∧
          ∀ (extensionRing : CommRingCat.{u})
            (ringMap : CommRingCat.of (Localization.Away denominator) ⟶ extensionRing),
            QuasiIso (((pullback (Spec.map ringMap)).mapHomologicalComplex (.up ℤ)).map
              comparison) := by
  let sections := (moduleSpecΓFunctor (R := baseRing)).mapHomologicalComplex (.up ℤ)
  let ringComplex : CochainComplex (ModuleCat.{u} baseRing) ℤ := sections.obj complex
  haveI : ringComplex.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro degree degreeBound
    exact (moduleSpecΓFunctor (R := baseRing)).map_isZero
      (complex.isZero_of_isStrictlyGE 0 degree degreeBound)
  haveI : ringComplex.IsStrictlyLE (upperBound : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree degreeBound
    exact (moduleSpecΓFunctor (R := baseRing)).map_isZero
      (complex.isZero_of_isStrictlyLE upperBound degree degreeBound)
  let reconstruction :
      ((tilde.functor baseRing).mapHomologicalComplex (.up ℤ)).obj ringComplex ⟶ complex :=
    { f degree := (complex.X degree).fromTildeΓ
      comm' sourceDegree targetDegree _ :=
        (fromTildeΓNatTrans.naturality (complex.d sourceDegree targetDegree)).symm }
  haveI componentIso (degree : ℤ) : IsIso (reconstruction.f degree) := by
    haveI := quasicoherent degree
    exact inferInstanceAs (IsIso (complex.X degree).fromTildeΓ)
  haveI : IsIso reconstruction := HomologicalComplex.Hom.isIso_of_components reconstruction
  obtain ⟨denominator, notMem, model, modelFree, comparison, quasiIso, baseChange⟩ :=
    exists_finiteFree_model_tilde baseRing ringComplex upperBound flat finite prime
  let localization := CommRingCat.ofHom (algebraMap baseRing (Localization.Away denominator))
  let inverseImage := (pullback (Spec.map localization)).mapHomologicalComplex (.up ℤ)
  haveI : QuasiIso comparison := quasiIso
  refine ⟨denominator, notMem, model, modelFree,
    comparison ≫ inverseImage.map reconstruction, inferInstance, ?_⟩
  intro extensionRing ringMap
  haveI := baseChange extensionRing ringMap
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
