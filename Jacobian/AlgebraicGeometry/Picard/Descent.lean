import Jacobian.AlgebraicGeometry.Modules.Descent
import Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.Dual
import Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import Jacobian.AlgebraicGeometry.Modules.PushforwardUnit
import Jacobian.AlgebraicGeometry.Picard.DescentCocycle
import Jacobian.AlgebraicGeometry.Modules.DescentIsomorphism
import Jacobian.AlgebraicGeometry.Picard.NormalizedSheaf
import Jacobian.AlgebraicGeometry.Sites.Fpqc
import Jacobian.AlgebraicGeometry.Sites.Fppf

/-!
# Effective descent of normalized Picard classes

A section rigidifies transition isomorphisms of invertible sheaves. If the
structure-sheaf pushforward unit is universally an isomorphism, normalized
transition maps are unique and satisfy the cocycle condition. Effective fpqc
descent glues these sheaves; twisting by the inverse section pullback gives
a normalized gluing. Thus normalized classes form an fpqc, hence fppf, sheaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme
variable {X S : Scheme.{u}}

/-- Two invertible sheaves with the same fpqc-local class differ by a sheaf from
the base when the structure-sheaf pushforward unit is universally an isomorphism. -/

theorem exists_iso_tensorObj_of_pic_map_eq (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) {T : Over S}
    {ι : Type*} {Z : ι → Scheme.{u}} (a : ∀ i, Z i ⟶ T.left)
    (hR : Presieve.ofArrows Z a ∈ fpqcPrecoverage T.left) (L L' : (Limits.pullback f T.hom).Pic)
    (heq : ∀ i, Pic.map (baseChangeMap f (Over.homMk (U := Over.mk (a i ≫ T.hom)) (a i))) L =
      Pic.map (baseChangeMap f (Over.homMk (U := Over.mk (a i ≫ T.hom)) (a i))) L') :
    ∃ N : T.left.Pic, Nonempty ((fromSkeleton _).obj L.val ≅ (fromSkeleton _).obj L'.val ⊗
      (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) := by
  have hbij (Y : Over S) : Function.Bijective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    bijective_appTop_of_isIso_pushforwardUnitMap _
  let T' (i : ι) : Over S := Over.mk (a i ≫ T.hom)
  let g (i : ι) : T' i ⟶ T := Over.homMk (a i)

  have hgT : Sieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcTopology T.left :=
    Precoverage.generate_mem_toGrothendieck hR
  have hgX : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
      fpqcTopology (pullback f T.hom) :=
    Precoverage.generate_mem_toGrothendieck
      (Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) hR (pullback.snd f T.hom)
        (fun i ↦ baseChangeMap f (g i)) (fun i ↦ pullback.snd f (T' i).hom)
        (fun i ↦ isPullback_baseChangeMap f (g i)))

  let A := (fromSkeleton _).obj L.val
  let B := (fromSkeleton _).obj L'.val
  have := L.isInvertible
  have := L'.isInvertible
  let eB := Modules.tensorObjDualIsoUnit B
  let K := A ⊗ Modules.dual B
  let P : (pullback f T.hom).Modules :=
    (Modules.pullback (pullback.snd f T.hom)).obj (𝟙_ T.left.Modules)
  have eK (i : ι) : Nonempty ((Modules.pullback (baseChangeMap f (g i))).obj K ≅
      (Modules.pullback (baseChangeMap f (g i))).obj P) := by
    obtain ⟨eAB⟩ := Pic.eq_iff_nonempty_iso.1 (heq i)
    exact ⟨(Modules.pullbackTensorObjIso _ _ _) ≪≫
      (((fromSkeletonToSkeletonIso _).symm ≪≫ eAB ≪≫ fromSkeletonToSkeletonIso _) ⊗ᵢ
        Iso.refl _) ≪≫ (Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Modules.pullback _).mapIso eB ≪≫ Modules.pullbackObjUnitIso _ ≪≫
      (Modules.pullbackObjUnitIso _).symm ≪≫
      (Modules.pullback _).mapIso (Modules.pullbackObjUnitIso _).symm⟩

  have hD₂ (i : ι) : SheafOfModules.IsInvertible.{u, u, u}
      ((((modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj P).obj i) :
        (pullback f (T' i).hom).Modules) :=
    inferInstanceAs ((Modules.pullback (baseChangeMap f (g i))).obj P).IsInvertible
  obtain ⟨cX, ⟨eKD⟩⟩ := DescentCocycle.exists_iso_twist
    (D₁ := (modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj K)
    (D₂ := (modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj P) eK

  let cT := cX.ofBaseChange hbij
  let DT := cT.twist ((modulesPseudofunctor.toDescentData fun i ↦ (g i).left).obj
    (𝟙_ T.left.Modules))
  obtain ⟨N, hNq, ⟨eN⟩⟩ := exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology _ hgT DT fun i ↦
    (by
      have : SheafOfModules.IsInvertible.{u, u, u}
          ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules)) :=
        inferInstance
      infer_instance :
      ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules)).IsQuasicoherent)
  have : SheafOfModules.IsInvertible.{u, u, u} (N : T.left.Modules) :=
    isInvertible_of_toDescentData_iso_of_isQuasicoherent _ hgT DT N hNq ⟨eN⟩ fun i ↦
      inferInstanceAs ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules)).IsInvertible
  let N' : T.left.Modules := N

  have w (i : ι) : pullback.snd f (T' i).hom ≫ (g (id i)).left =
      baseChangeMap f (g i) ≫ pullback.snd f T.hom :=
    (baseChangeMap_snd f (g i)).symm
  let E :=
    ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor w).app
      N).symm ≪≫
    (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor w).mapIso eN ≪≫
    eqToIso (cT.pullFunctor_obj_twist w _) ≪≫
    (cT.pull w).twistFunctor.mapIso
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor w).app _) ≪≫
    eqToIso (congrArg (fun c ↦ DescentCocycle.twist c _) (cX.pull_ofBaseChange hbij)) ≪≫
    eKD.symm
  have : SheafOfModules.IsInvertible.{u, u, u} K :=
    inferInstanceAs K.IsInvertible
  obtain ⟨eNK⟩ := nonempty_iso_of_toDescentData_iso _ hgX
    (inferInstanceAs ((Modules.pullback (pullback.snd f T.hom)).obj N').IsQuasicoherent)
    (inferInstanceAs K.IsQuasicoherent) E
  refine ⟨Pic.mk N', ⟨?_⟩⟩
  exact (ρ_ A).symm ≪≫ whiskerLeftIso A (eB.symm ≪≫ β_ B _) ≪≫ (α_ A _ B).symm ≪≫
    β_ K B ≪≫ whiskerLeftIso B (eNK.symm ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso N').symm)

/-- Normalized classes differing only by sheaves from the base are equal. -/
theorem picardFunctorNormalized_eq_of_iso_tensorObj (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {T : Over S}
    (L L' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T))
    (P : (Limits.pullback f T.hom).Modules) (N N' : T.left.Modules)
    (e : (fromSkeleton _).obj L.1.val ≅
      P ⊗ (Modules.pullback (Limits.pullback.snd f T.hom)).obj N)
    (e' : (fromSkeleton _).obj L'.1.val ≅
      P ⊗ (Modules.pullback (Limits.pullback.snd f T.hom)).obj N') :
    L = L' := by
  have key (M : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T)) (Q : T.left.Modules)
      (eM : (fromSkeleton _).obj M.1.val ≅
        P ⊗ (Modules.pullback (Limits.pullback.snd f T.hom)).obj Q) :
      Nonempty (𝟙_ T.left.Modules ≅
        (Modules.pullback (sectionBaseChange f σ hσ T)).obj P ⊗ Q) := by
    obtain ⟨n⟩ := Pic.nonempty_iso_unit_of_map_eq_one _ M.2
    let t := Modules.pullbackTensorObjIso (sectionBaseChange f σ hσ T) P
      ((Modules.pullback (Limits.pullback.snd f T.hom)).obj Q)
    exact ⟨n.symm ≪≫ (Modules.pullback _).mapIso eM ≪≫ t ≪≫
      whiskerLeftIso _ (pullbackSectionBaseChangeSndIso f σ hσ T Q)⟩
  obtain ⟨n⟩ := key L N e
  obtain ⟨n'⟩ := key L' N' e'

  let i : N ≅ N' := (λ_ N).symm ≪≫ whiskerRightIso n' N ≪≫ whiskerRightIso (β_ _ N') N ≪≫
    α_ N' _ N ≪≫ whiskerLeftIso N' n.symm ≪≫ ρ_ N'
  exact Subtype.ext (Pic.eq_iff_nonempty_iso.2
    ⟨e ≪≫ whiskerLeftIso P ((Modules.pullback _).mapIso i) ≪≫ e'.symm⟩)

/-- Universal triviality of the structure-sheaf pushforward unit makes normalized
Picard classes an fpqc sheaf, by effective descent of rigidified invertible sheaves. -/
theorem isSheaf_fpqc_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor := by
  have hsurj (Y : Over S) : Function.Surjective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    surjective_appTop_of_isIso_pushforwardUnitMap _
  rw [isSheaf_iff_isSheaf_of_type, over_toGrothendieck_eq_toGrothendieck_comap_forget,
    ← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage]
  intro T R hR
  obtain ⟨ι, T', g, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcPrecoverage T.left := by
    simpa [Precoverage.mem_comap_iff, Presieve.map_ofArrows] using hR
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  refine existsUnique_of_exists_of_unique ?_ ?_
  ·
    let L (i : ι) : (pullback f (T' i).hom).Modules := (fromSkeleton _).obj (x i).1.val
    have hL (i : ι) : (L i).IsInvertible :=
      (x i).1.isInvertible
    let α (i : ι) : (Modules.pullback (sectionBaseChange f σ hσ (T' i))).obj (L i) ≅
        (Modules.pullback (g i).left).obj (SheafOfModules.unit T.left.ringCatSheaf) :=
      (Pic.nonempty_iso_unit_of_map_eq_one _ (x i).2).some ≪≫ (Modules.pullbackObjUnitIso _).symm

    have hxij (i j : ι) : Pic.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁ (x i).1 =
        Pic.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂ (x j).1 :=
      congrArg Subtype.val (hx i j _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    let e (i j : ι) : (Modules.pullback (chosenPullbackBaseChangeMap f (g i) (g j)).p₁).obj (L i) ≅
        (Modules.pullback (chosenPullbackBaseChangeMap f (g i) (g j)).p₂).obj (L j) :=
      (fromSkeletonToSkeletonIso _).symm ≪≫ (Pic.eq_iff_nonempty_iso.1 (hxij i j)).some ≪≫
        fromSkeletonToSkeletonIso _
    let D := normalizedDescentData (sectionBaseChange_snd f σ hσ)
      (sectionBaseChange_comp_baseChangeMap f σ hσ) hsurj (L := L) α e

    have hg : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
        fpqcTopology (pullback f T.hom) :=
      Precoverage.generate_mem_toGrothendieck
        (Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) hR' (pullback.snd f T.hom)
          (fun i ↦ baseChangeMap f (g i)) (fun i ↦ pullback.snd f (T' i).hom)
          (fun i ↦ isPullback_baseChangeMap f (g i)))
    obtain ⟨M, hMq, ⟨eM⟩⟩ := exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology _ hg D.descentData
      (fun i ↦ by
        change (L i).IsQuasicoherent
        have : SheafOfModules.IsInvertible.{u, u, u} (L i) :=
          hL i
        infer_instance)
    have : SheafOfModules.IsInvertible.{u, u, u} (M : (pullback f T.hom).Modules) :=
      isInvertible_of_toDescentData_iso_of_isQuasicoherent _ hg D.descentData M hMq ⟨eM⟩
        (fun i ↦ hL i)
    let M' : (pullback f T.hom).Modules := M
    have hM : M'.IsInvertible := inferInstance

    let eMi (i : ι) : (Modules.pullback (baseChangeMap f (g i))).obj M' ≅ L i :=
      { hom := eM.hom.hom i
        inv := eM.inv.hom i
        hom_inv_id := by
          rw [← Pseudofunctor.DescentData.comp_hom, eM.hom_inv_id,
            Pseudofunctor.DescentData.id_hom]
          rfl
        inv_hom_id := by
          rw [← Pseudofunctor.DescentData.comp_hom, eM.inv_hom_id,
            Pseudofunctor.DescentData.id_hom]
          rfl }

    let Mσ := (Modules.pullback (sectionBaseChange f σ hσ T)).obj M'
    let eN' := Modules.tensorObjDualIsoUnit Mσ
    let M₁ := M' ⊗ (Modules.pullback (pullback.snd f T.hom)).obj (Modules.dual Mσ)
    have : SheafOfModules.IsInvertible.{u, u, u} M₁ :=
      inferInstanceAs M₁.IsInvertible
    refine ⟨⟨Pic.mk M₁, Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M₁) ≪≫
      (Modules.pullbackTensorObjIso _ _ _) ≪≫
      (Iso.refl Mσ ⊗ᵢ pullbackSectionBaseChangeSndIso f σ hσ T _) ≪≫ eN' ≪≫
      (fromSkeletonToSkeletonIso _).symm⟩⟩, fun i ↦ Subtype.ext ?_⟩

    let A : (Modules.pullback (g i).left).obj Mσ ≅ SheafOfModules.unit _ :=
      (Modules.pullbackComp _ _).app M' ≪≫
        (Modules.pullbackCongr (sectionBaseChange_comp_baseChangeMap f σ hσ (g i)).symm).app M' ≪≫
        ((Modules.pullbackComp _ _).app M').symm ≪≫ (Modules.pullback _).mapIso (eMi i) ≪≫
        (Pic.nonempty_iso_unit_of_map_eq_one _ (x i).2).some
    let E : (Modules.pullback (g i).left).obj (Modules.dual Mσ) ≅ SheafOfModules.unit _ :=
      (λ_ _).symm ≪≫ (A.symm ⊗ᵢ Iso.refl _) ≪≫
        (Modules.pullbackTensorObjIso _ _ _).symm ≪≫
        (Modules.pullback _).mapIso eN' ≪≫ Modules.pullbackObjUnitIso _
    exact Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M₁) ≪≫
      (Modules.pullbackTensorObjIso _ _ _) ≪≫
      (eMi i ⊗ᵢ ((Modules.pullbackComp _ _).app _ ≪≫
        (Modules.pullbackCongr (Limits.pullback.lift_snd _ _ _)).app _ ≪≫
        ((Modules.pullbackComp _ _).app _).symm ≪≫ (Modules.pullback _).mapIso E ≪≫
        Modules.pullbackObjUnitIso _)) ≪≫ ρ_ _⟩
  · intro t t' ht ht'
    have heq (i : ι) : Pic.map (baseChangeMap f
        (Over.homMk (U := Over.mk ((g i).left ≫ T.hom)) (g i).left)) t.1 =
          Pic.map (baseChangeMap f
            (Over.homMk (U := Over.mk ((g i).left ≫ T.hom)) (g i).left)) t'.1 := by
      have e : (Over.homMk (U := Over.mk ((g i).left ≫ T.hom)) (g i).left : _ ⟶ T) =
          Over.homMk (U := Over.mk ((g i).left ≫ T.hom)) (V := T' i) (𝟙 _)
            (by simpa using (Over.w (g i)).symm) ≫ g i := by
        ext
        simp
      have h := congrArg Subtype.val ((ht i).trans (ht' i).symm)
      rw [e, baseChangeMap_comp, Pic.map_comp, Pic.map_comp]
      exact congrArg _ h
    obtain ⟨N, ⟨e⟩⟩ := exists_iso_tensorObj_of_pic_map_eq f hf (fun i ↦ (g i).left) hR' t.1 t'.1
      heq
    exact picardFunctorNormalized_eq_of_iso_tensorObj f σ hσ t t' _ ((fromSkeleton _).obj N.val)
      (SheafOfModules.unit _) e
      ((ρ_ _).symm ≪≫ whiskerLeftIso _ (Modules.pullbackObjUnitIso _).symm)

/-- Normalized Picard classes form an fppf sheaf under the universal
structure-sheaf pushforward-unit hypothesis. -/
theorem isSheaf_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor :=
  (isSheaf_fpqc_picardFunctorNormalized f σ hσ hf).of_le fun T R hR ↦ by
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact Precoverage.toGrothendieck_mono fppfPrecoverage_le_fpqcPrecoverage _ hR

/-- Normalized Picard classes also satisfy Zariski descent. -/
theorem isSheaf_zariski_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor :=
  (isSheaf_picardFunctorNormalized f σ hσ hf).of_le fun T R hR ↦ by
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage _ hR

/-- Under the universal pushforward-unit hypothesis, the normalized presheaf maps
isomorphically onto the relative Picard sheaf. -/
theorem isIso_picardFunctorNormalized_ι_comp_toPicardFunctor (morphism : X ⟶ S)
    (sectionMorphism : S ⟶ X) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 S)
    (unitIsomorphism : ∀ parameter : Over S,
      IsIso (pushforwardUnitMap (pullback.snd morphism parameter.hom))) :
    IsIso ((picardFunctorNormalized morphism sectionMorphism sectionCondition).ι ≫
      toPicardFunctor morphism) :=
  (isIso_picardFunctorNormalized_ι_comp_toPicardFunctor_iff morphism
    sectionMorphism sectionCondition).mpr
      (isSheaf_picardFunctorNormalized morphism sectionMorphism sectionCondition unitIsomorphism)

/-- Universal triviality of the pushforward unit identifies normalized classes
with the fppf Picard functor, before sheafification. -/
def picardFunctorNormalizedIso (morphism : X ⟶ S) (sectionMorphism : S ⟶ X)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 S)
    (unitIsomorphism : ∀ parameter : Over S,
      IsIso (pushforwardUnitMap (pullback.snd morphism parameter.hom))) :
    (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor ≅
      (picardFunctor morphism).obj := by
  letI := isIso_picardFunctorNormalized_ι_comp_toPicardFunctor morphism
    sectionMorphism sectionCondition unitIsomorphism
  exact asIso ((picardFunctorNormalized morphism sectionMorphism sectionCondition).ι ≫
    toPicardFunctor morphism)

/-- Representability of normalized classes and of the relative Picard functor
are equivalent under the universal pushforward-unit hypothesis. -/
theorem isRepresentable_picardFunctorNormalized_iff (morphism : X ⟶ S)
    (sectionMorphism : S ⟶ X) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 S)
    (unitIsomorphism : ∀ parameter : Over S,
      IsIso (pushforwardUnitMap (pullback.snd morphism parameter.hom))) :
    (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor.IsRepresentable ↔
      (picardFunctor morphism).obj.IsRepresentable :=
  isRepresentable_picardFunctorNormalized_iff_of_isSheaf morphism sectionMorphism sectionCondition
    (isSheaf_picardFunctorNormalized morphism sectionMorphism sectionCondition unitIsomorphism)

end AlgebraicGeometry
