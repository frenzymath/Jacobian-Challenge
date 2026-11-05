import Jacobian.AlgebraicGeometry.Limits.Proper
import Jacobian.AlgebraicGeometry.Limits.Approximation

/-!
# Noetherian models of proper finitely presented families

A proper locally finitely presented family over any affine scheme is the
Cartesian base change of a proper finitely presented family over a Noetherian
ring. The original base need not be Noetherian, and no model is supplied.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A proper finitely presented family over an affine inverse limit descends
to a proper finitely presented family at an actual Noetherian ring stage. -/
theorem Scheme.exists_isPullback_of_isProper_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c)
    {Z : Scheme.{u}} (f : Z ⟶ c.pt) [IsProper f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (i : I) (Zi : Scheme.{u}) (fi : Zi ⟶ Spec (R.obj i)) (a : Z ⟶ Zi),
      IsProper fi ∧ LocallyOfFinitePresentation fi ∧ QuasiCompact fi ∧
        QuasiSeparated fi ∧ IsPullback a f fi (c.π.app (Opposite.op i)) := by
  let D := R.op ⋙ Scheme.Spec
  have (i : Iᵒᵖ) : IsLocallyNoetherian (D.obj i) := by dsimp [D]; infer_instance
  have (i : Iᵒᵖ) : CompactSpace (D.obj i) := by dsimp [D]; infer_instance
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by dsimp [D]; infer_instance
  have {i j : Iᵒᵖ} (t : i ⟶ j) : IsAffineHom (D.map t) := by
    dsimp [D]
    infer_instance
  obtain ⟨i, Zi, fi, hfp, hqc, hqs, a, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hc f
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Zi := QuasiCompact.compactSpace_of_compactSpace fi
  have : QuasiSeparatedSpace Zi := quasiSeparatedSpace_of_quasiSeparated fi
  have hs : IsProper (pullback.snd fi (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let ψ := pullback.map fi (c.π.app i) (𝟙 (D.obj i)) (c.π.app i)
    fi (𝟙 c.pt) (𝟙 (D.obj i)) (Category.comp_id fi)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hψ : IsProper ψ := by
    have he : ψ ≫ pullback.snd (𝟙 (D.obj i)) (c.π.app i) =
        pullback.snd fi (c.π.app i) := by
      dsimp [ψ]
      simp only [pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he] at hs
    exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mp hs
  obtain ⟨j, hij, hj⟩ := Scheme.exists_isProper_baseChange_of_isLimit D c hc i.unop
    fi (𝟙 (D.obj i)) fi (by simp) hψ
  let t := D.map (homOfLE hij).op
  let fj := pullback.snd fi t
  have hfj : IsProper fj := by
    have he :
        (pullback.map fi t (𝟙 (D.obj i)) t fi (𝟙 (D.obj (Opposite.op j)))
          (𝟙 (D.obj i)) (Category.comp_id fi) (Category.comp_id t)) ≫
            pullback.snd (𝟙 (D.obj i)) t = fj := by
      simp only [pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he]
    have := hj
    infer_instance
  let aj : Z ⟶ pullback fi t := pullback.lift a (f ≫ c.π.app (Opposite.op j)) (by
    rw [Category.assoc, c.w (homOfLE hij).op, H.w])
  have Hj : IsPullback aj f fj (c.π.app (Opposite.op j)) := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback fi t)
    · rw [show aj ≫ pullback.fst fi t = a from pullback.lift_fst _ _ _]
      change IsPullback a f fi (c.π.app (Opposite.op j) ≫ D.map (homOfLE hij).op)
      rw [c.w]
      exact H
    · simp only [aj, fj, pullback.lift_snd]
  exact ⟨j, pullback fi t, fj, aj, hfj, inferInstance, inferInstance,
    inferInstance, Hj⟩

/-- Construct a proper finitely presented Noetherian model over an arbitrary affine base. -/
theorem Scheme.exists_isPullback_over_noetherian_of_isProper
    {sourceScheme baseScheme : Scheme.{u}} [IsAffine baseScheme]
    (sourceMap : sourceScheme ⟶ baseScheme) [IsProper sourceMap]
    [LocallyOfFinitePresentation sourceMap] :
    ∃ (stageRing : CommRingCat.{u}) (_ : IsNoetherianRing stageRing)
      (stageScheme : Scheme.{u}) (stageMap : stageScheme ⟶ Spec stageRing)
      (_ : IsProper stageMap) (_ : LocallyOfFinitePresentation stageMap)
      (comparison : sourceScheme ⟶ stageScheme) (baseComparison : baseScheme ⟶ Spec stageRing),
      IsPullback comparison sourceMap stageMap baseComparison := by
  let ringDiagram := CommRingCat.fgSubalgebraDiagram Γ(baseScheme, ⊤)
  let ringCocone := CommRingCat.fgSubalgebraCocone Γ(baseScheme, ⊤)
  let diagram := ringDiagram.op ⋙ Scheme.Spec
  let specCone := Scheme.Spec.mapCone ringCocone.op
  have specLimit : IsLimit specCone := isLimitOfPreserves Scheme.Spec
    (CommRingCat.isColimitFgSubalgebraCocone Γ(baseScheme, ⊤)).op
  let cone := specCone.extend baseScheme.isoSpec.hom
  have limit : IsLimit cone := IsLimit.ofIsoLimit specLimit
    (Cone.extendIso specCone baseScheme.isoSpec.symm)
  haveI noetherianStages : ∀ stage, IsNoetherianRing (ringDiagram.obj stage) := by
    intro stage
    change IsNoetherianRing stage.1
    letI : Algebra.FiniteType ℤ stage.1 := (Subalgebra.fg_iff_finiteType _).mp stage.2
    exact Algebra.FiniteType.isNoetherianRing ℤ stage.1
  obtain ⟨stage, stageScheme, stageMap, comparison, proper, finitePresentation,
      _, _, square⟩ := Scheme.exists_isPullback_of_isProper_of_isLimit
        ringDiagram cone limit sourceMap
  exact ⟨ringDiagram.obj stage, noetherianStages stage, stageScheme, stageMap,
    proper, finitePresentation, comparison, cone.π.app (.op stage), square⟩

end AlgebraicGeometry
