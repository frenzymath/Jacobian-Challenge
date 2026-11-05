import Jacobian.AlgebraicGeometry.Limits.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Separatedness at a finite stage

The diagonal of a base-changed family is identified with the base change
of the stage diagonal. Closed immersion descent then gives separatedness
at a finite stage, without a finite type assumption on the original map.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in

/-- Base-changing the stage diagonal detects separatedness of the base-changed morphism. -/
theorem isClosedImmersion_overPullback_diagonal_iff
    {S T : Scheme.{u}} (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    IsClosedImmersion
        (((Over.pullback g).map
          (Over.homMk (pullback.diagonal f.left) (by simp) :
            X ⟶ Over.mk (pullback.snd f.left f.left ≫ X.hom))).left) ↔
      IsSeparated (((Over.pullback g).map f).left) := by
  let f' := ((Over.pullback g).map f).left
  let Z := Over.mk (pullback.snd f.left f.left ≫ X.hom)
  let γ : X ⟶ Z := Over.homMk (pullback.diagonal f.left) (by simp [Z])
  let a : pullback Z.hom g ⟶ pullback X.hom g :=
    pullback.lift (pullback.fst Z.hom g ≫ pullback.fst f.left f.left)
      (pullback.snd Z.hom g) (by
        rw [Category.assoc, ← Over.w f]
        rw [pullback.condition_assoc]
        simpa [Z, Category.assoc, Over.w f] using (pullback.condition (f := Z.hom) (g := g)))
  let b : pullback Z.hom g ⟶ pullback X.hom g :=
    pullback.lift (pullback.fst Z.hom g ≫ pullback.snd f.left f.left)
      (pullback.snd Z.hom g) (by
        simpa [Z, Category.assoc] using (pullback.condition (f := Z.hom) (g := g)))
  have hab : a ≫ f' = b ≫ f' := by
    apply pullback.hom_ext
    · simp [a, b, f', Over.pullback, pullback.condition]
    · simp [a, b, f', Over.pullback]
  let e : pullback Z.hom g ⟶ pullback f' f' := pullback.lift a b hab
  let d : pullback f' f' ⟶ pullback f.left f.left :=
    pullback.lift (pullback.fst f' f' ≫ pullback.fst X.hom g)
      (pullback.snd f' f' ≫ pullback.fst X.hom g) (by
        have h := congrArg (fun k ↦ k ≫ pullback.fst Y.hom g)
          (pullback.condition (f := f') (g := f'))
        simpa [f', Over.pullback] using h)
  have ht : pullback.fst f' f' ≫ pullback.snd X.hom g =
      pullback.snd f' f' ≫ pullback.snd X.hom g := by
    have h := congrArg (fun k ↦ k ≫ pullback.snd Y.hom g) (pullback.condition (f := f') (g := f'))
    simpa [f', Over.pullback] using h
  let v : pullback f' f' ⟶ pullback Z.hom g :=
    pullback.lift d (pullback.snd f' f' ≫ pullback.snd X.hom g) (by
      simp [d, Z, pullback.condition])
  have hev : e ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [e, v, d, a, b]
    · simp [e, v, b]
  have hve : v ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [e, v, a, d]
      · simpa [e, v, a] using ht.symm
    · apply pullback.hom_ext <;> simp [e, v, b, d]
  let E : pullback Z.hom g ≅ pullback f' f' := ⟨e, v, hev, hve⟩
  have heγ : ((Over.pullback g).map γ).left ≫ E.hom = pullback.diagonal f' := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [E, e, a, b, γ, Over.pullback]
  change IsClosedImmersion (((Over.pullback g).map γ).left) ↔ IsSeparated f'
  rw [show IsSeparated f' ↔ IsClosedImmersion (pullback.diagonal f') from
    ⟨fun h ↦ h.isClosedImmersion_diagonal, fun h ↦ ⟨h⟩⟩]
  have : IsIso E.hom := ⟨⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩⟩
  rw [← heγ]
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).symm

end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Separatedness of a stage map over an affine-transition limit descends to a finite stage. -/
theorem Scheme.exists_isSeparated_overPullbackMap
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀)
    (hsep : IsSeparated (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsSeparated (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  have : QuasiCompact f₀.left := quasiCompact_of_compactSpace _
  have : QuasiSeparated f₀.left := inferInstance
  have : QuasiSeparated (pullback.snd f₀.left f₀.left) := inferInstance
  have : CompactSpace ↥(pullback f₀.left f₀.left) := inferInstance
  have : QuasiSeparatedSpace ↥(pullback f₀.left f₀.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f₀.left f₀.left)
  let γ : X₀ ⟶ Over.mk (pullback.snd f₀.left f₀.left ≫ X₀.hom) :=
    Over.homMk (pullback.diagonal f₀.left) (by simp)
  have : LocallyOfFiniteType γ.left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.diagonal f₀.left))
  have : CompactSpace (Over.mk (pullback.snd f₀.left f₀.left ≫ X₀.hom)).left :=
    inferInstanceAs (CompactSpace ↥(pullback f₀.left f₀.left))
  have : QuasiSeparatedSpace (Over.mk (pullback.snd f₀.left f₀.left ≫ X₀.hom)).left :=
    inferInstanceAs (QuasiSeparatedSpace ↥(pullback f₀.left f₀.left))
  have hγ : IsClosedImmersion (((Over.pullback (c.π.app (op i₀))).map γ).left) :=
    (isClosedImmersion_overPullback_diagonal_iff (c.π.app (op i₀)) X₀ Y₀ f₀).mpr hsep
  obtain ⟨i, hi, hstage⟩ := Scheme.exists_isClosedImmersion_baseChange_of_isLimit
    D c hc i₀ X₀ (Over.mk (pullback.snd f₀.left f₀.left ≫ X₀.hom)) γ hγ
  exact ⟨i, hi,
    (isClosedImmersion_overPullback_diagonal_iff (D.map (homOfLE hi).op)
      X₀ Y₀ f₀).mp hstage⟩

end AlgebraicGeometry
end
