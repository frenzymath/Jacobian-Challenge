import Jacobian.AlgebraicGeometry.ProjectiveSpace.Segre
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Zero
import Jacobian.CategoryTheory.MorphismProperty.Products

/-!
# Closed immersions of finite products of projective spaces

Iterating the relative Segre closed immersion embeds a finite product of
projective spaces into another projective space over the same base. The empty
product is identified with projective space on one homogeneous coordinate.
-/

noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

section Binary

variable (coordinates otherCoordinates : Type u) (baseScheme : Scheme.{u})

/-- The relative Segre morphism as a morphism in `Over baseScheme` out of the binary product of
`ℙ(coordinates; baseScheme)` and `ℙ(otherCoordinates; baseScheme)` in `Over baseScheme`. -/
def segreOver :
    (Over.mk (ℙ(coordinates; baseScheme) ↘ baseScheme) ⨯ Over.mk (ℙ(otherCoordinates; baseScheme) ↘ baseScheme) : Over baseScheme) ⟶ Over.mk (ℙ(coordinates × otherCoordinates; baseScheme) ↘ baseScheme) :=
  Over.homMk ((Over.prodLeftIsoPullback _ _).hom ≫ segre coordinates otherCoordinates baseScheme) (by
    simp only [Category.assoc, Over.mk_hom, segre_over]
    exact (Over.prodLeftIsoPullback_hom_fst_assoc _ _ _).trans (Over.w prod.fst))

@[simp]
lemma segreOver_left :
    (segreOver coordinates otherCoordinates baseScheme).left = (Over.prodLeftIsoPullback _ _).hom ≫ segre coordinates otherCoordinates baseScheme :=
  rfl

instance : IsClosedImmersion (segreOver coordinates otherCoordinates baseScheme).left := by
  rw [segreOver_left]
  infer_instance

end Binary

variable {indexType : Type u} [Finite indexType] (coordinates : indexType → Type u) [∀ index, Finite (coordinates index)] (baseScheme : Scheme.{u})

/-- **A finite fibre product of projective spaces over `baseScheme` embeds into a projective space
over `baseScheme`**: the product `∏ᶜ fun index ↦ ℙ(coordinates index; baseScheme)` in `Over baseScheme` admits a closed immersion into
`ℙ(targetCoordinates; baseScheme)` for some finite index type `targetCoordinates`, namely the iterated Segre embedding. -/
theorem exists_isClosedImmersion_pi :
    ∃ (targetCoordinates : Type u) (_ : Finite targetCoordinates)
      (embedding : (∏ᶜ fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme)) ⟶ Over.mk (ℙ(targetCoordinates; baseScheme) ↘ baseScheme)),
      IsClosedImmersion embedding.left := by
  have : IsIso (ℙ(PUnit.{u + 1}; baseScheme) ↘ baseScheme) := inferInstance
  have hT' : IsTerminal (Over.mk (ℙ(PUnit.{u + 1}; baseScheme) ↘ baseScheme)) :=
    Over.mkIdTerminal.ofIso (Over.isoMk (asIso (ℙ(PUnit.{u + 1}; baseScheme) ↘ baseScheme)) (by simp)).symm
  refine Finite.induction_empty_option
    (P := fun indexType ↦ ∀ [Finite indexType] (coordinates : indexType → Type u) [∀ index, Finite (coordinates index)],
      ∃ (targetCoordinates : Type u) (_ : Finite targetCoordinates)
        (embedding : (∏ᶜ fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme)) ⟶ Over.mk (ℙ(targetCoordinates; baseScheme) ↘ baseScheme)),
        IsClosedImmersion embedding.left)
    ?_ ?_ ?_ indexType coordinates
  · intro firstIndex secondIndex equivalence induction_hyp _ coordinates _
    have : Finite firstIndex := Finite.of_equiv _ equivalence.symm
    obtain ⟨targetCoordinates, _, embedding, closedImmersion⟩ := induction_hyp fun sourceIndex ↦ coordinates (equivalence sourceIndex)
    have productIso : (∏ᶜ fun sourceIndex ↦ Over.mk (ℙ(coordinates (equivalence sourceIndex); baseScheme) ↘ baseScheme)) ≅ ∏ᶜ fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme) :=
      Pi.whiskerEquiv (f := fun sourceIndex ↦ Over.mk (ℙ(coordinates (equivalence sourceIndex); baseScheme) ↘ baseScheme))
        (g := fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme)) equivalence fun _ ↦ Iso.refl _
    refine ⟨targetCoordinates, ‹_›, productIso.inv ≫ embedding, ?_⟩
    have : IsIso (productIso.inv.left) := inferInstanceAs (IsIso ((Over.forget baseScheme).map _))
    rw [Over.comp_left]
    infer_instance
  · intro _ coordinates _
    have hT : IsTerminal (∏ᶜ fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme)) :=
      IsTerminal.ofUniqueHom (fun _ ↦ Pi.lift fun index ↦ index.elim)
        fun _ _ ↦ Pi.hom_ext _ _ fun index ↦ index.elim
    refine ⟨PUnit.{u + 1}, inferInstance, (hT.uniqueUpToIso hT').hom, ?_⟩
    have : IsIso ((hT.uniqueUpToIso hT').hom.left) :=
      inferInstanceAs (IsIso ((Over.forget baseScheme).map _))
    infer_instance
  · intro firstIndex _ induction_hyp _ coordinates _
    obtain ⟨targetCoordinates, _, embedding, closedImmersion⟩ := induction_hyp fun index ↦ coordinates (some index)
    refine ⟨coordinates none × targetCoordinates, inferInstance,
      (piOptionIso fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme)).hom ≫
        prod.map (𝟙 (Over.mk (ℙ(coordinates none; baseScheme) ↘ baseScheme))) embedding ≫ segreOver (coordinates none) targetCoordinates baseScheme, ?_⟩
    have : IsIso ((piOptionIso fun index ↦ Over.mk (ℙ(coordinates index; baseScheme) ↘ baseScheme)).hom.left) :=
      inferInstanceAs (IsIso ((Over.forget baseScheme).map _))
    have : IsClosedImmersion (prod.map (𝟙 (Over.mk (ℙ(coordinates none; baseScheme) ↘ baseScheme))) embedding).left :=
      MorphismProperty.left_prod_map_id _ embedding closedImmersion
    rw [Over.comp_left, Over.comp_left]
    infer_instance

end AlgebraicGeometry.ProjectiveSpace
