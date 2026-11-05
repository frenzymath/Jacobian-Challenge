import Jacobian.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant.Opens
import Jacobian.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Gluing morphisms that agree on a dense open

Compatible morphisms out of a family of opens glue on its union. For a
separated target over a base, agreement on a common scheme-theoretically
dense open suffices for compatibility.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {coverIndex : Type*} {sourceScheme targetScheme : Scheme.{u}} (cover : coverIndex → sourceScheme.Opens)

lemma Scheme.Opens.pullback_fst_comp_eq_snd_comp (maps : ∀ firstIndex, (cover firstIndex).toScheme ⟶ targetScheme)
    (compatible : ∀ firstIndex secondIndex, sourceScheme.homOfLE (inf_le_left : cover firstIndex ⊓ cover secondIndex ≤ cover firstIndex) ≫ maps firstIndex =
      sourceScheme.homOfLE (inf_le_right : cover firstIndex ⊓ cover secondIndex ≤ cover secondIndex) ≫ maps secondIndex) (firstIndex secondIndex : coverIndex) :
    pullback.fst (sourceScheme.homOfLE (le_iSup cover firstIndex)) (sourceScheme.homOfLE (le_iSup cover secondIndex)) ≫ maps firstIndex =
      pullback.snd _ _ ≫ maps secondIndex := by
  rw [← cancel_epi (isPullback_opens_inf_le (le_iSup cover firstIndex) (le_iSup cover secondIndex)).isoPullback.hom,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact compatible firstIndex secondIndex

noncomputable def Scheme.Opens.glueMorphisms (maps : ∀ firstIndex, (cover firstIndex).toScheme ⟶ targetScheme)
    (compatible : ∀ firstIndex secondIndex, sourceScheme.homOfLE (inf_le_left : cover firstIndex ⊓ cover secondIndex ≤ cover firstIndex) ≫ maps firstIndex =
      sourceScheme.homOfLE (inf_le_right : cover firstIndex ⊓ cover secondIndex ≤ cover secondIndex) ≫ maps secondIndex) :
    (⨆ firstIndex, cover firstIndex).toScheme ⟶ targetScheme :=
  (iSupOpenCover cover).glueMorphisms maps (Scheme.Opens.pullback_fst_comp_eq_snd_comp cover maps compatible)

@[reassoc (attr := simp)]
lemma Scheme.Opens.homOfLE_glueMorphisms (maps : ∀ firstIndex, (cover firstIndex).toScheme ⟶ targetScheme)
    (compatible : ∀ firstIndex secondIndex, sourceScheme.homOfLE (inf_le_left : cover firstIndex ⊓ cover secondIndex ≤ cover firstIndex) ≫ maps firstIndex =
      sourceScheme.homOfLE (inf_le_right : cover firstIndex ⊓ cover secondIndex ≤ cover secondIndex) ≫ maps secondIndex) (firstIndex : coverIndex) :
    sourceScheme.homOfLE (le_iSup cover firstIndex) ≫ Scheme.Opens.glueMorphisms cover maps compatible = maps firstIndex :=
  (iSupOpenCover cover).ι_glueMorphisms maps _ firstIndex

lemma Scheme.Opens.hom_ext_iSup (firstMap secondMap : (⨆ firstIndex, cover firstIndex).toScheme ⟶ targetScheme)
    (agree : ∀ firstIndex, sourceScheme.homOfLE (le_iSup cover firstIndex) ≫ firstMap = sourceScheme.homOfLE (le_iSup cover firstIndex) ≫ secondMap) : firstMap = secondMap :=
  (iSupOpenCover cover).hom_ext firstMap secondMap agree

section Dominant

variable {baseScheme : Scheme.{u}} (denseCover : coverIndex → sourceScheme.Opens) (denseOpen : sourceScheme.Opens)

lemma Scheme.Opens.homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant
    (dense_le : ∀ firstIndex, denseOpen ≤ denseCover firstIndex) [QuasiCompact denseOpen.ι] [IsSchemeTheoreticallyDominant denseOpen.ι]
    (targetMap : targetScheme ⟶ baseScheme) [IsSeparated targetMap] (sourceMap : sourceScheme ⟶ baseScheme)
    (maps : ∀ firstIndex, (denseCover firstIndex).toScheme ⟶ targetScheme) (over_base : ∀ firstIndex, maps firstIndex ≫ targetMap = (denseCover firstIndex).ι ≫ sourceMap)
    (agree_dense : ∀ firstIndex secondIndex, sourceScheme.homOfLE (dense_le firstIndex) ≫ maps firstIndex = sourceScheme.homOfLE (dense_le secondIndex) ≫ maps secondIndex) (firstIndex secondIndex : coverIndex) :
    sourceScheme.homOfLE (inf_le_left : denseCover firstIndex ⊓ denseCover secondIndex ≤ denseCover firstIndex) ≫ maps firstIndex =
      sourceScheme.homOfLE (inf_le_right : denseCover firstIndex ⊓ denseCover secondIndex ≤ denseCover secondIndex) ≫ maps secondIndex := by
  have := IsSchemeTheoreticallyDominant.homOfLE (le_inf (dense_le firstIndex) (dense_le secondIndex))
  refine ext_of_isSchemeTheoreticallyDominant targetMap ?_ (sourceScheme.homOfLE (le_inf (dense_le firstIndex) (dense_le secondIndex))) ?_
  · rw [Category.assoc, Category.assoc, over_base firstIndex, over_base secondIndex, sourceScheme.homOfLE_ι_assoc, sourceScheme.homOfLE_ι_assoc]
  · rw [← Category.assoc, ← Category.assoc, sourceScheme.homOfLE_homOfLE, sourceScheme.homOfLE_homOfLE]
    exact agree_dense firstIndex secondIndex

noncomputable def Scheme.Opens.glueMorphismsOfDominant
    (dense_le : ∀ firstIndex, denseOpen ≤ denseCover firstIndex) [QuasiCompact denseOpen.ι] [IsSchemeTheoreticallyDominant denseOpen.ι]
    (targetMap : targetScheme ⟶ baseScheme) [IsSeparated targetMap] (sourceMap : sourceScheme ⟶ baseScheme)
    (maps : ∀ firstIndex, (denseCover firstIndex).toScheme ⟶ targetScheme) (over_base : ∀ firstIndex, maps firstIndex ≫ targetMap = (denseCover firstIndex).ι ≫ sourceMap)
    (agree_dense : ∀ firstIndex secondIndex, sourceScheme.homOfLE (dense_le firstIndex) ≫ maps firstIndex = sourceScheme.homOfLE (dense_le secondIndex) ≫ maps secondIndex) :
    (⨆ firstIndex, denseCover firstIndex).toScheme ⟶ targetScheme :=
  Scheme.Opens.glueMorphisms denseCover maps
    (homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant denseCover denseOpen dense_le targetMap sourceMap maps over_base agree_dense)

@[reassoc (attr := simp)]
lemma Scheme.Opens.homOfLE_glueMorphismsOfDominant
    (dense_le : ∀ firstIndex, denseOpen ≤ denseCover firstIndex) [QuasiCompact denseOpen.ι] [IsSchemeTheoreticallyDominant denseOpen.ι]
    (targetMap : targetScheme ⟶ baseScheme) [IsSeparated targetMap] (sourceMap : sourceScheme ⟶ baseScheme)
    (maps : ∀ firstIndex, (denseCover firstIndex).toScheme ⟶ targetScheme) (over_base : ∀ firstIndex, maps firstIndex ≫ targetMap = (denseCover firstIndex).ι ≫ sourceMap)
    (agree_dense : ∀ firstIndex secondIndex, sourceScheme.homOfLE (dense_le firstIndex) ≫ maps firstIndex = sourceScheme.homOfLE (dense_le secondIndex) ≫ maps secondIndex) (firstIndex : coverIndex) :
    sourceScheme.homOfLE (le_iSup denseCover firstIndex) ≫ glueMorphismsOfDominant denseCover denseOpen dense_le targetMap sourceMap maps over_base agree_dense = maps firstIndex :=
  homOfLE_glueMorphisms denseCover maps _ firstIndex

lemma Scheme.Opens.glueMorphismsOfDominant_comp
    (dense_le : ∀ firstIndex, denseOpen ≤ denseCover firstIndex) [QuasiCompact denseOpen.ι] [IsSchemeTheoreticallyDominant denseOpen.ι]
    (targetMap : targetScheme ⟶ baseScheme) [IsSeparated targetMap] (sourceMap : sourceScheme ⟶ baseScheme)
    (maps : ∀ firstIndex, (denseCover firstIndex).toScheme ⟶ targetScheme) (over_base : ∀ firstIndex, maps firstIndex ≫ targetMap = (denseCover firstIndex).ι ≫ sourceMap)
    (agree_dense : ∀ firstIndex secondIndex, sourceScheme.homOfLE (dense_le firstIndex) ≫ maps firstIndex = sourceScheme.homOfLE (dense_le secondIndex) ≫ maps secondIndex) :
    glueMorphismsOfDominant denseCover denseOpen dense_le targetMap sourceMap maps over_base agree_dense ≫ targetMap = (⨆ firstIndex, denseCover firstIndex).ι ≫ sourceMap := by
  refine hom_ext_iSup denseCover _ _ fun firstIndex ↦ ?_
  rw [homOfLE_glueMorphismsOfDominant_assoc, over_base firstIndex, sourceScheme.homOfLE_ι_assoc]

end Dominant

end AlgebraicGeometry
