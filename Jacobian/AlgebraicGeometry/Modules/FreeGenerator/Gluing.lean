import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local

/-!
# Gluing maps prescribed on free generators

Local free generators with compatible transition functions determine a map of
module sheaves. If the prescribed images are free generators, the map is an
isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite

open TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme : Scheme.{u}} {moduleSheaf otherSheaf : scheme.Modules}

section Glue

variable {indexType : Type*} {openSubset : indexType → scheme.Opens} (firstGenerators : ∀ index, Γ(moduleSheaf, openSubset index)) (secondGenerators : ∀ index, Γ(otherSheaf, openSubset index))

/-- `n` is the value at `m` of the morphism `M ⟶ N` sending each `e i` to `f i`: whenever
`m = a • e i` on an open `W`, then `n = a • f i` on `W`. -/
def IsGlueValue {smallerOpen : scheme.Opens} (sectionValue : Γ(moduleSheaf, smallerOpen)) (otherSection : Γ(otherSheaf, smallerOpen)) : Prop :=
  ∀ index (smallestOpen : scheme.Opens) (hW : smallestOpen ≤ smallerOpen) (hWi : smallestOpen ≤ openSubset index) (firstElement : Γ(scheme, smallestOpen)),
    firstElement • moduleSheaf.presheaf.map (homOfLE hWi).op (firstGenerators index) = moduleSheaf.presheaf.map (homOfLE hW).op sectionValue →
      otherSheaf.presheaf.map (homOfLE hW).op otherSection = firstElement • otherSheaf.presheaf.map (homOfLE hWi).op (secondGenerators index)

variable {firstGenerators secondGenerators}

lemma IsGlueValue.unique (hU : ⨆ index, openSubset index = ⊤) (he : ∀ index, IsFreeGenerator (firstGenerators index)) {smallerOpen : scheme.Opens}
    {sectionValue : Γ(moduleSheaf, smallerOpen)} {otherSection otherOtherSection : Γ(otherSheaf, smallerOpen)} (hn : IsGlueValue firstGenerators secondGenerators sectionValue otherSection) (hn' : IsGlueValue firstGenerators secondGenerators sectionValue otherOtherSection) :
    otherSection = otherOtherSection := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨otherSheaf.presheaf, otherSheaf.isSheaf⟩ (fun index ↦ smallerOpen ⊓ openSubset index) smallerOpen
    (fun _ ↦ homOfLE inf_le_left) (fun element hx ↦ ?_) otherSection otherOtherSection fun index ↦ ?_
  · obtain ⟨index, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ element))
    exact Opens.mem_iSup.mpr ⟨index, hx, hi⟩
  · have hi := (he index).map (inf_le_right : smallerOpen ⊓ openSubset index ≤ openSubset index)
    have ha := hi.coeff_smul (moduleSheaf.presheaf.map (homOfLE inf_le_left).op sectionValue)
    exact (hn index _ inf_le_left inf_le_right _ ha).trans (hn' index _ inf_le_left inf_le_right _ ha).symm

variable (hU : ⨆ index, openSubset index = ⊤) (he : ∀ index, IsFreeGenerator (firstGenerators index))
  (hc : ∀ index otherIndex (smallestOpen : scheme.Opens) (hi : smallestOpen ≤ openSubset index) (hj : smallestOpen ≤ openSubset otherIndex) (firstElement secondElement : Γ(scheme, smallestOpen)),
    firstElement • moduleSheaf.presheaf.map (homOfLE hi).op (firstGenerators index) = secondElement • moduleSheaf.presheaf.map (homOfLE hj).op (firstGenerators otherIndex) →
      firstElement • otherSheaf.presheaf.map (homOfLE hi).op (secondGenerators index) = secondElement • otherSheaf.presheaf.map (homOfLE hj).op (secondGenerators otherIndex))

include hU he hc in
lemma exists_isGlueValue {smallerOpen : scheme.Opens} (sectionValue : Γ(moduleSheaf, smallerOpen)) : ∃ otherSection, IsGlueValue firstGenerators secondGenerators sectionValue otherSection := by
  have hi (index : indexType) := (he index).map (inf_le_right : smallerOpen ⊓ openSubset index ≤ openSubset index)
  let sf (index : indexType) : Γ(otherSheaf, smallerOpen ⊓ openSubset index) := (hi index).coeff (moduleSheaf.presheaf.map (homOfLE inf_le_left).op sectionValue) •
    otherSheaf.presheaf.map (homOfLE inf_le_right).op (secondGenerators index)
  have hsf : TopCat.Presheaf.IsCompatible otherSheaf.presheaf (fun index ↦ smallerOpen ⊓ openSubset index) sf := by
    intro index otherIndex
    change otherSheaf.presheaf.map (homOfLE inf_le_left).op (sf index) =
      otherSheaf.presheaf.map (homOfLE inf_le_right).op (sf otherIndex)
    simp only [sf, map_smul, presheaf_map_homOfLE_map_homOfLE]
    refine hc index otherIndex _ _ _ _ _ ?_
    rw [← presheaf_map_homOfLE_map_homOfLE (inf_le_right : smallerOpen ⊓ openSubset index ≤ openSubset index) inf_le_left,
      ← presheaf_map_homOfLE_map_homOfLE (inf_le_right : smallerOpen ⊓ openSubset otherIndex ≤ openSubset otherIndex) inf_le_right,
      ← map_smul, ← map_smul, (hi index).coeff_smul, (hi otherIndex).coeff_smul,
      presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  obtain ⟨otherSection, hn, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨otherSheaf.presheaf, otherSheaf.isSheaf⟩
    (fun index ↦ smallerOpen ⊓ openSubset index) smallerOpen (fun _ ↦ homOfLE inf_le_left) (fun element hx ↦ by
      obtain ⟨index, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ element))
      exact Opens.mem_iSup.mpr ⟨index, hx, hi⟩) sf hsf
  refine ⟨otherSection, fun index smallestOpen hW hWi firstElement ha ↦ ?_⟩
  have hWV : smallestOpen ≤ smallerOpen ⊓ openSubset index := le_inf hW hWi
  have h1 : otherSheaf.presheaf.map (homOfLE hW).op otherSection =
      otherSheaf.presheaf.map (homOfLE hWV).op (otherSheaf.presheaf.map (homOfLE inf_le_left).op otherSection) :=
    (presheaf_map_homOfLE_map_homOfLE _ _ _).symm
  rw [h1, hn index]
  simp only [sf, map_smul, presheaf_map_homOfLE_map_homOfLE]
  congr 1
  refine ((he index).map hWi).smul_left_injective ?_
  dsimp only
  rw [ha, ← presheaf_map_homOfLE_map_homOfLE (inf_le_right : smallerOpen ⊓ openSubset index ≤ openSubset index) hWV, ← map_smul,
    (hi index).coeff_smul, presheaf_map_homOfLE_map_homOfLE]


include he in
lemma isGlueValue_zero {smallerOpen : scheme.Opens} : IsGlueValue firstGenerators secondGenerators (0 : Γ(moduleSheaf, smallerOpen)) (0 : Γ(otherSheaf, smallerOpen)) := by
  intro index smallestOpen hW hWi firstElement ha
  rw [map_zero] at ha ⊢
  obtain rfl : firstElement = 0 := ((he index).map hWi).smul_left_injective (ha.trans (zero_smul _ _).symm)
  rw [zero_smul]

include he in
lemma IsGlueValue.add {smallerOpen : scheme.Opens} {sectionValue otherSectionValue : Γ(moduleSheaf, smallerOpen)} {otherSection otherOtherSection : Γ(otherSheaf, smallerOpen)}
    (hn : IsGlueValue firstGenerators secondGenerators sectionValue otherSection) (hn' : IsGlueValue firstGenerators secondGenerators otherSectionValue otherOtherSection) :
    IsGlueValue firstGenerators secondGenerators (sectionValue + otherSectionValue) (otherSection + otherOtherSection) := by
  intro index smallestOpen hW hWi firstElement ha
  have hi := (he index).map hWi
  have h1 := hn index smallestOpen hW hWi _ (hi.coeff_smul (moduleSheaf.presheaf.map (homOfLE hW).op sectionValue))
  have h2 := hn' index smallestOpen hW hWi _ (hi.coeff_smul (moduleSheaf.presheaf.map (homOfLE hW).op otherSectionValue))
  rw [map_add] at ha ⊢
  rw [h1, h2, ← add_smul]
  congr 1
  rw [← hi.coeff_add, ← ha, hi.coeff_smul_self]

include he in
lemma IsGlueValue.smul {smallerOpen : scheme.Opens} {sectionValue : Γ(moduleSheaf, smallerOpen)} {otherSection : Γ(otherSheaf, smallerOpen)} (hn : IsGlueValue firstGenerators secondGenerators sectionValue otherSection)
    (scalar : Γ(scheme, smallerOpen)) : IsGlueValue firstGenerators secondGenerators (scalar • sectionValue) (scalar • otherSection) := by
  intro index smallestOpen hW hWi firstElement ha
  have hi := (he index).map hWi
  have h1 := hn index smallestOpen hW hWi _ (hi.coeff_smul (moduleSheaf.presheaf.map (homOfLE hW).op sectionValue))
  rw [map_smul] at ha ⊢
  rw [h1, smul_smul]
  congr 1
  rw [← hi.coeff_smul_left, ← ha, hi.coeff_smul_self]

lemma IsGlueValue.map {smallerOpen otherSmallerOpen : scheme.Opens} (compatibility : otherSmallerOpen ≤ smallerOpen) {sectionValue : Γ(moduleSheaf, smallerOpen)} {otherSection : Γ(otherSheaf, smallerOpen)}
    (hn : IsGlueValue firstGenerators secondGenerators sectionValue otherSection) :
    IsGlueValue firstGenerators secondGenerators (moduleSheaf.presheaf.map (homOfLE compatibility).op sectionValue) (otherSheaf.presheaf.map (homOfLE compatibility).op otherSection) := by
  intro index smallestOpen hW hWi firstElement ha
  rw [presheaf_map_homOfLE_map_homOfLE] at ha ⊢
  exact hn index smallestOpen _ hWi firstElement ha

include he in
lemma IsGlueValue.symm (hf : ∀ index, IsFreeGenerator (secondGenerators index)) {smallerOpen : scheme.Opens} {sectionValue : Γ(moduleSheaf, smallerOpen)}
    {otherSection : Γ(otherSheaf, smallerOpen)} (hn : IsGlueValue firstGenerators secondGenerators sectionValue otherSection) : IsGlueValue secondGenerators firstGenerators otherSection sectionValue := by
  intro index smallestOpen hW hWi firstElement ha
  have hi := (he index).map hWi
  have h1 := hn index smallestOpen hW hWi _ (hi.coeff_smul (moduleSheaf.presheaf.map (homOfLE hW).op sectionValue))
  rw [← hi.coeff_smul (moduleSheaf.presheaf.map (homOfLE hW).op sectionValue)]
  congr 1
  exact ((hf index).map hWi).smul_left_injective (h1.symm.trans ha.symm)

include hU he hc in
/-- The morphism `M ⟶ N` sending the free generators `e i` to the sections `f i`. -/
noncomputable def glueHom : moduleSheaf ⟶ otherSheaf :=
  ⟨PresheafOfModules.homMk
    { app smallerOpen := AddCommGrpCat.ofHom
        { toFun sectionValue := (exists_isGlueValue hU he hc (smallerOpen := smallerOpen.unop) sectionValue).choose
          map_zero' := ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
            (isGlueValue_zero he)
          map_add' sectionValue otherSectionValue := ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
            (((exists_isGlueValue hU he hc sectionValue).choose_spec).add he
              (exists_isGlueValue hU he hc otherSectionValue).choose_spec) }
      naturality smallerOpen otherSmallerOpen index := by
        ext sectionValue
        exact ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
          (((exists_isGlueValue hU he hc sectionValue).choose_spec).map
            (otherSmallerOpen := otherSmallerOpen.unop) index.unop.le) }
    fun smallerOpen scalar sectionValue ↦ ((exists_isGlueValue hU he hc _).choose_spec).unique hU he
      (((exists_isGlueValue hU he hc sectionValue).choose_spec).smul he scalar)⟩

lemma isGlueValue_glueHom_app {smallerOpen : scheme.Opens} (sectionValue : Γ(moduleSheaf, smallerOpen)) :
    IsGlueValue firstGenerators secondGenerators sectionValue ((glueHom hU he hc).app smallerOpen sectionValue) :=
  (exists_isGlueValue hU he hc sectionValue).choose_spec


include hU he hc in
/-- **Invertible modules with the same transition functions are isomorphic.** Let `U i` be an
open cover of `X`, `e i` a free generator of `M` on `U i` and `f i` a free generator of `N` on
`U i`, such that `e i` and `e j` are related on every open of `U i ⊓ U j` in the same way as
`f i` and `f j` (i.e. both families have the same transition functions). Then `M ≅ N`. -/
theorem nonempty_iso_of_isFreeGenerator (hf : ∀ index, IsFreeGenerator (secondGenerators index)) :
    Nonempty (moduleSheaf ≅ otherSheaf) := by
  have hc' : ∀ index otherIndex (smallestOpen : scheme.Opens) (hi : smallestOpen ≤ openSubset index) (hj : smallestOpen ≤ openSubset otherIndex) (firstElement secondElement : Γ(scheme, smallestOpen)),
      firstElement • otherSheaf.presheaf.map (homOfLE hi).op (secondGenerators index) = secondElement • otherSheaf.presheaf.map (homOfLE hj).op (secondGenerators otherIndex) →
        firstElement • moduleSheaf.presheaf.map (homOfLE hi).op (firstGenerators index) = secondElement • moduleSheaf.presheaf.map (homOfLE hj).op (firstGenerators otherIndex) := by
    intro index otherIndex smallestOpen hi hj firstElement secondElement hab
    have hj' := (he otherIndex).map hj
    have compatibility := hc index otherIndex smallestOpen hi hj firstElement _ (hj'.coeff_smul _).symm
    rw [← hj'.coeff_smul (firstElement • moduleSheaf.presheaf.map (homOfLE hi).op (firstGenerators index))]
    congr 1
    exact ((hf otherIndex).map hj).smul_left_injective (compatibility.symm.trans hab)
  refine ⟨⟨glueHom hU he hc, glueHom hU hf hc', ?_, ?_⟩⟩
  · refine hom_ext _ _ fun smallerOpen ↦ ?_
    ext sectionValue
    exact (isGlueValue_glueHom_app hU hf hc' _).unique hU hf
      ((isGlueValue_glueHom_app hU he hc sectionValue).symm he hf)
  · refine hom_ext _ _ fun smallerOpen ↦ ?_
    ext sectionValue
    exact (isGlueValue_glueHom_app hU he hc _).unique hU he
      ((isGlueValue_glueHom_app hU hf hc' sectionValue).symm hf he)

end Glue

end AlgebraicGeometry.Scheme.Modules
