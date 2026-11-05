import Jacobian.AlgebraicGeometry.Descent.Affine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {source base : Scheme.{schemeUniverse}} {baseMap : source ⟶ base} {representation : Over source}

private theorem transport_left_comp (datum : DescentDatum baseMap representation)
    {test otherTest : Scheme.{schemeUniverse}}
    (comparison : test ⟶ otherTest) (firstMap secondMap : otherTest ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (otherPoint : Over.mk firstMap ⟶ representation)
    {restrictedFirst restrictedSecond : test ⟶ source}
    (restrictedEquality : restrictedFirst ≫ baseMap = restrictedSecond ≫ baseMap)
    (first_eq : restrictedFirst = comparison ≫ firstMap)
    (second_eq : restrictedSecond = comparison ≫ secondMap)
    (point : Over.mk restrictedFirst ⟶ representation)
    (point_eq : point.left = comparison ≫ otherPoint.left) :
    (datum.transport restrictedFirst restrictedSecond restrictedEquality point).left =
      comparison ≫ (datum.transport firstMap secondMap equality otherPoint).left := by
  subst first_eq second_eq
  obtain rfl : point = (Over.homMk comparison :
      Over.mk (comparison ≫ firstMap) ⟶ Over.mk firstMap) ≫ otherPoint := by
    ext
    simpa using point_eq
  rw [datum.transport_homMk_comp comparison firstMap secondMap equality otherPoint]
  rfl

section Localize

variable {baseOpen : base.Opens} {openSubset : representation.left.Opens}

private lemma range_ι_comp_hom_subset (overBase : openSubset ≤ (representation.hom ≫ baseMap) ⁻¹ᵁ baseOpen) :
    Set.range (openSubset.ι ≫ representation.hom) ⊆ Set.range (baseMap ⁻¹ᵁ baseOpen).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨openPoint, rfl⟩
  exact overBase openPoint.2

noncomputable def homToPreimage (overBase : openSubset ≤ (representation.hom ≫ baseMap) ⁻¹ᵁ baseOpen) :
    openSubset.toScheme ⟶ (baseMap ⁻¹ᵁ baseOpen).toScheme :=
  IsOpenImmersion.lift (baseMap ⁻¹ᵁ baseOpen).ι (openSubset.ι ≫ representation.hom) (range_ι_comp_hom_subset overBase)

@[reassoc (attr := simp)]
lemma homToPreimage_ι (overBase : openSubset ≤ (representation.hom ≫ baseMap) ⁻¹ᵁ baseOpen) :
    homToPreimage overBase ≫ (baseMap ⁻¹ᵁ baseOpen).ι = openSubset.ι ≫ representation.hom :=
  IsOpenImmersion.lift_fac _ _ _

private lemma comp_ι_comp_eq {test : Scheme.{schemeUniverse}} {f₁ f₂ : test ⟶ (baseMap ⁻¹ᵁ baseOpen).toScheme}
    (compatibility : f₁ ≫ baseMap ∣_ baseOpen = f₂ ≫ baseMap ∣_ baseOpen) :
    (f₁ ≫ (baseMap ⁻¹ᵁ baseOpen).ι) ≫ baseMap = (f₂ ≫ (baseMap ⁻¹ᵁ baseOpen).ι) ≫ baseMap := by
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% compatibility]

variable {datum : DescentDatum baseMap representation} (invariant : datum.IsInvariant openSubset)

private noncomputable abbrev pointOfPreimage (overBase : openSubset ≤ (representation.hom ≫ baseMap) ⁻¹ᵁ baseOpen) {test : Scheme.{schemeUniverse}}
    {map : test ⟶ (baseMap ⁻¹ᵁ baseOpen).toScheme} (point : Over.mk map ⟶ Over.mk (homToPreimage overBase)) :
    Over.mk (map ≫ (baseMap ⁻¹ᵁ baseOpen).ι) ⟶ Over.mk (openSubset.ι ≫ representation.hom) :=
  Over.homMk point.left (by
    have := Over.w_assoc point (baseMap ⁻¹ᵁ baseOpen).ι
    simp only [Over.mk_hom, homToPreimage_ι] at this ⊢
    exact this)

noncomputable def restrictBase (overBase : openSubset ≤ (representation.hom ≫ baseMap) ⁻¹ᵁ baseOpen) :
    DescentDatum (baseMap ∣_ baseOpen) (Over.mk (homToPreimage overBase)) where
  transport f₁ f₂ compatibility point := Over.homMk ((datum.restrict openSubset invariant).transport (f₁ ≫ (baseMap ⁻¹ᵁ baseOpen).ι)
      (f₂ ≫ (baseMap ⁻¹ᵁ baseOpen).ι) (comp_ι_comp_eq compatibility) (pointOfPreimage overBase point)).left (by
    rw [← cancel_mono (baseMap ⁻¹ᵁ baseOpen).ι]
    simp only [Over.mk_hom, Category.assoc, homToPreimage_ι]
    exact Over.w ((datum.restrict openSubset invariant).transport _ _ _ _))
  transport_homMk_comp comparison f₁ f₂ compatibility point := by
    refine Over.OverMorphism.ext ?_
    exact (datum.restrict openSubset invariant).transport_left_comp comparison _ _ _ _ _ (by simp) (by simp) _ (by simp)
  transport_self map point := by
    refine Over.OverMorphism.ext ?_
    have := congrArg CommaMorphism.left
      ((datum.restrict openSubset invariant).transport_self (map ≫ (baseMap ⁻¹ᵁ baseOpen).ι) (pointOfPreimage overBase point))
    exact this
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ point := by
    refine Over.OverMorphism.ext ?_
    refine ((datum.restrict openSubset invariant).transport_left_congr (comp_ι_comp_eq h₂₃) (comp_ι_comp_eq h₂₃)
      _ ((datum.restrict openSubset invariant).transport _ _ (comp_ι_comp_eq h₁₂) (pointOfPreimage overBase point))
      rfl rfl rfl).trans ?_
    exact congrArg CommaMorphism.left ((datum.restrict openSubset invariant).transport_transport _ _ _
      (comp_ι_comp_eq h₁₂) (comp_ι_comp_eq h₂₃) (pointOfPreimage overBase point))

end Localize

theorem isEffective_restrict_of_isAffineOpen [IsAffineHom baseMap] [Flat baseMap] [Surjective baseMap]
    (datum : DescentDatum baseMap representation) {openSubset : representation.left.Opens} (invariant : datum.IsInvariant openSubset) (affineOpen : IsAffineOpen openSubset)
    {baseOpen : base.Opens} (affineBase : IsAffineOpen baseOpen) (overBase : openSubset ≤ (representation.hom ≫ baseMap) ⁻¹ᵁ baseOpen) :
    (datum.restrict openSubset invariant).IsEffective := by
  have : IsAffine baseOpen := affineBase
  have : IsAffine (baseMap ⁻¹ᵁ baseOpen) := affineBase.preimage baseMap
  have : IsAffine (Over.mk (homToPreimage overBase)).left := affineOpen
  have : Flat (baseMap ∣_ baseOpen) := MorphismProperty.of_isPullback (isPullback_morphismRestrict baseMap baseOpen).flip
    inferInstance
  have : Surjective (baseMap ∣_ baseOpen) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict baseMap baseOpen).flip inferInstance
  obtain ⟨descendedObject, descentMap, hq, hinv⟩ := (restrictBase invariant overBase).isEffective_of_isAffine
  refine ⟨Over.mk (descendedObject.hom ≫ baseOpen.ι), descentMap, ?_, fun {test} f₁ f₂ compatibility point ↦ ?_⟩
  · simpa using hq.paste_vert (isPullback_morphismRestrict baseMap baseOpen)
  · have first_eq : f₁ = point.left ≫ openSubset.ι ≫ representation.hom := (Over.w point).symm
    have hr : Set.range f₂ ⊆ Set.range (baseMap ⁻¹ᵁ baseOpen).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨testPoint, rfl⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← compatibility, first_eq]
      exact overBase (point.left testPoint).2
    let f₂' := IsOpenImmersion.lift (baseMap ⁻¹ᵁ baseOpen).ι f₂ hr
    have hf₂' : f₂' ≫ (baseMap ⁻¹ᵁ baseOpen).ι = f₂ := IsOpenImmersion.lift_fac _ _ _
    have hf₁ : (point.left ≫ homToPreimage overBase) ≫ (baseMap ⁻¹ᵁ baseOpen).ι = f₁ := by
      rw [Category.assoc, homToPreimage_ι]
      exact first_eq.symm
    have h' : (point.left ≫ homToPreimage overBase) ≫ baseMap ∣_ baseOpen = f₂' ≫ baseMap ∣_ baseOpen := by
      rw [← cancel_mono baseOpen.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      rw [reassoc_of% hf₁, reassoc_of% hf₂', compatibility]
    have first_eq := (datum.restrict openSubset invariant).transport_left_congr (comp_ι_comp_eq h') compatibility
      (pointOfPreimage overBase (Over.homMk point.left rfl)) point hf₁ hf₂' rfl
    rw [← first_eq]
    exact hinv (point.left ≫ homToPreimage overBase) f₂' h' (Over.homMk point.left rfl)

end CategoryTheory.Over.DescentDatum
