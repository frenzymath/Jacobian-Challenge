import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Jacobian.CategoryTheory.Comma.Over.DescentDatum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Descending a representing object

Let `baseMap : source ⟶ target` be a morphism, `presheaf` a presheaf on `Over target`, and `representation` an object over `source`
representing the restriction of `presheaf` to `Over source`. Let `descendedObject` be an object over `target` with
`representation ≅ descendedObject ×_Y source` through `descentMap : representation ⟶ descendedObject`, such that `descentMap` is invariant under the canonical descent
datum of `representation`. If the base changes `test ×_Y source ⟶ test` of `baseMap` are epimorphisms along which the points
of `descendedObject` descend and for which `presheaf` satisfies the sheaf condition, then `descendedObject` represents `presheaf`.

## Main statements

- `CategoryTheory.Functor.RepresentableBy.nonempty_representableBy_of_descent`.
-/

section
universe valueUniverse homUniverse categoryUniverse

namespace CategoryTheory.Functor.RepresentableBy

open Limits Opposite

variable {CategoryType : Type categoryUniverse} [Category.{homUniverse} CategoryType] [HasPullbacks CategoryType] {source target : CategoryType} {baseMap : source ⟶ target}
  {presheaf : (Over target)ᵒᵖ ⥤ Type valueUniverse}

/-- The base change `test ×_Y source` of `baseMap` along `test ⟶ target`, as an object over `target`. -/
noncomputable abbrev descentCover (baseMap : source ⟶ target) (test : Over target) : Over target :=
  Over.mk (pullback.snd test.hom baseMap ≫ baseMap)

/-- The projection `test ×_Y source ⟶ test`, as a morphism over `target`. -/
noncomputable abbrev descentCoverπ (baseMap : source ⟶ target) (test : Over target) : descentCover baseMap test ⟶ test :=
  Over.homMk (pullback.fst test.hom baseMap) pullback.condition

/-- The fibre product `(test ×_Y source) ×_T (test ×_Y source)`, as an object over `target`. -/
noncomputable abbrev descentCover₂ (baseMap : source ⟶ target) (test : Over target) : Over target :=
  Over.mk (pullback.fst (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ pullback.fst test.hom baseMap ≫
    test.hom)

/-- The two projections `(test ×_Y source) ×_T (test ×_Y source) ⟶ test ×_Y source`, as morphisms over `target`. -/
noncomputable abbrev descentCoverPr₁ (baseMap : source ⟶ target) (test : Over target) :
    descentCover₂ baseMap test ⟶ descentCover baseMap test :=
  Over.homMk (pullback.fst (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap)) (by
    simp only [Over.mk_hom]
    rw [pullback.condition])

/-- The second projection of the fibre product, as a morphism over `target`. -/
noncomputable abbrev descentCoverPr₂ (baseMap : source ⟶ target) (test : Over target) :
    descentCover₂ baseMap test ⟶ descentCover baseMap test :=
  Over.homMk (pullback.snd (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap)) (by
    simp only [Over.mk_hom]
    rw [pullback.condition_assoc, pullback.condition])


variable {representation : Over source} (representability : ((Over.map baseMap).op ⋙ presheaf).RepresentableBy representation) {descendedObject : Over target}
  (descentMap : representation.left ⟶ descendedObject.left)
  (hq : IsPullback descentMap representation.hom descendedObject.hom baseMap)
  (hinv : ∀ {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation),
    (representability.overTransport f₁ f₂ equality point).left ≫ descentMap = point.left ≫ descentMap)

include hq hinv in
/-- A point of `representation` over `test ×_Y source` lies in the descent equaliser for `presheaf` exactly when its image
in `descendedObject` lies in the descent equaliser for `descendedObject`. -/
lemma map_descentCoverPr_eq_iff (test : Over target) (point : Over.mk (pullback.snd test.hom baseMap) ⟶ representation) :
    presheaf.map (descentCoverPr₁ baseMap test).op (representability.homEquiv point) =
        presheaf.map (descentCoverPr₂ baseMap test).op (representability.homEquiv point) ↔
      pullback.fst (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ point.left ≫ descentMap =
        pullback.snd (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ point.left ≫ descentMap := by
  let π := pullback.fst test.hom baseMap
  let sectionElement := pullback.snd test.hom baseMap
  let fst₂ := pullback.fst π π
  let snd₂ := pullback.snd π π
  have hc : π ≫ test.hom = sectionElement ≫ baseMap := pullback.condition
  have hc₂ : fst₂ ≫ π = snd₂ ≫ π := pullback.condition
  have equality : (fst₂ ≫ sectionElement) ≫ baseMap = (snd₂ ≫ sectionElement) ≫ baseMap := by
    simp only [Category.assoc]
    rw [← hc, ← Category.assoc, hc₂, Category.assoc]
  let a₁ : Over.mk (fst₂ ≫ sectionElement) ⟶ representation :=
    (Over.homMk (U := Over.mk (fst₂ ≫ sectionElement)) (V := Over.mk sectionElement) fst₂ rfl) ≫ point
  let a₂ : Over.mk (snd₂ ≫ sectionElement) ⟶ representation :=
    (Over.homMk (U := Over.mk (snd₂ ≫ sectionElement)) (V := Over.mk sectionElement) snd₂ rfl) ≫ point
  have w₁ : 𝟙 _ ≫ (fst₂ ≫ sectionElement) ≫ baseMap = fst₂ ≫ π ≫ test.hom := by
    rw [Category.id_comp, Category.assoc, hc]
  have w₂ : 𝟙 _ ≫ (snd₂ ≫ sectionElement) ≫ baseMap = fst₂ ≫ π ≫ test.hom := by
    rw [w₁.symm, Category.id_comp, Category.id_comp, equality]
  let e₁ : descentCover₂ baseMap test ⟶ (Over.map baseMap).obj (Over.mk (fst₂ ≫ sectionElement)) := Over.homMk (𝟙 _) w₁
  let e₂ : descentCover₂ baseMap test ⟶ (Over.map baseMap).obj (Over.mk (snd₂ ≫ sectionElement)) := Over.homMk (𝟙 _) w₂
  have he₂ : IsIso e₂ := ⟨Over.homMk (𝟙 _) (by
      rw [Category.id_comp]
      exact (Category.id_comp _).symm.trans w₂ |>.symm), by ext; simp [e₂],
    by ext; simp [e₂]⟩
  have hPr₁ : descentCoverPr₁ baseMap test =
      e₁ ≫ (Over.map baseMap).map (Over.homMk (U := Over.mk (fst₂ ≫ sectionElement)) (V := Over.mk sectionElement) fst₂ rfl) := by
    ext; simp [e₁, fst₂, π]
  have hPr₂ : descentCoverPr₂ baseMap test =
      e₂ ≫ (Over.map baseMap).map (Over.homMk (U := Over.mk (snd₂ ≫ sectionElement)) (V := Over.mk sectionElement) snd₂ rfl) := by
    ext; simp [e₂, snd₂, π]
  have he : e₁ = e₂ ≫ overMapHomMkId (fst₂ ≫ sectionElement) (snd₂ ≫ sectionElement) equality := by
    ext; simp [e₁, e₂]
  have hF₁ : presheaf.map (descentCoverPr₁ baseMap test).op (representability.homEquiv point) =
      presheaf.map e₂.op (representability.homEquiv (representability.overTransport _ _ equality a₁)) := by
    erw [homEquiv_overTransport]
    rw [representability.homEquiv_comp, hPr₁, he]
    simp only [Functor.comp_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  have hF₂ : presheaf.map (descentCoverPr₂ baseMap test).op (representability.homEquiv point) = presheaf.map e₂.op (representability.homEquiv a₂) := by
    rw [representability.homEquiv_comp, hPr₂]
    simp only [Functor.comp_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  have hinj : Function.Injective (presheaf.map e₂.op) := by
    have : IsIso (presheaf.map e₂.op) := inferInstance
    exact (isIso_iff_bijective _).1 this |>.1
  rw [hF₁, hF₂, hinj.eq_iff, representability.homEquiv.injective.eq_iff]
  constructor
  · intro hta
    have := hinv _ _ equality a₁
    rw [hta] at this
    simpa [a₁, a₂, fst₂, snd₂, π] using this.symm
  · intro hla
    refine Over.OverMorphism.ext (hq.hom_ext ?_ ?_)
    · rw [hinv]
      simpa [a₁, a₂, fst₂, snd₂, π] using hla
    · simp only [Over.w]

include hq hinv in
/-- **Descending a representing object.** Let `representation` represent the restriction of `presheaf` to `Over source`,
and let `descentMap : representation ⟶ descendedObject` exhibit `representation` as `descendedObject ×_Y source` compatibly with the canonical descent datum of
`representation`:
```
  representation ---descentMap---> descendedObject
  |          |
  homUniverse          homUniverse
  source ---baseMap---> target
```
For `T` over `Y` consider the base change `π : T ×_Y X ⟶ T` of `p` and the two projections
```
                         pr₁
  (test ×_Y source) ×_T (test ×_Y source) ====> test ×_Y source --π--> test
                         pr₂
```
If every such `π` is an epimorphism along which the points of `V₀` descend (point point of `V₀` over
`T ×_Y X` whose two pullbacks along `pr₁`, `pr₂` agree comes from `T`), and `F` satisfies the
sheaf condition for the covering `π`, then `V₀` represents `F`. -/
theorem exists_representableBy_of_descent
    (hepi : ∀ test : Over target, Epi (pullback.fst test.hom baseMap))
    (hV₀ : ∀ (test : Over target) (point : pullback test.hom baseMap ⟶ descendedObject.left),
      pullback.fst (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ point =
        pullback.snd (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ point →
      ∃ secondPoint : test.left ⟶ descendedObject.left, pullback.fst test.hom baseMap ≫ secondPoint = point)
    (hF : ∀ test : Over target, Presieve.IsSheafFor presheaf (.singleton (descentCoverπ baseMap test))) :
    ∃ equivalence : presheaf.RepresentableBy descendedObject, ∀ (test : Over target) (secondPoint : test ⟶ descendedObject),
      presheaf.map (descentCoverπ baseMap test).op (equivalence.homEquiv secondPoint) =
        representability.homEquiv (Over.homMk (hq.lift (pullback.fst test.hom baseMap ≫ secondPoint.left) (pullback.snd test.hom baseMap)
          (by rw [Category.assoc, Over.w secondPoint, pullback.condition])) (hq.lift_snd _ _ _) :
            Over.mk (pullback.snd test.hom baseMap) ⟶ representation) := by
  have hFinj (test : Over target) (x₁ x₂ : presheaf.obj (op test))
      (equality : presheaf.map (descentCoverπ baseMap test).op x₁ = presheaf.map (descentCoverπ baseMap test).op x₂) : x₁ = x₂ :=
    (Presieve.isSheafFor_singleton.1 (hF test) _ fun p₁ p₂ hp ↦ by
      simp only [← Functor.map_comp_apply, ← op_comp, hp]).unique rfl equality.symm
  have hFglue (test : Over target) (imageElement : presheaf.obj (op (descentCover baseMap test)))
      (hy : presheaf.map (descentCoverPr₁ baseMap test).op imageElement = presheaf.map (descentCoverPr₂ baseMap test).op imageElement) :
      ∃ element, presheaf.map (descentCoverπ baseMap test).op element = imageElement := by
    refine (Presieve.isSheafFor_singleton.1 (hF test) imageElement fun {Z} p₁ p₂ hp ↦ ?_).exists
    let c : Z ⟶ descentCover₂ baseMap test := Over.homMk (pullback.lift p₁.left p₂.left
      (congrArg CommaMorphism.left hp)) (by
        simp only [Over.mk_hom, pullback.lift_fst_assoc]
        rw [pullback.condition, ← Category.assoc]
        exact (Category.assoc _ _ _).trans (Over.w p₁))
    have h₁ : p₁ = c ≫ descentCoverPr₁ baseMap test := by
      ext
      simp [c]
    have h₂ : p₂ = c ≫ descentCoverPr₂ baseMap test := by
      ext
      simp [c]
    rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      hy]
  -- the point of `representation` over `test ×_Y source` attached to a point `secondPoint` of `descendedObject` over `test`
  let lift (test : Over target) (secondPoint : test ⟶ descendedObject) : Over.mk (pullback.snd test.hom baseMap) ⟶ representation :=
    Over.homMk (hq.lift (pullback.fst test.hom baseMap ≫ secondPoint.left) (pullback.snd test.hom baseMap) (by
      rw [Category.assoc, Over.w secondPoint, pullback.condition])) (hq.lift_snd _ _ _)
  have hlift (test : Over target) (secondPoint : test ⟶ descendedObject) :
      (lift test secondPoint).left ≫ descentMap = pullback.fst test.hom baseMap ≫ secondPoint.left := hq.lift_fst _ _ _
  have hdesc (test : Over target) (secondPoint : test ⟶ descendedObject) :
      presheaf.map (descentCoverPr₁ baseMap test).op (representability.homEquiv (lift test secondPoint)) =
        presheaf.map (descentCoverPr₂ baseMap test).op (representability.homEquiv (lift test secondPoint)) := by
    rw [map_descentCoverPr_eq_iff representability descentMap hq hinv, hlift, ← Category.assoc, pullback.condition,
      Category.assoc]
  let toPt (test : Over target) (imageElement : presheaf.obj (op (descentCover baseMap test))) :
      Over.mk (pullback.snd test.hom baseMap) ⟶ representation := representability.homEquiv.symm imageElement
  -- the point of `descendedObject` over `test` attached to a section of `presheaf` over `test`
  have hpt (test : Over target) (element : presheaf.obj (op test)) : ∃ secondPoint : test ⟶ descendedObject,
      (toPt test (presheaf.map (descentCoverπ baseMap test).op element)).left ≫ descentMap =
        pullback.fst test.hom baseMap ≫ secondPoint.left := by
    let point := toPt test (presheaf.map (descentCoverπ baseMap test).op element)
    have ha : presheaf.map (descentCoverPr₁ baseMap test).op (representability.homEquiv point) =
        presheaf.map (descentCoverPr₂ baseMap test).op (representability.homEquiv point) := by
      have hpr : descentCoverPr₁ baseMap test ≫ descentCoverπ baseMap test =
          descentCoverPr₂ baseMap test ≫ descentCoverπ baseMap test := by
        ext
        exact pullback.condition
      simp only [point, toPt, Equiv.apply_symm_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← op_comp, hpr]
    obtain ⟨secondPoint, hb⟩ := hV₀ test (point.left ≫ descentMap) ((map_descentCoverPr_eq_iff representability descentMap hq hinv test point).1 ha)
    have := hepi test
    refine ⟨Over.homMk secondPoint ?_, hb.symm⟩
    rw [← cancel_epi (pullback.fst test.hom baseMap), ← Category.assoc, hb, Category.assoc, hq.w,
      ← Category.assoc, Over.w point, pullback.condition]
    rfl
  choose Φ hΦ using hpt
  have hlift_eq (test : Over target) (point : Over.mk (pullback.snd test.hom baseMap) ⟶ representation) (secondPoint : test ⟶ descendedObject)
      (hab : point.left ≫ descentMap = pullback.fst test.hom baseMap ≫ secondPoint.left) : point = lift test secondPoint := by
    refine Over.OverMorphism.ext (hq.hom_ext ?_ ?_)
    · rw [hab, hlift]
    · rw [Over.w point, Over.w (lift test secondPoint)]
  have hΦ_eq (test : Over target) (element : presheaf.obj (op test)) :
      presheaf.map (descentCoverπ baseMap test).op element = representability.homEquiv (lift test (Φ test element)) := by
    rw [← hlift_eq test _ _ (hΦ test element)]
    exact (Equiv.apply_symm_apply _ _).symm
  refine ⟨{
    homEquiv {test} := {
      toFun secondPoint := (hFglue test _ (hdesc test secondPoint)).choose
      invFun element := Φ test element
      left_inv secondPoint := ?_
      right_inv element := ?_
    }
    homEquiv_comp {test' test} c secondPoint := ?_
  }, fun test secondPoint ↦ (hFglue test _ (hdesc test secondPoint)).choose_spec⟩
  · have := hepi test
    have h₁ := (hFglue test _ (hdesc test secondPoint)).choose_spec
    refine Over.OverMorphism.ext ((cancel_epi (pullback.fst test.hom baseMap)).1 ?_)
    rw [← hΦ, h₁]
    change (representability.homEquiv.symm (representability.homEquiv (lift test secondPoint))).left ≫ descentMap = _
    rw [Equiv.symm_apply_apply, hlift]
  · apply hFinj
    rw [(hFglue test _ (hdesc test (Φ test element))).choose_spec, hΦ_eq]
  · apply hFinj
    change presheaf.map (descentCoverπ baseMap test').op (hFglue test' _ (hdesc test' (c ≫ secondPoint))).choose =
      presheaf.map (descentCoverπ baseMap test').op (presheaf.map c.op (hFglue test _ (hdesc test secondPoint)).choose)
    rw [(hFglue test' _ (hdesc test' (c ≫ secondPoint))).choose_spec, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp]
    let cc : Over.mk (pullback.snd test'.hom baseMap) ⟶ Over.mk (pullback.snd test.hom baseMap) :=
      Over.homMk (pullback.map _ _ _ _ c.left (𝟙 source) (𝟙 target) (by simp) (by simp))
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
    have hcc : descentCoverπ baseMap test' ≫ c = (Over.map baseMap).map cc ≫ descentCoverπ baseMap test := by
      ext
      simp only [Over.comp_left, Over.homMk_left, Over.map_map_left, cc]
      exact (pullback.lift_fst _ _ _).symm
    rw [hcc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [(hFglue test _ (hdesc test secondPoint)).choose_spec]
    change _ = ((Over.map baseMap).op ⋙ presheaf).map cc.op (representability.homEquiv (lift test secondPoint))
    rw [← representability.homEquiv_comp]
    congr 1
    refine (hlift_eq test' _ _ ?_).symm
    simp only [Over.comp_left, Category.assoc, hlift, cc, Over.homMk_left]
    rw [pullback.lift_fst_assoc, Category.assoc]

include hq hinv in
/-- **Descending a representing object**, without the compatibility of
`CategoryTheory.Functor.RepresentableBy.exists_representableBy_of_descent`. -/
theorem nonempty_representableBy_of_descent
    (hepi : ∀ test : Over target, Epi (pullback.fst test.hom baseMap))
    (hV₀ : ∀ (test : Over target) (point : pullback test.hom baseMap ⟶ descendedObject.left),
      pullback.fst (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ point =
        pullback.snd (pullback.fst test.hom baseMap) (pullback.fst test.hom baseMap) ≫ point →
      ∃ secondPoint : test.left ⟶ descendedObject.left, pullback.fst test.hom baseMap ≫ secondPoint = point)
    (hF : ∀ test : Over target, Presieve.IsSheafFor presheaf (.singleton (descentCoverπ baseMap test))) :
    Nonempty (presheaf.RepresentableBy descendedObject) :=
  ⟨(exists_representableBy_of_descent representability descentMap hq hinv hepi hV₀ hF).choose⟩


omit [HasPullbacks CategoryType] in
/-- **The sheaf condition for a single morphism transfers along `Over.map comparison`.** If `P` satisfies the
sheaf condition for the image of `π : test' ⟶ test` under `Over.map comparison`, then `(Over.map comparison).op ⋙ P`
satisfies it for `π`: an object over `source'` with a morphism to `(Over.map comparison).obj test'` is an
object over `source`. -/
lemma isSheafFor_singleton_overMap {source' : CategoryType} (comparison : source ⟶ source') {secondPresheaf : (Over source')ᵒᵖ ⥤ Type valueUniverse}
    {test test' : Over source} (π : test' ⟶ test)
    (equality : Presieve.IsSheafFor secondPresheaf (.singleton ((Over.map comparison).map π))) :
    Presieve.IsSheafFor ((Over.map comparison).op ⋙ secondPresheaf) (.singleton π) := by
  rw [Presieve.isSheafFor_singleton] at equality ⊢
  intro imageElement hy
  -- an object `Z'` over `source'` with a morphism `point` to `test'` is an object over `source`
  let lift {Z' : Over source'} (point : Z' ⟶ (Over.map comparison).obj test') : Over source := Over.mk (point.left ≫ test'.hom)
  let equivalence {Z' : Over source'} (point : Z' ⟶ (Over.map comparison).obj test') : Z' ⟶ (Over.map comparison).obj (lift point) :=
    Over.homMk (𝟙 _) (by simp [lift, ← Over.w point])
  obtain ⟨element, hx, hxu⟩ := equality imageElement fun {Z'} p₁ p₂ hp ↦ by
    have hl : p₂.left ≫ test'.hom = p₁.left ≫ test'.hom := by
      rw [← Over.w π]
      simpa using congrArg (fun φ ↦ φ.left ≫ test.hom) hp.symm
    let q₁ : lift p₁ ⟶ test' := Over.homMk p₁.left rfl
    let q₂ : lift p₁ ⟶ test' := Over.homMk p₂.left hl
    have hq : q₁ ≫ π = q₂ ≫ π := by
      ext
      simpa [q₁, q₂] using congrArg CommaMorphism.left hp
    have h₁ : p₁ = equivalence p₁ ≫ (Over.map comparison).map q₁ := by
      ext
      simp [equivalence, q₁]
    have h₂ : p₂ = equivalence p₁ ≫ (Over.map comparison).map q₂ := by
      ext
      simp [equivalence, q₂]
    rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (secondPresheaf.map (equivalence p₁).op) (hy q₁ q₂ hq)
  exact ⟨element, hx, fun element' hx' ↦ hxu element' hx'⟩

end CategoryTheory.Functor.RepresentableBy
