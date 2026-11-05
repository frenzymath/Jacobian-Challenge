import Jacobian.AlgebraicGeometry.Modules.AmpleFamily
import Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import Jacobian.AlgebraicGeometry.IdealSheaf.FiniteImage
import Jacobian.AlgebraicGeometry.Regular
import Jacobian.AlgebraicGeometry.Morphisms.FiniteFlatChart
import Jacobian.AlgebraicGeometry.Group.Translations
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Cartier complements on group schemes

A finite flat chart sends translates of an effective Cartier divisor to a
family of Cartier divisors. Rational points identify the affine complements of
its fibres and show that those complements cover the closed points.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe schemeUniverse

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

section AlgClosed

variable {baseField : Type schemeUniverse} [Field baseField] [IsAlgClosed baseField]

variable (baseField) in

noncomputable def unitPoint : (𝟙_ (Over (Spec (.of baseField)))).left :=
  IsLocalRing.closedPoint baseField

local notation "pt" => unitPoint baseField

lemma isClosed_singleton_left_apply {target : Over (Spec (.of baseField))} [LocallyOfFiniteType target.hom]
    (targetPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ target) : IsClosed {targetPoint.left pt} :=
  ((pointEquivClosedPoint target.hom) ⟨targetPoint.left, Over.w targetPoint⟩).2

theorem left_apply_mem_image_iff {scheme target : Over (Spec (.of baseField))} [LocallyOfFiniteType scheme.hom]
    [LocallyOfFiniteType target.hom] [CompactSpace scheme.left] (morphism : scheme ⟶ target) {Z : Set scheme.left}
    (hZ : IsClosed Z) (targetPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ target) :
    targetPoint.left pt ∈ morphism.left '' Z ↔ ∃ point : 𝟙_ (Over (Spec (.of baseField))) ⟶ scheme, point ≫ morphism = targetPoint ∧ point.left pt ∈ Z := by
  refine ⟨fun ⟨sourcePoint, hz, hfz⟩ ↦ ?_, fun ⟨point, hx, hxZ⟩ ↦
    ⟨point.left pt, hxZ, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]⟩⟩
  obtain ⟨z', hz', hcl⟩ := isClosed_closure.exists_closed_singleton
    (⟨sourcePoint, subset_closure rfl⟩ : (closure {sourcePoint}).Nonempty)
  have hfz' : morphism.left z' = targetPoint.left pt := by
    have := image_closure_subset_closure_image morphism.left.continuous ⟨z', hz', rfl⟩
    rwa [Set.image_singleton, hfz, (isClosed_singleton_left_apply targetPoint).closure_eq] at this
  refine ⟨Over.homMk (pointOfClosedPoint scheme.hom z' hcl) (pointOfClosedPoint_comp _ _ _), ?_,
    by simpa using hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz) hz'⟩
  refine Over.OverMorphism.ext (ext_of_apply_closedPoint_eq target.hom (by simp) (Over.w targetPoint) ?_)
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.homMk_left, pointOfClosedPoint_apply]
  exact hfz'

lemma finite_hom_comp_eq {chart parameterSpace : Over (Spec (.of baseField))} [LocallyOfFiniteType chart.hom] (finiteMap : chart ⟶ parameterSpace)
    [IsFinite finiteMap.left] (rationalPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ parameterSpace) :
    Finite {member : 𝟙_ (Over (Spec (.of baseField))) ⟶ chart // member ≫ finiteMap = rationalPoint} := by
  have := (finiteMap.left.finite_preimage_singleton (rationalPoint.left pt)).to_subtype
  refine Finite.of_injective (β := finiteMap.left ⁻¹' {rationalPoint.left pt})
    (fun member ↦ ⟨member.1.left pt, by simp [← Scheme.Hom.comp_apply, ← Over.comp_left, member.2]⟩)
    fun member w' compatibility ↦ Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq chart.hom (Over.w member.1) (Over.w w'.1) congr($(compatibility).1)

section Group

variable (group : Over (Spec (.of baseField))) [GrpObj group]

omit [IsAlgClosed baseField] in

lemma GrpObj.comp_mulRight (groupPoint compatibility : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    groupPoint ≫ GrpObj.mulRight group compatibility = lift groupPoint compatibility ≫ μ[group] := by
  rw [GrpObj.mulRight, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (groupPoint ≫ toUnit group) (𝟙 _), Category.id_comp]

omit [IsAlgClosed baseField] in

lemma GrpObj.comp_mulLeft (groupPoint compatibility : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    compatibility ≫ GrpObj.mulLeft group groupPoint = lift groupPoint compatibility ≫ μ[group] := by
  rw [GrpObj.mulLeft, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (compatibility ≫ toUnit group) (𝟙 _), Category.id_comp]

omit [IsAlgClosed baseField] in

instance (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) : IsIso (GrpObj.mulRight group groupPoint).left :=
  inferInstanceAs (IsIso ((Over.forget _).mapIso (GrpObj.mulRightIso group groupPoint)).hom)

variable {chart parameterSpace : Over (Spec (.of baseField))} (chartImmersion : chart ⟶ group) (finiteMap : chart ⟶ parameterSpace)
  (cartierIdeal : group.left.IdealSheafData) (imageIdeal : (group ⊗ parameterSpace).left.IdealSheafData)

theorem GrpObj.left_apply_mem_support_comap_iff [LocallyOfFiniteType (group ⊗ chart).hom]
    [LocallyOfFiniteType (group ⊗ parameterSpace).hom] [CompactSpace (group ⊗ chart).left]
    (hE : (imageIdeal.support : Set (group ⊗ parameterSpace).left) =
      (group ◁ finiteMap).left '' (cartierIdeal.comap ((group ◁ chartImmersion) ≫ μ[group]).left).support)
    (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) (rationalPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ parameterSpace) :
    groupPoint.left pt ∈ (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ rationalPoint)).left).support ↔
      ∃ member : 𝟙_ (Over (Spec (.of baseField))) ⟶ chart, member ≫ finiteMap = rationalPoint ∧
        (GrpObj.mulRight group (member ≫ chartImmersion)).left (groupPoint.left pt) ∈ cartierIdeal.support := by
  have hgv : groupPoint ≫ lift (𝟙 group) (toUnit group ≫ rationalPoint) = lift groupPoint rationalPoint := by simp
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_comap, Set.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, hgv, hE,
    left_apply_mem_image_iff _ (Scheme.IdealSheafData.support _).isClosed]
  have key (point : 𝟙_ (Over (Spec (.of baseField))) ⟶ group ⊗ chart) :
      point.left pt ∈ (cartierIdeal.comap ((group ◁ chartImmersion) ≫ μ[group]).left).support ↔
        (point ≫ (group ◁ chartImmersion) ≫ μ[group]).left pt ∈ cartierIdeal.support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_comap, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, ← Over.comp_left, SetLike.mem_coe]
  constructor
  · rintro ⟨point, hx, hxs⟩
    have hg : point ≫ fst _ _ = groupPoint := by
      rw [← whiskerLeft_fst group finiteMap, ← Category.assoc, hx, lift_fst]
    refine ⟨point ≫ snd _ _, ?_, ?_⟩
    · rw [Category.assoc, ← whiskerLeft_snd, ← Category.assoc, hx, lift_snd]
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_mulRight]
      have compatibility : lift groupPoint ((point ≫ snd _ _) ≫ chartImmersion) ≫ μ[group] = point ≫ (group ◁ chartImmersion) ≫ μ[group] := by
        rw [← hg, ← Category.assoc]
        congr 1
        ext <;> simp
      rw [compatibility]
      exact (key point).mp hxs
  · rintro ⟨member, hw, hmem⟩
    refine ⟨lift groupPoint member, by rw [lift_whiskerLeft, hw], (key _).mpr ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_mulRight] at hmem
    rwa [← Category.assoc, lift_whiskerLeft]

noncomputable abbrev overPointOfClosedPoint [LocallyOfFiniteType group.hom] (point : group.left)
    (hx : IsClosed {point}) :
    𝟙_ (Over (Spec (.of baseField))) ⟶ group :=
  Over.homMk (pointOfClosedPoint group.hom point hx) (pointOfClosedPoint_comp _ _ _)

omit [GrpObj group] in

lemma overPointOfClosedPoint_left_apply [LocallyOfFiniteType group.hom] (point : group.left)
    (hx : IsClosed {point}) :
    (overPointOfClosedPoint group point hx).left pt = point :=
  pointOfClosedPoint_apply _ _ _ _

theorem GrpObj.compl_support_comap_eq [LocallyOfFiniteType group.hom] [LocallyOfFiniteType chart.hom]
    [LocallyOfFiniteType (group ⊗ chart).hom] [LocallyOfFiniteType (group ⊗ parameterSpace).hom]
    [CompactSpace (group ⊗ chart).left] [IsFinite finiteMap.left]
    (hE : (imageIdeal.support : Set (group ⊗ parameterSpace).left) =
      (group ◁ finiteMap).left '' (cartierIdeal.comap ((group ◁ chartImmersion) ≫ μ[group]).left).support)
    {affineOpen : group.left.Opens} (hJU : (cartierIdeal.support : Set group.left) = (affineOpen : Set group.left)ᶜ)
    (rationalPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ parameterSpace) :
    (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ rationalPoint)).left).support.compl =
      ⨅ member : {member : 𝟙_ (Over (Spec (.of baseField))) ⟶ chart // member ≫ finiteMap = rationalPoint},
        (GrpObj.mulRight group (member.1 ≫ chartImmersion)).left ⁻¹ᵁ affineOpen := by
  have : JacobsonSpace group.left := LocallyOfFiniteType.jacobsonSpace group.hom
  refine TopologicalSpace.Opens.eq_of_forall_isClosed_singleton fun point hx ↦ ?_
  rw [← overPointOfClosedPoint_left_apply group point hx]
  have := finite_hom_comp_eq finiteMap rationalPoint
  have hc (targetPoint : group.left) (C : group.left.IdealSheafData) : targetPoint ∈ C.support.compl ↔ targetPoint ∉ C.support :=
    Iff.rfl
  rw [← SetLike.mem_coe (p := ⨅ _, _), TopologicalSpace.Opens.coe_iInf, hc,
    GrpObj.left_apply_mem_support_comap_iff group chartImmersion finiteMap cartierIdeal imageIdeal hE]
  simp [← SetLike.mem_coe, hJU]

theorem GrpObj.exists_notMem_support_comap [LocallyOfFiniteType group.hom]
    [LocallyOfFiniteType (group ⊗ chart).hom] [LocallyOfFiniteType (group ⊗ parameterSpace).hom]
    [CompactSpace (group ⊗ chart).left] [LocallyOfFiniteType parameterSpace.hom] [Nonempty parameterSpace.left] [Flat chartImmersion.left]
    (hπ : ∀ C : chart.left.IdealSheafData, C.IsInvertible →
      ∃ E' : parameterSpace.left.IdealSheafData, E'.IsInvertible ∧
        (E'.support : Set parameterSpace.left) = finiteMap.left '' C.support)
    (hJ : cartierIdeal.IsInvertible)
    (hE : (imageIdeal.support : Set (group ⊗ parameterSpace).left) =
      (group ◁ finiteMap).left '' (cartierIdeal.comap ((group ◁ chartImmersion) ≫ μ[group]).left).support)
    (point : group.left) (hx : IsClosed {point}) :
    ∃ rationalPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ parameterSpace, point ∉ (imageIdeal.comap (lift (𝟙 group) (toUnit group ≫ rationalPoint)).left).support := by
  have := GrpObj.isIso_mulLeft_left group (overPointOfClosedPoint group point hx)
  have : Flat (chartImmersion ≫ GrpObj.mulLeft group (overPointOfClosedPoint group point hx)).left := by
    rw [Over.comp_left]
    infer_instance
  obtain ⟨E', hE', hE's⟩ :=
    hπ _ (hJ.comap_of_flat (chartImmersion ≫ GrpObj.mulLeft group (overPointOfClosedPoint group point hx)).left)
  obtain ⟨v₀, hv₀⟩ := hE'.exists_notMem_support
  have : JacobsonSpace parameterSpace.left := LocallyOfFiniteType.jacobsonSpace parameterSpace.hom
  obtain ⟨v₁, hv₁, hv₁c⟩ := nonempty_inter_closedPoints (Z := (E'.support : Set parameterSpace.left)ᶜ) ⟨v₀, hv₀⟩
    E'.support.isClosed.isOpen_compl.isLocallyClosed
  rw [mem_closedPoints_iff] at hv₁c
  refine ⟨Over.homMk (pointOfClosedPoint parameterSpace.hom v₁ hv₁c) (pointOfClosedPoint_comp _ _ _), ?_⟩
  rw [← overPointOfClosedPoint_left_apply group point hx,
    GrpObj.left_apply_mem_support_comap_iff group chartImmersion finiteMap cartierIdeal imageIdeal hE]
  rintro ⟨member, hw, hmem⟩
  refine hv₁ (hE's ▸ ⟨member.left pt, ?_, ?_⟩)
  · rw [Scheme.IdealSheafData.coe_support_comap, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Category.assoc, GrpObj.comp_mulLeft,
      ← GrpObj.comp_mulRight, Over.comp_left, Scheme.Hom.comp_apply]
    exact hmem
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw]
    exact pointOfClosedPoint_apply _ _ _ _

end Group

end AlgClosed

end AlgebraicGeometry
