import Jacobian.AlgebraicGeometry.Hilbert.Basic
import Jacobian.AlgebraicGeometry.Morphisms.FiniteRank

/-!
# Hilbert schemes of degree zero and one

The empty subscheme is the unique finite flat family of degree zero. For a
separated morphism, finite flat families of degree one are precisely graphs of
sections. Consequently the degree-zero Hilbert functor is represented by the
base, and the degree-one Hilbert functor by the source.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The empty subscheme is a finite flat family of degree zero. -/
lemma isHilbertSubscheme_top (f : X ⟶ S) (test : Over S) :
    IsHilbertSubscheme f 0 test ⊤ :=
  ⟨inferInstance, inferInstance, inferInstance,
    fun point ↦ Scheme.Hom.finrank_eq_zero_of_isEmpty _ point⟩

/-- A finite flat family of degree zero is empty. -/
lemma IsHilbertSubscheme.eq_top_of_zero {f : X ⟶ S} {test : Over S}
    {ideal : (pullback f test.hom).IdealSheafData}
    (family : IsHilbertSubscheme f 0 test ideal) : ideal = ⊤ := by
  obtain ⟨_, _, _, rank⟩ := family
  have : IsEmpty ideal.subscheme := ⟨fun point ↦ by
    simpa [rank] using
      Scheme.Hom.one_le_finrank_map (ideal.subschemeι ≫ pullback.snd f test.hom) point⟩
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, ← SetLike.coe_set_eq,
    ← Scheme.IdealSheafData.range_subschemeι]
  simp [Set.range_eq_empty]

instance hilbertPresheaf_zero_subsingleton (f : X ⟶ S) (test : (Over S)ᵒᵖ) :
    Subsingleton ((hilbertPresheaf f 0).obj test) :=
  ⟨fun first second ↦
    Subtype.ext (first.2.eq_top_of_zero.trans second.2.eq_top_of_zero.symm)⟩

/-- There is exactly one degree-zero family over each test scheme. -/
def hilbertPresheafZeroEquiv (f : X ⟶ S) (test : Over S) :
    (test ⟶ Over.mk (𝟙 S)) ≃ (hilbertPresheaf f 0).obj (op test) where
  toFun _ := ⟨⊤, isHilbertSubscheme_top f test⟩
  invFun _ := Over.homMk test.hom (by simp)
  left_inv morphism := by
    ext1
    simpa using (Over.w morphism).symm
  right_inv _ := Subsingleton.elim _ _

/-- The base represents the degree-zero Hilbert functor. -/
def hilbertPresheafZeroRepresentableBy (f : X ⟶ S) :
    (hilbertPresheaf f 0).RepresentableBy (Over.mk (𝟙 S)) where
  homEquiv := hilbertPresheafZeroEquiv f _
  homEquiv_comp _ _ := Subsingleton.elim _ _

/-- A scheme representing the degree-zero Hilbert functor is isomorphic to the base. -/
theorem isIso_of_representableBy_hilbertPresheaf_zero (f : X ⟶ S)
    {representative : Over S}
    (representation : (hilbertPresheaf f 0).RepresentableBy representative) :
    IsIso representative.hom := by
  have unique : ∀ {test : Over S} (first second : test ⟶ representative), first = second :=
    fun first second ↦ representation.homEquiv.injective (Subsingleton.elim _ _)
  let sectionMap : Over.mk (𝟙 S) ⟶ representative :=
    representation.homEquiv.symm ⟨⊤, isHilbertSubscheme_top f _⟩
  refine ⟨sectionMap.left, ?_, by simp⟩
  have equality := congrArg CommaMorphism.left
    (unique (Over.homMk (representative.hom ≫ sectionMap.left)
      (by simp [Over.w sectionMap]) : representative ⟶ representative) (𝟙 representative))
  simpa using equality

/-- The graph of a morphism into a separated scheme is closed. -/
lemma isClosedImmersion_lift_id (f : X ⟶ S) [IsSeparated f] {test : Over S}
    (point : test.left ⟶ X) (over_base : point ≫ f = test.hom) :
    IsClosedImmersion
      (pullback.lift point (𝟙 test.left) (by simp [over_base]) :
        test.left ⟶ pullback f test.hom) := by
  have : IsClosedImmersion
      ((pullback.lift point (𝟙 test.left) (by simp [over_base]) :
        test.left ⟶ pullback f test.hom) ≫ pullback.snd f test.hom) := by
    rw [pullback.lift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f test.hom)

/-- A graph defines a finite flat family of degree one. -/
lemma isHilbertSubscheme_ker_lift_id (f : X ⟶ S) [IsSeparated f] {test : Over S}
    (point : test.left ⟶ X) (over_base : point ≫ f = test.hom) :
    IsHilbertSubscheme f 1 test
      (pullback.lift point (𝟙 test.left) (by simp [over_base]) :
        test.left ⟶ pullback f test.hom).ker := by
  set graph : test.left ⟶ pullback f test.hom :=
    pullback.lift point (𝟙 test.left) (by simp [over_base])
  have := isClosedImmersion_lift_id f point over_base
  have := IsClosedImmersion.isIso_lift graph.ker.subschemeι graph
    (Scheme.IdealSheafData.ker_subschemeι _)
  set graphIso := asIso (IsClosedImmersion.lift graph.ker.subschemeι graph
    (Scheme.IdealSheafData.ker_subschemeι graph.ker).le)
  have factorization : graphIso.hom ≫ graph.ker.subschemeι = graph :=
    IsClosedImmersion.lift_fac _ _ _
  have projection : graph.ker.subschemeι ≫ pullback.snd f test.hom = graphIso.inv := by
    rw [← cancel_epi graphIso.hom, ← Category.assoc, factorization,
      graphIso.hom_inv_id, pullback.lift_snd]
  rw [IsHilbertSubscheme, projection]
  exact ⟨inferInstance, inferInstance, inferInstance, fun parameter ↦ by
    rw [Scheme.Hom.finrank_eq_one_of_isIso]
    rfl⟩

/-- Graph ideals commute with change of parameter scheme. -/
lemma ker_lift_id_comap_baseChangeMap (f : X ⟶ S) [IsSeparated f]
    {test smallerTest : Over S} (restriction : smallerTest ⟶ test)
    (point : test.left ⟶ X) (over_base : point ≫ f = test.hom)
    (restrictedPoint : smallerTest.left ⟶ X)
    (restricted_over_base : restrictedPoint ≫ f = smallerTest.hom)
    (point_equality : restrictedPoint = restriction.left ≫ point) :
    (pullback.lift point (𝟙 test.left) (by simp [over_base]) :
      test.left ⟶ pullback f test.hom).ker.comap (baseChangeMap f restriction) =
        (pullback.lift restrictedPoint (𝟙 smallerTest.left)
          (by simp [restricted_over_base]) :
            smallerTest.left ⟶ pullback f smallerTest.hom).ker := by
  subst point_equality
  have := isClosedImmersion_lift_id f point over_base
  have square : IsPullback restriction.left
      (pullback.lift (restriction.left ≫ point) (𝟙 smallerTest.left)
        (by simp [restricted_over_base]) : smallerTest.left ⟶ pullback f smallerTest.hom)
      (pullback.lift point (𝟙 test.left) (by simp [over_base]) :
        test.left ⟶ pullback f test.hom) (baseChangeMap f restriction) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeMap f restriction)
    · simp only [pullback.lift_snd]
      exact IsPullback.of_vert_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
    · apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, pullback.lift_snd, Category.comp_id,
          pullback.lift_snd_assoc]
        rfl
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← square.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- A degree-one family projects isomorphically to its parameter scheme. -/
lemma IsHilbertSubscheme.isIso_projection_of_one {f : X ⟶ S} {test : Over S}
    {ideal : (pullback f test.hom).IdealSheafData}
    (family : IsHilbertSubscheme f 1 test ideal) :
    IsIso (ideal.subschemeι ≫ pullback.snd f test.hom) := by
  obtain ⟨_, _, _, rank⟩ := family
  exact (Scheme.Hom.isIso_iff_finrank_eq _).2 (funext rank)

/-- Every degree-one family is the graph of a morphism to the source. -/
lemma IsHilbertSubscheme.exists_eq_ker_lift_id {f : X ⟶ S} {test : Over S}
    {ideal : (pullback f test.hom).IdealSheafData}
    (family : IsHilbertSubscheme f 1 test ideal) :
    ∃ (point : test.left ⟶ X) (over_base : point ≫ f = test.hom),
      ideal = (pullback.lift point (𝟙 test.left) (by simp [over_base]) :
        test.left ⟶ pullback f test.hom).ker := by
  let projection := ideal.subschemeι ≫ pullback.snd f test.hom
  have : IsIso projection := family.isIso_projection_of_one
  let point := inv projection ≫ ideal.subschemeι ≫ pullback.fst f test.hom
  have over_base : point ≫ f = test.hom := by
    calc
      point ≫ f = inv projection ≫ projection ≫ test.hom := by
        simp only [point, projection, Category.assoc, pullback.condition]
      _ = test.hom := by simp
  refine ⟨point, over_base, ?_⟩
  have graph_equality :
      (pullback.lift point (𝟙 test.left) (by simp [over_base]) :
        test.left ⟶ pullback f test.hom) = inv projection ≫ ideal.subschemeι := by
    apply pullback.hom_ext
    · simp [point, Category.assoc]
    · simp only [Category.assoc, pullback.lift_snd]
      change 𝟙 test.left = inv projection ≫ projection
      simp
  rw [graph_equality, Scheme.Hom.ker_comp_of_isIso, ideal.ker_subschemeι]

/-- A graph ideal determines its section uniquely. -/
lemma ker_lift_id_injective (f : X ⟶ S) [IsSeparated f] {test : Over S}
    (first second : test.left ⟶ X)
    (first_over_base : first ≫ f = test.hom) (second_over_base : second ≫ f = test.hom)
    (equality : (pullback.lift first (𝟙 test.left) (by simp [first_over_base]) :
        test.left ⟶ pullback f test.hom).ker =
      (pullback.lift second (𝟙 test.left) (by simp [second_over_base]) :
        test.left ⟶ pullback f test.hom).ker) : first = second := by
  let firstGraph : test.left ⟶ pullback f test.hom :=
    pullback.lift first (𝟙 test.left) (by simp [first_over_base])
  let secondGraph : test.left ⟶ pullback f test.hom :=
    pullback.lift second (𝟙 test.left) (by simp [second_over_base])
  have := isClosedImmersion_lift_id f second second_over_base
  let comparison := IsClosedImmersion.lift secondGraph firstGraph equality.symm.le
  have factorization : comparison ≫ secondGraph = firstGraph :=
    IsClosedImmersion.lift_fac _ _ _
  have comparison_id : comparison = 𝟙 test.left := by
    simpa [firstGraph, secondGraph, Category.assoc] using
      congrArg (fun morphism ↦ morphism ≫ pullback.snd f test.hom) factorization
  have graph_equality : secondGraph = firstGraph := by
    simpa [comparison_id] using factorization
  simpa [firstGraph, secondGraph] using
    (congrArg (fun morphism ↦ morphism ≫ pullback.fst f test.hom) graph_equality).symm

/-- Sections of the source correspond bijectively to degree-one families. -/
def hilbertPresheafOneEquiv (f : X ⟶ S) [IsSeparated f] (test : Over S) :
    (test ⟶ Over.mk f) ≃ (hilbertPresheaf f 1).obj (op test) :=
  Equiv.ofBijective
    (fun point ↦ ⟨(pullback.lift point.left (𝟙 test.left) (by
      rw [Category.id_comp]
      exact Over.w point) :
      test.left ⟶ pullback f test.hom).ker,
        isHilbertSubscheme_ker_lift_id f point.left (Over.w point)⟩)
    ⟨fun first second equality ↦ by
      apply Over.OverMorphism.ext
      exact ker_lift_id_injective f first.left second.left (Over.w first) (Over.w second)
        (congrArg Subtype.val equality),
      fun family ↦ by
        obtain ⟨point, over_base, equality⟩ := family.2.exists_eq_ker_lift_id
        exact ⟨Over.homMk point over_base, Subtype.ext equality.symm⟩⟩

/-- The source of a separated morphism represents its degree-one Hilbert functor. -/
def hilbertPresheafOneRepresentableBy (f : X ⟶ S) [IsSeparated f] :
    (hilbertPresheaf f 1).RepresentableBy (Over.mk f) where
  homEquiv := hilbertPresheafOneEquiv f _
  homEquiv_comp restriction point := by
    apply Subtype.ext
    exact (ker_lift_id_comap_baseChangeMap f restriction point.left (Over.w point)
      (restriction.left ≫ point.left) (by
        rw [Category.assoc]
        exact (congrArg (fun morphism ↦ restriction.left ≫ morphism)
          (show point.left ≫ f = _ from Over.w point)).trans (Over.w restriction)) rfl).symm

/-- Any degree-one Hilbert scheme is canonically isomorphic to the source over the base. -/
def hilbertPresheafOneIso (f : X ⟶ S) [IsSeparated f] {representative : Over S}
    (representation : (hilbertPresheaf f 1).RepresentableBy representative) :
    representative ≅ Over.mk f :=
  representation.uniqueUpToIso (hilbertPresheafOneRepresentableBy f)

end AlgebraicGeometry
