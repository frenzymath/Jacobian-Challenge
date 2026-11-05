import Jacobian.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks

/-!
# Ordered Čech complexes of abelian presheaves and their exactness for injective sheaves.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe coefficientUniverse indexUniverse

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {scheme : TopCat.{coefficientUniverse}} {indexType : Type indexUniverse} (cover : indexType → Opens scheme)

lemma iInf_le_iInf_comp {degree otherDegree : ℕ} (otherElement : Fin (otherDegree + 1) → indexType) (simplexMap : Fin (degree + 1) → Fin (otherDegree + 1)) :
    ⨅ position, cover (otherElement position) ≤ ⨅ position, cover ((otherElement ∘ simplexMap) position) :=
  le_iInf fun position ↦ iInf_le _ (simplexMap position)

/-- Restriction maps of a presheaf on `Opens X` compose: the composite of two restrictions is
the restriction along the composite inclusion. -/
lemma map_homOfLE_map_homOfLE_apply (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) {openSubset smallerOpen thirdSpace : Opens scheme}
    (h₁ : openSubset ≤ smallerOpen) (h₂ : smallerOpen ≤ thirdSpace) (element : presheaf.obj (op thirdSpace)) :
    presheaf.map (homOfLE h₁).op (presheaf.map (homOfLE h₂).op element) = presheaf.map (homOfLE (h₁.trans h₂)).op element := by
  rw [← ConcreteCategory.comp_apply, ← presheaf.map_comp]
  rfl

/-- Restricting a section along an equality of open subsets does nothing. -/
lemma map_homOfLE_self_apply (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) {openSubset : Opens scheme} (compatibility : openSubset ≤ openSubset)
    (element : presheaf.obj (op openSubset)) : presheaf.map (homOfLE compatibility).op element = element := by
  exact ConcreteCategory.congr_hom (presheaf.map_id (op openSubset)) element

/-- The Čech cochains of degree `k` of the family `U` with values in `P`: the families of
sections `c y ∈ P(U (y 0) ⊓ ⋯ ⊓ U (y k))` indexed by the tuples `y : Fin (k + 1) → ι`. -/
abbrev CechCochain (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) (degree : ℕ) : Type (max coefficientUniverse indexUniverse) :=
  ∀ otherElement : Fin (degree + 1) → indexType, presheaf.obj (op (⨅ position, cover (otherElement position)))

/-- The Čech cosimplicial abelian group of the family `U` with values in a presheaf `P`, as a
functor of `P`. In degree `k` it is the group `CechCochain U P k`, and a map `θ` of the simplex
category acts by `c ↦ (y ↦ c (y ∘ θ))`, restricted to the smaller intersection. -/
@[simps]
noncomputable def cechCosimplicialObject :
    ((Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) ⥤ CosimplicialObject AddCommGrpCat.{max coefficientUniverse indexUniverse} where
  obj presheaf :=
    { obj degree := AddCommGrpCat.of (CechCochain cover presheaf degree.len)
      map {degree otherDegree} simplexMap := AddCommGrpCat.ofHom (AddMonoidHom.pi fun otherElement ↦
        (presheaf.map (homOfLE (iInf_le_iInf_comp cover otherElement simplexMap.toOrderHom)).op).hom.comp
          (Pi.evalAddMonoidHom _ (otherElement ∘ simplexMap.toOrderHom)))
      map_id degree := by
        refine AddCommGrpCat.ext fun cochain ↦ funext fun otherElement ↦ ?_
        exact map_homOfLE_self_apply presheaf _ (cochain otherElement)
      map_comp simplexMap simplexMap' := by
        refine AddCommGrpCat.ext fun cochain ↦ funext fun otherElement ↦ ?_
        exact (map_homOfLE_map_homOfLE_apply presheaf _ _ _).symm }
  map coefficientMap :=
    { app degree := AddCommGrpCat.ofHom (AddMonoidHom.pi fun otherElement ↦
        (coefficientMap.app _).hom.comp (Pi.evalAddMonoidHom _ otherElement))
      naturality degree otherDegree simplexMap := by
        refine AddCommGrpCat.ext fun cochain ↦ funext fun otherElement ↦ ?_
        exact NatTrans.naturality_apply coefficientMap (homOfLE _).op (cochain _) }
  map_id presheaf := rfl
  map_comp coefficientMap secondMap := rfl

/-- The Čech complex `Č(U, P)` of the family `U` with values in a presheaf `P`, as a functor
of `P`: the alternating coface map complex of `cechCosimplicialObject U`. -/
noncomputable def cechComplex :
    ((Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) ⥤ CochainComplex AddCommGrpCat.{max coefficientUniverse indexUniverse} ℕ :=
  cechCosimplicialObject cover ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

instance : (cechComplex cover).Additive where
  map_add := rfl

variable (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse})

/-- The Čech differential is the alternating sum of the restrictions of the faces. -/
lemma cechComplex_d_apply (degree : ℕ) (cochain : CechCochain cover presheaf degree) (otherElement : Fin (degree + 2) → indexType) :
    ((cechComplex cover).obj presheaf).d degree (degree + 1) cochain otherElement =
      ∑ index : Fin (degree + 2), (-1 : ℤ) ^ (index : ℕ) •
        presheaf.map (homOfLE (iInf_le_iInf_comp cover otherElement index.succAbove)).op (cochain (otherElement ∘ index.succAbove)) := by
  have compatibility : ((cechComplex cover).obj presheaf).d degree (degree + 1) =
      ∑ index : Fin (degree + 2), (-1 : ℤ) ^ (index : ℕ) • ((cechCosimplicialObject cover).obj presheaf).δ index :=
    CochainComplex.of_d (fun otherDegree ↦ ((cechCosimplicialObject cover).obj presheaf).obj (SimplexCategory.mk otherDegree))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) degree
  rw [compatibility]
  refine (congrFun (AddCommGrpCat.sum_apply (fun index : Fin (degree + 2) ↦
    (-1 : ℤ) ^ (index : ℕ) • ((cechCosimplicialObject cover).obj presheaf).δ index) Finset.univ cochain) otherElement).trans ?_
  refine (Finset.sum_apply _ _ _).trans ?_
  rfl

@[simp]
lemma cechComplex_map_f_apply {presheaf targetPresheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}} (coefficientMap : presheaf ⟶ targetPresheaf) (degree : ℕ)
    (cochain : CechCochain cover presheaf degree) (otherElement : Fin (degree + 1) → indexType) :
    ((cechComplex cover).map coefficientMap).f degree cochain otherElement = coefficientMap.app _ (cochain otherElement) :=
  rfl

/-- Exactness of the Čech complex in degree `q + 1`, in terms of cochains: every cocycle is a
coboundary. -/
lemma exactAt_cechComplex_iff (cohomologyDegree : ℕ) :
    ((cechComplex cover).obj presheaf).ExactAt (cohomologyDegree + 1) ↔
      ∀ cochain : CechCochain cover presheaf (cohomologyDegree + 1), ((cechComplex cover).obj presheaf).d (cohomologyDegree + 1) (cohomologyDegree + 2) cochain = 0 →
        ∃ primitive : CechCochain cover presheaf cohomologyDegree, ((cechComplex cover).obj presheaf).d cohomologyDegree (cohomologyDegree + 1) primitive = cochain := by
  rw [HomologicalComplex.exactAt_iff' _ cohomologyDegree (cohomologyDegree + 1) (cohomologyDegree + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  rfl

/-- Restrictions of the components of a cochain along two equal tuples agree. -/
lemma map_homOfLE_apply_congr {degree : ℕ} (cochain : CechCochain cover presheaf degree) {otherElement otherElement' : Fin (degree + 1) → indexType}
    (hy : otherElement = otherElement') {openSubset : Opens scheme} (compatibility : openSubset ≤ ⨅ position, cover (otherElement position)) (compatibility' : openSubset ≤ ⨅ position, cover (otherElement' position)) :
    presheaf.map (homOfLE compatibility).op (cochain otherElement) = presheaf.map (homOfLE compatibility').op (cochain otherElement') := by
  subst hy
  rfl

/-- An open subset of `U j` and of `⨅ l, U (z l)` is contained in the intersection indexed by
the tuple `Fin.cons j z`. -/
lemma le_iInf_cons {degree : ℕ} {openSubset : Opens scheme} {selectedIndex : indexType} {thirdElement : Fin (degree + 1) → indexType} (hj : openSubset ≤ cover selectedIndex)
    (hz : openSubset ≤ ⨅ position, cover (thirdElement position)) : openSubset ≤ ⨅ position, cover ((Fin.cons selectedIndex thirdElement : Fin (degree + 2) → indexType) position) := by
  refine le_iInf fun position ↦ ?_
  cases position using Fin.cases with
  | zero => simpa using hj
  | succ position => simpa using hz.trans (iInf_le _ position)

/-- Deleting the entry `i + 1` of `Fin.cons j y` is the same as deleting the entry `i` of `y`. -/
lemma cons_comp_succAbove_succ {degree : ℕ} (selectedIndex : indexType) (otherElement : Fin (degree + 1) → indexType) (index : Fin (degree + 1)) :
    (Fin.cons selectedIndex otherElement : Fin (degree + 2) → indexType) ∘ index.succ.succAbove =
      (Fin.cons selectedIndex (otherElement ∘ index.succAbove) : Fin (degree + 1) → indexType) := by
  funext position
  cases position using Fin.cases <;> simp

/-- The cocycle condition at the tuple `Fin.cons j y`, restricted to an open subset `V` of
`U j ⊓ ⨅ l, U (y l)`: the component `c y` is the alternating sum of the components
`c (Fin.cons j (y ∘ Fin.succAbove i))`. -/
lemma map_cocycle_eq_sum_cons {cohomologyDegree : ℕ} (cochain : CechCochain cover presheaf (cohomologyDegree + 1))
    (hc : ((cechComplex cover).obj presheaf).d (cohomologyDegree + 1) (cohomologyDegree + 2) cochain = 0) (selectedIndex : indexType)
    (otherElement : Fin (cohomologyDegree + 2) → indexType) {openSubset : Opens scheme} (hVj : openSubset ≤ cover selectedIndex) (hV : openSubset ≤ ⨅ position, cover (otherElement position)) :
    presheaf.map (homOfLE hV).op (cochain otherElement) = ∑ index : Fin (cohomologyDegree + 2), (-1 : ℤ) ^ (index : ℕ) •
      presheaf.map (homOfLE (le_iInf_cons cover hVj (hV.trans (iInf_le_iInf_comp cover otherElement index.succAbove)))).op
        (cochain (Fin.cons selectedIndex (otherElement ∘ index.succAbove))) := by
  have hc' : ((cechComplex cover).obj presheaf).d (cohomologyDegree + 1) (cohomologyDegree + 1 + 1) cochain (Fin.cons selectedIndex otherElement) = 0 :=
    congrFun hc _
  have h₀ := congrArg (presheaf.map (homOfLE (le_iInf_cons cover hVj hV)).op)
    ((cechComplex_d_apply cover presheaf (cohomologyDegree + 1) cochain (Fin.cons selectedIndex otherElement)).symm.trans hc')
  simp only [map_sum, map_zsmul, map_zero, map_homOfLE_map_homOfLE_apply] at h₀
  rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul,
    map_homOfLE_apply_congr cover presheaf cochain (by funext position; simp) _ hV] at h₀
  rw [eq_neg_of_add_eq_zero_left h₀, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg,
    map_homOfLE_apply_congr cover presheaf cochain (cons_comp_succAbove_succ selectedIndex otherElement index)]

/-- If for some index `j` restricting to `U j` is bijective on the sections of `P` over all the
finite intersections of the family, then the Čech complex `Č(U, P)` is exact in positive
degrees: inserting the index `j` in the first slot, `(h c) y = c (Fin.cons j y)`, is a
contraction. -/
theorem exactAt_cechComplex_of_bijective {selectedIndex : indexType}
    (hj : ∀ (degree : ℕ) (otherElement : Fin (degree + 1) → indexType),
      Function.Bijective (presheaf.map (homOfLE (inf_le_left : (⨅ position, cover (otherElement position)) ⊓ cover selectedIndex ≤ _)).op))
    (cohomologyDegree : ℕ) : ((cechComplex cover).obj presheaf).ExactAt (cohomologyDegree + 1) := by
  rw [exactAt_cechComplex_iff]
  intro cochain hc
  let isomorphism (thirdElement : Fin (cohomologyDegree + 1) → indexType) := Equiv.ofBijective _ (hj cohomologyDegree thirdElement)
  have he (thirdElement : Fin (cohomologyDegree + 1) → indexType) (element) :
      presheaf.map (homOfLE (inf_le_left : (⨅ position, cover (thirdElement position)) ⊓ cover selectedIndex ≤ _)).op ((isomorphism thirdElement).symm element) = element :=
    (isomorphism thirdElement).apply_symm_apply element
  refine ⟨fun thirdElement ↦ (isomorphism thirdElement).symm (presheaf.map (homOfLE (le_iInf_cons cover inf_le_right inf_le_left)).op
    (cochain (Fin.cons selectedIndex thirdElement))), funext fun (otherElement : Fin (cohomologyDegree + 2) → indexType) ↦ (hj (cohomologyDegree + 1) otherElement).injective ?_⟩
  rw [map_cocycle_eq_sum_cons cover presheaf cochain hc selectedIndex otherElement inf_le_right inf_le_left, cechComplex_d_apply,
    map_sum]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  rw [map_zsmul, map_homOfLE_map_homOfLE_apply, ← map_homOfLE_map_homOfLE_apply presheaf
    (inf_le_inf_right (cover selectedIndex) (iInf_le_iInf_comp cover otherElement index.succAbove)) inf_le_left,
    he (otherElement ∘ index.succAbove), map_homOfLE_map_homOfLE_apply]

/-- If some member `U j` of the family contains all the others, then the Čech complex
`Č(U, P)` is exact in positive degrees. -/
theorem exactAt_cechComplex_of_le {selectedIndex : indexType} (hj : ∀ index, cover index ≤ cover selectedIndex) (cohomologyDegree : ℕ) :
    ((cechComplex cover).obj presheaf).ExactAt (cohomologyDegree + 1) := by
  refine exactAt_cechComplex_of_bijective cover presheaf (selectedIndex := selectedIndex) (fun degree otherElement ↦ ?_) cohomologyDegree
  have heq : (⨅ position, cover (otherElement position)) ⊓ cover selectedIndex = ⨅ position, cover (otherElement position) := inf_eq_left.2 ((iInf_le _ 0).trans (hj _))
  rw [Subsingleton.elim (homOfLE _) (eqToHom heq), eqToHom_op, eqToHom_map]
  exact ConcreteCategory.bijective_of_isIso _

/-- The presheaf of all, not necessarily continuous, sections of a family `S` of abelian groups
indexed by the points of `X`: its sections over `W` are the families `(s x)_{x ∈ W}`. -/
@[simps]
noncomputable def godement (sequence : scheme → Type coefficientUniverse) [∀ element, AddCommGroup (sequence element)] :
    (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse} where
  obj smallerOpen := AddCommGrpCat.of (∀ element : smallerOpen.unop, sequence element)
  map {smallerOpen smallerOpen'} morphism := AddCommGrpCat.ofHom (AddMonoidHom.pi fun element : smallerOpen'.unop ↦
    Pi.evalAddMonoidHom (fun element : smallerOpen.unop ↦ sequence element) ⟨element.1, morphism.unop.le element.2⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Čech complex of the presheaf of all sections of a family of abelian groups is exact in
positive degrees. -/
theorem exactAt_cechComplex_godement (sequence : scheme → Type coefficientUniverse) [∀ element, AddCommGroup (sequence element)] (cohomologyDegree : ℕ) :
    ((cechComplex cover).obj (godement sequence)).ExactAt (cohomologyDegree + 1) := by
  rw [exactAt_cechComplex_iff]
  intro cochain hc
  let selectedIndex (element : scheme) (compatibility : ∃ index, element ∈ cover index) : indexType := compatibility.choose
  have hj (element : scheme) (compatibility : ∃ index, element ∈ cover index) : element ∈ cover (selectedIndex element compatibility) := compatibility.choose_spec
  have hmem {degree : ℕ} (otherElement : Fin (degree + 1) → indexType) (element : ↥(⨅ position, cover (otherElement position))) : element.1 ∈ cover (otherElement 0) :=
    (iInf_le _ 0 : _ ≤ cover (otherElement 0)) element.2
  refine ⟨fun otherElement element ↦ cochain (Fin.cons (selectedIndex element ⟨otherElement 0, hmem otherElement element⟩) otherElement)
    ⟨element, le_iInf_cons cover inf_le_right inf_le_left (Opens.mem_inf.2 ⟨element.2, hj _ _⟩)⟩, ?_⟩
  refine funext fun (otherElement : Fin (cohomologyDegree + 2) → indexType) ↦ funext fun element ↦ ?_
  have compatibility := congrFun (map_cocycle_eq_sum_cons cover _ cochain hc (selectedIndex element.1 ⟨otherElement 0, hmem otherElement element⟩) otherElement
    (openSubset := (⨅ position, cover (otherElement position)) ⊓ cover (selectedIndex element.1 ⟨otherElement 0, hmem otherElement element⟩)) inf_le_right inf_le_left)
    ⟨element.1, Opens.mem_inf.2 ⟨element.2, hj _ _⟩⟩
  refine (congrFun (cechComplex_d_apply cover _ cohomologyDegree _ otherElement) element).trans ?_
  exact (Finset.sum_apply (M := fun element : ↥(⨅ position, cover (otherElement position)) ↦ sequence element) _ _ _).trans
    (compatibility.trans (Finset.sum_apply (M := fun thirdElement : ↥((⨅ position, cover (otherElement position)) ⊓ cover (selectedIndex element.1 ⟨otherElement 0, hmem otherElement element⟩)) ↦
      sequence thirdElement) _ _ _)).symm

/-- The map from an abelian sheaf to the presheaf of all sections of its stalks, sending a
section to its germs. -/
noncomputable def toGodement
    (sheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) :
    sheaf.obj ⟶ godement fun element : scheme ↦
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{coefficientUniverse}) sheaf.obj element : Type coefficientUniverse) where
  app smallerOpen := AddCommGrpCat.ofHom (AddMonoidHom.pi fun element : smallerOpen.unop ↦
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{coefficientUniverse}) sheaf.obj smallerOpen.unop element.1 element.2).hom)
  naturality smallerOpen smallerOpen' morphism := by
    refine AddCommGrpCat.ext fun sectionValue ↦ funext fun element ↦ ?_
    exact TopCat.Presheaf.germ_res_apply sheaf.obj morphism.unop element.1 element.2 sectionValue

instance (sheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) :
    Mono (toGodement sheaf) := by
  have (smallerOpen : (Opens scheme)ᵒᵖ) : Mono ((toGodement sheaf).app smallerOpen) :=
    (AddCommGrpCat.mono_iff_injective _).2 fun sectionValue liftedSection hst ↦
      TopCat.Presheaf.section_ext sheaf smallerOpen.unop sectionValue liftedSection fun element hx ↦ congrFun hst ⟨element, hx⟩
  exact NatTrans.mono_of_mono_app _

/-- The Čech complex of an injective abelian sheaf is exact in positive degrees: the sheaf is a
direct summand of the presheaf of all sections of its stalks, whose Čech complex is exact. -/
theorem exactAt_cechComplex_of_injective
    (injectiveSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) [Injective injectiveSheaf]
    (cohomologyDegree : ℕ) : ((cechComplex cover).obj injectiveSheaf.obj).ExactAt (cohomologyDegree + 1) := by
  have hI : Injective injectiveSheaf.obj := (sheafificationAdjunction _ _).map_injective injectiveSheaf inferInstance
  have hr := Injective.comp_factorThru (𝟙 injectiveSheaf.obj) (toGodement injectiveSheaf)
  set indexType := (cechComplex cover).map (toGodement injectiveSheaf)
  set ρ := (cechComplex cover).map (Injective.factorThru (𝟙 injectiveSheaf.obj) (toGodement injectiveSheaf))
  have hιρ (degree : ℕ) (cochain : ((cechComplex cover).obj injectiveSheaf.obj).X degree) : ρ.f degree (indexType.f degree cochain) = cochain := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hr,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro cochain hc
  obtain ⟨primitive, hb⟩ := (exactAt_cechComplex_iff cover _ cohomologyDegree).1 (exactAt_cechComplex_godement cover _ cohomologyDegree)
    (indexType.f (cohomologyDegree + 1) cochain) (by
      exact (ConcreteCategory.congr_hom (indexType.comm (cohomologyDegree + 1) (cohomologyDegree + 2)) cochain).trans
        ((congrArg (indexType.f (cohomologyDegree + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f cohomologyDegree primitive, (ConcreteCategory.congr_hom (ρ.comm cohomologyDegree (cohomologyDegree + 1)) primitive).trans
    ((congrArg (ρ.f (cohomologyDegree + 1)) hb).trans (hιρ _ cochain))⟩

/-- Restriction of Čech cochains from a family `U` to a pointwise smaller family `U'`. -/
noncomputable def cechCochainRestrict (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse})
    {cover cover' : indexType → Opens scheme} (compatibility : ∀ index, cover' index ≤ cover index) (degree : ℕ) :
    CechCochain cover presheaf degree →+ CechCochain cover' presheaf degree where
  toFun cochain otherElement := presheaf.map (homOfLE (iInf_mono fun position ↦ compatibility (otherElement position))).op (cochain otherElement)
  map_zero' := funext fun _ ↦ map_zero _
  map_add' _ _ := funext fun _ ↦ map_add _ _ _

@[simp]
lemma cechCochainRestrict_apply (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse})
    {cover cover' : indexType → Opens scheme} (compatibility : ∀ index, cover' index ≤ cover index) (degree : ℕ) (cochain : CechCochain cover presheaf degree)
    (otherElement : Fin (degree + 1) → indexType) :
    cechCochainRestrict presheaf compatibility degree cochain otherElement = presheaf.map (homOfLE (iInf_mono fun position ↦ compatibility (otherElement position))).op (cochain otherElement) :=
  rfl

/-- Restriction of Čech cochains to a pointwise smaller family commutes with the differential. -/
lemma cechComplex_d_cechCochainRestrict (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse})
    {cover cover' : indexType → Opens scheme} (compatibility : ∀ index, cover' index ≤ cover index) (degree : ℕ) (cochain : CechCochain cover presheaf degree) :
    ((cechComplex cover').obj presheaf).d degree (degree + 1) (cechCochainRestrict presheaf compatibility degree cochain) =
      cechCochainRestrict presheaf compatibility (degree + 1) (((cechComplex cover).obj presheaf).d degree (degree + 1) cochain) := by
  funext (otherElement : Fin (degree + 1 + 1) → indexType)
  dsimp only [cechCochainRestrict, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  simp only [cechComplex_d_apply, map_sum, map_zsmul,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end TopCat.Presheaf
