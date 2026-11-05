import Jacobian.AlgebraicGeometry.ProjectiveSpace.MonomialCech
import Jacobian.AlgebraicGeometry.ProjectiveSpace.TwistSections
import Jacobian.Topology.Sheaves.CechComparison

/-!
# The Čech complex of a twisting sheaf

On the standard cover of a polynomial projective spectrum, each section has a
unique Laurent monomial expansion. The expansions commute with restriction,
identifying the actual Čech complex with the monomial Čech complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits Opposite

private lemma linearCombination_restrictScalars
    {coefficientRing baseRing sectionRing : Type*}
    [Ring coefficientRing] [Ring baseRing] [Ring sectionRing]
    (scalarMap : coefficientRing →+* baseRing) (restriction : baseRing →+* sectionRing)
    (sections : ModuleCat sectionRing) {exponents : Type*}
    (coefficientMap : coefficientRing → sectionRing)
    (scalarMap_eq : ∀ scalar, restriction (scalarMap scalar) = coefficientMap scalar)
    (monomials : exponents → sections) (coefficients : exponents →₀ coefficientRing) :
    Finsupp.linearCombination coefficientRing
        (fun exponent ↦ (show (ModuleCat.restrictScalars scalarMap).obj
          ((ModuleCat.restrictScalars restriction).obj sections) from monomials exponent))
        coefficients =
      coefficients.sum fun exponent scalar ↦ coefficientMap scalar • monomials exponent := by
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun exponent scalar ↦ ?_
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def, scalarMap_eq]

private noncomputable def restrictedPiLinearMap
    {coefficientRing baseRing : Type*} [Ring coefficientRing] [Ring baseRing]
    (scalarMap : coefficientRing →+* baseRing) {indices : Type v}
    (modules : indices → ModuleCat.{max u v} baseRing)
    {source : Type*} [AddCommGroup source] [Module coefficientRing source]
    (components : ∀ index,
      source →ₗ[coefficientRing] (ModuleCat.restrictScalars scalarMap).obj (modules index)) :
    source →ₗ[coefficientRing] (ModuleCat.restrictScalars scalarMap).obj (∏ᶜ modules) := by
  let familyMap : source →ₗ[coefficientRing] (ModuleCat.restrictScalars scalarMap).obj
      (ModuleCat.of baseRing (∀ index, modules index)) :=
    LinearMap.pi components
  let productMap := (ModuleCat.restrictScalars scalarMap).map (ModuleCat.piIsoPi modules).inv
  exact productMap.hom.comp familyMap

private lemma restrictedPiLinearMap_π
    {coefficientRing baseRing : Type*} [Ring coefficientRing] [Ring baseRing]
    (scalarMap : coefficientRing →+* baseRing) {indices : Type v}
    (modules : indices → ModuleCat.{max u v} baseRing)
    {source : Type*} [AddCommGroup source] [Module coefficientRing source]
    (components : ∀ index,
      source →ₗ[coefficientRing] (ModuleCat.restrictScalars scalarMap).obj (modules index))
    (element : source) (index : indices) :
    Pi.π modules index (restrictedPiLinearMap scalarMap modules components element) =
      components index element := by
  change Pi.π modules index
    ((ModuleCat.piIsoPi modules).inv (fun index ↦ components index element)) = _
  exact ModuleCat.piIsoPi_inv_kernel_ι_apply modules index (fun index ↦ components index element)

private lemma bijective_restrictedPiLinearMap
    {coefficientRing baseRing : Type*} [Ring coefficientRing] [Ring baseRing]
    (scalarMap : coefficientRing →+* baseRing) {indices : Type v}
    (modules : indices → ModuleCat.{max u v} baseRing)
    {sourceModules : indices → Type*}
    [∀ index, AddCommGroup (sourceModules index)]
    [∀ index, Module coefficientRing (sourceModules index)]
    (components : ∀ index, sourceModules index →ₗ[coefficientRing]
      (ModuleCat.restrictScalars scalarMap).obj (modules index))
    (bijectiveComponents : ∀ index, Function.Bijective (components index)) :
    Function.Bijective (restrictedPiLinearMap (source := ∀ index, sourceModules index)
      scalarMap modules (fun index ↦ (components index).comp (LinearMap.proj index))) := by
  let familyEquiv := LinearEquiv.piCongrRight fun index ↦
    LinearEquiv.ofBijective (components index) (bijectiveComponents index)
  let productMap := (ModuleCat.restrictScalars scalarMap).map (ModuleCat.piIsoPi modules).inv
  have productBijective := ConcreteCategory.bijective_of_isIso productMap
  exact productBijective.comp familyEquiv.bijective

private lemma cechDifferential_eq_of_projections
    {space : TopCat.{max u v}} {indices : Type v}
    (cover : indices → TopologicalSpace.Opens space) {baseRing : Type*} [Ring baseRing]
    (presheaf : (TopologicalSpace.Opens space)ᵒᵖ ⥤ ModuleCat.{max u v} baseRing)
    (degree : ℕ) (current : ((cechComplexFunctor cover).obj presheaf).X degree)
    (next : ((cechComplexFunctor cover).obj presheaf).X (degree + 1))
    (components : ∀ tuple : Fin (degree + 2) → indices,
      (∑ index : Fin (degree + 2), (-1 : ℤ) ^ (index : ℕ) •
        presheaf.map (Pi.lift fun position ↦
          Pi.π (fun position ↦ cover (tuple position)) (index.succAbove position)).op
          (TopCat.Presheaf.cechComplexFunctorπ cover presheaf degree
            (tuple ∘ index.succAbove) current)) =
        TopCat.Presheaf.cechComplexFunctorπ cover presheaf (degree + 1) tuple next) :
    ((cechComplexFunctor cover).obj presheaf).d degree (degree + 1) current = next := by
  refine TopCat.Presheaf.cechComplexFunctor_ext cover presheaf fun tuple ↦ ?_
  exact (TopCat.Presheaf.cechComplexFunctorπ_d_apply cover presheaf degree tuple current).trans
    (components tuple)

namespace AlgebraicGeometry.Proj

local instance (R : Type (max u v)) [Ring R] :
    HasProducts.{v} (ModuleCat.{max u v} R) :=
  fun _ ↦ ModuleCat.hasLimitsOfShape

open Scheme.Modules Opposite MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type v} [Fintype n]

variable (k : Type (max u v)) [CommRing k] (m : ℤ)

/-- The `k`-linear map sending a finitely supported family of coefficients `(cₑ)` to the section
`∑ cₑ xᵉ` of `𝒪(m)` over `⋂_{i ∈ s} D₊(xᵢ) ⊆ Proj k[Xᵢ]`. -/
noncomputable def twistMonomialLinearMap (s : Set n) :
    (laurentExponents s m →₀ k) →ₗ[k] (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom).obj
        ((twist (homogeneousSubmodule n k) m).presheafModuleCat.obj
          (op (monomialOpen k s))) :=
  Finsupp.linearCombination k fun e ↦ twistMonomial k s e

variable {k m}

lemma twistMonomialLinearMap_apply (s : Set n) (coefficients : laurentExponents s m →₀ k) :
    twistMonomialLinearMap k m s coefficients = twistMonomialSum k s m coefficients := by
  let projectiveScheme := projectiveSpaceOverAffine.{u, v} n k
  let openSubset := monomialOpen.{u, v} (n := n) k s
  let scalarMap := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (projectiveSpaceOverAffineToSpec.{u, v} n k).appTop).hom
  let restriction := (projectiveScheme.ringCatSheaf.obj.map
    (homOfLE (le_top : openSubset ≤ ⊤)).op).hom
  let coefficientMap := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (projectiveSpaceOverAffineToSpec.{u, v} n k).appTop ≫
      projectiveScheme.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op).hom
  have scalarMap_eq (scalar : k) : restriction (scalarMap scalar) = coefficientMap scalar := rfl
  let sections := (twist (homogeneousSubmodule n k) m).val.obj (op openSubset)
  let monomials := twistMonomial.{u, v} (n := n) k s (m := m)
  have evaluation := linearCombination_restrictScalars (coefficientRing := k)
    (baseRing := projectiveScheme.ringCatSheaf.obj.obj (op ⊤))
    (sectionRing := projectiveScheme.ringCatSheaf.obj.obj (op openSubset))
    scalarMap restriction sections
    coefficientMap scalarMap_eq monomials coefficients
  exact evaluation

lemma bijective_twistMonomialLinearMap {s : Set n} (hs : s.Nonempty) :
    Function.Bijective (twistMonomialLinearMap.{u, v} (n := n) k m s) := by
  have sumBijective := bijective_sum_twistMonomial.{u, v} (n := n) k hs m
  constructor
  · intro first second equality
    apply sumBijective.1
    exact (twistMonomialLinearMap_apply.{u, v} (n := n) (k := k) (m := m) s first).symm.trans
      (equality.trans (twistMonomialLinearMap_apply.{u, v}
        (n := n) (k := k) (m := m) s second))
  · intro sectionValue
    obtain ⟨coefficients, equality⟩ := sumBijective.2 sectionValue
    exact ⟨coefficients, (twistMonomialLinearMap_apply.{u, v}
      (n := n) (k := k) (m := m) s coefficients).trans equality⟩

/-- The sections `∑ cₑ xᵉ` are compatible with restriction. -/
lemma twistMonomialLinearMap_mapDomain {s t : Set n} (hts : t ⊆ s)
    (c : laurentExponents t m →₀ k) :
    twistMonomialLinearMap k m s (c.mapDomain (Set.inclusion (laurentExponents_mono hts m))) =
      (twist (homogeneousSubmodule n k) m).presheafModuleCat.map (homOfLE (basicOpen_monomialToNat_indicator_mono (R := k) hts)).op
        (twistMonomialLinearMap k m t c) := by
  rw [twistMonomialLinearMap, twistMonomialLinearMap, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun e _ ↦ ?_
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
  erw [(((twist (homogeneousSubmodule n k) m).presheafModuleCat.map _).hom).map_smul]
  congr 1
  exact (twist_presheaf_map_twistMonomial hts e).symm

variable (k m) in
private noncomputable def monomialCechComponent (p : ℕ) (indices : Fin (p + 1) → n) :
    Finsupp.supported k k (laurentExponents (Set.range indices) m) →ₗ[k]
      (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom).obj
        ((twist (homogeneousSubmodule n k) m).presheafModuleCat.obj
          (op (∏ᶜ fun index ↦ standardOpen n k (indices index)))) := by
  let coefficientEquivalence := (Finsupp.supportedEquivFinsupp (M := k) (R := k)
    (laurentExponents (Set.range indices) m)).toLinearMap
  let sectionExpansion := twistMonomialLinearMap.{u, v} (n := n) k m (Set.range indices)
  let sections := sectionExpansion.comp coefficientEquivalence
  let scalarRestriction := ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom
  let presheaf := (twist (homogeneousSubmodule n k) m).presheafModuleCat
  let sectionRestriction := (scalarRestriction.map
    (presheaf.map (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ indices).trans
      (monomialOpen_range k indices).ge)).op)).hom
  exact sectionRestriction.comp sections

private lemma monomialCechComponent_apply (p : ℕ) (indices : Fin (p + 1) → n)
    (coefficients : Finsupp.supported k k (laurentExponents (Set.range indices) m)) :
    monomialCechComponent.{u, v} (n := n) k m p indices coefficients =
      (twist (homogeneousSubmodule n k) m).presheafModuleCat.map
        (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ indices).trans
          (monomialOpen_range k indices).ge)).op
        (twistMonomialLinearMap.{u, v} (n := n) k m (Set.range indices)
          (Finsupp.supportedEquivFinsupp (laurentExponents (Set.range indices) m)
            coefficients)) :=
  rfl

private lemma bijective_monomialCechComponent (p : ℕ) (indices : Fin (p + 1) → n) :
    Function.Bijective (monomialCechComponent.{u, v} (n := n) k m p indices) := by
  let coefficientEquivalence := Finsupp.supportedEquivFinsupp (M := k) (R := k)
    (laurentExponents (Set.range indices) m)
  have expansionBijective := bijective_twistMonomialLinearMap.{u, v}
    (n := n) (k := k) (m := m) (Set.range_nonempty indices)
  let scalarRestriction := ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom
  let presheaf := (twist (homogeneousSubmodule n k) m).presheafModuleCat
  have smaller : (∏ᶜ fun index ↦ standardOpen n k (indices index)) ≤
      monomialOpen k (Set.range indices) :=
    (TopCat.Presheaf.piObj_le_iInf _ indices).trans (monomialOpen_range k indices).ge
  have larger : monomialOpen k (Set.range indices) ≤
      ∏ᶜ fun index ↦ standardOpen n k (indices index) :=
    (monomialOpen_range k indices).le.trans (TopCat.Presheaf.iInf_le_piObj _ indices)
  let inclusion := homOfLE smaller
  haveI : IsIso inclusion := homOfLE_isIso_of_eq smaller (le_antisymm smaller larger)
  let sectionRestriction := scalarRestriction.map (presheaf.map inclusion.op)
  have restrictionBijective := ConcreteCategory.bijective_of_isIso sectionRestriction
  have componentBijective := restrictionBijective.comp
    (expansionBijective.comp coefficientEquivalence.bijective)
  exact componentBijective

variable (k m) in
/-- The degree-`p` comparison map from monomial cochains to sections of `𝒪(m)`
on the standard intersections, linear over `k`. -/
noncomputable def monomialCechToCech (p : ℕ) :
    ProjectiveSpace.MonomialCechCochain n k m p →ₗ[k] (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom).obj
        (((cechComplexFunctor (standardOpen n k)).obj
          (twist (homogeneousSubmodule n k) m).presheafModuleCat).X p) := by
  let scalarMap :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom
  let presheaf := (twist (homogeneousSubmodule n k) m).presheafModuleCat
  let modules := fun indices : Fin (p + 1) → n ↦
    presheaf.obj (op (∏ᶜ fun index ↦ standardOpen n k (indices index)))
  let components := fun indices : Fin (p + 1) → n ↦
    (monomialCechComponent.{u, v} (n := n) k m p indices).comp
      (LinearMap.proj indices : ProjectiveSpace.MonomialCechCochain n k m p →ₗ[k]
        Finsupp.supported k k (laurentExponents (Set.range indices) m))
  let assemble := restrictedPiLinearMap.{u, v} (coefficientRing := k)
    (source := ProjectiveSpace.MonomialCechCochain n k m p) scalarMap modules
  let comparison := assemble components
  exact comparison

variable (k m) in
/-- The family of sections obtained by expanding each monomial cochain. -/
noncomputable def monomialCechToCechFun (p : ℕ)
    (coefficients : ProjectiveSpace.MonomialCechCochain n k m p) :
    ((cechComplexFunctor (standardOpen n k)).obj
      (twist (homogeneousSubmodule n k) m).presheafModuleCat).X p := by
  let comparison := monomialCechToCech.{u, v} (n := n) k m p
  exact comparison coefficients

lemma cechComplexFunctorπ_monomialCechToCechFun (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) (σ : Fin (p + 1) → n) :
    TopCat.Presheaf.cechComplexFunctorπ (standardOpen n k)
      (twist (homogeneousSubmodule n k) m).presheafModuleCat p σ
        (monomialCechToCechFun.{u, v} (n := n) k m p c) =
      (twist (homogeneousSubmodule n k) m).presheafModuleCat.map
        (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
          (monomialOpen_range k σ).ge)).op
        (twistMonomialLinearMap k m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ))) := by
  let scalarMap :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom
  let presheaf := (twist (homogeneousSubmodule n k) m).presheafModuleCat
  let modules := fun indices : Fin (p + 1) → n ↦
    presheaf.obj (op (∏ᶜ fun index ↦ standardOpen n k (indices index)))
  let components := fun indices : Fin (p + 1) → n ↦
    (monomialCechComponent.{u, v} (n := n) k m p indices).comp
      (LinearMap.proj indices : ProjectiveSpace.MonomialCechCochain n k m p →ₗ[k]
        Finsupp.supported k k (laurentExponents (Set.range indices) m))
  have projection := restrictedPiLinearMap_π.{u, v}
    (source := ProjectiveSpace.MonomialCechCochain n k m p)
    scalarMap modules components c σ
  have componentValue := monomialCechComponent_apply.{u, v}
    (n := n) (k := k) (m := m) p σ (c σ)
  exact projection.trans componentValue

@[simp]
lemma monomialCechToCech_apply (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) :
    monomialCechToCech.{u, v} (n := n) k m p c =
      monomialCechToCechFun.{u, v} (n := n) k m p c :=
  rfl

omit [Fintype n] in
private lemma supportedEquivFinsupp_apply (s : Set (n → ℤ)) (x : Finsupp.supported k k s) (e : s) :
    Finsupp.supportedEquivFinsupp s x e = (x : (n → ℤ) →₀ k) e := by
  simp

/-- The differential of the monomial Čech complex, on the coefficients of a component. -/
lemma supportedEquivFinsupp_monomialCechComplex_d (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) (τ : Fin (p + 2) → n) :
    Finsupp.supportedEquivFinsupp (laurentExponents (Set.range τ) m)
        (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c τ) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Finsupp.supportedEquivFinsupp (laurentExponents (Set.range (τ ∘ i.succAbove)) m)
          (c (τ ∘ i.succAbove))).mapDomain
          (Set.inclusion (laurentExponents_mono (Set.range_comp_subset_range _ _) m)) := by
  ext e
  rw [supportedEquivFinsupp_apply, Finsupp.finsetSum_apply]
  have h := ProjectiveSpace.monomialCechComplex_d_apply p c τ e.1
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Finsupp.smul_apply]
  congr 1
  by_cases he : e.1 ∈ laurentExponents (Set.range (τ ∘ i.succAbove)) m
  · rw [show e = Set.inclusion (laurentExponents_mono (Set.range_comp_subset_range _ _) m)
        ⟨e.1, he⟩ from rfl, Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _),
      supportedEquivFinsupp_apply]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨e', he'⟩ ↦ he (he' ▸ e'.2)]
    exact ProjectiveSpace.MonomialCechCochain.coeff_eq_zero_of_notMem c _ he

set_option maxHeartbeats 400000 in
/-- The comparison maps commute with the differentials. -/
lemma monomialCechToCechFun_d (p : ℕ) (c : ProjectiveSpace.MonomialCechCochain n k m p) :
    ((cechComplexFunctor (standardOpen n k)).obj
      (twist (homogeneousSubmodule n k) m).presheafModuleCat).d p (p + 1)
        (monomialCechToCechFun.{u, v} (n := n) k m p c) =
      monomialCechToCechFun.{u, v} (n := n) k m (p + 1)
        (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c) := by
  refine cechDifferential_eq_of_projections.{u, v} (standardOpen n k)
    (twist (homogeneousSubmodule n k) m).presheafModuleCat p
    (monomialCechToCechFun.{u, v} (n := n) k m p c)
    (monomialCechToCechFun.{u, v} (n := n) k m (p + 1)
      (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c)) ?_
  intro τ
  simp only [cechComplexFunctorπ_monomialCechToCechFun,
    supportedEquivFinsupp_monomialCechComplex_d, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : (∏ᶜ fun l ↦ standardOpen n k (τ l)) ≤
      monomialOpen k (Set.range (τ ∘ i.succAbove)) :=
    (TopCat.Presheaf.piObj_le_iInf _ τ).trans ((monomialOpen_range k τ).ge.trans
      (basicOpen_monomialToNat_indicator_mono (R := k) (Set.range_comp_subset_range _ _)))
  rw [map_zsmul, map_zsmul]
  congr 1
  rw [twistMonomialLinearMap_mapDomain, TopCat.Presheaf.map_map_apply _ _ _ (homOfLE h).op]
  · exact TopCat.Presheaf.map_map_apply _ _ _ (homOfLE h).op _
  · exact Set.range_comp_subset_range _ _

include n k m in
set_option maxHeartbeats 800000 in
/-- The comparison maps are bijective. -/
lemma bijective_monomialCechToCech (p : ℕ) :
    Function.Bijective (monomialCechToCech.{u, v} (n := n) k m p) := by
  let scalarMap :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (projectiveSpaceOverAffineToSpec n k).appTop).hom
  let presheaf := (twist (homogeneousSubmodule n k) m).presheafModuleCat
  let modules := fun indices : Fin (p + 1) → n ↦
    presheaf.obj (op (∏ᶜ fun index ↦ standardOpen n k (indices index)))
  let components := monomialCechComponent.{u, v} (n := n) k m p
  have componentsBijective := bijective_monomialCechComponent.{u, v}
    (n := n) (k := k) (m := m) p
  have comparisonBijective := bijective_restrictedPiLinearMap.{u, v}
    (sourceModules := fun indices : Fin (p + 1) → n ↦
      Finsupp.supported k k (laurentExponents (Set.range indices) m))
    scalarMap modules components componentsBijective
  exact comparisonBijective

variable (n k m) in
/-- The Čech complex of a polynomial twisting sheaf is the monomial Čech complex. -/
noncomputable def cechComplexTwistIso :
    ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          (projectiveSpaceOverAffineToSpec n k).appTop).hom).mapHomologicalComplex _).obj
      ((cechComplexFunctor (standardOpen n k)).obj
        (twist (homogeneousSubmodule n k) m).presheafModuleCat) ≅
      ProjectiveSpace.monomialCechComplex n k m :=
  (HomologicalComplex.Hom.isoOfComponents (fun p ↦
    (LinearEquiv.ofBijective (monomialCechToCech.{u, v} (n := n) k m p)
      (bijective_monomialCechToCech.{u, v} (n := n) (k := k) (m := m) p)).toModuleIso) (by
    rintro p _ rfl
    ext c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.mapHomologicalComplex_obj_d,
      LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, monomialCechToCech_apply]
    exact monomialCechToCechFun_d.{u, v} (n := n) (k := k) (m := m) p c)).symm


/-- The monomial comparison identifies homology after restriction to the
coefficient ring. -/
opaque cechComplexTwistHomologyIso
    (coordinates : Type v) [Fintype coordinates]
    (coefficients : Type (max u v)) [CommRing coefficients]
    (twistDegree : ℤ) (degree : ℕ) :
    (((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of coefficients)).inv ≫
          (projectiveSpaceOverAffineToSpec coordinates coefficients).appTop).hom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
      ((cechComplexFunctor (standardOpen coordinates coefficients)).obj
        (twist (homogeneousSubmodule coordinates coefficients) twistDegree).presheafModuleCat)).homology
        degree ≅
      (ProjectiveSpace.monomialCechComplex coordinates coefficients twistDegree).homology degree :=
  (HomologicalComplex.homologyFunctor (ModuleCat coefficients) (ComplexShape.up ℕ) degree).mapIso
    (cechComplexTwistIso.{u, v} (n := coordinates) (k := coefficients) (m := twistDegree))

end AlgebraicGeometry.Proj
