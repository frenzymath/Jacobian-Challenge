import Jacobian.AlgebraicGeometry.ProjectiveLine.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Koszul
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Polynomial

/-!
# The coordinate Koszul sequence on polynomial projective space of dimension one

The two variables of `k[X₀, X₁]` give a short exact sequence
`0 → 𝒪(a) → 𝒪(a + 1)² → 𝒪(a + 2) → 0` on its projective spectrum.
On each standard open one coordinate is invertible, so the sequence splits.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

private lemma mono_map_koszulLeft
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [Category targetCategory]
    [Preadditive sourceCategory] [Preadditive targetCategory]
    {sourceModule middleModule : sourceCategory}
    [HasBinaryBiproduct middleModule middleModule]
    (restrictionFunctor : sourceCategory ⥤ targetCategory)
    (coordinateMap : Fin 2 → (sourceModule ⟶ middleModule))
    (coordinate : Fin 2)
    [coordinateIso : IsIso (restrictionFunctor.map (coordinateMap coordinate))] :
    Mono (restrictionFunctor.map (biprod.lift (coordinateMap 1) (-coordinateMap 0))) := by
  fin_cases coordinate
  · let : IsIso (restrictionFunctor.map (coordinateMap 0)) := coordinateIso
    let : Mono (restrictionFunctor.map (coordinateMap 0)) := inferInstance
    exact mono_of_mono_fac
      (show restrictionFunctor.map (biprod.lift (coordinateMap 1) (-coordinateMap 0)) ≫
          restrictionFunctor.map (-biprod.snd) =
            restrictionFunctor.map (coordinateMap 0) by
        rw [← restrictionFunctor.map_comp]
        simp)
  · let : IsIso (restrictionFunctor.map (coordinateMap 1)) := coordinateIso
    let : Mono (restrictionFunctor.map (coordinateMap 1)) := inferInstance
    exact mono_of_mono_fac
      (show restrictionFunctor.map (biprod.lift (coordinateMap 1) (-coordinateMap 0)) ≫
          restrictionFunctor.map biprod.fst =
            restrictionFunctor.map (coordinateMap 1) by
        rw [← restrictionFunctor.map_comp, biprod.lift_fst])

private lemma isIso_map_koszulDesc
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [Category targetCategory]
    [Preadditive sourceCategory] [Preadditive targetCategory]
    {sourceModule middleModule targetModule quotientModule : sourceCategory}
    [HasBinaryBiproduct middleModule middleModule]
    (restrictionFunctor : sourceCategory ⥤ targetCategory) [restrictionFunctor.Additive]
    (coordinateMap : Fin 2 → (sourceModule ⟶ middleModule))
    (targetCoordinateMap : Fin 2 → (middleModule ⟶ targetModule))
    (quotientMap : middleModule ⊞ middleModule ⟶ quotientModule)
    [Epi (restrictionFunctor.map quotientMap)]
    (descendedMap : quotientModule ⟶ targetModule)
    (coordinateCommutes : coordinateMap 0 ≫ targetCoordinateMap 1 =
      coordinateMap 1 ≫ targetCoordinateMap 0)
    (quotientZero : biprod.lift (coordinateMap 1) (-coordinateMap 0) ≫ quotientMap = 0)
    (factorization : quotientMap ≫ descendedMap =
      biprod.desc (targetCoordinateMap 0) (targetCoordinateMap 1))
    (coordinate : Fin 2)
    [coordinateIso : IsIso (restrictionFunctor.map (coordinateMap coordinate))]
    [targetCoordinateIso : IsIso (restrictionFunctor.map (targetCoordinateMap coordinate))] :
    IsIso (restrictionFunctor.map descendedMap) := by
  have projections :
      restrictionFunctor.map (biprod.fst : middleModule ⊞ middleModule ⟶ middleModule) ≫
          restrictionFunctor.map biprod.inl +
        restrictionFunctor.map (biprod.snd : middleModule ⊞ middleModule ⟶ middleModule) ≫
          restrictionFunctor.map biprod.inr = 𝟙 _ := by
    rw [← restrictionFunctor.map_comp, ← restrictionFunctor.map_comp,
      ← restrictionFunctor.map_add, biprod.total, restrictionFunctor.map_id]
  have quotientRelation :
      (coordinateMap 1 ≫ biprod.inl - coordinateMap 0 ≫ biprod.inr) ≫ quotientMap = 0 := by
    simpa only [biprod.lift_eq, Preadditive.neg_comp, sub_eq_add_neg] using quotientZero
  rw [Preadditive.sub_comp, sub_eq_zero, Category.assoc, Category.assoc]
    at quotientRelation
  have restrictedRelation := congrArg restrictionFunctor.map quotientRelation
  simp only [restrictionFunctor.map_comp] at restrictedRelation
  have commutes := congrArg restrictionFunctor.map coordinateCommutes
  simp only [restrictionFunctor.map_comp] at commutes
  have restrictedFactorization :
      restrictionFunctor.map quotientMap ≫ restrictionFunctor.map descendedMap =
        restrictionFunctor.map (biprod.desc (targetCoordinateMap 0) (targetCoordinateMap 1)) := by
    rw [← restrictionFunctor.map_comp, factorization]
  fin_cases coordinate
  · let : IsIso (restrictionFunctor.map (coordinateMap 0)) := coordinateIso
    let : IsIso (restrictionFunctor.map (targetCoordinateMap 0)) := targetCoordinateIso
    exact isIso_of_koszul
      (restrictionFunctor.map biprod.inl) (restrictionFunctor.map biprod.inr)
      (restrictionFunctor.map biprod.fst) (restrictionFunctor.map biprod.snd)
      projections (restrictionFunctor.map (coordinateMap 0))
      (restrictionFunctor.map (coordinateMap 1))
      (restrictionFunctor.map (targetCoordinateMap 0))
      (restrictionFunctor.map (targetCoordinateMap 1)) commutes
      (restrictionFunctor.map quotientMap) restrictedRelation
      (restrictionFunctor.map (biprod.desc (targetCoordinateMap 0) (targetCoordinateMap 1)))
      (by rw [← restrictionFunctor.map_comp, biprod.inl_desc])
      (by rw [← restrictionFunctor.map_comp, biprod.inr_desc])
      (restrictionFunctor.map descendedMap) restrictedFactorization
  · let : IsIso (restrictionFunctor.map (coordinateMap 1)) := coordinateIso
    let : IsIso (restrictionFunctor.map (targetCoordinateMap 1)) := targetCoordinateIso
    exact isIso_of_koszul
      (restrictionFunctor.map biprod.inr) (restrictionFunctor.map biprod.inl)
      (restrictionFunctor.map biprod.snd) (restrictionFunctor.map biprod.fst)
      ((add_comm _ _).trans projections)
      (restrictionFunctor.map (coordinateMap 1))
      (restrictionFunctor.map (coordinateMap 0))
      (restrictionFunctor.map (targetCoordinateMap 1))
      (restrictionFunctor.map (targetCoordinateMap 0)) commutes.symm
      (restrictionFunctor.map quotientMap) restrictedRelation.symm
      (restrictionFunctor.map (biprod.desc (targetCoordinateMap 0) (targetCoordinateMap 1)))
      (by rw [← restrictionFunctor.map_comp, biprod.inr_desc])
      (by rw [← restrictionFunctor.map_comp, biprod.inl_desc])
      (restrictionFunctor.map descendedMap) restrictedFactorization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type u) [Field baseField] (twistDegree : ℤ)

local notation "lineGrading" => MvPolynomial.homogeneousSubmodule (Fin 2) baseField

/-- Multiplication by one of the two homogeneous coordinates. -/
abbrev mulX (coordinate : Fin 2) :
    twist lineGrading twistDegree ⟶ twist lineGrading (twistDegree + 1) :=
  twistMul twistDegree (MvPolynomial.isHomogeneous_X baseField coordinate)

/-- The first Koszul differential, with components `(X₁, -X₀)`. -/
def koszulLeft : twist lineGrading twistDegree ⟶
    twist lineGrading (twistDegree + 1) ⊞ twist lineGrading (twistDegree + 1) :=
  biprod.lift (mulX baseField twistDegree 1) (-mulX baseField twistDegree 0)

/-- The second Koszul differential, with components `(X₀, X₁)`. -/
def koszulRight :
    twist lineGrading (twistDegree + 1) ⊞ twist lineGrading (twistDegree + 1) ⟶
      twist lineGrading (twistDegree + 1 + 1) :=
  biprod.desc (mulX baseField (twistDegree + 1) 0)
    (mulX baseField (twistDegree + 1) 1)

/-- The coordinate multiplications commute, so the two differentials compose to zero. -/
@[reassoc (attr := simp)]
lemma koszulLeft_comp_koszulRight :
    koszulLeft baseField twistDegree ≫ koszulRight baseField twistDegree = 0 := by
  simp only [koszulLeft, koszulRight, biprod.lift_desc, Preadditive.neg_comp]
  have commutes :
      mulX baseField twistDegree 1 ≫ mulX baseField (twistDegree + 1) 0 =
        mulX baseField twistDegree 0 ≫ mulX baseField (twistDegree + 1) 1 :=
    twistMul_comp_twistMul twistDegree
      (MvPolynomial.isHomogeneous_X baseField (1 : Fin 2))
      (MvPolynomial.isHomogeneous_X baseField (0 : Fin 2))
  rw [commutes, add_neg_cancel]

/-- The coordinate Koszul complex of the twisting sheaves on `Proj k[X₀, X₁]`. -/
@[simps!]
def koszul : ShortComplex (Proj lineGrading).Modules :=
  ShortComplex.mk _ _ (koszulLeft_comp_koszulRight baseField twistDegree)

/-- The negative second projection recovers multiplication by the first coordinate. -/
lemma koszulLeft_comp_neg_snd :
    koszulLeft baseField twistDegree ≫ (-biprod.snd) = mulX baseField twistDegree 0 := by
  simp [koszulLeft]

/-- The first differential is injective on each of the two standard opens. -/
instance mono_koszulLeft : Mono (koszulLeft baseField twistDegree) := by
  refine mono_of_restrict _ (ProjectiveLine.chart baseField)
    (ProjectiveLine.iSup_chart_eq_top baseField) fun coordinate ↦ ?_
  let restrictionFunctor := restrictFunctor (ProjectiveLine.chart baseField coordinate).ι
  let : IsIso (restrictionFunctor.map (mulX baseField twistDegree coordinate)) :=
    isIso_restrict_twistMul twistDegree
      (MvPolynomial.isHomogeneous_X baseField coordinate)
  exact mono_map_koszulLeft restrictionFunctor (mulX baseField twistDegree) coordinate

/-- The second differential induces a map from the cokernel of the first. -/
abbrev koszulCokernelDesc :
    cokernel (koszulLeft baseField twistDegree) ⟶
      twist lineGrading (twistDegree + 1 + 1) :=
  cokernel.desc _ _ (koszulLeft_comp_koszulRight baseField twistDegree)

/-- The coordinate Koszul cokernel is the final twist on either standard open. -/
instance isIso_restrict_koszulCokernelDesc (coordinate : Fin 2) :
    IsIso ((restrictFunctor (ProjectiveLine.chart baseField coordinate).ι).map
      (koszulCokernelDesc baseField twistDegree)) := by
  let restrictionFunctor := restrictFunctor (ProjectiveLine.chart baseField coordinate).ι
  let : restrictionFunctor.Additive := ⟨by intros; rfl⟩
  let : IsIso (restrictionFunctor.map (mulX baseField twistDegree coordinate)) :=
    isIso_restrict_twistMul twistDegree
      (MvPolynomial.isHomogeneous_X baseField coordinate)
  let : IsIso (restrictionFunctor.map (mulX baseField (twistDegree + 1) coordinate)) :=
    isIso_restrict_twistMul (twistDegree + 1)
      (MvPolynomial.isHomogeneous_X baseField coordinate)
  exact isIso_map_koszulDesc restrictionFunctor
    (mulX baseField twistDegree) (mulX baseField (twistDegree + 1))
    (cokernel.π (koszulLeft baseField twistDegree)) (koszulCokernelDesc baseField twistDegree)
    (twistMul_comp_twistMul twistDegree
      (MvPolynomial.isHomogeneous_X baseField (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X baseField (1 : Fin 2)))
    (cokernel.condition (koszulLeft baseField twistDegree))
    (cokernel.π_desc _ _ _) coordinate

/-- The two local splittings identify the cokernel globally. -/
instance isIso_koszulCokernelDesc : IsIso (koszulCokernelDesc baseField twistDegree) := by
  refine Hom.isIso_of_forall_bijective_app _ fun point ↦ ?_
  obtain ⟨coordinate, membership⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((ProjectiveLine.iSup_chart_eq_top baseField).ge (Set.mem_univ point))
  let : IsIso ((restrictFunctor (ProjectiveLine.chart baseField coordinate).ι).map
      (koszulCokernelDesc baseField twistDegree)) :=
    isIso_restrict_koszulCokernelDesc baseField twistDegree coordinate
  exact ⟨ProjectiveLine.chart baseField coordinate, membership,
    fun _ inclusion ↦
      bijective_app_of_isIso_restrict (koszulCokernelDesc baseField twistDegree) inclusion⟩

/-- The coordinate Koszul sequence of twists on `Proj k[X₀, X₁]` is short exact. -/
theorem koszul_shortExact : (koszul baseField twistDegree).ShortExact := by
  have factorization : koszulRight baseField twistDegree =
      cokernel.π (koszulLeft baseField twistDegree) ≫
        koszulCokernelDesc baseField twistDegree :=
    (cokernel.π_desc _ _ _).symm
  have : Epi (koszul baseField twistDegree).g := by
    change Epi (koszulRight baseField twistDegree)
    rw [factorization]
    infer_instance
  have injective : Mono (koszul baseField twistDegree).f :=
    mono_koszulLeft baseField twistDegree
  refine ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ ?_) injective this
  exact IsColimit.ofIsoColimit (cokernelIsCokernel (koszulLeft baseField twistDegree))
    (Cofork.ext (asIso (koszulCokernelDesc baseField twistDegree))
      (cokernel.π_desc _ _ _))

end AlgebraicGeometry.Proj
