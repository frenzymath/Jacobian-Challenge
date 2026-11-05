import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator
import Jacobian.AlgebraicGeometry.ProjectiveSpace.OfSections
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing
import Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import Jacobian.AlgebraicGeometry.Modules.RestrictionIsomorphism

/-!
# The coordinate Koszul sequence on the projective line

Multiplication by a homogeneous coordinate gives a morphism between consecutive
twists, invertible on its standard open. The two coordinates of the projective
line form a short exact Koszul sequence. Exactness follows from local splittings
on the standard affine cover.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

section Koszul

variable {category : Type*} [Category category] [Preadditive category]

/-- **The local splitting of the Koszul complex.** Let `sumObject` be a direct sum of two copies of `factorObject`,
with inclusions `i₀, i₁` and projections `q₀, q₁`, let `a₀, a₁ : sourceObject ⟶ factorObject` and `b₀, b₁ : factorObject ⟶ targetObject`
with `a₀ ≫ b₁ = a₁ ≫ b₀`, and assume that `a₀` and `b₀` are isomorphisms. If `quotientMap : sumObject ⟶ quotientObject` is an
epimorphism killing `a₁ ≫ i₀ - a₀ ≫ i₁`, then the morphism `quotientObject ⟶ targetObject` induced by `(b₀, b₁)` is an
isomorphism. -/
lemma isIso_of_koszul {sourceObject factorObject targetObject sumObject quotientObject : category} (i₀ i₁ : factorObject ⟶ sumObject) (q₀ q₁ : sumObject ⟶ factorObject)
    (hq : q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 sumObject) (a₀ a₁ : sourceObject ⟶ factorObject) (b₀ b₁ : factorObject ⟶ targetObject) [IsIso a₀] [IsIso b₀]
    (hab : a₀ ≫ b₁ = a₁ ≫ b₀) (quotientMap : sumObject ⟶ quotientObject) [Epi quotientMap] (hc : a₁ ≫ i₀ ≫ quotientMap = a₀ ≫ i₁ ≫ quotientMap)
    (sumMap : sumObject ⟶ targetObject) (hv₀ : i₀ ≫ sumMap = b₀) (hv₁ : i₁ ≫ sumMap = b₁) (descendedMap : quotientObject ⟶ targetObject) (hv' : quotientMap ≫ descendedMap = sumMap) :
    IsIso descendedMap := by
  have h₁ : b₁ ≫ inv b₀ ≫ i₀ ≫ quotientMap = i₁ ≫ quotientMap := by
    rw [← cancel_epi a₀, reassoc_of% hab, IsIso.hom_inv_id_assoc, hc]
  refine ⟨inv b₀ ≫ i₀ ≫ quotientMap, ?_, by simp [hv', hv₀]⟩
  rw [← cancel_epi quotientMap, reassoc_of% hv', Category.comp_id]
  conv_lhs => rw [← Category.id_comp sumMap, ← hq]
  simp only [Preadditive.add_comp, Category.assoc, hv₀, hv₁, IsIso.hom_inv_id_assoc, h₁]
  rw [← Category.assoc q₀, ← Category.assoc q₁, ← Preadditive.add_comp, hq, Category.id_comp]

end Koszul


namespace ProjectiveLine

open ProjectiveSpace Scheme.Modules

variable (baseScheme : Scheme.{schemeUniverse}) (twistDegree : ℤ)

/-- Multiplication by the homogeneous coordinate `xᵢ`, `𝒪(twistDegree) ⟶ 𝒪(twistDegree + 1)` on `ℙ¹_S`. -/
abbrev mulX (coordinateIndex : Fin 2) :
    twist (ULift.{schemeUniverse} (Fin 2)) baseScheme twistDegree ⟶ twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1) :=
  twistMulX (ULift.{schemeUniverse} (Fin 2)) baseScheme ⟨coordinateIndex⟩ twistDegree

/-- The first map `(x₁, -x₀) : 𝒪(twistDegree) ⟶ 𝒪(twistDegree + 1) ⊕ 𝒪(twistDegree + 1)` of the Koszul complex of the
homogeneous coordinates `x₀, x₁` of `ℙ¹_S`. -/
def koszulLeft : twist (ULift.{schemeUniverse} (Fin 2)) baseScheme twistDegree ⟶
    twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1) ⊞ twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1) :=
  biprod.lift (mulX baseScheme twistDegree 1) (-mulX baseScheme twistDegree 0)

/-- The second map `(x₀, x₁) : 𝒪(twistDegree + 1) ⊕ 𝒪(twistDegree + 1) ⟶ 𝒪(twistDegree + 2)` of the Koszul complex of the
homogeneous coordinates `x₀, x₁` of `ℙ¹_S`. -/
def koszulRight : twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1) ⊞ twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1) ⟶
    twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1 + 1) :=
  biprod.desc (mulX baseScheme (twistDegree + 1) 0) (mulX baseScheme (twistDegree + 1) 1)

@[reassoc (attr := simp)]
lemma koszulLeft_comp_koszulRight : koszulLeft baseScheme twistDegree ≫ koszulRight baseScheme twistDegree = 0 := by
  simp only [koszulLeft, koszulRight, biprod.lift_desc, Preadditive.neg_comp]
  rw [twistMulX_comp_twistMulX]
  exact add_neg_cancel _

/-- **The Koszul complex** `0 → 𝒪(twistDegree) → 𝒪(twistDegree + 1)² → 𝒪(twistDegree + 2) → 0` of the homogeneous
coordinates on `ℙ¹_S`. -/
@[simps!]
def koszul : ShortComplex (ProjectiveSpace (ULift.{schemeUniverse} (Fin 2)) baseScheme).Modules :=
  ShortComplex.mk _ _ (koszulLeft_comp_koszulRight baseScheme twistDegree)

lemma koszulLeft_comp_neg_snd :
    koszulLeft baseScheme twistDegree ≫ (-biprod.snd) = mulX baseScheme twistDegree 0 := by
  simp [koszulLeft]

lemma ulift_fin_two_cases (pairIndex : ULift.{schemeUniverse} (Fin 2)) : pairIndex = ULift.up 0 ∨ pairIndex = ULift.up 1 := by
  obtain ⟨pairIndex⟩ := pairIndex
  fin_cases pairIndex
  · exact Or.inl rfl
  · exact Or.inr rfl

instance mono_koszulLeft : Mono (koszulLeft baseScheme twistDegree) := by
  refine mono_of_restrict _ (standardOpen _ baseScheme) (iSup_standardOpen _ baseScheme) fun pairIndex ↦ ?_
  set restrictionFunctor := restrictFunctor (standardOpen (ULift.{schemeUniverse} (Fin 2)) baseScheme pairIndex).ι
  rcases ulift_fin_two_cases pairIndex with rfl | rfl
  · exact mono_of_mono_fac (show restrictionFunctor.map (koszulLeft baseScheme twistDegree) ≫ restrictionFunctor.map (-biprod.snd) =
      restrictionFunctor.map (mulX baseScheme twistDegree 0) by rw [← restrictionFunctor.map_comp, koszulLeft_comp_neg_snd])
  · exact mono_of_mono_fac (show restrictionFunctor.map (koszulLeft baseScheme twistDegree) ≫ restrictionFunctor.map biprod.fst =
      restrictionFunctor.map (mulX baseScheme twistDegree 1) by
        rw [← restrictionFunctor.map_comp, koszulLeft, biprod.lift_fst])

/-- The morphism `coker (x₁, -x₀) ⟶ 𝒪(twistDegree + 2)` induced by `(x₀, x₁)`. -/
abbrev koszulCokernelDesc : cokernel (koszulLeft baseScheme twistDegree) ⟶ twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1 + 1) :=
  cokernel.desc _ _ (koszulLeft_comp_koszulRight baseScheme twistDegree)

instance isIso_restrict_koszulCokernelDesc (pairIndex : ULift.{schemeUniverse} (Fin 2)) :
    IsIso ((restrictFunctor (standardOpen _ baseScheme pairIndex).ι).map (koszulCokernelDesc baseScheme twistDegree)) := by
  set restrictionFunctor := restrictFunctor (standardOpen (ULift.{schemeUniverse} (Fin 2)) baseScheme pairIndex).ι
  set twistModule := twist (ULift.{schemeUniverse} (Fin 2)) baseScheme (twistDegree + 1)
  letI : restrictionFunctor.Additive := ⟨by intros; rfl⟩
  have hq : restrictionFunctor.map (biprod.fst : twistModule ⊞ twistModule ⟶ twistModule) ≫ restrictionFunctor.map biprod.inl +
      restrictionFunctor.map (biprod.snd : twistModule ⊞ twistModule ⟶ twistModule) ≫ restrictionFunctor.map biprod.inr = 𝟙 _ := by
    rw [← restrictionFunctor.map_comp, ← restrictionFunctor.map_comp, ← restrictionFunctor.map_add, biprod.total, restrictionFunctor.map_id]
  have hc : (mulX baseScheme twistDegree 1 ≫ biprod.inl - mulX baseScheme twistDegree 0 ≫ biprod.inr) ≫
      cokernel.π (koszulLeft baseScheme twistDegree) = 0 := by
    rw [← cokernel.condition (koszulLeft baseScheme twistDegree), koszulLeft, biprod.lift_eq, Preadditive.neg_comp,
      sub_eq_add_neg]
  rw [Preadditive.sub_comp, sub_eq_zero, Category.assoc, Category.assoc] at hc
  have hc' := congrArg restrictionFunctor.map hc
  simp only [restrictionFunctor.map_comp] at hc'
  have hab := congrArg restrictionFunctor.map (twistMulX_comp_twistMulX (ULift.{schemeUniverse} (Fin 2)) baseScheme ⟨0⟩ ⟨1⟩ twistDegree)
  simp only [restrictionFunctor.map_comp] at hab
  rcases ulift_fin_two_cases pairIndex with rfl | rfl
  · exact isIso_of_koszul (restrictionFunctor.map biprod.inl) (restrictionFunctor.map biprod.inr) (restrictionFunctor.map biprod.fst)
      (restrictionFunctor.map biprod.snd) hq (restrictionFunctor.map (mulX baseScheme twistDegree 0)) (restrictionFunctor.map (mulX baseScheme twistDegree 1))
      (restrictionFunctor.map (mulX baseScheme (twistDegree + 1) 0)) (restrictionFunctor.map (mulX baseScheme (twistDegree + 1) 1)) hab
      (restrictionFunctor.map (cokernel.π _)) hc' (restrictionFunctor.map (koszulRight baseScheme twistDegree))
      (by rw [← restrictionFunctor.map_comp, koszulRight, biprod.inl_desc])
      (by rw [← restrictionFunctor.map_comp, koszulRight, biprod.inr_desc])
      _ (by rw [← restrictionFunctor.map_comp, cokernel.π_desc])
  · exact isIso_of_koszul (restrictionFunctor.map biprod.inr) (restrictionFunctor.map biprod.inl) (restrictionFunctor.map biprod.snd)
      (restrictionFunctor.map biprod.fst) ((add_comm _ _).trans hq) (restrictionFunctor.map (mulX baseScheme twistDegree 1))
      (restrictionFunctor.map (mulX baseScheme twistDegree 0))
      (restrictionFunctor.map (mulX baseScheme (twistDegree + 1) 1)) (restrictionFunctor.map (mulX baseScheme (twistDegree + 1) 0)) hab.symm
      (restrictionFunctor.map (cokernel.π _)) hc'.symm (restrictionFunctor.map (koszulRight baseScheme twistDegree))
      (by rw [← restrictionFunctor.map_comp, koszulRight, biprod.inr_desc])
      (by rw [← restrictionFunctor.map_comp, koszulRight, biprod.inl_desc])
      _ (by rw [← restrictionFunctor.map_comp, cokernel.π_desc])

instance isIso_koszulCokernelDesc : IsIso (koszulCokernelDesc baseScheme twistDegree) := by
  refine Hom.isIso_of_forall_bijective_app _ fun point ↦ ?_
  obtain ⟨pairIndex, membership⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen (ULift.{schemeUniverse} (Fin 2)) baseScheme).ge (Set.mem_univ point))
  exact ⟨standardOpen _ baseScheme pairIndex, membership,
    fun _ inclusion ↦ bijective_app_of_isIso_restrict _ inclusion⟩

/-- **The Koszul complex is exact**: `0 → 𝒪(twistDegree) → 𝒪(twistDegree + 1)² → 𝒪(twistDegree + 2) → 0` is a short exact
sequence on `ℙ¹_S`. -/
theorem koszul_shortExact : (koszul baseScheme twistDegree).ShortExact := by
  have hg : koszulRight baseScheme twistDegree = cokernel.π (koszulLeft baseScheme twistDegree) ≫ koszulCokernelDesc baseScheme twistDegree :=
    (cokernel.π_desc _ _ _).symm
  have : Epi (koszul baseScheme twistDegree).g := by
    change Epi (koszulRight baseScheme twistDegree)
    rw [hg]
    infer_instance
  have hf : Mono (koszul baseScheme twistDegree).f := mono_koszulLeft baseScheme twistDegree
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ ?_) hf this
  exact IsColimit.ofIsoColimit (cokernelIsCokernel (koszulLeft baseScheme twistDegree))
    (Cofork.ext (asIso (koszulCokernelDesc baseScheme twistDegree)) (cokernel.π_desc _ _ _))

end ProjectiveLine

end AlgebraicGeometry
