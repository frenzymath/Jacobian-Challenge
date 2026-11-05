import Jacobian.Algebra.Homology.ShortComplex.Ab
import Jacobian.AlgebraicGeometry.Cohomology.AcyclicResolution
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Affine
import Jacobian.CategoryTheory.Abelian.Injective.Cycles

/-!
# Sheaf cohomology and derived global sections

The native module-sheaf cohomology agrees with the right derived functors
of global sections. Injective module sheaves are flasque, so their global
sections compute the same cohomology as the underlying abelian sheaves.
The comparison is natural in the coefficient sheaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Global sections of a module sheaf, regarded as an abelian group. -/
def globalSectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} :=
  toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)

instance : (globalSectionsFunctor X).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (globalSectionsFunctor X) := by
  have : PreservesFiniteLimits (toPresheaf X) := inferInstance
  have : PreservesFiniteLimits
      ((CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) := inferInstance
  exact comp_preservesFiniteLimits _ _

variable (ℱ : X.Modules)

section RightDerivedGlobalSections

/-- In the complex of global sections of `K`, the image of `Γ(Kⁿ)` among the cocycles of degree
`n + 1` is the subgroup of coboundaries. -/
lemma range_abToCycles_globalSections (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    AddMonoidHom.range
        ((((globalSectionsFunctor X).mapHomologicalComplex _).obj K).sc' n (n + 1)
          (n + 2)).abToCycles = sectionsBoundaries K n := by
  ext ⟨x, hx⟩
  simp only [AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩


variable [HasInjectiveResolutions X.Modules]

/-- **Sheaf cohomology is the right derived functor of global sections**:
`R^{n+1} Γ(X, ℱ) ≅ H^{n+1}(X, ℱ)`, computed with an injective resolution `I` of `ℱ`. Both sides
are the cohomology of the complex `Γ(X, I)`, the right side because injective `𝒪_X`-modules
are acyclic. -/
noncomputable def rightDerivedGlobalSectionsSuccAddEquiv (I : InjectiveResolution ℱ) (n : ℕ) :
    ((globalSectionsFunctor X).rightDerived (n + 1)).obj ℱ ≃+ ℱ.H (n + 1) :=
  let C := ((globalSectionsFunctor X).mapHomologicalComplex _).obj I.cocomplex
  (I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).addCommGroupIsoToAddEquiv.trans <|
  (CochainComplex.abHomologySuccAddEquiv C n).trans <|
  (QuotientAddGroup.quotientAddEquivOfEq
    (range_abToCycles_globalSections I.cocomplex n)).trans <|
  (cyclesQuotientAddEquiv I.cocomplex n).symm.trans <|
  (H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
    (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm.trans <|
  H.mapAddEquiv I.isoCyclesZero.symm (n + 1)


/-- **Sheaf cohomology is the right derived functor of global sections**: for every `q`,
`R^q Γ(X, ℱ) ≅ H^q(X, ℱ)` (in degree `0` both sides are `Γ(X, ℱ)`). -/
theorem nonempty_rightDerived_globalSections_addEquiv_H (q : ℕ) :
    Nonempty (((globalSectionsFunctor X).rightDerived q).obj ℱ ≃+ ℱ.H q) := by
  cases q with
  | zero =>
    exact ⟨((globalSectionsFunctor X).rightDerivedZeroIsoSelf.app ℱ).addCommGroupIsoToAddEquiv.trans
      (H.zeroLinearEquiv ℱ).symm.toAddEquiv⟩
  | succ n => exact ⟨rightDerivedGlobalSectionsSuccAddEquiv ℱ (injectiveResolution ℱ) n⟩


lemma rightDerivedGlobalSectionsSuccAddEquiv_apply (I : InjectiveResolution ℱ) (n : ℕ)
    (x : ((globalSectionsFunctor X).rightDerived (n + 1)).obj ℱ) :
    rightDerivedGlobalSectionsSuccAddEquiv ℱ I n x =
      H.map I.isoCyclesZero.inv (n + 1) ((H.cyclesZeroSuccAddEquiv I.cocomplex
        I.cocomplex_exactAt_succ (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm
        ((cyclesQuotientAddEquiv I.cocomplex n).symm
          (QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles_globalSections I.cocomplex n)
            (CochainComplex.abHomologySuccAddEquiv _ n
              ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x))))) :=
  rfl

set_option maxHeartbeats 1600000 in
/-- `R^{n+1} Γ(X, ℱ) ≅ H^{n+1}(X, ℱ)` is natural in `ℱ`. -/
lemma rightDerivedGlobalSectionsSuccAddEquiv_naturality (𝒢 : X.Modules) (φ : ℱ ⟶ 𝒢)
    (I : InjectiveResolution ℱ) (J : InjectiveResolution 𝒢) (n : ℕ)
    (x : ((globalSectionsFunctor X).rightDerived (n + 1)).obj ℱ) :
    rightDerivedGlobalSectionsSuccAddEquiv 𝒢 J n
        (((globalSectionsFunctor X).rightDerived (n + 1)).map φ x) =
      H.map φ (n + 1) (rightDerivedGlobalSectionsSuccAddEquiv ℱ I n x) := by
  let ψ := InjectiveResolution.desc φ J I
  let Γψ := ((globalSectionsFunctor X).mapHomologicalComplex _).map ψ
  have hK := I.cocomplex_exactAt_succ
  have hK' := J.cocomplex_exactAt_succ
  have hacyc : ∀ j m, Subsingleton ((I.cocomplex.X j).H (m + 1)) :=
    fun _ m ↦ subsingleton_H_of_injective _ m
  have hacyc' : ∀ j m, Subsingleton ((J.cocomplex.X j).H (m + 1)) :=
    fun _ m ↦ subsingleton_H_of_injective _ m
  have h1 : (J.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom
      (((globalSectionsFunctor X).rightDerived (n + 1)).map φ x) =
      HomologicalComplex.homologyMap Γψ (n + 1)
        ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x) := by
    rw [← ConcreteCategory.comp_apply, InjectiveResolution.isoRightDerivedObj_hom_naturality φ I J
      ψ (InjectiveResolution.desc_commutes_zero φ J I)]
    rfl
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (HomologicalComplex.homologyπ
      (((globalSectionsFunctor X).mapHomologicalComplex _).obj I.cocomplex) (n + 1))).mp
    inferInstance
    ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x)
  let CI := ((globalSectionsFunctor X).mapHomologicalComplex _).obj I.cocomplex
  let CJ := ((globalSectionsFunctor X).mapHomologicalComplex _).obj J.cocomplex
  have hv : CJ.iCycles (n + 1) (HomologicalComplex.cyclesMap Γψ (n + 1) c) =
      (ψ.f (n + 1)).app ⊤ (CI.iCycles (n + 1) c) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
    rfl
  have hI : QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles_globalSections I.cocomplex n)
      (CochainComplex.abHomologySuccAddEquiv CI n
        ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x))
      = QuotientAddGroup.mk ⟨CI.iCycles (n + 1) c, by
        change (CI.iCycles (n + 1) ≫ CI.d (n + 1) (n + 2)) c = 0
        rw [HomologicalComplex.iCycles_d]; rfl⟩ := by
    rw [← hc, CochainComplex.abHomologySuccAddEquiv_homologyπ]
    rfl
  have hJ : QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles_globalSections J.cocomplex n)
      (CochainComplex.abHomologySuccAddEquiv CJ n
        ((J.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom
        (((globalSectionsFunctor X).rightDerived (n + 1)).map φ x))) =
      QuotientAddGroup.map _ _ (sectionsCyclesMap ψ n) (sectionsBoundaries_le_comap ψ n)
        (QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles_globalSections I.cocomplex n)
          (CochainComplex.abHomologySuccAddEquiv CI n
            ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x))) := by
    have hπ : HomologicalComplex.homologyMap Γψ (n + 1) (CI.homologyπ (n + 1) c) =
        CJ.homologyπ (n + 1) (HomologicalComplex.cyclesMap Γψ (n + 1) c) := by
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality]
      rfl
    rw [hI, h1, ← hc, hπ]
    rw [CochainComplex.abHomologySuccAddEquiv_homologyπ, QuotientAddGroup.map_mk]
    refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
    exact hv
  rw [rightDerivedGlobalSectionsSuccAddEquiv_apply, rightDerivedGlobalSectionsSuccAddEquiv_apply,
    hJ]
  have hc' : (cyclesQuotientAddEquiv J.cocomplex n).symm
      (QuotientAddGroup.map _ _ (sectionsCyclesMap ψ n) (sectionsBoundaries_le_comap ψ n)
        (QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles_globalSections I.cocomplex n)
          (CochainComplex.abHomologySuccAddEquiv CI n
            ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x)))) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) ((cyclesQuotientAddEquiv I.cocomplex n).symm
          (QuotientAddGroup.quotientAddEquivOfEq (range_abToCycles_globalSections I.cocomplex n)
            (CochainComplex.abHomologySuccAddEquiv CI n
              ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)).hom x)))) := by
    rw [AddEquiv.symm_apply_eq, cyclesQuotientAddEquiv_naturality, AddEquiv.apply_symm_apply]
  rw [hc', H.cyclesZeroSuccAddEquiv_naturality_symm ψ hK hacyc hK' hacyc', ← H.map_comp_apply,
    ← H.map_comp_apply, InjectiveResolution.isoCyclesZero_inv_naturality]

end RightDerivedGlobalSections

end AlgebraicGeometry.Scheme.Modules
