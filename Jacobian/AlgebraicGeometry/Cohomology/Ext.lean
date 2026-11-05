import Jacobian.AlgebraicGeometry.Cohomology.ExtZero
import Jacobian.AlgebraicGeometry.Cohomology.AcyclicResolution
import Jacobian.AlgebraicGeometry.Modules.Linear
import Jacobian.CategoryTheory.Abelian.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Module Ext and sheaf cohomology

The Ext groups from the structure module agree naturally with the cohomology
of the underlying abelian sheaf. Evaluation at one gives the comparison in
degree zero. Dimension shifting gives the higher comparisons because injective
module sheaves are acyclic for abelian-sheaf cohomology.

The comparison respects multiplication by global functions, and hence any
coefficient ring acting through global functions. No quasi-coherence, affine
cover, or separation hypothesis is needed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe coefficientUniverse u

open CategoryTheory CategoryTheory.Abelian Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}}

local instance : HasExt.{u + 1} scheme.Modules := HasExt.standard scheme.Modules

private abbrev liftedCohomologyFunctor (scheme : Scheme.{u}) (degree : ℕ) :
    scheme.Modules ⥤ AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf scheme.ringCatSheaf) ⋙
    Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology scheme) degree ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}

private theorem extFunctorMap_apply {moduleSheaf targetSheaf : scheme.Modules}
    (coefficientMap : moduleSheaf ⟶ targetSheaf) (degree : ℕ)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf degree) :
    (extFunctorObj (unit scheme) degree).map coefficientMap extension =
      extension.comp (Ext.mk₀ coefficientMap) (add_zero degree) := rfl

private theorem liftedCohomologyMap_down {moduleSheaf targetSheaf : scheme.Modules}
    (coefficientMap : moduleSheaf ⟶ targetSheaf) (degree : ℕ)
    (sectionValue : ULift.{u + 1} (moduleSheaf.H degree)) :
    ((liftedCohomologyFunctor scheme degree).map coefficientMap sectionValue).down =
      H.map coefficientMap degree sectionValue.down := rfl

private def extConnecting (sequence : ShortComplex scheme.Modules)
    (shortExact : sequence.ShortExact) (degree : ℕ) :
    (extFunctorObj (unit scheme) degree).obj sequence.X₃ ⟶
      (extFunctorObj (unit scheme) (degree + 1)).obj sequence.X₁ :=
  AddCommGrpCat.ofHom (shortExact.extClass.postcomp (unit scheme) rfl)

private def liftedCohomologyConnecting (sequence : ShortComplex scheme.Modules)
    (shortExact : sequence.ShortExact) (degree : ℕ) :
    (liftedCohomologyFunctor scheme degree).obj sequence.X₃ ⟶
      (liftedCohomologyFunctor scheme (degree + 1)).obj sequence.X₁ :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.map (AddCommGrpCat.ofHom (H.δ shortExact degree))

private def extZeroIso (scheme : Scheme.{u}) :
    (⊤ : ObjectProperty scheme.Modules).ι ⋙ extFunctorObj (unit scheme) 0 ≅
      (⊤ : ObjectProperty scheme.Modules).ι ⋙ liftedCohomologyFunctor scheme 0 :=
  NatIso.ofComponents
    (fun moduleSheaf ↦
      ((extZeroEquivH moduleSheaf.obj).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    fun coefficientMap ↦ by
      apply ConcreteCategory.hom_ext
      intro extension
      apply ULift.ext
      apply (H.zeroLinearEquiv _).injective
      change H.zeroLinearEquiv _
          (extZeroEquivH _ (extension.comp (Ext.mk₀ coefficientMap.hom) (add_zero 0))) =
        H.zeroLinearEquiv _ (H.map coefficientMap.hom 0 (extZeroEquivH _ extension))
      rw [H.zeroLinearEquiv_map]
      change H.zeroLinearEquiv _ ((H.zeroLinearEquiv _).symm
          (extZeroAddEquiv _ (extension.comp (Ext.mk₀ coefficientMap.hom) (add_zero 0)))) =
        coefficientMap.hom.app ⊤
          (H.zeroLinearEquiv _ ((H.zeroLinearEquiv _).symm (extZeroAddEquiv _ extension)))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact extZeroAddEquiv_naturality coefficientMap.hom extension

private theorem nonempty_extCohomologyIso (scheme : Scheme.{u}) (degree : ℕ) :
    Nonempty ((⊤ : ObjectProperty scheme.Modules).ι ⋙ extFunctorObj (unit scheme) degree ≅
      (⊤ : ObjectProperty scheme.Modules).ι ⋙ liftedCohomologyFunctor scheme degree) := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := scheme.Modules)
  refine (⊤ : ObjectProperty scheme.Modules).nonempty_iso_of_connecting
    (fun _ _ ↦ ⟨trivial, trivial⟩)
    (fun degree ↦ extFunctorObj (unit scheme) degree)
    (liftedCohomologyFunctor scheme)
    (fun sequence shortExact _ degree ↦ extConnecting sequence shortExact degree)
    (fun sequence shortExact _ degree ↦
      liftedCohomologyConnecting sequence shortExact degree)
    ?_ ?_ ?_ ?_ ?_ ?_ (extZeroIso scheme) degree
  · intro firstSequence secondSequence coefficientMap firstExact secondExact _ _ degree
    apply ConcreteCategory.hom_ext
    intro extension
    change (extension.comp firstExact.extClass rfl).comp
        (Ext.mk₀ coefficientMap.τ₁) (add_zero (degree + 1)) =
      (extension.comp (Ext.mk₀ coefficientMap.τ₃) (add_zero degree)).comp
        secondExact.extClass rfl
    rw [Ext.comp_assoc_of_third_deg_zero,
      firstExact.extClass_naturality secondExact coefficientMap,
      Ext.comp_assoc_of_second_deg_zero]
  · intro firstSequence secondSequence coefficientMap firstExact secondExact _ _ degree
    apply ConcreteCategory.hom_ext
    intro extension
    apply ULift.ext
    exact (H.δ_naturality firstExact secondExact coefficientMap degree extension.down).symm
  · intro sequence shortExact _ degree extension
    exact (ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.covariant_sequence_exact₃' (unit scheme) shortExact degree _ rfl) extension
  · intro sequence shortExact _ degree extension
    constructor
    · intro zeroImage
      have membership : extension.down ∈ (H.δ shortExact degree).ker :=
        congrArg ULift.down zeroImage
      rw [H.ker_δ_eq_range_map_g shortExact degree] at membership
      obtain ⟨preimage, image_eq⟩ := membership
      exact ⟨ULift.up preimage, ULift.ext image_eq⟩
    · rintro ⟨preimage, rfl⟩
      apply ULift.ext
      change H.δ shortExact degree (H.map sequence.g degree preimage.down) = 0
      exact (H.ker_δ_eq_range_map_g shortExact degree).ge ⟨preimage.down, rfl⟩
  · intro sequence shortExact _ degree injective extension
    letI : Injective sequence.X₂ := injective
    exact Ext.covariant_sequence_exact₁ (unit scheme) shortExact extension
      (Ext.eq_zero_of_injective _) rfl
  · intro sequence shortExact _ degree injective extension
    letI : Injective sequence.X₂ := injective
    letI := subsingleton_H_of_injective sequence.X₂ degree
    have membership : extension.down ∈ (H.map sequence.f (degree + 1)).ker :=
      Subsingleton.elim _ _
    rw [H.ker_map_f_eq_range_δ shortExact degree] at membership
    obtain ⟨preimage, image_eq⟩ := membership
    exact ⟨ULift.up preimage, ULift.ext image_eq⟩

private def extCohomologyIso (scheme : Scheme.{u}) (degree : ℕ) :
    (⊤ : ObjectProperty scheme.Modules).ι ⋙ extFunctorObj (unit scheme) degree ≅
      (⊤ : ObjectProperty scheme.Modules).ι ⋙ liftedCohomologyFunctor scheme degree :=
  match degree with
  | 0 => extZeroIso scheme
  | degree + 1 => (nonempty_extCohomologyIso scheme (degree + 1)).some

/-- Module Ext from the structure sheaf agrees with native abelian-sheaf cohomology. -/
def extAddEquivH (moduleSheaf : scheme.Modules) (degree : ℕ) :
    Ext.{u + 1} (unit scheme) moduleSheaf degree ≃+ moduleSheaf.H degree :=
  ((extCohomologyIso scheme degree).app ⟨moduleSheaf, trivial⟩).addCommGroupIsoToAddEquiv.trans
    AddEquiv.ulift

private theorem extAddEquivH_apply (moduleSheaf : scheme.Modules) (degree : ℕ)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf degree) :
    extAddEquivH moduleSheaf degree extension =
      ((extCohomologyIso scheme degree).hom.app ⟨moduleSheaf, trivial⟩ extension).down := rfl

@[simp]
theorem extAddEquivH_zero (moduleSheaf : scheme.Modules)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf 0) :
    extAddEquivH moduleSheaf 0 extension = extZeroEquivH moduleSheaf extension := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem extCohomologyIso_naturality (degree : ℕ)
    (comparison :
      (⊤ : ObjectProperty scheme.Modules).ι ⋙ extFunctorObj (unit scheme) degree ≅
        (⊤ : ObjectProperty scheme.Modules).ι ⋙ liftedCohomologyFunctor scheme degree)
    {moduleSheaf targetSheaf : scheme.Modules}
    (coefficientMap : moduleSheaf ⟶ targetSheaf)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf degree) :
    (comparison.hom.app ⟨targetSheaf, trivial⟩
        (extension.comp (Ext.mk₀ coefficientMap) (add_zero degree))).down =
      H.map coefficientMap degree
        (comparison.hom.app ⟨moduleSheaf, trivial⟩ extension).down := by
  let sourceObject : (⊤ : ObjectProperty scheme.Modules).FullSubcategory :=
    ⟨moduleSheaf, trivial⟩
  let targetObject : (⊤ : ObjectProperty scheme.Modules).FullSubcategory :=
    ⟨targetSheaf, trivial⟩
  let objectMap : sourceObject ⟶ targetObject := ObjectProperty.homMk coefficientMap
  let sourceGroup : AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.of (Ext.{u + 1} (unit scheme) moduleSheaf degree)
  let targetGroup : AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.of (ULift.{u + 1} (targetSheaf.H degree))
  have square :
      ((extFunctorObj (unit scheme) degree).map coefficientMap ≫
          comparison.hom.app targetObject : sourceGroup ⟶ targetGroup) =
        comparison.hom.app sourceObject ≫
          (liftedCohomologyFunctor scheme degree).map coefficientMap :=
    comparison.hom.naturality objectMap
  have onExtension := congrArg
    (fun morphism : sourceGroup ⟶ targetGroup ↦
      (AddCommGrpCat.Hom.hom morphism) extension) square
  have downEquality := congrArg
    (fun sectionValue : ULift.{u + 1} (targetSheaf.H degree) ↦ sectionValue.down) onExtension
  rw [← extFunctorMap_apply (scheme := scheme) coefficientMap degree extension,
    ← liftedCohomologyMap_down (scheme := scheme) coefficientMap degree
      (comparison.hom.app sourceObject extension)]
  exact downEquality

/-- The Ext/cohomology comparison commutes with maps of coefficient sheaves. -/
theorem extAddEquivH_naturality {moduleSheaf targetSheaf : scheme.Modules}
    (coefficientMap : moduleSheaf ⟶ targetSheaf) (degree : ℕ)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf degree) :
    extAddEquivH targetSheaf degree
        (extension.comp (Ext.mk₀ coefficientMap) (add_zero degree)) =
      H.map coefficientMap degree (extAddEquivH moduleSheaf degree extension) := by
  rw [extAddEquivH_apply, extAddEquivH_apply]
  exact extCohomologyIso_naturality degree (extCohomologyIso scheme degree)
    coefficientMap extension

/-- Multiplication on the Ext coefficient agrees with multiplication by global functions on cohomology. -/
theorem extAddEquivH_comp_smulHom (moduleSheaf : scheme.Modules) (degree : ℕ)
    (scalar : Γ(scheme, ⊤)) (extension : Ext.{u + 1} (unit scheme) moduleSheaf degree) :
    extAddEquivH moduleSheaf degree
        (extension.comp (Ext.mk₀ (moduleSheaf.smulHom scalar)) (add_zero degree)) =
      scalar • extAddEquivH moduleSheaf degree extension :=
  extAddEquivH_naturality (moduleSheaf.smulHom scalar) degree extension

/-- The Ext/cohomology comparison is linear over every ring acting through global functions. -/
def extLinearEquivH {coefficientRing : Type coefficientUniverse} [CommRing coefficientRing]
    (scalarMap : coefficientRing →+* Γ(scheme, ⊤))
    (moduleSheaf : scheme.Modules) (degree : ℕ) :
    letI := linearOfRingHom scheme scalarMap
    letI : Module coefficientRing (moduleSheaf.H degree) :=
      Module.compHom (moduleSheaf.H degree) scalarMap
    Ext.{u + 1} (unit scheme) moduleSheaf degree ≃ₗ[coefficientRing] moduleSheaf.H degree := by
  letI := linearOfRingHom scheme scalarMap
  letI : Module coefficientRing (moduleSheaf.H degree) :=
    Module.compHom (moduleSheaf.H degree) scalarMap
  refine { extAddEquivH moduleSheaf degree with map_smul' := ?_ }
  intro scalar extension
  rw [Ext.smul_eq_comp_mk₀, linearOfRingHom_smul_id scheme scalarMap moduleSheaf scalar]
  exact extAddEquivH_comp_smulHom moduleSheaf degree (scalarMap scalar) extension

/-- Module Ext and native sheaf cohomology have the same dimension over the ground field. -/
theorem finrank_ext_eq_finrankH (baseField : Type u) [Field baseField]
    [scheme.Over (Spec (.of baseField))] (moduleSheaf : scheme.Modules) (degree : ℕ) :
    letI := linearOfRingHom scheme (Scheme.globalSectionsRingHom baseField (X := scheme))
    Module.finrank baseField (Ext.{u + 1} (unit scheme) moduleSheaf degree) =
      moduleSheaf.finrankH baseField degree := by
  letI := linearOfRingHom scheme (Scheme.globalSectionsRingHom baseField (X := scheme))
  exact (extLinearEquivH (Scheme.globalSectionsRingHom baseField (X := scheme))
    moduleSheaf degree).finrank_eq

end AlgebraicGeometry.Scheme.Modules
