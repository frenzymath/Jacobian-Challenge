import Jacobian.AlgebraicGeometry.ProjectiveSpace.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Projective space over a scheme

Projective space is the base change of the integral projective space. Its
structure morphism is proper, the construction commutes with base change,
and the cartesian universal property supplies lifts of projective embeddings.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Projective space over a scheme, obtained by base change from the integral model. -/
def ProjectiveSpace (coordinates : Type u) (baseScheme : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from baseScheme) (terminal.from (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ)))

namespace ProjectiveSpace

scoped[AlgebraicGeometry] notation "ℙ(" coordinates "; " baseScheme ")" => ProjectiveSpace coordinates baseScheme

variable (coordinates : Type u) (baseScheme : Scheme.{u})

@[simps -isSimp]
instance over : ℙ(coordinates; baseScheme).CanonicallyOver baseScheme where
  hom := pullback.fst _ _

/-- The projection from relative projective space to its integral model. -/
def toIntegralModel : ℙ(coordinates; baseScheme) ⟶ Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ) := pullback.snd _ _

@[ext 1100]
lemma hom_ext {sourceScheme : Scheme.{u}} {firstMap secondMap : sourceScheme ⟶ ℙ(coordinates; baseScheme)}
    (structureMapEq : firstMap ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = secondMap ≫ ℙ(coordinates; baseScheme) ↘ baseScheme)
    (integralModelMapEq : firstMap ≫ toIntegralModel coordinates baseScheme = secondMap ≫ toIntegralModel coordinates baseScheme) : firstMap = secondMap :=
  pullback.hom_ext structureMapEq integralModelMapEq

lemma isPullback_over_toIntegralModel :
    IsPullback (ℙ(coordinates; baseScheme) ↘ baseScheme) (toIntegralModel coordinates baseScheme) (terminal.from baseScheme)
      (terminal.from (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ))) :=
  IsPullback.of_hasPullback _ _

instance instIsProper [Finite coordinates] : IsProper (ℙ(coordinates; baseScheme) ↘ baseScheme) := by
  have terminalMapEq : terminal.from (Spec (.of (ULift.{u} ℤ))) =
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  have projectiveTerminalEq : terminal.from (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ)) =
      Proj.projectiveSpaceOverAffineToSpec coordinates (ULift.{u} ℤ) ≫ terminal.from _ := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := terminalMapEq ▸ inferInstance
  have : IsProper (terminal.from (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ))) :=
    projectiveTerminalEq ▸ inferInstance
  exact inferInstanceAs (IsProper (pullback.fst _ _))

attribute [local instance] MvPolynomial.gradedAlgebra in

instance instIsEmpty [IsEmpty coordinates] : IsEmpty ℙ(coordinates; baseScheme) := by
  have square := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ))
    MvPolynomial.X (fun coordinate ↦ ⟨1, MvPolynomial.isHomogeneous_X _ coordinate⟩)
    (MvPolynomial.adjoin_range_X_eq_top coordinates _)
  rw [iSup_of_empty] at square
  refine ⟨fun point ↦ ?_⟩
  have : (toIntegralModel coordinates baseScheme).base point ∈ (⊤ : (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ)).Opens) :=
    trivial
  rw [← square] at this
  exact this

/-- The morphism of projective spaces induced by a morphism of bases. -/
def map {baseScheme targetScheme : Scheme.{u}} (firstMap : baseScheme ⟶ targetScheme) : ℙ(coordinates; baseScheme) ⟶ ℙ(coordinates; targetScheme) :=
  pullback.lift (ℙ(coordinates; baseScheme) ↘ baseScheme ≫ firstMap) (toIntegralModel coordinates baseScheme) (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma map_over {baseScheme targetScheme : Scheme.{u}} (firstMap : baseScheme ⟶ targetScheme) :
    map coordinates firstMap ≫ ℙ(coordinates; targetScheme) ↘ targetScheme = ℙ(coordinates; baseScheme) ↘ baseScheme ≫ firstMap :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_toIntegralModel {baseScheme targetScheme : Scheme.{u}} (firstMap : baseScheme ⟶ targetScheme) :
    map coordinates firstMap ≫ toIntegralModel coordinates targetScheme = toIntegralModel coordinates baseScheme :=
  pullback.lift_snd _ _ _

@[simp]
lemma map_id : map coordinates (𝟙 baseScheme) = 𝟙 ℙ(coordinates; baseScheme) := by
  ext1 <;> simp

@[reassoc, simp]
lemma map_comp {baseScheme baseScheme' baseScheme'' : Scheme.{u}} (firstMap : baseScheme ⟶ baseScheme') (secondMap : baseScheme' ⟶ baseScheme'') :
    map coordinates (firstMap ≫ secondMap) = map coordinates firstMap ≫ map coordinates secondMap := by
  ext1 <;> simp

lemma isPullback_map {sourceScheme baseScheme : Scheme.{u}} (secondMap : sourceScheme ⟶ baseScheme) :
    IsPullback (map coordinates secondMap) (ℙ(coordinates; sourceScheme) ↘ sourceScheme) (ℙ(coordinates; baseScheme) ↘ baseScheme) secondMap := by
  refine (IsPullback.paste_horiz_iff (isPullback_over_toIntegralModel coordinates baseScheme).flip (map_over coordinates secondMap)).mp ?_
  rw [map_toIntegralModel, terminal.comp_from]
  exact (isPullback_over_toIntegralModel coordinates sourceScheme).flip

instance isProper_map {sourceScheme baseScheme : Scheme.{u}} (secondMap : sourceScheme ⟶ baseScheme) [IsProper secondMap] : IsProper (map coordinates secondMap) :=
  MorphismProperty.of_isPullback (isPullback_map coordinates secondMap).flip inferInstance

section LiftBaseChange

variable {coordinates} {sourceScheme baseScheme targetScheme : Scheme.{u}} {secondMap : sourceScheme ⟶ baseScheme} (sourceMap : targetScheme ⟶ sourceScheme) (projectiveMap : targetScheme ⟶ ℙ(coordinates; baseScheme))
  (compatibility : sourceMap ≫ secondMap = projectiveMap ≫ ℙ(coordinates; baseScheme) ↘ baseScheme)

/-- The lift supplied by the cartesian square for projective base change. -/
def liftBaseChange : targetScheme ⟶ ℙ(coordinates; sourceScheme) :=
  (isPullback_map coordinates secondMap).lift projectiveMap sourceMap compatibility.symm

@[reassoc (attr := simp)]
lemma liftBaseChange_over : liftBaseChange sourceMap projectiveMap compatibility ≫ ℙ(coordinates; sourceScheme) ↘ sourceScheme = sourceMap :=
  (isPullback_map coordinates secondMap).lift_snd _ _ _

@[reassoc (attr := simp)]
lemma liftBaseChange_map : liftBaseChange sourceMap projectiveMap compatibility ≫ map coordinates secondMap = projectiveMap :=
  (isPullback_map coordinates secondMap).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma liftBaseChange_toIntegralModel :
    liftBaseChange sourceMap projectiveMap compatibility ≫ toIntegralModel coordinates sourceScheme = projectiveMap ≫ toIntegralModel coordinates baseScheme := by
  rw [← map_toIntegralModel coordinates secondMap, liftBaseChange_map_assoc]

instance isSeparated_map [IsSeparated secondMap] : IsSeparated (map coordinates secondMap) :=
  MorphismProperty.of_isPullback (isPullback_map coordinates secondMap).flip inferInstance

instance isImmersion_liftBaseChange [IsImmersion projectiveMap] : IsImmersion (liftBaseChange sourceMap projectiveMap compatibility) :=
  have : IsImmersion (liftBaseChange sourceMap projectiveMap compatibility ≫ map coordinates secondMap) := by
    rw [liftBaseChange_map]
    infer_instance
  .of_comp _ (map coordinates secondMap)

instance isClosedImmersion_liftBaseChange [IsSeparated secondMap] [IsClosedImmersion projectiveMap] :
    IsClosedImmersion (liftBaseChange sourceMap projectiveMap compatibility) :=
  have : IsClosedImmersion (liftBaseChange sourceMap projectiveMap compatibility ≫ map coordinates secondMap) := by
    rw [liftBaseChange_map]
    infer_instance
  .of_comp _ (map coordinates secondMap)

lemma isPullback_liftBaseChange {originalScheme : Scheme.{u}} {pullbackMap : targetScheme ⟶ originalScheme} {embedding : originalScheme ⟶ ℙ(coordinates; baseScheme)}
    (square : IsPullback pullbackMap sourceMap (embedding ≫ ℙ(coordinates; baseScheme) ↘ baseScheme) secondMap) (compatibility : sourceMap ≫ secondMap = (pullbackMap ≫ embedding) ≫ ℙ(coordinates; baseScheme) ↘ baseScheme) :
    IsPullback pullbackMap (liftBaseChange sourceMap (pullbackMap ≫ embedding) compatibility) embedding (map coordinates secondMap) :=
  square.of_bot' (isPullback_map coordinates secondMap)

end LiftBaseChange

end ProjectiveSpace

end AlgebraicGeometry
