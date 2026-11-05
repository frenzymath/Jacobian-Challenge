import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import Jacobian.CategoryTheory.Abelian.DimensionShifting
import Jacobian.CategoryTheory.Sites.SheafCohomology.ExactSequence
import Jacobian.Topology.Sheaves.CechCriterion

/-!
# Cohomology of direct image by dimension shifting through injective sheaves.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe coefficientUniverse

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {scheme target : TopCat.{coefficientUniverse}} (morphism : scheme ⟶ target)

/-- The pushforward of abelian sheaves along a continuous map. -/
noncomputable abbrev pushforwardAb :
    CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology target) AddCommGrpCat.{coefficientUniverse} :=
  (Opens.map morphism).sheafPushforwardContinuous AddCommGrpCat.{coefficientUniverse} _ _

/-- The pushforward of an injective abelian sheaf is injective: the pushforward has an exact
left adjoint, the pullback. -/
lemma injective_pushforwardAb_obj
    (injectiveSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) [Injective injectiveSheaf] :
    Injective ((pushforwardAb morphism).obj injectiveSheaf) := by
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{coefficientUniverse}) (Opens.map morphism)
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback (Opens.map morphism)
      AddCommGrpCat.{coefficientUniverse} (Opens.grothendieckTopology target) (Opens.grothendieckTopology scheme)) :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback _ _ _ _
  exact Injective.injective_of_adjoint
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map morphism) AddCommGrpCat.{coefficientUniverse}
      (Opens.grothendieckTopology target) (Opens.grothendieckTopology scheme)) injectiveSheaf

variable {morphism} in
/-- The pushforward of a short exact sequence of abelian sheaves is short exact as soon as it
is surjective on the sections over the preimages of the members of a basis. -/
lemma shortExact_map_pushforward
    {sequence : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) {basis : Set (Opens target)} (hB : Opens.IsBasis basis)
    (compatibility : ∀ openSubset ∈ basis, Function.Surjective (sequence.g.hom.app (op ((Opens.map morphism).obj openSubset)))) :
    (sequence.map (pushforwardAb morphism)).ShortExact := by
  have hadj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map morphism)
    AddCommGrpCat.{coefficientUniverse} (Opens.grothendieckTopology target) (Opens.grothendieckTopology scheme)
  have := hadj.rightAdjoint_preservesLimits
  have := hS.mono_f
  have hepi : Epi ((pushforwardAb morphism).map sequence.g) := by
    refine (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{coefficientUniverse}
      ((pushforwardAb morphism).map sequence.g)).1 ?_
    refine (Presheaf.isLocallySurjective_iff ((pushforwardAb morphism).map sequence.g).hom).2
      fun smallerOpen liftedSection otherElement hy ↦ ?_
    obtain ⟨openSubset, hV, hyV, hVW⟩ := Opens.isBasis_iff_nbhd.1 hB hy
    obtain ⟨sectionValue, hs⟩ := compatibility openSubset hV (sequence.X₃.obj.map (homOfLE ((Opens.map morphism).monotone
      (show openSubset ≤ smallerOpen from hVW))).op liftedSection)
    exact ⟨openSubset, hVW, ⟨sectionValue, hs⟩, hyV⟩
  exact ShortComplex.ShortExact.mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance
    inferInstance) (Functor.map_mono (pushforwardAb morphism) sequence.f) hepi

/-- `H⁰(Y, f_* F) = F(X) = H⁰(X, F)`. -/
noncomputable def functorHZeroIsoPushforwardAb :
    CategoryTheory.Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology scheme) 0 ≅
      pushforwardAb morphism ⋙ CategoryTheory.Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology target) 0 :=
  CategoryTheory.Sheaf.functorHZeroIso.{coefficientUniverse} _ isTerminalTop ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      ((evaluation _ _).mapIso (eqToIso (congrArg op (Opens.map_top morphism).symm))) ≪≫
    (Functor.isoWhiskerLeft (pushforwardAb morphism)
      (CategoryTheory.Sheaf.functorHZeroIso.{coefficientUniverse} _ isTerminalTop)).symm

/-- **Cohomology of a pushforward.** Let `f : X ⟶ Y` be continuous and `P` a property of
abelian sheaves on `X`, stable under passing from `F` to the chosen injective sheaf `I` under
`F` and to the cokernel of `F ⟶ I`, such that the pushforward of a short exact sequence
`0 → F → G → H → 0` with `P F` is short exact. Then `H^q(X, F) ≅ H^q(Y, f_* F)`, naturally in
the sheaves `F` with `P F`. -/
theorem nonempty_functorH_iso_pushforwardAb
    (presheaf : ObjectProperty (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}))
    (hP : ∀ sheaf, presheaf sheaf → presheaf (Injective.under sheaf) ∧ presheaf (cokernel (Injective.ι sheaf)))
    (hf : ∀ sequence : ShortComplex
        (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}), sequence.ShortExact →
        presheaf sequence.X₁ → (sequence.map (pushforwardAb morphism)).ShortExact) (cohomologyDegree : ℕ) :
    Nonempty (presheaf.ι ⋙ CategoryTheory.Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology scheme) cohomologyDegree ≅
      presheaf.ι ⋙ pushforwardAb morphism ⋙
        CategoryTheory.Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology target) cohomologyDegree) := by
  refine presheaf.nonempty_iso_of_connecting hP
    (CategoryTheory.Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology scheme))
    (fun cohomologyDegree ↦ pushforwardAb morphism ⋙
      CategoryTheory.Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology target) cohomologyDegree)
    (fun sequence hS _ cohomologyDegree ↦ CategoryTheory.Sheaf.functorHδ hS cohomologyDegree)
    (fun sequence hS compatibility cohomologyDegree ↦ CategoryTheory.Sheaf.functorHδ (hf sequence hS compatibility) cohomologyDegree) ?_ ?_ ?_ ?_ ?_ ?_ ?_ cohomologyDegree
  · intro S₁ S₂ coefficientMap h₁ h₂ _ _ cohomologyDegree
    exact CategoryTheory.Sheaf.functorHδ_naturality.{coefficientUniverse} h₁ cohomologyDegree h₂ coefficientMap
  · intro S₁ S₂ coefficientMap h₁ h₂ p₁ p₂ cohomologyDegree
    exact CategoryTheory.Sheaf.functorHδ_naturality.{coefficientUniverse} (hf _ h₁ p₁) cohomologyDegree (hf _ h₂ p₂)
      ((pushforwardAb morphism).mapShortComplex.map coefficientMap)
  · intro sequence hS _ cohomologyDegree element
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{coefficientUniverse} hS cohomologyDegree element
  · intro sequence hS compatibility cohomologyDegree element
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{coefficientUniverse} (hf sequence hS compatibility) cohomologyDegree element
  · intro sequence hS _ cohomologyDegree _
    exact CategoryTheory.Sheaf.functorHδ_surjective.{coefficientUniverse} hS cohomologyDegree
  · intro sequence hS compatibility cohomologyDegree _
    have : Injective (sequence.map (pushforwardAb morphism)).X₂ := injective_pushforwardAb_obj morphism sequence.X₂
    exact CategoryTheory.Sheaf.functorHδ_surjective.{coefficientUniverse} (hf sequence hS compatibility) cohomologyDegree
  · exact Functor.isoWhiskerLeft presheaf.ι (functorHZeroIsoPushforwardAb morphism)

end TopCat.Sheaf
