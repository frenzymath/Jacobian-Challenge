import Jacobian.AlgebraicGeometry.IdealSheaf.Modules
import Jacobian.AlgebraicGeometry.Modules.TensorEquivalence
import Jacobian.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Exact sequences of ideal sheaves

The restriction to a closed subscheme is an epimorphism of module sheaves. Its kernel is the
ideal module, and tensoring the inclusion by a line bundle gives the corresponding quotient
sequence.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A module morphism is an epimorphism if its sections lift locally. -/
lemma Hom.epi_of_locally_surjective {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (W : X.Opens) (y : Γ(N, W)) (x : X), x ∈ W →
      ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
        ∃ z : Γ(M, V), φ.app V z = N.presheaf.map (homOfLE hVW).op y) :
    Epi φ := by
  have h₁ : TopCat.Presheaf.IsLocallySurjective ((toPresheaf X).map φ) := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W y x hx
    obtain ⟨V, hVW, hxV, z, hz⟩ := h W y x hx
    exact ⟨V, hVW, ⟨z, hz⟩, hxV⟩
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := h₁
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

instance epi_toPushforwardSubscheme (J : X.IdealSheafData) :
    Epi J.toPushforwardSubscheme := by
  refine Modules.Hom.epi_of_locally_surjective _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hx
  obtain ⟨z, hz⟩ := J.subschemeι.app_surjective V hV
    (J.subscheme.presheaf.map
      ((TopologicalSpace.Opens.map J.subschemeι.base).map (homOfLE hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

/-- The quotient by the ideal module is the structure module of the closed subscheme,
pushed forward to the ambient scheme. -/
def cokernelToModulesιIsoPushforward (J : X.IdealSheafData) :
    cokernel J.toModulesι ≅
      (Modules.pushforward J.subschemeι).obj (𝟙_ J.subscheme.Modules) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel J.toPushforwardSubscheme))

/-- The quotient of a line bundle by an ideal is its restriction to the closed subscheme,
pushed forward to the ambient scheme. -/
def tensorCokernelIsoPushforward (J : X.IdealSheafData) (M : X.Modules) [M.IsInvertible] :
    cokernel (J.toModulesι ▷ M) ≅
      (Modules.pushforward J.subschemeι).obj ((Modules.pullback J.subschemeι).obj M) :=
  (PreservesCokernel.iso (tensorRight M) J.toModulesι).symm ≪≫
    whiskerRightIso (J.cokernelToModulesιIsoPushforward) M ≪≫
      (Modules.pushforwardPullbackLineIso J.subschemeι M).symm

/-- The inclusion of an ideal module tensored by a module and its cokernel. -/
def tensorSequence (J : X.IdealSheafData) (M : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (J.toModulesι ▷ M) (cokernel.π _) (cokernel.condition _)

/-- Tensoring the ideal inclusion by a line bundle gives a short exact sequence. -/
theorem tensorSequence_shortExact (J : X.IdealSheafData)
    (M : X.Modules) [M.IsInvertible] : (J.tensorSequence M).ShortExact := by
  haveI : Mono ((tensorRight M).map J.toModulesι) := Functor.map_mono _ _
  change (ShortComplex.mk (J.toModulesι ▷ M) (cokernel.π _)
    (cokernel.condition _)).ShortExact
  exact .mk' (ShortComplex.exact_cokernel _)
    (show Mono ((tensorRight M).map J.toModulesι) from inferInstance) inferInstance

end AlgebraicGeometry.Scheme.IdealSheafData
