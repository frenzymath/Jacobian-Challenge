import Jacobian.AlgebraicGeometry.Cohomology.InjectiveFlasque
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Pushforward
import Jacobian.AlgebraicGeometry.Cohomology.LongExact
import Jacobian.AlgebraicGeometry.Modules.LocallySurjective
import Jacobian.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Higher direct images along affine morphisms

Quasi-coherent module sheaves are acyclic for affine pushforward. Injectives
are Čech-acyclic on affine opens; this property survives the successive
cokernels of an injective resolution and ensures right exactness of affine
pushforward on the resulting short exact sequences.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

local instance : Functor.PreservesZeroMorphisms (C := X.Modules)
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

section AffineMorphism

/-- The underlying abelian sheaf of an injective `𝒪_X`-module is Čech-acyclic on affine opens,
since it is flasque. -/
lemma cechAcyclicOnAffines_toSheaf_of_injective (I : X.Modules) [Injective I] :
    cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
  have := isFlasque_of_injective I
  fun _ _ _ _ _ q ↦ TopCat.Sheaf.exactAt_cechComplex_of_isFlasque _ q _

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` and `M₂`
Čech-acyclic on affine opens, `M₃` is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_toSheaf_X₃ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁))
    (h₂ : cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂)) :
    cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃) :=
  cechAcyclicOnAffines_X₃ (sequence := S.map (SheafOfModules.toSheaf X.ringCatSheaf))
    (shortExact_map_toSheaf hS) h₁ h₂

/-- Let `f : X ⟶ T` be affine. The pushforward along `f` of a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules, with `M₁` Čech-acyclic on affine opens, is right
exact: `M₂ ⟶ M₃` is surjective on the sections over the affine opens `f ⁻¹ᵁ V`, `V` affine. -/
lemma epi_pushforward_map_g_of_cechAcyclicOnAffines (f : X ⟶ T) [IsAffineHom f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁)) : Epi ((pushforward f).map S.g) := by
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens hx
  obtain ⟨z, hz⟩ := surjective_app_of_cechAcyclicOnAffines (shortExact_map_toSheaf hS) h₁
    (IsAffineOpen.preimage hV f) (S.X₃.presheaf.map (homOfLE (f.preimage_mono hVW)).op y)
  exact ⟨V, hVW, hxV, z, hz⟩

/-- **The higher direct images along an affine morphism vanish.** Let `f : X ⟶ T` be affine
and `ℱ` a quasi-coherent `𝒪_X`-module. Then `R^q f_* ℱ = 0` for `q > 0`.

The underlying abelian sheaves of quasi-coherent modules and of injective `𝒪_X`-modules, which
are flasque, are Čech-acyclic on the affine opens of `X`, and this class is stable under
cokernels of monomorphisms. A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` in this
class is surjective on the sections over the affine opens `f ⁻¹ᵁ V`, `V` affine in `T`, so `f_*`
keeps it short exact; hence `ℱ` is `f_*`-acyclic by dimension shifting
(`CategoryTheory.Functor.rightAcyclic_of_epi_map_g`). -/
theorem isZero_higherDirectImage_of_isAffineHom (f : X ⟶ T) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {q : ℕ} (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj ℱ) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have : PreservesFiniteLimits (pushforward f) :=
    have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have h : (pushforward f).rightAcyclic ℱ := Functor.rightAcyclic_of_epi_map_g (pushforward f)
    (fun M ↦ cechAcyclicOnAffines X ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (fun I _ ↦ cechAcyclicOnAffines_toSheaf_of_injective I)
    (fun _ hS h₁ h₂ ↦ cechAcyclicOnAffines_toSheaf_X₃ hS h₁ h₂)
    (fun S hS h₁ ↦ epi_pushforward_map_g_of_cechAcyclicOnAffines f hS h₁)
    (cechAcyclicOnAffines_of_isQuasicoherent ℱ)
  exact h q


end AffineMorphism

end AlgebraicGeometry.Scheme.Modules
