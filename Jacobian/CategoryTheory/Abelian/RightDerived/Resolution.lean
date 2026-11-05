import Jacobian.Algebra.Homology.Cycles
import Jacobian.Algebra.Homology.Embedding.Map
import Jacobian.Algebra.Homology.Embedding.Property
import Jacobian.Algebra.Homology.MappingCone.Acyclic
import Jacobian.CategoryTheory.Abelian.Injective.Comparison
import Jacobian.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Acyclic resolutions compute right derived functors

A left exact functor preserves quasi-isomorphisms between bounded below complexes of acyclic objects. Such a resolution computes its right derived functors.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace HomologicalComplex
open CategoryTheory Limits
variable {C ι : Type*} [Category C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K : HomologicalComplex C c}

/-- Acyclicity is invariant under isomorphisms of complexes. -/
lemma Acyclic.of_iso (hK : K.Acyclic) {L : HomologicalComplex C c} (e : K ≅ L) :
    L.Acyclic := by
  rw [acyclic_iff]
  exact fun n ↦ (hK n).of_iso e

end HomologicalComplex

namespace HomologicalComplex

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

/-- A left exact additive functor `F : C ⥤ D` sends an exact cochain complex `K` which is
bounded below and whose terms are all `F`-acyclic to an exact complex `F(K)`:
```
  0 ──▶ Kᵃ ──d──▶ Kᵃ⁺¹ ──d──▶ Kᵃ⁺² ──▶ ⋯      exact
                      │ F
                      ▼
  0 ──▶ F Kᵃ ──F d──▶ F Kᵃ⁺¹ ──F d──▶ F Kᵃ⁺² ──▶ ⋯    exact
```
The proof is by dimension shifting: the short exact sequences `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0` of
cycles show inductively that all `Zⁿ` are `F`-acyclic, so `F` keeps them short exact. -/
theorem Acyclic.map_of_rightAcyclic {K : CochainComplex C ℤ} (hK : K.Acyclic) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] (a : ℤ) [K.IsStrictlyGE a]
    (hK' : ∀ n, F.rightAcyclic (K.X n)) :
    ((F.mapHomologicalComplex _).obj K).Acyclic := by
  have hS (n : ℤ) := (hK (n + 1)).shortExact_cyclesShortComplex (i := n) (by simp)
  have hZ (n : ℤ) : F.rightAcyclic (K.cycles n) := by
    obtain hn | hn := lt_or_ge n a
    · exact F.rightAcyclic.prop_of_isZero
        (IsZero.of_mono (K.iCycles n) (K.isZero_of_isStrictlyGE a n hn))
    · induction n, hn using Int.leInduction with
      | base =>
        have := (hK a).epi_toCycles (a - 1) (by simp)
        exact F.rightAcyclic.prop_of_isZero (IsZero.of_epi (K.toCycles (a - 1) a)
          (K.isZero_of_isStrictlyGE a (a - 1) (by lia)))
      | succ n _ ih => exact (hS n).rightAcyclic_X₃ ih (hK' n)
  intro m
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by lia⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; lia)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; lia))
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    ((hS n).map_of_rightAcyclic (hZ n)).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

end HomologicalComplex

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- A left exact additive functor `F : C ⥤ D` sends a quasi-isomorphism `φ : K ⟶ L` between
bounded below `ℤ`-indexed cochain complexes whose terms are all `F`-acyclic to a
quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`:
```
    F Kᵃ ──F d──▶ F Kᵃ⁺¹ ──F d──▶ ⋯
     │F φᵃ          │F φᵃ⁺¹
     ▼              ▼
    F Lᵃ ──F d──▶ F Lᵃ⁺¹ ──F d──▶ ⋯
```
The proof applies `HomologicalComplex.Acyclic.map_of_rightAcyclic` to the mapping cone. -/
theorem quasiIso_map_of_rightAcyclic {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (a : ℤ) [K.IsStrictlyGE a] [L.IsStrictlyGE a] (hK : ∀ n, F.rightAcyclic (K.X n))
    (hL : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  have := CochainComplex.isStrictlyGE_mappingCone φ a a (a - 1)
  have hφ := (CochainComplex.mappingCone.quasiIso_iff_acyclic φ).1 ‹_›
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  refine HomologicalComplex.Acyclic.of_iso ?_
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)
  refine hφ.map_of_rightAcyclic F (a - 1) fun n ↦ ?_
  exact F.rightAcyclic.prop_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
    (rightAcyclic_biprod (hK (n + 1)) (hL n))

/-- The `ℕ`-indexed version of `Functor.quasiIso_map_of_rightAcyclic`: `F` sends a
quasi-isomorphism `φ : K ⟶ L` between `ℕ`-indexed cochain complexes whose terms are all
`F`-acyclic to a quasi-isomorphism `F(φ) : F(K) ⟶ F(L)`. The proof extends `φ` to `ℤ` along
`e = ComplexShape.embeddingUpNat` and uses that `F` commutes with extension:
```
  F(K.extend e) ──F(extendMap φ e)──▶ F(L.extend e)
        │ ≅ mapExtendIso                    │ ≅ mapExtendIso
        ▼                                   ▼
  (F K).extend e ──extendMap (F φ) e──▶ (F L).extend e
```
-/
theorem quasiIso_map_of_rightAcyclic_nat {K L : CochainComplex C ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, F.rightAcyclic (K.X n)) (hL : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map φ) := by
  let e := ComplexShape.embeddingUpNat
  have : QuasiIso (HomologicalComplex.extendMap φ e) :=
    (HomologicalComplex.quasiIso_extendMap_iff φ e).2 ‹_›
  have := F.quasiIso_map_of_rightAcyclic (HomologicalComplex.extendMap φ e) 0
    (HomologicalComplex.prop_extend_X _ e hK) (HomologicalComplex.prop_extend_X _ e hL)
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ e]
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (K.mapExtendIso e F) (L.mapExtendIso e F) (by ext; simp))).1 this

end Functor

namespace InjectiveResolution

variable {X : C} {I : CochainComplex C ℕ} (J : InjectiveResolution X) (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] (φ : I ⟶ J.cocomplex) [QuasiIso φ]

/-- The isomorphism `R^q F X ≅ H^q(F I)` induced by a quasi-isomorphism `φ : I ⟶ J` from a
complex `I` of `F`-acyclic objects to an injective resolution `J` of `X`:
```
    R^q F X ──J.isoRightDerivedObj F q──▶ H^q(F J) ◀──H^q(F φ)── H^q(F I)
```
`H^q(F φ)` is an isomorphism by `Functor.quasiIso_map_of_rightAcyclic_nat`. This generalises
`InjectiveResolution.isoRightDerivedObj`. -/
@[simps!]
noncomputable def isoRightDerivedObjOfQuasiIso (hI : ∀ n, F.rightAcyclic (I.X n)) (q : ℕ) :
    (F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q :=
  have := F.quasiIso_map_of_rightAcyclic_nat φ hI fun _ ↦ Functor.rightAcyclic_of_injective _
  J.isoRightDerivedObj F q ≪≫
    (asIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) q)).symm

end InjectiveResolution

namespace Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {X : C} {I : CochainComplex C ℕ}
  (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]

/-- **Acyclic resolutions compute right derived functors.** If `ι : single₀ X ⟶ I` is a
resolution `X → I⁰ → I¹ → ⋯` of `X` by `F`-acyclic objects, then `R^q F X ≅ H^q(F I)`.
It is `InjectiveResolution.isoRightDerivedObjOfQuasiIso` applied to the lift
`φ : I ⟶ J` of the identity of `X` to an injective resolution `J` of `X`:
```
  single₀ X ──ι──▶ I
        ╲          │ φ = descOfQuasiIso (𝟙 X) J ι
      J.ι ╲        ▼
            ╲────▶ J
``` -/
noncomputable def rightDerivedObjIsoOfResolution (hI : ∀ n, F.rightAcyclic (I.X n)) (q : ℕ) :
    (F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q :=
  (injectiveResolution X).isoRightDerivedObjOfQuasiIso F
    (InjectiveResolution.descOfQuasiIso (𝟙 X) _ ι) hI q

end Functor

end CategoryTheory
