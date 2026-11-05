import Jacobian.AlgebraicGeometry.Modules.Limits
import Jacobian.AlgebraicGeometry.Modules.Cokernel
import Jacobian.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Jacobian.AlgebraicGeometry.Cohomology.LongExact

/-!
# Extensions of quasi-coherent module sheaves

Quasi-coherence is stable under extensions and finite sums. Consequently,
the middle term of a five-term exact sequence with quasi-coherent outer
terms is quasi-coherent. The extension argument uses exact affine sections
and the localization criterion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance : Functor.PreservesZeroMorphisms (C := X.Modules)
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

variable {S : ShortComplex X.Modules}

/-- **Left exactness of sections.** In an exact sequence `M₁ ⟶ M₂ ⟶ M₃` with `M₁ ⟶ M₂` a
monomorphism, the sections of `M₂` over `U` killed by `M₂ ⟶ M₃` come from `M₁`. -/
lemma exists_app_f_eq_of_app_g_eq_zero (hS : S.Exact) [Mono S.f] (U : X.Opens) (y : Γ(S.X₂, U))
    (hy : S.g.app U y = 0) : ∃ x, S.f.app U x = y :=
  have : (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive := { map_add := rfl }
  have : PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op U)) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ (op U)
  (ShortComplex.moduleCat_exact_iff _).mp
    (hS.map_of_mono_of_preservesKernel (SheafOfModules.evaluation X.ringCatSheaf (op U))
      inferInstance inferInstance) y hy

/-- **Extensions of quasi-coherent modules are quasi-coherent.** In a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` and `M₃` quasi-coherent, `M₂` is
quasi-coherent. -/
theorem isQuasicoherent_of_shortExact (hS : S.ShortExact)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₁]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₃] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₂ := by
  have := hS.mono_f
  have hsurj {W : X.Opens} (hW : IsAffineOpen W) : Function.Surjective (S.g.app W) :=
    surjective_app_of_cechAcyclicOnAffines (shortExact_map_toSheaf hS)
      (cechAcyclicOnAffines_of_isQuasicoherent S.X₁) hW
  refine isQuasicoherent_of_forall_isAffineOpen _ (fun W hW f s ↦ ?_) (fun W hW f t ht ↦ ?_)
  · obtain ⟨n, c, hc⟩ := exists_map_eq_pow_smul_of_basicOpen_eq S.X₃ hW f rfl
      (X.basicOpen_le f) (S.g.app _ s)
    obtain ⟨b, rfl⟩ := hsurj hW c
    obtain ⟨a', ha'⟩ := exists_app_f_eq_of_app_g_eq_zero hS.exact _
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s -
        S.X₂.presheaf.map (homOfLE (X.basicOpen_le f)).op b) (by
        rw [map_sub, Hom.app_smul, Hom.app_presheaf_map, hc, sub_self])
    obtain ⟨m, a, ha⟩ := exists_map_eq_pow_smul_of_basicOpen_eq S.X₁ hW f rfl (X.basicOpen_le f)
      a'
    refine ⟨m + n, S.f.app W a + f ^ m • b, ?_⟩
    rw [map_add, ← Hom.app_presheaf_map, ha, Hom.app_smul, ha', map_smul, map_pow, smul_sub,
      sub_add_cancel, pow_add, mul_smul]
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq S.X₃ hW f rfl (X.basicOpen_le f)
      (S.g.app W t) (by rw [← Hom.app_presheaf_map, ht, map_zero])
    obtain ⟨a, ha⟩ := exists_app_f_eq_of_app_g_eq_zero hS.exact W (f ^ n • t)
      (by rw [Hom.app_smul, hn])
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq S.X₁ hW f rfl (X.basicOpen_le f) a
      (injective_app_of_mono S.f (by
        rw [Hom.app_presheaf_map, ha, map_smul, ht, smul_zero, map_zero]))
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_smul, ← ha, ← Hom.app_smul, hm, map_zero]

/-- A zero `𝒪_X`-module is quasi-coherent. -/
lemma isQuasicoherent_of_isZero {M : X.Modules} (hM : IsZero M) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M :=
  have h (U : X.Opens) (x : Γ(M, U)) : x = 0 := by
    simpa using congrArg (fun φ : M ⟶ M ↦ φ.app U x) (hM.eq_of_src (𝟙 M) 0)
  isQuasicoherent_of_forall_isAffineOpen M
    (fun _ _ _ _ ↦ ⟨0, 0, (h _ _).trans (h _ _).symm⟩) (fun _ _ _ _ _ ↦ ⟨0, h _ _⟩)

/-- A binary biproduct of quasi-coherent modules is quasi-coherent. -/
lemma isQuasicoherent_biprod (M N : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (M ⊞ N) :=
  isQuasicoherent_of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact

/-- **The middle term of a five-term exact sequence.** In an exact sequence
`A₁ ⟶ A₂ ⟶ B ⟶ A₄ ⟶ A₅` of `𝒪_X`-modules with `A₁`, `A₂`, `A₄` and `A₅` quasi-coherent, `B` is
quasi-coherent: it is an extension of the kernel of `A₄ ⟶ A₅` by the cokernel of `A₁ ⟶ A₂`. -/
theorem isQuasicoherent_of_exact {A₁ A₂ B A₄ A₅ : X.Modules} {a : A₁ ⟶ A₂} {δ : A₂ ⟶ B}
    {b : B ⟶ A₄} {c : A₄ ⟶ A₅} {w₁ : a ≫ δ = 0} {w₂ : δ ≫ b = 0} {w₃ : b ≫ c = 0}
    (h₁ : (ShortComplex.mk a δ w₁).Exact) (h₂ : (ShortComplex.mk δ b w₂).Exact)
    (h₃ : (ShortComplex.mk b c w₃).Exact)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) A₁]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) A₂]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) A₄]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) A₅] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) B := by
  let T₁ := ShortComplex.mk a (kernel.lift b δ w₂) (by simp [← cancel_mono (kernel.ι b), w₁])
  have hT₁ : T₁.Exact := by
    let φ : T₁ ⟶ ShortComplex.mk a δ w₁ :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι b }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h₁
  have : Epi T₁.g := (ShortComplex.exact_iff_epi_kernel_lift _).1 h₂
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (kernel b) :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hT₁.gIsCokernel)
      (isQuasicoherent_cokernel a)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (kernel c) :=
    isQuasicoherent_kernel c
  let T₂ := ShortComplex.mk (kernel.ι b) (kernel.lift c b w₃)
    (by simp [← cancel_mono (kernel.ι c)])
  have hT₂ : T₂.ShortExact := by
    refine .mk' ?_ inferInstance ((ShortComplex.exact_iff_epi_kernel_lift _).1 h₃)
    let φ : T₂ ⟶ ShortComplex.mk (kernel.ι b) b (kernel.condition b) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι c }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel b))
  exact isQuasicoherent_of_shortExact hT₂

end AlgebraicGeometry.Scheme.Modules
