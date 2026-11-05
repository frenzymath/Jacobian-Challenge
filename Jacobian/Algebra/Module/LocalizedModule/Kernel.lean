import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Localization of kernels

A map between kernels is a localization if the ambient maps are localizations
and the elements being inverted already act invertibly on the target kernel.
-/

/-- **Localization commutes with kernels.** Let `0 → K → M → N` and `K' → M' → N'` be exact
sequences of `R`-modules with `K' → M'` injective, compatible with maps `K → K'`, `M → M'`,
`N → N'`, the last two of which are localizations at `S`. If the elements of `S` act invertibly on
`K'`, then `K → K'` is a localization at `S`. -/
lemma IsLocalizedModule.of_injective_of_exact {R : Type*} [CommRing R] (S : Submonoid R)
    {K M N K' M' N' : Type*} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup K'] [AddCommGroup M'] [AddCommGroup N'] [Module R K] [Module R M] [Module R N]
    [Module R K'] [Module R M'] [Module R N'] {ι : K →ₗ[R] M} {φ : M →ₗ[R] N}
    {ι' : K' →ₗ[R] M'} {φ' : M' →ₗ[R] N'} (lK : K →ₗ[R] K') (lM : M →ₗ[R] M')
    (lN : N →ₗ[R] N') [IsLocalizedModule S lM] [IsLocalizedModule S lN]
    (hι : Function.Injective ι) (hex : Function.Exact ι φ) (hι' : Function.Injective ι')
    (hφι' : ∀ y, φ' (ι' y) = 0) (h₁ : ∀ k, lM (ι k) = ι' (lK k))
    (h₂ : ∀ m, lN (φ m) = φ' (lM m)) (hu : ∀ s : S, IsUnit (algebraMap R (Module.End R K') s)) :
    IsLocalizedModule S lK where
  map_units := hu
  surj y := by
    obtain ⟨⟨m, s⟩, hm⟩ := IsLocalizedModule.surj S lM (ι' y)
    dsimp only at hm
    rw [Submonoid.smul_def] at hm
    have h0 : lN (φ m) = lN 0 := by
      rw [h₂, ← hm, map_zero, map_smul, hφι', smul_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    rw [smul_zero, Submonoid.smul_def, ← map_smul] at hc
    obtain ⟨k, hk⟩ := (hex _).mp hc
    refine ⟨⟨k, c * s⟩, hι' ?_⟩
    rw [← h₁, hk, Submonoid.smul_def, map_smul, map_smul, ← hm, smul_smul, Submonoid.coe_mul]
  exists_of_eq {k₁ k₂} h := by
    have : lM (ι k₁) = lM (ι k₂) := by rw [h₁, h₁, h]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) this
    refine ⟨c, hι ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul]
    exact hc
