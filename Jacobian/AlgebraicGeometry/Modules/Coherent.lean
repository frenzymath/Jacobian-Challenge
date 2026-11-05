import Jacobian.Algebra.Module.LocalizedModule.Kernel
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.RestrictionLimits
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Kernels of coherent module sheaves

Kernels of morphisms of quasi-coherent module sheaves are quasi-coherent. On a
locally Noetherian scheme, a kernel with finitely presented source is finitely
presented, since its sections on an affine open form a submodule of a finite
module over a Noetherian ring.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec R`, the kernel of a morphism of localizing modules is localizing: its sections are the
kernels of the sections, and localization is exact. -/
theorem isLocalizing_kernel {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (hM : IsLocalizing (modulesSpecToSheaf.obj M)) (hN : IsLocalizing (modulesSpecToSheaf.obj N))
    (φ : M ⟶ N) : IsLocalizing (modulesSpecToSheaf.obj (kernel φ)) := by
  intro f
  have := hM f
  have := hN f
  let D := PrimeSpectrum.basicOpen f
  let ι (U : (Spec R).Opens) := ((modulesSpecToSheaf.map (kernel.ι φ)).hom.app (op U)).hom
  let φ' (U : (Spec R).Opens) := ((modulesSpecToSheaf.map φ).hom.app (op U)).hom
  have hinj (U : (Spec R).Opens) : Function.Injective (ι U) := injective_kernelι_app φ U
  have hex (U : (Spec R).Opens) : Function.Exact (ι U) (φ' U) := fun y ↦
    (Set.ext_iff.mp (range_kernelι_app φ U) y).symm
  have hu : ∀ s : Submonoid.powers f, IsUnit (algebraMap R
      (Module.End R ((modulesSpecToSheaf.obj (kernel φ)).obj.obj (op D))) s) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (isUnit_algebraMap_end_of_le_basicOpen (M := kernel φ) f le_rfl).pow n
  have h₁ (k : (modulesSpecToSheaf.obj (kernel φ)).obj.obj (op ⊤)) :
      ((modulesSpecToSheaf.obj M).obj.map D.leTop.op).hom (ι ⊤ k) =
        ι D (((modulesSpecToSheaf.obj (kernel φ)).obj.map D.leTop.op).hom k) := by
    have := (modulesSpecToSheaf.map (kernel.ι φ)).hom.naturality D.leTop.op
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) k).symm
  have h₂ (k : (modulesSpecToSheaf.obj M).obj.obj (op ⊤)) :
      ((modulesSpecToSheaf.obj N).obj.map D.leTop.op).hom (φ' ⊤ k) =
        φ' D (((modulesSpecToSheaf.obj M).obj.map D.leTop.op).hom k) := by
    have := (modulesSpecToSheaf.map φ).hom.naturality D.leTop.op
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) k).symm
  exact IsLocalizedModule.of_injective_of_exact (.powers f) _ _ _ (hinj ⊤) (hex ⊤) (hinj D)
    (fun y ↦ (hex D _).mpr ⟨y, rfl⟩) h₁ h₂ hu


variable {X : Scheme.{u}}

/-- **The kernel of a morphism of quasi-coherent modules is quasi-coherent.** On an affine open
`U`, restriction along `Spec Γ(X, U) ⟶ X` commutes with kernels, and on `Spec Γ(X, U)` the kernel of
a morphism of localizing modules is localizing (`isLocalizing_kernel`). -/
theorem isQuasicoherent_kernel {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (kernel φ) := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top (kernel φ)
    (fun U : X.affineOpens ↦ U.2.fromSpec)
    (by simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top X)
    fun U ↦ ?_
  have : IsIso (kernel ((restrictFunctor U.2.fromSpec).map φ)).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mpr (isLocalizing_kernel
      ((isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance)
      ((isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance) _)
  let e := PreservesKernel.iso (restrictFunctor U.2.fromSpec) φ
  haveI : IsIso (C := SheafOfModules.{u} (Spec Γ(X, U.1)).ringCatSheaf) e.inv :=
    (inferInstance : IsIso e.inv)
  exact (presentationOfIsIsoFromTildeΓ _).ofIsIso e.inv


/-- A kernel of coherent sheaves on a locally Noetherian scheme is coherent. -/
theorem isFinitePresentation_kernel [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsFinitePresentation] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (kernel φ).IsFinitePresentation := by
  letI := isQuasicoherent_kernel φ
  refine (isFinitePresentation_iff_forall_isAffineOpen (kernel φ)).mpr ?_
  intro U hU
  letI := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := finitePresentation_sections_of_isFinitePresentation M hU
  letI : _root_.IsNoetherian Γ(X, U) Γ(M, U) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  letI : Module.Finite Γ(X, U) Γ(kernel φ, U) :=
    Module.Finite.of_injective (Hom.appₗ (kernel.ι φ) U) (injective_kernelι_app φ U)
  exact Module.finitePresentation_of_finite Γ(X, U) Γ(kernel φ, U)

end AlgebraicGeometry.Scheme.Modules
