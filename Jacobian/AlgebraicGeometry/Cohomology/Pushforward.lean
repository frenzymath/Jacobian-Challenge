import Jacobian.AlgebraicGeometry.Cohomology.Basic

/-!
# The scalar-compatible identification of baseField-zero cohomology with direct-image global sections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe coefficientUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (baseField : Type coefficientUniverse) [Field baseField] {scheme target : Scheme.{coefficientUniverse}} [scheme.Over (Spec (.of baseField))]
  [target.Over (Spec (.of baseField))]

/-- The structure maps `k →+* Γ(Y, ⊤)` and `k →+* Γ(X, ⊤)` of `k`-schemes are compatible with a
morphism `g : X ⟶ Y` of `k`-schemes. -/
lemma Hom.appTop_globalSectionsRingHom (morphism : scheme ⟶ target) [morphism.IsOver (Spec (.of baseField))] (scalar : baseField) :
    morphism.appTop (globalSectionsRingHom baseField (X := target) scalar) = globalSectionsRingHom baseField (X := scheme) scalar := by
  rw [globalSectionsRingHom, globalSectionsRingHom,
    ← (Hom.isOver_iff (Spec (.of baseField))).mp ‹morphism.IsOver _›, Scheme.Hom.comp_appTop]
  rfl

namespace Modules

/-- `H⁰(Y, g_* M) ≅ H⁰(X, M)`, both being global sections of `M`. -/
noncomputable def H.zeroPushforwardLinearEquiv (morphism : scheme ⟶ target) [morphism.IsOver (Spec (.of baseField))]
    (moduleSheaf : scheme.Modules) : ((pushforward morphism).obj moduleSheaf).H 0 ≃ₗ[baseField] moduleSheaf.H 0 :=
  ((H.zeroLinearEquiv ((pushforward morphism).obj moduleSheaf)).toAddEquiv.trans
    (H.zeroLinearEquiv moduleSheaf).symm.toAddEquiv).toLinearEquiv fun scalar element ↦ by
    let sectionValue : Γ(moduleSheaf, ⊤) := H.zeroLinearEquiv ((pushforward morphism).obj moduleSheaf) element
    have h₁ : H.zeroLinearEquiv ((pushforward morphism).obj moduleSheaf) (scalar • element) =
        morphism.appTop (globalSectionsRingHom baseField (X := target) scalar) • sectionValue :=
      (H.zeroLinearEquiv ((pushforward morphism).obj moduleSheaf)).map_smul (globalSectionsRingHom baseField scalar) element
    have h₂ : (H.zeroLinearEquiv moduleSheaf).symm (globalSectionsRingHom baseField (X := scheme) scalar • sectionValue) =
        scalar • (H.zeroLinearEquiv moduleSheaf).symm sectionValue :=
      (H.zeroLinearEquiv moduleSheaf).symm.map_smul _ _
    refine (congrArg (H.zeroLinearEquiv moduleSheaf).symm h₁).trans ?_
    rw [Hom.appTop_globalSectionsRingHom]
    exact h₂

omit [scheme.Over (Spec (.of baseField))] in
/-- The identification `H⁰(X, M) ≅ Γ(X, M)` is natural in `M`. -/
lemma H.zeroLinearEquiv_map {moduleSheaf targetSheaf : scheme.Modules} (coefficientMap : moduleSheaf ⟶ targetSheaf) (element : moduleSheaf.H 0) :
    H.zeroLinearEquiv targetSheaf (H.map coefficientMap 0 element) = coefficientMap.app ⊤ (H.zeroLinearEquiv moduleSheaf element) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    ((SheafOfModules.toSheaf scheme.ringCatSheaf).map coefficientMap) element).symm

/-- **Global sections of a pushforward.** `H⁰(Y, g_* M) ≅ H⁰(X, M)`, naturally in `M`, for a
morphism `g : X ⟶ Y` of `k`-schemes: both are the global sections of `M`. -/
noncomputable def pushforwardCompCohomologyFunctorZeroIso (morphism : scheme ⟶ target) [morphism.IsOver (Spec (.of baseField))] :
    pushforward morphism ⋙ cohomologyFunctor baseField 0 ≅ cohomologyFunctor baseField 0 :=
  NatIso.ofComponents (fun moduleSheaf ↦ (H.zeroPushforwardLinearEquiv baseField morphism moduleSheaf).toModuleIso) fun {moduleSheaf targetSheaf} coefficientMap ↦ by
    ext element
    refine (H.zeroLinearEquiv targetSheaf).injective ?_
    change H.zeroLinearEquiv targetSheaf ((H.zeroLinearEquiv targetSheaf).symm
      (H.zeroLinearEquiv ((pushforward morphism).obj targetSheaf) (H.map ((pushforward morphism).map coefficientMap) 0 element))) =
      H.zeroLinearEquiv targetSheaf (H.map coefficientMap 0 ((H.zeroLinearEquiv moduleSheaf).symm
        (H.zeroLinearEquiv ((pushforward morphism).obj moduleSheaf) element)))
    rw [H.zeroLinearEquiv_map, H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    rfl

end Modules

end AlgebraicGeometry.Scheme
