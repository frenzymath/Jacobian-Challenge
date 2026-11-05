import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Jacobian.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Jacobian.AlgebraicGeometry.Cohomology.Pushforward
import Jacobian.Topology.Sheaves.Cohomology

/-!
# Cohomology along affine morphisms

Pushforward along an affine morphism preserves the cohomology of quasi-coherent
modules. The comparison is natural in the module and respects its scalar action.
It therefore preserves cohomology dimensions and Euler characteristics over a field.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe coefficientUniverse

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme target : Scheme.{coefficientUniverse}}

/-- An affine morphism preserves the cohomology of abelian sheaves that are
Čech-acyclic on affine opens. -/
theorem nonempty_functorH_iso_pushforwardAb_of_isAffineHom (morphism : scheme ⟶ target)
    [IsAffineHom morphism] (degree : ℕ) :
    Nonempty ((cechAcyclicOnAffines scheme).ι ⋙
        Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology scheme) degree ≅
      (cechAcyclicOnAffines scheme).ι ⋙ TopCat.Sheaf.pushforwardAb morphism.base ⋙
        Sheaf.functorH.{coefficientUniverse} (Opens.grothendieckTopology target) degree) :=
  TopCat.Sheaf.nonempty_functorH_iso_pushforwardAb morphism.base (cechAcyclicOnAffines scheme)
    (fun _ acyclic ↦ cechAcyclicOnAffines_under_cokernel acyclic)
    (fun _ shortExact acyclic ↦
      TopCat.Sheaf.shortExact_map_pushforward shortExact target.isBasis_affineOpens
        fun _ affineOpen ↦ surjective_app_of_cechAcyclicOnAffines shortExact acyclic
          (IsAffineOpen.preimage affineOpen morphism)) degree

variable (baseField : Type coefficientUniverse) [Field baseField]
  [scheme.Over (Spec (.of baseField))] [target.Over (Spec (.of baseField))]

/-- Cohomology of quasi-coherent modules is naturally unchanged by affine
pushforward, as a vector space over the base field. -/
theorem nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom
    (morphism : scheme ⟶ target) [morphism.IsOver (Spec (.of baseField))]
    [IsAffineHom morphism] (degree : ℕ) :
    Nonempty ((SheafOfModules.isQuasicoherent scheme.ringCatSheaf).ι ⋙
        cohomologyFunctor baseField degree ≅
      (SheafOfModules.isQuasicoherent scheme.ringCatSheaf).ι ⋙ pushforward morphism ⋙
        cohomologyFunctor baseField degree) := by
  obtain ⟨comparison⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom morphism degree
  let quasicoherent := SheafOfModules.isQuasicoherent scheme.ringCatSheaf
  let underlying (moduleSheaf : quasicoherent.FullSubcategory) :
      (cechAcyclicOnAffines scheme).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf scheme.ringCatSheaf).obj moduleSheaf.obj,
      have : SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf.obj :=
        moduleSheaf.property
      cechAcyclicOnAffines_of_isQuasicoherent moduleSheaf.obj⟩
  have naturality {moduleSheaf targetSheaf : quasicoherent.FullSubcategory}
      (coefficientMap : moduleSheaf ⟶ targetSheaf)
      (cohomologyClass : Sheaf.H
        ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj moduleSheaf.obj) degree) :
      comparison.hom.app (underlying targetSheaf)
          (Sheaf.H.map ((SheafOfModules.toSheaf scheme.ringCatSheaf).map coefficientMap.hom)
            degree cohomologyClass) =
        Sheaf.H.map ((TopCat.Sheaf.pushforwardAb morphism.base).map
          ((SheafOfModules.toSheaf scheme.ringCatSheaf).map coefficientMap.hom)) degree
          (comparison.hom.app (underlying moduleSheaf) cohomologyClass) := by
    have naturalitySquare := NatTrans.naturality_apply comparison.hom (ObjectProperty.homMk
      ((SheafOfModules.toSheaf scheme.ringCatSheaf).map coefficientMap.hom) :
        underlying moduleSheaf ⟶ underlying targetSheaf) cohomologyClass
    exact naturalitySquare
  have scalarCompatibility (moduleSheaf : quasicoherent.FullSubcategory) (scalar : baseField)
      (cohomologyClass : Sheaf.H
        ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj moduleSheaf.obj) degree) :
      comparison.hom.app (underlying moduleSheaf)
          (Sheaf.H.map ((SheafOfModules.toSheaf scheme.ringCatSheaf).map
            (smulHom moduleSheaf.obj (globalSectionsRingHom baseField scalar)))
              degree cohomologyClass) =
        Sheaf.H.map ((SheafOfModules.toSheaf target.ringCatSheaf).map
          (smulHom ((pushforward morphism).obj moduleSheaf.obj)
            (globalSectionsRingHom baseField scalar))) degree
          (comparison.hom.app (underlying moduleSheaf) cohomologyClass) := by
    rw [← Hom.appTop_globalSectionsRingHom baseField morphism scalar,
      ← pushforward_map_smulHom]
    exact naturality (ObjectProperty.homMk
      (smulHom moduleSheaf.obj (morphism.appTop (globalSectionsRingHom baseField scalar))))
        cohomologyClass
  refine ⟨NatIso.ofComponents (fun moduleSheaf ↦ LinearEquiv.toModuleIso
    ({ toAddEquiv := (comparison.app (underlying moduleSheaf)).addCommGroupIsoToAddEquiv
       map_smul' := fun scalar cohomologyClass ↦ ?_ } :
      (quasicoherent.ι ⋙ cohomologyFunctor baseField degree).obj moduleSheaf ≃ₗ[baseField]
        (quasicoherent.ι ⋙ pushforward morphism ⋙
          cohomologyFunctor baseField degree).obj moduleSheaf))
    fun {moduleSheaf targetSheaf} coefficientMap ↦ ?_⟩
  · exact scalarCompatibility moduleSheaf scalar cohomologyClass
  · ext cohomologyClass
    exact naturality coefficientMap cohomologyClass

/-- An affine morphism preserves every cohomology dimension of a quasi-coherent module. -/
theorem finrankH_pushforward_of_isAffineHom (morphism : scheme ⟶ target)
    [morphism.IsOver (Spec (.of baseField))] [IsAffineHom morphism]
    (moduleSheaf : scheme.Modules) [moduleSheaf.IsQuasicoherent] (degree : ℕ) :
    ((pushforward morphism).obj moduleSheaf).finrankH baseField degree =
      moduleSheaf.finrankH baseField degree := by
  obtain ⟨comparison⟩ :=
    nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom baseField morphism degree
  exact ((comparison.app ⟨moduleSheaf, inferInstance⟩).toLinearEquiv.finrank_eq).symm

/-- An affine morphism preserves the Euler characteristic of a quasi-coherent module. -/
theorem eulerChar_pushforward_of_isAffineHom (morphism : scheme ⟶ target)
    [morphism.IsOver (Spec (.of baseField))] [IsAffineHom morphism]
    (moduleSheaf : scheme.Modules) [moduleSheaf.IsQuasicoherent] :
    ((pushforward morphism).obj moduleSheaf).eulerChar baseField =
      moduleSheaf.eulerChar baseField := by
  simp only [eulerChar, finrankH_pushforward_of_isAffineHom baseField morphism moduleSheaf]

end AlgebraicGeometry.Scheme.Modules
