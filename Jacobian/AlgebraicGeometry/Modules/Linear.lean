import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Mathlib.CategoryTheory.Center.Linear

/-!
# Linear structures on module sheaves

Global functions act centrally on the category of module sheaves. A ring map
into the global functions therefore makes this category linear over its source.
-/

noncomputable section

universe coefficientUniverse schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (scheme : Scheme.{schemeUniverse})

/-- Multiplication by global functions is a central endomorphism of module sheaves. -/
def globalSectionsCenter : Γ(scheme, ⊤) →+* CatCenter scheme.Modules where
  toFun scalar :=
    { app moduleSheaf := moduleSheaf.smulHom scalar
      naturality _ _ coefficientMap := (smulHom_naturality coefficientMap scalar).symm }
  map_one' := NatTrans.ext (funext fun moduleSheaf ↦ smulHom_one moduleSheaf)
  map_mul' scalar otherScalar :=
    NatTrans.ext (funext fun moduleSheaf ↦ smulHom_mul moduleSheaf scalar otherScalar)
  map_zero' := NatTrans.ext (funext fun moduleSheaf ↦ smulHom_zero moduleSheaf)
  map_add' scalar otherScalar :=
    NatTrans.ext (funext fun moduleSheaf ↦ smulHom_add moduleSheaf scalar otherScalar)

/-- A ring acting on global functions acts linearly on the category of module sheaves. -/
@[instance_reducible]
def linearOfRingHom {coefficientRing : Type coefficientUniverse} [CommRing coefficientRing]
    (scalarMap : coefficientRing →+* Γ(scheme, ⊤)) : Linear coefficientRing scheme.Modules :=
  Linear.ofRingMorphism ((globalSectionsCenter scheme).comp scalarMap)

/-- Scalar multiplication on an identity is multiplication by the corresponding global function. -/
theorem linearOfRingHom_smul_id {coefficientRing : Type coefficientUniverse}
    [CommRing coefficientRing] (scalarMap : coefficientRing →+* Γ(scheme, ⊤))
    (moduleSheaf : scheme.Modules) (scalar : coefficientRing) :
    letI := linearOfRingHom scheme scalarMap
    scalar • 𝟙 moduleSheaf = moduleSheaf.smulHom (scalarMap scalar) := by
  change moduleSheaf.smulHom (scalarMap scalar) ≫ 𝟙 moduleSheaf = _
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Modules
