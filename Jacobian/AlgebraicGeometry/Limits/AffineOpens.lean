import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Affineness of open preimages at a finite stage

For an inverse limit with affine transition maps, an affine preimage of a
quasi-compact open is already affine at some later stage.
-/

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse
open CategoryTheory Limits
namespace AlgebraicGeometry
variable {stageIndex : Type schemeUniverse} [Category.{schemeUniverse} stageIndex]
  {diagram : stageIndex ⥤ Scheme.{schemeUniverse}} {cone : Cone diagram} (limit : IsLimit cone)
  [IsCofiltered stageIndex]
  [∀ {index otherIndex : stageIndex} (transition : index ⟶ otherIndex), IsAffineHom (diagram.map transition)]
  [∀ index, QuasiSeparatedSpace (diagram.obj index)]

include limit in
theorem exists_isAffineOpen_preimage {index : stageIndex} {openSubset : (diagram.obj index).Opens}
    (compact : IsCompact (openSubset : Set (diagram.obj index)))
    (affine : IsAffineOpen (cone.π.app index ⁻¹ᵁ openSubset)) :
    ∃ laterIndex : Over index, IsAffineOpen (diagram.map laterIndex.hom ⁻¹ᵁ openSubset) := by
  have (laterIndex : Over index) : CompactSpace ((opensDiagram diagram index openSubset).obj laterIndex) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ openSubset.2 compact)
  have (laterIndex : Over index) : QuasiSeparatedSpace ((opensDiagram diagram index openSubset).obj laterIndex) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (diagram.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone diagram cone index openSubset).pt := affine
  exact Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone diagram cone limit index openSubset)

end AlgebraicGeometry
