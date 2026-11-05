import Jacobian.AlgebraicGeometry.Modules.HomSection
import Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import Jacobian.AlgebraicGeometry.Modules.PullbackSections
import Jacobian.AlgebraicGeometry.Modules.TensorInvertible
import Jacobian.AlgebraicGeometry.Modules.TensorSection

/-!
# Tensor pencils of sections

Two sections of each of two line bundles define a section of their external
tensor product. The pullback formula below uses the monoidal comparison of the
actual pullback functor, so it applies to both residue fibres and endpoints.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open CategoryTheory.Limits (zero_comp comp_zero)
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

variable {source parameter family test : Scheme.{u}}

/-- The external tensor product in which a pencil takes values. -/
abbrev pencilLine (sourceProjection : family ⟶ source)
    (parameterProjection : family ⟶ parameter)
    (sourceLine : source.Modules) (parameterLine : parameter.Modules) : family.Modules :=
  (Scheme.Modules.pullback sourceProjection).obj sourceLine ⊗
    (Scheme.Modules.pullback parameterProjection).obj parameterLine

/-- The unit comparison used to form the two tensor-product sections. -/
def pencilSourceIso (sourceProjection : family ⟶ source)
    (parameterProjection : family ⟶ parameter) :
    unit family ≅
      (Scheme.Modules.pullback sourceProjection).obj (unit source) ⊗
        (Scheme.Modules.pullback parameterProjection).obj (unit parameter) :=
  (λ_ (unit family)).symm ≪≫
    ((pullbackObjUnitIso sourceProjection).symm ⊗ᵢ
      (pullbackObjUnitIso parameterProjection).symm)

/-- The section given by the sum of the two external tensor products. -/
def pencilSection (sourceProjection : family ⟶ source)
    (parameterProjection : family ⟶ parameter)
    {sourceLine : source.Modules} {parameterLine : parameter.Modules}
    (firstSection secondSection : unit source ⟶ sourceLine)
    (firstCoefficient secondCoefficient : unit parameter ⟶ parameterLine) :
    unit family ⟶ pencilLine sourceProjection parameterProjection sourceLine parameterLine :=
  (pencilSourceIso sourceProjection parameterProjection).hom ≫
    ((Scheme.Modules.pullback sourceProjection).map firstSection ⊗ₘ
        (Scheme.Modules.pullback parameterProjection).map firstCoefficient +
      (Scheme.Modules.pullback sourceProjection).map secondSection ⊗ₘ
        (Scheme.Modules.pullback parameterProjection).map secondCoefficient)

/-- The source comparison after further pullback of a pencil. -/
def pulledSourceIso (restriction : test ⟶ family)
    (sourceProjection : family ⟶ source) (parameterProjection : family ⟶ parameter) :
    (Scheme.Modules.pullback restriction).obj (unit family) ≅
      (Scheme.Modules.pullback restriction).obj
          ((Scheme.Modules.pullback sourceProjection).obj (unit source)) ⊗
        (Scheme.Modules.pullback restriction).obj
          ((Scheme.Modules.pullback parameterProjection).obj (unit parameter)) :=
  (Scheme.Modules.pullback restriction).mapIso
      (pencilSourceIso sourceProjection parameterProjection) ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback restriction) _ _).symm

/-- Pullback of the actual pencil is the sum of the pulled tensor sections. -/
theorem pulledSourceIso_inv_comp (restriction : test ⟶ family)
    (sourceProjection : family ⟶ source) (parameterProjection : family ⟶ parameter)
    {sourceLine : source.Modules} {parameterLine : parameter.Modules}
    (firstSection secondSection : unit source ⟶ sourceLine)
    (firstCoefficient secondCoefficient : unit parameter ⟶ parameterLine) :
    (pulledSourceIso restriction sourceProjection parameterProjection).inv ≫
      (Scheme.Modules.pullback restriction).map
        (pencilSection sourceProjection parameterProjection
          firstSection secondSection firstCoefficient secondCoefficient) ≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback restriction)
          ((Scheme.Modules.pullback sourceProjection).obj sourceLine)
          ((Scheme.Modules.pullback parameterProjection).obj parameterLine)).inv =
      (Scheme.Modules.pullback restriction).map
          ((Scheme.Modules.pullback sourceProjection).map firstSection) ⊗ₘ
        (Scheme.Modules.pullback restriction).map
          ((Scheme.Modules.pullback parameterProjection).map firstCoefficient) +
      (Scheme.Modules.pullback restriction).map
          ((Scheme.Modules.pullback sourceProjection).map secondSection) ⊗ₘ
        (Scheme.Modules.pullback restriction).map
          ((Scheme.Modules.pullback parameterProjection).map secondCoefficient) := by
  simp only [pulledSourceIso, pencilSection, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [← (Scheme.Modules.pullback restriction).map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_add]
  rw [Functor.Monoidal.map_tensor, Functor.Monoidal.map_tensor]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    Functor.Monoidal.μ_δ, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.δ_μ_assoc, Category.comp_id]

/-- The global section of a pencil is the sum of its two elementary tensors. -/
theorem pencilSection_app_one (sourceProjection : family ⟶ source)
    (parameterProjection : family ⟶ parameter)
    {sourceLine : source.Modules} {parameterLine : parameter.Modules}
    (firstSection secondSection : unit source ⟶ sourceLine)
    (firstCoefficient secondCoefficient : unit parameter ⟶ parameterLine) :
    (pencilSection sourceProjection parameterProjection firstSection secondSection
      firstCoefficient secondCoefficient).app ⊤ (1 : Γ(family, ⊤)) =
      tmulSection
          (pullbackΓ sourceProjection sourceLine (firstSection.app ⊤ (1 : Γ(source, ⊤))))
          (pullbackΓ parameterProjection parameterLine
            (firstCoefficient.app ⊤ (1 : Γ(parameter, ⊤)))) +
        tmulSection
          (pullbackΓ sourceProjection sourceLine (secondSection.app ⊤ (1 : Γ(source, ⊤))))
          (pullbackΓ parameterProjection parameterLine
            (secondCoefficient.app ⊤ (1 : Γ(parameter, ⊤)))) := by
  have unitValue {domain codomain : Scheme.{u}} (morphism : domain ⟶ codomain) :
      (pullbackObjUnitIso morphism).inv.app ⊤ (1 : Γ(domain, ⊤)) =
        pullbackΓ morphism (unit codomain) (1 : Γ(codomain, ⊤)) := by
    rw [pullbackΓ_apply]
    exact (pullbackSection_one_eq morphism).symm
  have sumValue (firstMap secondMap :
      (Scheme.Modules.pullback sourceProjection).obj (unit source) ⊗
          (Scheme.Modules.pullback parameterProjection).obj (unit parameter) ⟶
        pencilLine sourceProjection parameterProjection sourceLine parameterLine)
      (element : Γ((Scheme.Modules.pullback sourceProjection).obj (unit source) ⊗
        (Scheme.Modules.pullback parameterProjection).obj (unit parameter), ⊤)) :
      (firstMap + secondMap).app ⊤ element =
        firstMap.app ⊤ element + secondMap.app ⊤ element := rfl
  simp only [pencilSection, pencilSourceIso, Iso.trans_hom, Iso.symm_hom,
    Hom.comp_app, ConcreteCategory.comp_apply, tensorIso_hom,
    leftUnitor_inv_app, tensorHom_app_tmulSection, unitValue, sumValue,
    pullbackΓ_naturality]
  change tmulSection
      (((Scheme.Modules.pullback sourceProjection).map firstSection).app ⊤
        ((pullbackObjUnitIso sourceProjection).inv.app ⊤ (1 : Γ(family, ⊤))))
      (pullbackΓ parameterProjection parameterLine
        (firstCoefficient.app ⊤ (1 : Γ(parameter, ⊤)))) +
    tmulSection
      (((Scheme.Modules.pullback sourceProjection).map secondSection).app ⊤
        ((pullbackObjUnitIso sourceProjection).inv.app ⊤ (1 : Γ(family, ⊤))))
      (pullbackΓ parameterProjection parameterLine
        (secondCoefficient.app ⊤ (1 : Γ(parameter, ⊤)))) = _
  simp only [unitValue, pullbackΓ_naturality]

end AlgebraicGeometry.SectionPencil
