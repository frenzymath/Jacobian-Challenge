import Jacobian.AlgebraicGeometry.AbelianVariety.Albanese
import Jacobian.AlgebraicGeometry.Group.Rigidity

/-!
# The Albanese universal property for scheme morphisms

The universal property for group homomorphisms also gives uniqueness among
all scheme morphisms to a smooth proper geometrically irreducible group scheme.
Such a target is commutative, and any competing normalized factorization is a
group homomorphism by rigidity. No geometric hypothesis on the pointed source
is needed beyond the specified Albanese property.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry.IsAlbanese

/-- Normalized maps factor uniquely through an Albanese map even when competing
factorizations are arbitrary scheme morphisms rather than group homomorphisms. -/
theorem existsUnique_schemeMap
    {baseField : Type u} [Field baseField]
    {source : Over (Spec (.of baseField))}
    {point : 𝟙_ (Over (Spec (.of baseField))) ⟶ source}
    {variety : AbelianVariety baseField}
    {albaneseMap : source ⟶ variety.group.X}
    (property : IsAlbanese point variety albaneseMap)
    {target : Over (Spec (.of baseField))}
    [Smooth target.hom] [IsProper target.hom] [GrpObj target]
    [GeometricallyIrreducible target.hom]
    (morphism : source ⟶ target) (normalized : point ≫ morphism = η[target]) :
    ∃! factorization : variety.group.X ⟶ target,
      morphism = albaneseMap ≫ factorization := by
  letI : IsCommMonObj target :=
    isCommMonObj_of_isProper_of_smooth_of_geometricallyIrreducible target
  let targetVariety : AbelianVariety baseField := ⟨CommGrp.mk target⟩
  obtain ⟨factorization, factorization_eq, unique⟩ :=
    property.2 targetVariety morphism normalized
  refine ⟨factorization.hom.hom.hom, factorization_eq.symm, ?_⟩
  intro other other_eq
  have pointed : η[variety.group.X] ≫ other = η[target] := by
    rw [← property.1, Category.assoc, ← other_eq, normalized]
  letI : GeometricallyIntegral variety.group.X.hom :=
    Smooth.geometricallyIntegral variety.group.X.hom
  letI : IsMonHom other :=
    isMonHom_of_isProper_of_geometricallyIntegral other pointed
  let otherGroupMap : variety.group ⟶ targetVariety.group := ⟨Grp.homMk other⟩
  exact congrArg
    (fun comparison : variety.group ⟶ targetVariety.group ↦ comparison.hom.hom.hom)
    (unique otherGroupMap other_eq.symm)

end AlgebraicGeometry.IsAlbanese
