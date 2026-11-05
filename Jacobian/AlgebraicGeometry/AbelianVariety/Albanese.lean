import Jacobian.AlgebraicGeometry.AbelianVariety.Basic

/-!
# The Albanese universal property

A specified normalized map from a pointed scheme to an abelian variety is
Albanese when every normalized map to an abelian variety factors uniquely through
it as a group homomorphism. This property implies uniqueness of the target and
functoriality for maps preserving the point; it does not assert existence.

The source need not be a smooth proper curve. Only the universal property is
used in the uniqueness and composition arguments.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The universal property of a specified Albanese map from a pointed scheme. -/
def IsAlbanese {baseField : Type u} [Field baseField]
    {sourceScheme : Over (Spec (.of baseField))}
    (point : 𝟙_ (Over (Spec (.of baseField))) ⟶ sourceScheme)
    (variety : AbelianVariety baseField) (albaneseMap : sourceScheme ⟶ variety.group.X) : Prop :=
  point ≫ albaneseMap = η[variety.group.X] ∧
    ∀ (target : AbelianVariety baseField) (morphism : sourceScheme ⟶ target.group.X),
      point ≫ morphism = η[target.group.X] →
        ∃! groupMap : variety.group ⟶ target.group,
          albaneseMap ≫ groupMap.hom.hom.hom = morphism

namespace IsAlbanese

variable {baseField : Type u} [Field baseField]
  {sourceScheme : Over (Spec (.of baseField))}
  {point : 𝟙_ (Over (Spec (.of baseField))) ⟶ sourceScheme}
  {variety : AbelianVariety baseField} {albaneseMap : sourceScheme ⟶ variety.group.X}

private theorem normalized_comp (property : IsAlbanese point variety albaneseMap)
    (target : AbelianVariety baseField) (groupMap : variety.group ⟶ target.group) :
    point ≫ (albaneseMap ≫ groupMap.hom.hom.hom) = η[target.group.X] := by
  rw [← Category.assoc, property.1]
  simp

/-- Group homomorphisms out of an Albanese variety are determined on its source. -/
theorem hom_ext (property : IsAlbanese point variety albaneseMap)
    (target : AbelianVariety baseField) (first second : variety.group ⟶ target.group)
    (compatibility : albaneseMap ≫ first.hom.hom.hom = albaneseMap ≫ second.hom.hom.hom) :
    first = second := by
  have normalized := normalized_comp property target first
  exact (property.2 target (albaneseMap ≫ first.hom.hom.hom) normalized).unique
    rfl compatibility.symm

/-- Two Albanese maps from the same pointed scheme have a unique compatible group isomorphism. -/
theorem existsUnique_iso (property : IsAlbanese point variety albaneseMap)
    (target : AbelianVariety baseField) (targetMap : sourceScheme ⟶ target.group.X)
    (targetProperty : IsAlbanese point target targetMap) :
    ∃! comparison : variety.group ≅ target.group,
      albaneseMap ≫ comparison.hom.hom.hom.hom = targetMap := by
  obtain ⟨forward, forward_fac, forward_unique⟩ := property.2 target targetMap targetProperty.1
  obtain ⟨backward, backward_fac, backward_unique⟩ :=
    targetProperty.2 variety albaneseMap property.1
  have forward_backward : forward ≫ backward = 𝟙 variety.group := by
    apply property.hom_ext variety
    change albaneseMap ≫ forward.hom.hom.hom ≫ backward.hom.hom.hom = albaneseMap
    calc
      (albaneseMap ≫ forward.hom.hom.hom) ≫ backward.hom.hom.hom =
          targetMap ≫ backward.hom.hom.hom :=
        congrArg (fun morphism ↦ morphism ≫ backward.hom.hom.hom) forward_fac
      _ = albaneseMap := backward_fac
  have backward_forward : backward ≫ forward = 𝟙 target.group := by
    apply targetProperty.hom_ext target
    change targetMap ≫ backward.hom.hom.hom ≫ forward.hom.hom.hom = targetMap
    calc
      (targetMap ≫ backward.hom.hom.hom) ≫ forward.hom.hom.hom =
          albaneseMap ≫ forward.hom.hom.hom :=
        congrArg (fun morphism ↦ morphism ≫ forward.hom.hom.hom) backward_fac
      _ = targetMap := forward_fac
  let comparison : variety.group ≅ target.group :=
    { hom := forward
      inv := backward
      hom_inv_id := forward_backward
      inv_hom_id := backward_forward }
  refine ⟨comparison, forward_fac, ?_⟩
  intro other compatibility
  apply Iso.ext
  exact forward_unique other.hom compatibility

/-- A point-preserving map to a normalized target induces a unique Albanese homomorphism. -/
theorem existsUnique_map (property : IsAlbanese point variety albaneseMap)
    {targetScheme : Over (Spec (.of baseField))}
    (targetPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ targetScheme)
    (target : AbelianVariety baseField) (targetMap : targetScheme ⟶ target.group.X)
    (normalized : targetPoint ≫ targetMap = η[target.group.X])
    (morphism : sourceScheme ⟶ targetScheme) (point_map : point ≫ morphism = targetPoint) :
    ∃! groupMap : variety.group ⟶ target.group,
      albaneseMap ≫ groupMap.hom.hom.hom = morphism ≫ targetMap := by
  apply property.2 target (morphism ≫ targetMap)
  rw [← Category.assoc, point_map, normalized]

/-- An Albanese endomorphism fixing the specified map is the identity. -/
theorem eq_id (property : IsAlbanese point variety albaneseMap)
    (groupMap : variety.group ⟶ variety.group)
    (compatibility : albaneseMap ≫ groupMap.hom.hom.hom = albaneseMap) :
    groupMap = 𝟙 variety.group :=
  (property.2 variety albaneseMap property.1).unique compatibility (by simp)

/-- Homomorphisms compatible with successive source maps compose compatibly. -/
theorem comp_eq (property : IsAlbanese point variety albaneseMap)
    {middleScheme targetScheme : Over (Spec (.of baseField))}
    (middleVariety targetVariety : AbelianVariety baseField)
    (middleMap : middleScheme ⟶ middleVariety.group.X)
    (targetMap : targetScheme ⟶ targetVariety.group.X)
    (firstSchemeMap : sourceScheme ⟶ middleScheme)
    (secondSchemeMap : middleScheme ⟶ targetScheme)
    (first : variety.group ⟶ middleVariety.group)
    (second : middleVariety.group ⟶ targetVariety.group)
    (total : variety.group ⟶ targetVariety.group)
    (first_fac : albaneseMap ≫ first.hom.hom.hom = firstSchemeMap ≫ middleMap)
    (second_fac : middleMap ≫ second.hom.hom.hom = secondSchemeMap ≫ targetMap)
    (total_fac : albaneseMap ≫ total.hom.hom.hom =
      (firstSchemeMap ≫ secondSchemeMap) ≫ targetMap) : first ≫ second = total := by
  apply property.hom_ext targetVariety
  calc
    albaneseMap ≫ (first ≫ second).hom.hom.hom =
        (albaneseMap ≫ first.hom.hom.hom) ≫ second.hom.hom.hom := by simp [Category.assoc]
    _ = (firstSchemeMap ≫ middleMap) ≫ second.hom.hom.hom :=
      congrArg (fun morphism ↦ morphism ≫ second.hom.hom.hom) first_fac
    _ = firstSchemeMap ≫ (middleMap ≫ second.hom.hom.hom) := Category.assoc _ _ _
    _ = firstSchemeMap ≫ (secondSchemeMap ≫ targetMap) :=
      congrArg (fun morphism ↦ firstSchemeMap ≫ morphism) second_fac
    _ = (firstSchemeMap ≫ secondSchemeMap) ≫ targetMap := (Category.assoc _ _ _).symm
    _ = albaneseMap ≫ total.hom.hom.hom := total_fac.symm

end IsAlbanese
end AlgebraicGeometry
