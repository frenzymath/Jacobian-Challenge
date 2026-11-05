import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Images and open subschemes of geometrically irreducible schemes

Geometric irreducibility descends along a surjective morphism. A nonempty
open subscheme of a geometrically irreducible scheme over a field is again
geometrically irreducible. Conversely, geometric irreducibility extends from
a dense open subscheme over a field. Geometric irreducibility also implies geometric
connectedness, with no openness hypothesis on the structure morphism.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Every geometrically irreducible morphism is geometrically connected. -/
instance (priority := low) GeometricallyIrreducible.geometricallyConnected
    {source target : Scheme.{u}} (morphism : source ⟶ target)
    [GeometricallyIrreducible morphism] : GeometricallyConnected morphism := by
  refine ⟨fun field _ point fiber first second square ↦ ?_⟩
  have : IrreducibleSpace fiber :=
    GeometricallyIrreducible.geometrically_irreducibleSpace point first second square
  infer_instance

/-- Geometric irreducibility descends along a surjective morphism of schemes. -/
lemma GeometricallyIrreducible.of_surjective {source target base : Scheme.{u}}
    (sourceToTarget : source ⟶ target) (targetToBase : target ⟶ base)
    [Surjective sourceToTarget] [GeometricallyIrreducible (sourceToTarget ≫ targetToBase)] :
    GeometricallyIrreducible targetToBase := by
  refine ⟨fun field _ point fiber first second square ↦ ?_⟩
  have compositeSquare : IsPullback (pullback.fst sourceToTarget first)
      (pullback.snd sourceToTarget first ≫ second) (sourceToTarget ≫ targetToBase) point :=
    (IsPullback.of_hasPullback sourceToTarget first).paste_vert square
  have : IrreducibleSpace (pullback sourceToTarget first : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ compositeSquare
  exact Function.Surjective.irreducibleSpace (pullback.snd sourceToTarget first).continuous
    (pullback.snd sourceToTarget first).surjective

/-- A nonempty open subscheme of a geometrically irreducible scheme over a
field is geometrically irreducible over that field. -/
lemma GeometricallyIrreducible.comp_of_isOpenImmersion {field : Type u} [Field field]
    {source target : Scheme.{u}} (immersion : source ⟶ target) [IsOpenImmersion immersion]
    [Nonempty source] (structureMap : target ⟶ Spec (.of field))
    [GeometricallyIrreducible structureMap] :
    GeometricallyIrreducible (immersion ≫ structureMap) := by
  have : Surjective (immersion ≫ structureMap) :=
    ⟨fun point ↦ ⟨Classical.choice ‹Nonempty source›, Subsingleton.elim _ point⟩⟩
  infer_instance

/-- Geometric irreducibility over a field extends from a dense open subscheme. -/
lemma GeometricallyIrreducible.of_dense_open {field : Type u} [Field field]
    {source target : Scheme.{u}} (immersion : source ⟶ target) [IsOpenImmersion immersion]
    (structureMap : target ⟶ Spec (.of field)) (denseRange : DenseRange immersion)
    [GeometricallyIrreducible (immersion ≫ structureMap)] :
    GeometricallyIrreducible structureMap := by
  refine ⟨fun extensionField _ point fiber first second square ↦ ?_⟩
  have compositeSquare : IsPullback (pullback.fst immersion first)
      (pullback.snd immersion first ≫ second) (immersion ≫ structureMap) point :=
    (IsPullback.of_hasPullback immersion first).paste_vert square
  letI : IrreducibleSpace (pullback immersion first : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ compositeSquare
  letI : UniversallyOpen first := MorphismProperty.of_isPullback square.flip inferInstance
  have denseImage : Dense (Set.range (pullback.snd immersion first)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    exact (show Dense (Set.range immersion) from denseRange).preimage first.isOpenMap
  have irreducibleImage : IsIrreducible (Set.range (pullback.snd immersion first)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (pullback immersion first : Scheme.{u})).image
        (pullback.snd immersion first) (pullback.snd immersion first).continuous.continuousOn
  apply (irreducibleSpace_def fiber).mpr
  simpa only [denseImage.closure_eq, Set.top_eq_univ] using irreducibleImage.closure

end AlgebraicGeometry
