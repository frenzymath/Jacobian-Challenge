module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Jacobians in algebraic geometry, with field base change (`sorry` version)

This is the `sorry`-based sibling of the `def_wanted` blueprint: every "wanted" declaration is a real
declaration with a `sorry` placeholder, so it compiles on Mathlib master without any `*_wanted`
machinery. The base-change scaffolding (`baseChange`, the stability instances, `idIso`, `compIso`,
the helper instances, and the derivation of `congr` from `Jacobian.functor`) is genuinely proved;
only the genuinely-missing pieces are `sorry`.

The functoriality of the Jacobian is packaged as a single bundled contravariant functor
`Jacobian.functor : (Curve k)ᵒᵖ ⥤ Grp (Over (Spec k))` (pullback of line bundles), with the functor
laws embedded in it; the "Jacobian respects isomorphisms of curves" map used in the coherences is
*derived* from it via `Functor.mapIso`.

By a smooth curve we mean a geometrically irreducible, smooth scheme of relative dimension one
over a field.
-/

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom]
  [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The category of smooth, proper, geometrically irreducible curves over `k`, with morphisms the
morphisms of `k`-schemes. -/
structure Curve (k : Type u) [Field k] where
  /-- The underlying `k`-scheme. -/
  carrier : Over (Spec (.of k))
  [isProper : IsProper carrier.hom]
  [smoothOfRelativeDimension : SmoothOfRelativeDimension 1 carrier.hom]
  [geometricallyIrreducible : GeometricallyIrreducible carrier.hom]

attribute [instance] Curve.isProper Curve.smoothOfRelativeDimension Curve.geometricallyIrreducible

noncomputable instance (k : Type u) [Field k] : Category (Curve k) where
  Hom X Y := X.carrier ⟶ Y.carrier
  id X := 𝟙 X.carrier
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- The genus of a smooth proper curve. -/
noncomputable def genus (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ := sorry

/-- The Jacobian of a smooth, proper curve over a field `k`. -/
noncomputable def Jacobian (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Over (Spec (.of k)) := sorry

namespace Jacobian

/-- The group scheme structure on the Jacobian of the curve `C`. -/
noncomputable instance instGrpObj : GrpObj (Jacobian C) := sorry

/-- The Jacobian of `C` is smooth of relative dimension `g` over `k`. -/
instance : SmoothOfRelativeDimension (genus C) (Jacobian C).hom := sorry

/-- The Jacobian of `C` is proper over `k`. -/
instance : IsProper (Jacobian C).hom := sorry

/-- The Jacobian of `C` is geometrically irreducible over `k`. -/
instance : GeometricallyIrreducible (Jacobian C).hom := sorry

/-- The Abel-Jacobi map from a smooth, proper curve to its Jacobian associated to a
`k`-rational point of `C`. -/
noncomputable def ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    C ⟶ Jacobian C := sorry

/-- The Abel-Jacobi map sends the `k`-rational point `P` to `0`. -/
theorem comp_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ofCurve P = η[Jacobian C] := sorry

/-- The universal property of the Jacobian variety: `Jacobian C` is the Albanese variety of `C`. -/
theorem exists_unique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : Jacobian C ⟶ A), f = ofCurve P ≫ g := sorry

/-- **Functoriality of the Jacobian**, bundled as a single contravariant functor: a curve goes to
its Jacobian group scheme over `k`, and a morphism of curves to the pullback of line bundles. The
functor laws (`map_id`, `map_comp`) are embedded in this `Functor`. The object action is pinned to
the `Jacobian` above, so everything downstream stays phrased in terms of `Jacobian C`. -/
noncomputable def functor (k : Type u) [Field k] :
    (Curve k)ᵒᵖ ⥤ Grp (Over (Spec (.of k))) where
  obj X := .mk (Jacobian X.unop.carrier)
  map _ := sorry
  map_id := sorry
  map_comp := sorry

end Jacobian

/-! # Base change of fields

These are genuine definitions on Mathlib master (no `sorry`). -/

/-- Base change of `k`-schemes along a field homomorphism `k → L`, i.e. `X ↦ X ×_{Spec k} Spec L`. -/
noncomputable abbrev baseChange (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Over (Spec (.of k)) ⥤ Over (Spec (.of L)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))

instance {k L : Type u} [Field k] [Field L] [Algebra k L] (C : Over (Spec (.of k)))
    [IsProper C.hom] : IsProper ((baseChange k L).obj C).hom :=
  MorphismProperty.baseChange_obj (Spec.map (CommRingCat.ofHom (algebraMap k L))) C inferInstance

instance {k L : Type u} [Field k] [Field L] [Algebra k L] (C : Over (Spec (.of k)))
    [GeometricallyIrreducible C.hom] : GeometricallyIrreducible ((baseChange k L).obj C).hom :=
  MorphismProperty.baseChange_obj (Spec.map (CommRingCat.ofHom (algebraMap k L))) C inferInstance

instance {k L : Type u} [Field k] [Field L] [Algebra k L] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] :
    SmoothOfRelativeDimension 1 ((baseChange k L).obj C).hom :=
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  MorphismProperty.baseChange_obj (Spec.map (CommRingCat.ofHom (algebraMap k L))) C inferInstance

-- The coherences mention curves of the form `(𝟭 _).obj C` and `(F ⋙ G).obj C`.
instance {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom] :
    IsProper ((𝟭 (Over (Spec (.of k)))).obj C).hom := ‹_›
instance {k : Type u} [Field k] (C : Over (Spec (.of k))) [GeometricallyIrreducible C.hom] :
    GeometricallyIrreducible ((𝟭 (Over (Spec (.of k)))).obj C).hom := ‹_›
instance {k : Type u} [Field k] (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] :
    SmoothOfRelativeDimension 1 ((𝟭 (Over (Spec (.of k)))).obj C).hom := ‹_›

instance {k L M : Type u} [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M]
    (C : Over (Spec (.of k))) [IsProper C.hom] :
    IsProper ((baseChange k L ⋙ baseChange L M).obj C).hom :=
  inferInstanceAs (IsProper ((baseChange L M).obj ((baseChange k L).obj C)).hom)
instance {k L M : Type u} [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M]
    (C : Over (Spec (.of k))) [GeometricallyIrreducible C.hom] :
    GeometricallyIrreducible ((baseChange k L ⋙ baseChange L M).obj C).hom :=
  inferInstanceAs (GeometricallyIrreducible ((baseChange L M).obj ((baseChange k L).obj C)).hom)
instance {k L M : Type u} [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] :
    SmoothOfRelativeDimension 1 ((baseChange k L ⋙ baseChange L M).obj C).hom :=
  inferInstanceAs (SmoothOfRelativeDimension 1 ((baseChange L M).obj ((baseChange k L).obj C)).hom)

/-- Base change along `k → k` is the identity functor. -/
noncomputable def baseChange.idIso (k : Type u) [Field k] :
    baseChange k k ≅ 𝟭 (Over (Spec (.of k))) :=
  eqToIso (by
    show Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k k))) = Over.pullback (𝟙 _)
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]) ≪≫ Over.pullbackId

/-- Base change along a tower `k → L → M` is the composite of the two base changes. -/
noncomputable def baseChange.compIso (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M] :
    baseChange k M ≅ baseChange k L ⋙ baseChange L M :=
  eqToIso (by
    show Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k M))) =
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) ≪≫
    Over.pullbackComp _ _

namespace Jacobian

/-- The Jacobian respects isomorphisms of curves -- *derived* from the bundled functor
`Jacobian.functor` via `Functor.mapIso`, not a primitive. Used to compare the two sides of the
cocycle, whose curves agree only up to `baseChange.compIso`. -/
noncomputable def congr {k : Type u} [Field k] {C C' : Over (Spec (.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsProper C'.hom] [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]
    (e : C ≅ C') :
    (.mk (Jacobian C) : Grp (Over (Spec (.of k)))) ≅ .mk (Jacobian C') :=
  let j : (⟨C⟩ : Curve k) ≅ ⟨C'⟩ :=
    { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }
  (Jacobian.functor k).mapIso j.symm.op

/-- **The missing condition.** Jacobians commute with base change of fields: a canonical
isomorphism `Jac(C)_L ≅ Jac(C_L)`, as group schemes over `L`. -/
noncomputable def baseChangeIso (k L : Type u) [Field k] [Field L] [Algebra k L]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    (baseChange k L).mapGrp.obj (.mk (Jacobian C)) ≅ .mk (Jacobian ((baseChange k L).obj C)) :=
  sorry

/-! ## Functoriality: the base change isomorphisms form a coherent system. -/

/-- Identity coherence. -/
theorem baseChangeIso_id (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    baseChangeIso k k C =
      (Functor.mapGrpNatIso (baseChange.idIso k)).app _
        ≪≫ (Functor.mapGrpIdIso (C := Over (Spec (.of k)))).app _
        ≪≫ Jacobian.congr ((baseChange.idIso k).app C).symm :=
  sorry

/-- Cocycle coherence for a tower `k → L → M`. -/
theorem baseChangeIso_comp (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    baseChangeIso k M C
        ≪≫ Jacobian.congr ((baseChange.compIso k L M).app C) =
      (Functor.mapGrpNatIso (baseChange.compIso k L M)).app _
        ≪≫ (Functor.mapGrpCompIso (F := baseChange k L) (G := baseChange L M)).app _
        ≪≫ (baseChange L M).mapGrp.mapIso (baseChangeIso k L C)
        ≪≫ baseChangeIso L M ((baseChange k L).obj C) :=
  sorry

end Jacobian

/-! ## Compatibility with the Abel-Jacobi map -/

namespace Jacobian

variable {L : Type u} [Field L] [Algebra k L]

theorem baseChange_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (baseChange k L).map (ofCurve P) ≫ (baseChangeIso k L C).hom.hom.hom =
      ofCurve (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P) :=
  sorry

end Jacobian

end AlgebraicGeometry
