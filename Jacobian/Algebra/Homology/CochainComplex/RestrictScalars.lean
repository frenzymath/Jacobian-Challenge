import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Homology and restriction of scalars

Restriction of scalars preserves exactness and therefore commutes with homology
of complexes of modules.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u₁ u₂

open CategoryTheory

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- **Restriction of scalars preserves homology**, since it preserves the exactness of short
complexes. -/
instance preservesHomology_restrictScalars : (restrictScalars.{v} f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun T hT ↦ by
    rw [ShortComplex.moduleCat_exact_iff] at hT ⊢
    exact hT

/-- The homology of a homological complex of `S`-modules, with scalars restricted along
`f : R →+* S`, is the restriction of scalars of its homology. -/
noncomputable def restrictScalarsHomologyIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} S) c) (i : ι) :
    (((restrictScalars.{v} f).mapHomologicalComplex c).obj K).homology i ≅
      (restrictScalars.{v} f).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (restrictScalars.{v} f)

end ModuleCat
