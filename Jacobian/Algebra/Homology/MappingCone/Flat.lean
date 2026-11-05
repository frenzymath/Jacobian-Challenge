import Jacobian.Algebra.Homology.CochainComplex.Flat
import Jacobian.Algebra.Homology.MappingCone.Acyclic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases

/-!
# Mapping cones of flat complexes

The mapping cone of a map between bounded-above flat complexes is bounded
above with flat terms. If the map is a quasi-isomorphism, its cone is acyclic
and stays acyclic under tensoring with an arbitrary module. Additive functors
commute with mapping cones, so this criterion detects quasi-isomorphisms
without an exactness hypothesis on the functor.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe v v' u u'

open CategoryTheory Limits MonoidalCategory

namespace Module.Flat

/-- A binary product of flat modules is flat, via the actual finite direct sum. -/
theorem prod_of_flat {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (hM : Module.Flat R M) (hN : Module.Flat R N) :
    Module.Flat R (M × N) := by
  let V : Fin 2 → ModuleCat.{u} R := ![M, N]
  letI (i : Fin 2) : Module.Flat R (V i) := by
    fin_cases i
    · exact hM
    · exact hN
  let e : (Π₀ i : Fin 2, V i) ≃ₗ[R] (M × N) :=
    (DFinsupp.linearEquivFunOnFintype (R := R)).trans
      (LinearEquiv.piFinTwo R (fun i => V i))
  exact Module.Flat.of_linearEquiv e.symm

end Module.Flat

namespace CochainComplex
variable {R : Type u} [CommRing R]

/-- Actual mapping cones retain a common upper bound. -/
theorem mappingCone_isStrictlyLE_of_common_bound
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ⟶ Q) (b : ℤ)
    [P.IsStrictlyLE b] [Q.IsStrictlyLE b] :
    (mappingCone e).IsStrictlyLE b := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact (mappingCone.isZero_X_iff e i).mpr
    ⟨P.isZero_of_isStrictlyLE b (i + 1) (by omega),
      Q.isZero_of_isStrictlyLE b i hi⟩

/-- The actual cone terms are flat whenever the original terms are flat. -/
theorem mappingCone_flat_X
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ⟶ Q)
    (hP : ∀ n, Module.Flat R (P.X n)) (hQ : ∀ n, Module.Flat R (Q.X n))
    (n : ℤ) : Module.Flat R ((mappingCone e).X n) := by
  letI : Module.Flat R (P.X (n + 1) × Q.X n) :=
    Module.Flat.prod_of_flat _ _ (hP (n + 1)) (hQ n)
  exact Module.Flat.of_linearEquiv
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod e n (n + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv

/-- An actual acyclic cone of bounded-above flat complexes stays exact under
arbitrary tensor. Acyclicity remains explicit; its quasi-isomorphism criterion
is supplied by the acyclic cone criterion. -/
theorem tensorRight_mappingCone_exactAt_of_flat
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ⟶ Q) (b : ℤ)
    [P.IsStrictlyLE b] [Q.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat R (P.X n)) (hQ : ∀ n, Module.Flat R (Q.X n))
    (he : ∀ n : ℤ, (mappingCone e).ExactAt n)
    (N : ModuleCat.{u} R) (n : ℤ) :
    (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj (mappingCone e)).ExactAt n := by
  letI := mappingCone_isStrictlyLE_of_common_bound e b
  exact tensorRight_exactAt_of_boundedAbove_acyclic_flat (mappingCone e) b
    (mappingCone_flat_X e hP hQ) he N n

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {P Q : CochainComplex C ℤ} (f : P ⟶ Q)

/-- An additive image map is a quasi-isomorphism exactly when the image of its
mapping cone is acyclic. The additive functor need not preserve finite limits. -/
theorem quasiIso_map_iff_acyclic_map_mappingCone (F : C ⥤ D) [F.Additive] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) ↔
      ((F.mapHomologicalComplex (.up ℤ)).obj (mappingCone f)).Acyclic := by
  rw [mappingCone.quasiIso_iff_acyclic]
  let e := mappingCone.mapHomologicalComplexIso f F
  constructor
  · intro h i
    exact (h i).of_iso e.symm
  · intro h i
    exact (h i).of_iso e

end CochainComplex
