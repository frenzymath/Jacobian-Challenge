import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Ordered sums in commutative group schemes

A morphism from a curve to a commutative group scheme induces a morphism on
every finite ordered power. It sums the coordinate images and is invariant
under coordinate permutations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped BigOperators CategoryTheory.MonObj

namespace AlgebraicGeometry.Hilbert.OrderedDivisors

variable {k : Type u} [Field k] (C : Curve k)
  (G : CommGrp (Over (Spec (.of k)))) (φ : C.carrier ⟶ G.X)

/-- Apply the curve map to each coordinate and sum in the group scheme. -/
def abelianSum (n : ℕ) : (∏ᶜ fun _ : Fin n => C.carrier) ⟶ G.X :=
  ∏ i, Pi.π (fun _ : Fin n => C.carrier) i ≫ φ

/-- The formula on every test scheme follows from the Yoneda monoid. -/
theorem abelianSum_comp (n : ℕ) {T : Over (Spec (.of k))}
    (t : T ⟶ ∏ᶜ fun _ : Fin n => C.carrier) :
    t ≫ abelianSum C G φ n =
      ∏ i, (t ≫ Pi.π (fun _ : Fin n => C.carrier) i) ≫ φ := by
  let precomp : ((∏ᶜ fun _ : Fin n => C.carrier) ⟶ G.X) →* (T ⟶ G.X) :=
    ((yonedaMonObj G.X).map t.op).hom
  have h := map_prod precomp
    (fun i : Fin n => Pi.π (fun _ : Fin n => C.carrier) i ≫ φ) Finset.univ
  change t ≫ (∏ i : Fin n, Pi.π (fun _ : Fin n => C.carrier) i ≫ φ) =
    ∏ i : Fin n, t ≫ (Pi.π (fun _ : Fin n => C.carrier) i ≫ φ) at h
  simpa only [abelianSum, Category.assoc] using h

/-- On a tuple of test-scheme points, the morphism is their group-valued sum. -/
theorem abelianSum_lift (n : ℕ) {T : Over (Spec (.of k))}
    (x : Fin n → (T ⟶ C.carrier)) :
    Pi.lift x ≫ abelianSum C G φ n = ∏ i, x i ≫ φ := by
  rw [abelianSum_comp]
  simp only [Pi.lift_π]

/-- The empty tuple maps to the identity section of the group scheme. -/
theorem abelianSum_zero :
    abelianSum C G φ 0 =
      CartesianMonoidalCategory.toUnit (∏ᶜ fun _ : Fin 0 => C.carrier) ≫
        MonObj.one (X := G.X) := by
  change (∏ i : Fin 0, Pi.π (fun _ : Fin 0 => C.carrier) i ≫ φ) = _
  rw [Fin.prod_univ_zero]
  exact CategoryTheory.Hom.one_def

/-- The one-coordinate sum is the supplied curve map after the sole projection. -/
theorem abelianSum_one :
    abelianSum C G φ 1 = Pi.π (fun _ : Fin 1 => C.carrier) 0 ≫ φ :=
  Fin.prod_univ_one _

/-- Coordinate permutations leave the morphism to the group unchanged. -/
theorem abelianSum_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permute C.carrier.hom n σ ≫ abelianSum C G φ n = abelianSum C G φ n := by
  change Pi.lift (fun i : Fin n => Pi.π (fun _ : Fin n => C.carrier) (σ i)) ≫
    abelianSum C G φ n = _
  rw [abelianSum_lift]
  exact Equiv.prod_comp σ (fun i : Fin n => Pi.π (fun _ : Fin n => C.carrier) i ≫ φ)

/-- Repeating a test-scheme point gives its `n`-fold group sum. -/
theorem abelianSum_repeated (n : ℕ) {T : Over (Spec (.of k))}
    (x : T ⟶ C.carrier) :
    Pi.lift (fun _ : Fin n => x) ≫ abelianSum C G φ n = (x ≫ φ) ^ n := by
  rw [abelianSum_lift]
  simp

end AlgebraicGeometry.Hilbert.OrderedDivisors
