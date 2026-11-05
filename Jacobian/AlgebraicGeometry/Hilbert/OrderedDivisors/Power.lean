import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Finite ordered powers over a scheme

The recursive fibre product is a product in the over category. Its coordinate
morphisms identify it with the chosen categorical finite product.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Hilbert.OrderedDivisors

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The zero power is the base; the successor is the actual fibre product
of the preceding power and the curve. -/
def power : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | n + 1 => Over.mk (pullback.fst (power n).hom f ≫ (power n).hom)

/-- Delete the last coordinate. -/
def drop (n : ℕ) : power f (n + 1) ⟶ power f n :=
  Over.homMk (pullback.fst (power f n).hom f)

/-- The last coordinate. -/
def last (n : ℕ) : power f (n + 1) ⟶ Over.mk f :=
  Over.homMk (pullback.snd (power f n).hom f) pullback.condition.symm

/-- The coordinate maps of the ordered power. -/
def projection : (n : ℕ) → Fin n → (power f n ⟶ Over.mk f)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.lastCases (last f n) (fun j => drop f n ≫ projection n j) i

@[simp] theorem projection_last (n : ℕ) :
    projection f (n + 1) (Fin.last n) = last f n := by
  simp [projection]

@[simp] theorem projection_castSucc (n : ℕ) (i : Fin n) :
    projection f (n + 1) i.castSucc = drop f n ≫ projection f n i := by
  simp [projection]

/-- A tuple of morphisms determines a morphism into the power. -/
def lift : (n : ℕ) → {T : Over S} → (Fin n → (T ⟶ Over.mk f)) → (T ⟶ power f n)
  | 0, T, _ => Over.homMk T.hom (by simp [power])
  | n + 1, T, x =>
      let y : T ⟶ power f n := lift n (fun i => x i.castSucc)
      Over.homMk (pullback.lift y.left (x (Fin.last n)).left
        ((Over.w y).trans (Over.w (x (Fin.last n))).symm)) (by
          change pullback.lift y.left (x (Fin.last n)).left _ ≫
            (pullback.fst (power f n).hom f ≫ (power f n).hom) = T.hom
          rw [pullback.lift_fst_assoc]
          exact Over.w y)

@[simp] theorem lift_drop (n : ℕ) {T : Over S} (x : Fin (n + 1) → (T ⟶ Over.mk f)) :
    lift f (n + 1) x ≫ drop f n = lift f n (fun i => x i.castSucc) := by
  ext1
  exact pullback.lift_fst _ _ _

@[simp] theorem lift_last (n : ℕ) {T : Over S} (x : Fin (n + 1) → (T ⟶ Over.mk f)) :
    lift f (n + 1) x ≫ last f n = x (Fin.last n) := by
  ext1
  exact pullback.lift_snd _ _ _

@[simp] theorem lift_projection (n : ℕ) {T : Over S} (x : Fin n → (T ⟶ Over.mk f))
    (i : Fin n) : lift f n x ≫ projection f n i = x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [projection_last, lift_last]
      · rw [projection_castSucc, ← Category.assoc, lift_drop, ih]

/-- The coordinates determine a morphism into the recursive power. -/
theorem hom_ext (n : ℕ) {T : Over S} (a b : T ⟶ power f n)
    (h : ∀ i, a ≫ projection f n i = b ≫ projection f n i) : a = b := by
  induction n with
  | zero =>
      ext1
      change a.left = b.left
      have ha : a.left ≫ (𝟙 S) = T.hom := Over.w a
      have hb : b.left ≫ (𝟙 S) = T.hom := Over.w b
      exact (Category.comp_id a.left).symm.trans
        (ha.trans (hb.symm.trans (Category.comp_id b.left)))
  | succ n ih =>
      have hd : a ≫ drop f n = b ≫ drop f n := by
        apply ih
        intro i
        simpa only [Category.assoc, ← projection_castSucc] using h i.castSucc
      have hl : a ≫ last f n = b ≫ last f n := by
        simpa only [projection_last] using h (Fin.last n)
      ext1
      have hd' : a.left ≫ pullback.fst (power f n).hom f =
          b.left ≫ pullback.fst (power f n).hom f :=
        congrArg CommaMorphism.left hd
      have hl' : a.left ≫ pullback.snd (power f n).hom f =
          b.left ≫ pullback.snd (power f n).hom f :=
        congrArg CommaMorphism.left hl
      exact pullback.hom_ext hd' hl'

/-- The recursive power has the universal property of the `Fin n` product. -/
def powerIsProduct (n : ℕ) :
    IsLimit (Fan.mk (power f n) (projection f n)) :=
  Fan.IsLimit.mk _ (fun t => lift f n t.proj) (fun t i => lift_projection f n t.proj i)
    (fun t m hm => hom_ext f n m (lift f n t.proj) (fun i => by
      have hmi : m ≫ projection f n i = t.proj i := hm i
      exact hmi.trans (lift_projection f n t.proj i).symm))

/-- Identification with the ordinary chosen categorical `Fin n` power. -/
def powerIso (n : ℕ) :
    (∏ᶜ fun _ : Fin n => Over.mk f) ≅ power f n :=
  (productIsProduct (fun _ : Fin n => Over.mk f)).conePointUniqueUpToIso
    (powerIsProduct f n)

@[simp, reassoc] theorem powerIso_hom_projection (n : ℕ) (i : Fin n) :
    (powerIso f n).hom ≫ projection f n i = Pi.π (fun _ : Fin n => Over.mk f) i :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (productIsProduct (fun _ : Fin n => Over.mk f)) (powerIsProduct f n) (Discrete.mk i)

end AlgebraicGeometry.Hilbert.OrderedDivisors
