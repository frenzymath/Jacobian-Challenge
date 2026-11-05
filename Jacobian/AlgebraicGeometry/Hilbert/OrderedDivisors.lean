import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors.Power
import Jacobian.AlgebraicGeometry.Hilbert.CurveRepresentability
import Jacobian.AlgebraicGeometry.Hilbert.Addition
import Jacobian.AlgebraicGeometry.Curve.Basic
import Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Jacobian.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.Algebra.BigOperators.Fin

/-!
# The ordered-divisor cover

An ordered tuple defines the product of its graph ideals. On a proper smooth
geometrically integral curve, the resulting map to any representative of the
degree-`n` Hilbert functor is finite flat and surjective, of constant rank `n!`.
This holds in every characteristic, including along repeated divisors.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped BigOperators

namespace AlgebraicGeometry.Hilbert.OrderedDivisors

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The graph ideal of a section over a test scheme. -/
def graphIdeal {T : Over S} (x : T ⟶ Over.mk f) :
    (pullback f T.hom).IdealSheafData :=
  (pullback.lift x.left (𝟙 T.left) (by simpa using Over.w x) :
    T.left ⟶ pullback f T.hom).ker

/-- The product of graph ideals, with the empty product equal to the unit ideal. -/
def ideal {n : ℕ} {T : Over S} (x : Fin n → (T ⟶ Over.mk f)) :
    (pullback f T.hom).IdealSheafData :=
  ∏ i, graphIdeal f (x i)

@[simp] theorem ideal_zero {T : Over S} (x : Fin 0 → (T ⟶ Over.mk f)) :
    ideal f x = ⊤ := by simp [ideal]

theorem ideal_succ {n : ℕ} {T : Over S} (x : Fin (n + 1) → (T ⟶ Over.mk f)) :
    ideal f x = ideal f (fun i => x i.castSucc) * graphIdeal f (x (Fin.last n)) :=
  Fin.prod_univ_castSucc _

theorem ideal_isHilbert [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {T : Over S} (x : Fin n → (T ⟶ Over.mk f)) :
    IsHilbertSubscheme f n T (ideal f x) := by
  induction n with
  | zero => simpa only [ideal_zero] using isHilbertSubscheme_top f T
  | succ n ih =>
      rw [ideal_succ]
      exact (ih (fun i => x i.castSucc)).mul f
        (isHilbertSubscheme_ker_lift_id f (test := T) (x (Fin.last n)).left (Over.w _))

/-- The Hilbert point defined by a tuple of sections. -/
def element [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {T : Over S} (x : Fin n → (T ⟶ Over.mk f)) :
    (hilbertPresheaf f n).obj (op T) :=
  ⟨ideal f x, ideal_isHilbert f x⟩

theorem graphIdeal_comap [IsSeparated f] {T T' : Over S} (φ : T' ⟶ T)
    (x : T ⟶ Over.mk f) :
    (graphIdeal f x).comap (baseChangeMap f φ) = graphIdeal f (φ ≫ x) :=
  ker_lift_id_comap_baseChangeMap f φ x.left (Over.w x) (φ ≫ x).left (Over.w _) rfl

/-- The graph-ideal product is compatible with arbitrary change of test scheme. -/
theorem ideal_comap [IsSeparated f] {n : ℕ} {T T' : Over S} (φ : T' ⟶ T)
    (x : Fin n → (T ⟶ Over.mk f)) :
    (ideal f x).comap (baseChangeMap f φ) = ideal f (fun i => φ ≫ x i) := by
  induction n with
  | zero => simp only [ideal_zero, Scheme.IdealSheafData.comap_top]
  | succ n ih =>
      rw [ideal_succ, Scheme.IdealSheafData.comap_mul, ideal_succ,
        ih (fun i => x i.castSucc), graphIdeal_comap]

/-- Reordering a tuple leaves its divisor ideal unchanged. -/
theorem ideal_permutation {n : ℕ} {T : Over S} (x : Fin n → (T ⟶ Over.mk f))
    (σ : Equiv.Perm (Fin n)) : ideal f (fun i => x (σ i)) = ideal f x :=
  Equiv.prod_comp σ (fun i => graphIdeal f (x i))

/-- A repeated point gives the power of its graph ideal. -/
theorem ideal_const (n : ℕ) {T : Over S} (x : T ⟶ Over.mk f) :
    ideal f (fun _ : Fin n => x) = graphIdeal f x ^ n := by
  simp [ideal]

/-- Classify the graph-ideal product in a Hilbert representative. -/
def classify [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (x : Fin n → (T ⟶ Over.mk f)) : T ⟶ H :=
  e.homEquiv.symm (element f x)

@[simp] theorem classify_val [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (x : Fin n → (T ⟶ Over.mk f)) :
    (e.homEquiv (classify f e x)).val = ideal f x :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

theorem classify_comp [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T T' : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (φ : T' ⟶ T) (x : Fin n → (T ⟶ Over.mk f)) :
    φ ≫ classify f e x = classify f e (fun i => φ ≫ x i) := by
  apply e.homEquiv.injective
  apply Subtype.ext
  rw [hilbertPresheaf_homEquiv_comp_val, classify_val, classify_val, ideal_comap]

theorem classify_permutation [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (x : Fin n → (T ⟶ Over.mk f)) (σ : Equiv.Perm (Fin n)) :
    classify f e (fun i => x (σ i)) = classify f e x := by
  apply e.homEquiv.injective
  apply Subtype.ext
  simpa only [classify_val] using ideal_permutation f x σ

/-- The divisor classifier on the recursively constructed power. -/
def recursiveMap [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H : Over S} (e : (hilbertPresheaf f n).RepresentableBy H) : power f n ⟶ H :=
  classify f e (projection f n)

/-- Its value on every test scheme is the product of its graph ideals. -/
theorem recursiveMap_val [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (t : T ⟶ power f n) :
    (e.homEquiv (t ≫ recursiveMap f e)).val = ideal f (fun i => t ≫ projection f n i) := by
  rw [recursiveMap, classify_comp, classify_val]

/-- The ordered-divisor map from the chosen categorical `Fin n` power. -/
def map [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H : Over S} (e : (hilbertPresheaf f n).RepresentableBy H) :
    (∏ᶜ fun _ : Fin n => Over.mk f) ⟶ H :=
  (powerIso f n).hom ≫ recursiveMap f e

/-- On every test scheme the map is literally the product of graph ideals. -/
theorem map_val [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (t : T ⟶ ∏ᶜ fun _ : Fin n => Over.mk f) :
    (e.homEquiv (t ≫ map f e)).val =
      ideal f (fun i => t ≫ Pi.π (fun _ : Fin n => Over.mk f) i) := by
  rw [map, ← Category.assoc, recursiveMap_val]
  congr 1
  funext i
  simp only [Category.assoc, powerIso_hom_projection]

/-- The point obtained from an tuple has precisely the tuple's graph ideals. -/
theorem map_lift_val [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H T : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (x : Fin n → (T ⟶ Over.mk f)) :
    (e.homEquiv (Pi.lift x ≫ map f e)).val = ideal f x := by
  rw [map_val]
  simp only [Pi.lift_comp_π]

/-- The permutation action is the permutation of the coordinate projections. -/
def permute (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (∏ᶜ fun _ : Fin n => Over.mk f) ⟶ (∏ᶜ fun _ : Fin n => Over.mk f) :=
  Pi.lift (fun i => Pi.π (fun _ : Fin n => Over.mk f) (σ i))

/-- The ordered cover is invariant as a morphism under every permutation. -/
theorem permute_map [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {n : ℕ} {H : Over S} (e : (hilbertPresheaf f n).RepresentableBy H)
    (σ : Equiv.Perm (Fin n)) : permute f n σ ≫ map f e = map f e := by
  apply e.homEquiv.injective
  apply Subtype.ext
  rw [map_val]
  simpa only [permute, Pi.lift_comp_π, Category.id_comp] using
    (ideal_permutation f (Pi.π (fun _ : Fin n => Over.mk f)) σ).trans
      (by simpa only [Category.id_comp] using (map_val f e (𝟙 _)).symm)

end Relative

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]

/-- Iterated graph addition is finite locally free of rank `n!`.
The intermediate Hilbert representatives exist by the representability theorem for curves. -/
theorem recursiveMap_properties (n : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf f n).RepresentableBy H) :
    IsFinite (recursiveMap f e).left ∧ Flat (recursiveMap f e).left ∧
      LocallyOfFinitePresentation (recursiveMap f e).left ∧
        ∀ t, (recursiveMap f e).left.finrank t = n.factorial := by
  induction n generalizing H with
  | zero =>
      have : IsIso H.hom := isIso_of_representableBy_hilbertPresheaf_zero f e
      have heq : (recursiveMap f e).left = inv H.hom := by
        apply (cancel_mono H.hom).mp
        have hw : (recursiveMap f e).left ≫ H.hom = (𝟙 (Spec (.of k))) :=
          Over.w (recursiveMap f e)
        have hi : inv H.hom ≫ H.hom = (𝟙 (Spec (.of k))) := IsIso.inv_hom_id H.hom
        exact hw.trans hi.symm
      rw [heq]
      exact ⟨inferInstance, inferInstance, inferInstance, fun t => by
        simpa only [Nat.factorial_zero, Pi.one_apply] using
          congrFun (Scheme.Hom.finrank_eq_one_of_isIso (inv H.hom)) t⟩
  | succ n ih =>
      obtain ⟨H₀, ⟨e₀⟩⟩ := isRepresentable_hilbertPresheaf_curve f n
      let δ := recursiveMap f e₀
      obtain ⟨hfin, hflat, hlfp, hrank⟩ := ih H₀ e₀
      letI : IsFinite δ.left := hfin
      letI : Flat δ.left := hflat
      letI : LocallyOfFinitePresentation δ.left := hlfp
      obtain ⟨a, ha, hafin, haflat, halfp, harank, haformula⟩ :=
        exists_addition_hilbertPresheaf f n H₀ H e₀ e
      let m : (power f (n + 1)).left ⟶ pullback H₀.hom f :=
        pullback.lift (pullback.fst (power f n).hom f ≫ δ.left)
          (pullback.snd (power f n).hom f) (by
            rw [Category.assoc, Over.w δ, pullback.condition])
      have pb : IsPullback (pullback.fst (power f n).hom f) m δ.left
          (pullback.fst H₀.hom f) := by
        refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
          (IsPullback.of_hasPullback H₀.hom f)
        rw [pullback.lift_snd, Over.w δ]
        exact IsPullback.of_hasPullback (power f n).hom f
      letI : IsFinite m := MorphismProperty.of_isPullback (P := @IsFinite) pb hfin
      letI : Flat m := MorphismProperty.of_isPullback (P := @Flat) pb hflat
      letI : LocallyOfFinitePresentation m :=
        MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) pb hlfp
      have hmrank (t : (pullback H₀.hom f : Scheme.{u})) : m.finrank t = n.factorial := by
        rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ pb]
        exact hrank _
      let t : power f (n + 1) ⟶ H := Over.homMk (m ≫ a) (by
        rw [Category.assoc, ha, pullback.lift_snd_assoc]
        exact pullback.condition.symm)
      have ht := haformula (power f (n + 1)) (drop f n ≫ δ) (last f n).left
        (Over.w (last f n)) t rfl
      have heq : recursiveMap f e = t := by
        apply e.homEquiv.injective
        apply Subtype.ext
        rw [show (e.homEquiv (recursiveMap f e)).val = ideal f (projection f (n + 1))
          from classify_val f e _, ht, recursiveMap_val, ideal_succ]
        simp only [projection_castSucc, projection_last, graphIdeal]
      have heq' : (recursiveMap f e).left = m ≫ a := congrArg CommaMorphism.left heq
      letI : IsFinite a := hafin
      letI : Flat a := haflat
      letI : LocallyOfFinitePresentation a := halfp
      rw [heq']
      refine ⟨inferInstance, inferInstance, inferInstance, fun y => ?_⟩
      rw [Scheme.Hom.finrank_comp_of_forall_finrank_eq m a hmrank, harank,
        Nat.factorial_succ, Nat.mul_comm]

/-- The chosen categorical power covers any Hilbert representative by a
finite, flat, locally finitely presented morphism of constant rank `n!`. -/
theorem map_properties (n : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf f n).RepresentableBy H) :
    IsFinite (map f e).left ∧ Flat (map f e).left ∧
      LocallyOfFinitePresentation (map f e).left ∧
        (∀ t, (map f e).left.finrank t = n.factorial) ∧ Surjective (map f e).left := by
  obtain ⟨hfin, hflat, hlfp, hrank⟩ := recursiveMap_properties f n H e
  letI := hfin
  letI := hflat
  letI := hlfp
  letI : IsIso ((powerIso f n).hom).left := (Over.forget _).map_isIso _
  have hmap : (map f e).left = ((powerIso f n).hom).left ≫ (recursiveMap f e).left := rfl
  have hfin' : IsFinite (map f e).left := by rw [hmap]; infer_instance
  have hflat' : Flat (map f e).left := by rw [hmap]; infer_instance
  have hlfp' : LocallyOfFinitePresentation (map f e).left := by rw [hmap]; infer_instance
  have hrank' (t : H.left) : (map f e).left.finrank t = n.factorial := by
    rw [hmap, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrank t
  letI := hfin'
  letI := hflat'
  letI := hlfp'
  refine ⟨hfin', hflat', hlfp', hrank',
    (Scheme.Hom.one_le_finrank_iff_surjective (map f e).left).mp ?_⟩
  intro t
  rw [hrank']
  exact Nat.factorial_pos n

end Curve

/-- The ordered-divisor cover of a proper smooth geometrically irreducible curve. -/
theorem curve_map_properties {k : Type u} [Field k] (C : Curve k)
    (n : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H) :
    IsFinite (map C.carrier.hom e).left ∧ Flat (map C.carrier.hom e).left ∧
      LocallyOfFinitePresentation (map C.carrier.hom e).left ∧
        (∀ t, (map C.carrier.hom e).left.finrank t = n.factorial) ∧
          Surjective (map C.carrier.hom e).left := by
  letI : Smooth C.carrier.hom := SmoothOfRelativeDimension.smooth 1 C.carrier.hom
  letI : GeometricallyIntegral C.carrier.hom :=
    Smooth.geometricallyIntegral C.carrier.hom
  exact map_properties C.carrier.hom n H e

end AlgebraicGeometry.Hilbert.OrderedDivisors
