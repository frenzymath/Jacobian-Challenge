import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors.AbelianSum
import Jacobian.AlgebraicGeometry.Morphisms.GenericFiber
import Jacobian.AlgebraicGeometry.Morphisms.FiniteRank
import Jacobian.AlgebraicGeometry.FiniteOverField
import Jacobian.AlgebraicGeometry.FiniteOverField.Split
import Jacobian.AlgebraicGeometry.Curve.Dimension
import Jacobian.RingTheory.FiniteAlgebra.Points
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Data.Fintype.Perm

/-!
# Descent of ordered sums to the Hilbert scheme

For a proper smooth geometrically irreducible curve with a rational point,
the generic kernel pair of the degree-`n` ordered-divisor cover splits into
its `n!` permutation sections. The ordered sum into a separated commutative
group scheme agrees on these sections. Flatness and generic reducedness extend
this equality to the full kernel pair, and finite faithfully flat descent gives
a unique morphism from the Hilbert representative. Special divisor fibres need
not be reduced, and no characteristic restriction is imposed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped BigOperators

namespace AlgebraicGeometry.Hilbert.OrderedDivisors

section Relative

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
  [SmoothOfRelativeDimension 1 f] {n : ℕ} {H : Over S}
  (e : (hilbertPresheaf f n).RepresentableBy H)

/-- A permutation graph in the scheme-theoretic kernel pair. -/
def permutationGraph (σ : Equiv.Perm (Fin n)) :
    (∏ᶜ fun _ : Fin n => Over.mk f).left ⟶
      pullback (map f e).left (map f e).left :=
  pullback.lift (𝟙 _) (permute f n σ).left (by
    have h := congrArg CommaMorphism.left (permute_map f e σ)
    change (permute f n σ).left ≫ (map f e).left = (map f e).left at h
    exact (Category.id_comp _).trans h.symm)

@[reassoc] theorem permutationGraph_fst (σ : Equiv.Perm (Fin n)) :
    permutationGraph f e σ ≫ pullback.fst (map f e).left (map f e).left = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc] theorem permutationGraph_snd (σ : Equiv.Perm (Fin n)) :
    permutationGraph f e σ ≫ pullback.snd (map f e).left (map f e).left =
      (permute f n σ).left :=
  pullback.lift_snd _ _ _

/-- The graph supplies a rational point after every base change of the first
kernel-pair projection, including its generic base change. -/
def permutationPoint {T : Scheme.{u}}
    (t : T ⟶ (∏ᶜ fun _ : Fin n => Over.mk f).left)
    (σ : Equiv.Perm (Fin n)) :
    T ⟶ pullback (pullback.fst (map f e).left (map f e).left) t :=
  pullback.lift (t ≫ permutationGraph f e σ) (𝟙 _) (by
    rw [Category.assoc, permutationGraph_fst, Category.comp_id, Category.id_comp])

@[reassoc] theorem permutationPoint_base {T : Scheme.{u}}
    (t : T ⟶ (∏ᶜ fun _ : Fin n => Over.mk f).left)
    (σ : Equiv.Perm (Fin n)) :
    permutationPoint f e t σ ≫
      pullback.snd (pullback.fst (map f e).left (map f e).left) t = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc] theorem permutationPoint_second {T : Scheme.{u}}
    (t : T ⟶ (∏ᶜ fun _ : Fin n => Over.mk f).left)
    (σ : Equiv.Perm (Fin n)) :
    permutationPoint f e t σ ≫
      pullback.fst (pullback.fst (map f e).left (map f e).left) t ≫
        pullback.snd (map f e).left (map f e).left = t ≫ (permute f n σ).left := by
  simp only [permutationPoint, pullback.lift_fst_assoc, Category.assoc,
    permutationGraph_snd]

@[reassoc] theorem permutationPoint_first {T : Scheme.{u}}
    (t : T ⟶ (∏ᶜ fun _ : Fin n => Over.mk f).left)
    (σ : Equiv.Perm (Fin n)) :
    permutationPoint f e t σ ≫
      pullback.fst (pullback.fst (map f e).left (map f e).left) t ≫
        pullback.fst (map f e).left (map f e).left = t := by
  simp only [permutationPoint, pullback.lift_fst_assoc, Category.assoc,
    permutationGraph_fst, Category.comp_id]

end Relative

section CurveKernelPair

variable {k : Type u} [Field k] (C : Curve k) {n : ℕ}
  {H : Over (Spec (.of k))} (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H)

/-- The rank of the base-changed first kernel-pair projection is still
`n!`; over a field this is exactly the dimension of its global algebra. -/
theorem kernelPair_baseChange_finrankΓ {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ (∏ᶜ fun _ : Fin n => C.carrier).left) :
    (pullback.snd (pullback.fst (map C.carrier.hom e).left
      (map C.carrier.hom e).left) t).finrankΓ = n.factorial := by
  obtain ⟨hfin, hflat, _, hrank, _⟩ := curve_map_properties C n H e
  letI := hfin
  letI := hflat
  let g := pullback.snd (pullback.fst (map C.carrier.hom e).left
    (map C.carrier.hom e).left) t
  have hrankg (x : Spec (.of K)) : g.finrank x = n.factorial := by
    dsimp only [g]
    rw [Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_pullback_fst, hrank]
  exact (Scheme.Hom.finrank_eq_finrankΓ_of_field g
    (IsLocalRing.closedPoint K)).symm.trans (hrankg _)

/-- The sum agrees on every permutation graph in the kernel pair. -/
theorem abelianSum_permutationGraph (G : CommGrp (Over (Spec (.of k))))
    (φ : C.carrier ⟶ G.X) (σ : Equiv.Perm (Fin n)) :
    permutationGraph C.carrier.hom e σ ≫
        pullback.fst (map C.carrier.hom e).left (map C.carrier.hom e).left ≫
          (abelianSum C G φ n).left =
      permutationGraph C.carrier.hom e σ ≫
        pullback.snd (map C.carrier.hom e).left (map C.carrier.hom e).left ≫
          (abelianSum C G φ n).left := by
  rw [permutationGraph_fst_assoc, permutationGraph_snd_assoc]
  exact (congrArg CommaMorphism.left (abelianSum_permutation C G φ n σ)).symm

end CurveKernelPair

section Pointed

variable {k : Type u} [Field k]

/-- A smooth curve of relative dimension one cannot be its constant pointed map. -/
theorem curve_id_ne_constant (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) :
    (𝟙 C.carrier) ≠ CartesianMonoidalCategory.toUnit C.carrier ≫ point := by
  intro h
  have hi : C.carrier.hom ≫ point.left = 𝟙 C.carrier.left := by
    have hh := congrArg CommaMorphism.left h
    exact hh.symm
  have hp : point.left ≫ C.carrier.hom = 𝟙 (Spec (.of k)) := Over.w point
  letI : IsIso C.carrier.hom := ⟨⟨point.left, hi, hp⟩⟩
  letI : Nonempty C.carrier.left :=
    Nonempty.map point.left (inferInstance : Nonempty (Spec (.of k)))
  have hzero := topologicalKrullDim_eq_of_smoothOfRelativeDimension C.carrier.hom 0
  have hone := topologicalKrullDim_eq_of_smoothOfRelativeDimension C.carrier.hom 1
  have h01 : (0 : ℕ) = 1 := by exact_mod_cast hzero.symm.trans hone
  exact Nat.zero_ne_one h01

/-- The coordinate projections of a pointed curve power are distinct. -/
theorem curve_projection_ne (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {i j : Fin n} (hij : i ≠ j) :
    Pi.π (fun _ : Fin n => C.carrier) i ≠
      Pi.π (fun _ : Fin n => C.carrier) j := by
  classical
  intro h
  let c : C.carrier ⟶ C.carrier :=
    CartesianMonoidalCategory.toUnit C.carrier ≫ point
  let t := Pi.lift (fun l : Fin n => if l = i then 𝟙 C.carrier else c)
  have ht := congrArg (fun a => t ≫ a) h
  have hji : j ≠ i := Ne.symm hij
  apply curve_id_ne_constant C point
  simpa only [t, Pi.lift_comp_π, if_pos rfl, if_true, if_neg hji, c] using ht

/-- The coordinate permutation action is faithful on a pointed curve. -/
theorem curve_permute_injective (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ) :
    Function.Injective (permute C.carrier.hom n) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  by_contra hne
  apply curve_projection_ne C point n hne
  have hπ := congrArg (fun a => a ≫ Pi.π (fun _ : Fin n => C.carrier) i) h
  change Pi.lift (fun j : Fin n => Pi.π (fun _ : Fin n => C.carrier) (σ j)) ≫
      Pi.π (fun _ : Fin n => C.carrier) i =
    Pi.lift (fun j : Fin n => Pi.π (fun _ : Fin n => C.carrier) (τ j)) ≫
      Pi.π (fun _ : Fin n => C.carrier) i at hπ
  simpa only [Pi.lift_comp_π] using hπ

/-- Integrality and local noetherianness of the literal recursive ordered power. -/
theorem curve_power_integral_noetherian (C : Curve k) (n : ℕ) :
    IsIntegral (power C.carrier.hom n).left ∧
      IsLocallyNoetherian (power C.carrier.hom n).left := by
  letI : Smooth C.carrier.hom := SmoothOfRelativeDimension.smooth 1 C.carrier.hom
  letI : GeometricallyIntegral C.carrier.hom :=
    Smooth.geometricallyIntegral C.carrier.hom
  induction n with
  | zero =>
      change IsIntegral (Spec (.of k)) ∧ IsLocallyNoetherian (Spec (.of k))
      exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
      letI : IsIntegral (power C.carrier.hom n).left := ih.1
      letI : IsLocallyNoetherian (power C.carrier.hom n).left := ih.2
      change IsIntegral (pullback (power C.carrier.hom n).hom C.carrier.hom) ∧
        IsLocallyNoetherian (pullback (power C.carrier.hom n).hom C.carrier.hom)
      exact ⟨inferInstance, inferInstance⟩

/-- Integrality of the chosen categorical power, via the recursive power isomorphism. -/
theorem curve_product_integral (C : Curve k) (n : ℕ) :
    IsIntegral (∏ᶜ fun _ : Fin n => C.carrier).left := by
  letI : IsIntegral (power C.carrier.hom n).left :=
    (curve_power_integral_noetherian C n).1
  letI : IsIso (powerIso C.carrier.hom n).inv := (powerIso C.carrier.hom n).isIso_inv
  letI : IsIso (powerIso C.carrier.hom n).inv.left :=
    (Over.forget (Spec (.of k))).map_isIso (powerIso C.carrier.hom n).inv
  exact IsIntegral.of_isIso (powerIso C.carrier.hom n).inv.left

/-- Distinct coordinate permutations stay distinct over the function field
of the ordered power. Dominance extends an equality of generic coordinate maps. -/
theorem genericPermutation_injective (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ) :
    letI := curve_product_integral C n
    Function.Injective (fun σ : Equiv.Perm (Fin n) =>
      (∏ᶜ fun _ : Fin n => C.carrier).left.fromSpecStalk
        (genericPoint (∏ᶜ fun _ : Fin n => C.carrier).left) ≫
          (permute C.carrier.hom n σ).left) := by
  letI := curve_product_integral C n
  letI : IsIntegral (∏ᶜ fun _ : Fin n => Over.mk C.carrier.hom).left :=
    curve_product_integral C n
  let P := (∏ᶜ fun _ : Fin n => Over.mk C.carrier.hom).left
  let η := P.fromSpecStalk (genericPoint P)
  obtain ⟨hqc, hdom⟩ := genericPointMap_properties P
  letI := hqc
  letI := hdom
  change Function.Injective (fun σ : Equiv.Perm (Fin n) =>
    η ≫ (permute C.carrier.hom n σ).left)
  intro σ τ h
  apply curve_permute_injective C point n
  apply Pi.hom_ext
  intro i
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated (X := P) C.carrier.hom ?_ η ?_
  · simpa only [Over.comp_left, Over.mk_hom] using
      (Over.w (permute C.carrier.hom n σ ≫
        Pi.π (fun _ : Fin n => Over.mk C.carrier.hom) i)).trans
          (Over.w (permute C.carrier.hom n τ ≫
            Pi.π (fun _ : Fin n => Over.mk C.carrier.hom) i)).symm
  · simpa only [Over.comp_left, Category.assoc] using
      congrArg (fun a => a ≫
        (Pi.π (fun _ : Fin n => Over.mk C.carrier.hom) i).left) h

/-- The generic kernel pair has `n!` distinct rational permutation points. -/
theorem genericPermutationPoint_injective (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {H : Over (Spec (.of k))}
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H) :
    letI := curve_product_integral C n
    Function.Injective (fun σ : Equiv.Perm (Fin n) =>
      permutationPoint C.carrier.hom e
        ((∏ᶜ fun _ : Fin n => C.carrier).left.fromSpecStalk
          (genericPoint (∏ᶜ fun _ : Fin n => C.carrier).left)) σ) := by
  letI := curve_product_integral C n
  intro σ τ h
  apply genericPermutation_injective C point n
  have hh := congrArg (fun a => a ≫
    pullback.fst (pullback.fst (map C.carrier.hom e).left
      (map C.carrier.hom e).left)
      ((∏ᶜ fun _ : Fin n => C.carrier).left.fromSpecStalk
        (genericPoint (∏ᶜ fun _ : Fin n => C.carrier).left)) ≫
    pullback.snd (map C.carrier.hom e).left (map C.carrier.hom e).left) h
  simpa only [permutationPoint_second] using hh

/-- Actual generic permutation points exhaust the generic fibre algebra.
`ULift` merely places the finite permutation index in the scheme universe. -/
theorem genericKernelPair_bijective_evaluation (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {H : Over (Spec (.of k))}
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H) :
    letI := curve_product_integral C n
    let P := (∏ᶜ fun _ : Fin n => C.carrier).left
    let η := P.fromSpecStalk (genericPoint P)
    let q := (map C.carrier.hom e).left
    let g := pullback.snd (pullback.fst q q) η
    letI := g.ΓAlgebra
    Function.Bijective (AlgHom.pi (fun σ : ULift.{u} (Equiv.Perm (Fin n)) =>
      rationalPointEvaluation g (permutationPoint C.carrier.hom e η σ.down)
        (permutationPoint_base C.carrier.hom e η σ.down))) := by
  letI := curve_product_integral C n
  let P := (∏ᶜ fun _ : Fin n => C.carrier).left
  let K := P.functionField
  let η : Spec (.of K) ⟶ P := P.fromSpecStalk (genericPoint P)
  let q := (map C.carrier.hom e).left
  let g := pullback.snd (pullback.fst q q) η
  obtain ⟨hfin, hflat, _, _, _⟩ := curve_map_properties C n H e
  letI := hfin
  letI := hflat
  letI : IsAffine (pullback (pullback.fst q q) η) := isAffine_of_isAffineHom g
  letI := g.ΓAlgebra
  letI : Module.Finite K Γ(pullback (pullback.fst q q) η, ⊤) :=
    finite_globalSections_of_isFinite g
  apply AlgHom.evaluation_bijective_of_card_eq_finrank
  · apply rationalPointEvaluation_injective
    intro σ τ h
    apply ULift.ext
    exact genericPermutationPoint_injective C point n e h
  · rw [Fintype.card_ulift, Fintype.card_perm, Fintype.card_fin]
    exact (kernelPair_baseChange_finrankΓ C e η).symm

/-- The generic kernel pair is reduced in every characteristic, even though
the special fibres over repeated divisors need not be reduced. -/
theorem genericKernelPair_isReduced (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {H : Over (Spec (.of k))}
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H) :
    letI := curve_product_integral C n
    let P := (∏ᶜ fun _ : Fin n => C.carrier).left
    IsReduced (pullback (pullback.fst (map C.carrier.hom e).left
      (map C.carrier.hom e).left) (P.fromSpecStalk (genericPoint P))) := by
  letI := curve_product_integral C n
  let P := (∏ᶜ fun _ : Fin n => C.carrier).left
  let K := P.functionField
  let η : Spec (.of K) ⟶ P := P.fromSpecStalk (genericPoint P)
  let q := (map C.carrier.hom e).left
  let Q := pullback (pullback.fst q q) η
  let g : Q ⟶ Spec (.of K) := pullback.snd (pullback.fst q q) η
  obtain ⟨hfin, hflat, _, _, _⟩ := curve_map_properties C n H e
  letI := hfin
  letI := hflat
  letI : IsAffine Q := isAffine_of_isAffineHom g
  letI := g.ΓAlgebra
  letI : _root_.IsReduced Γ(Q, ⊤) :=
    isReduced_of_injective
      (AlgHom.pi (fun σ : ULift.{u} (Equiv.Perm (Fin n)) =>
        rationalPointEvaluation g (permutationPoint C.carrier.hom e η σ.down)
          (permutationPoint_base C.carrier.hom e η σ.down)))
      (genericKernelPair_bijective_evaluation C point n e).injective
  exact isReduced_of_isAffine_isReduced Q

/-- Equality of the sum maps on the generic kernel pair follows from
its exhaustive rational permutation sections. -/
theorem abelianSum_genericKernelPair (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {H : Over (Spec (.of k))}
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H)
    (G : CommGrp (Over (Spec (.of k)))) (φ : C.carrier ⟶ G.X) :
    letI := curve_product_integral C n
    let P := (∏ᶜ fun _ : Fin n => C.carrier).left
    let η := P.fromSpecStalk (genericPoint P)
    let q := (map C.carrier.hom e).left
    pullback.fst (pullback.fst q q) η ≫ pullback.fst q q ≫
        (abelianSum C G φ n).left =
      pullback.fst (pullback.fst q q) η ≫ pullback.snd q q ≫
        (abelianSum C G φ n).left := by
  letI := curve_product_integral C n
  let P := (∏ᶜ fun _ : Fin n => C.carrier).left
  let K := P.functionField
  let η : Spec (.of K) ⟶ P := P.fromSpecStalk (genericPoint P)
  let q := (map C.carrier.hom e).left
  let Q := pullback (pullback.fst q q) η
  let g : Q ⟶ Spec (.of K) := pullback.snd (pullback.fst q q) η
  obtain ⟨hfin, hflat, _, _, _⟩ := curve_map_properties C n H e
  letI := hfin
  letI := hflat
  letI : IsAffine Q := isAffine_of_isAffineHom g
  apply hom_ext_of_bijective_evaluation g
    (fun σ : ULift.{u} (Equiv.Perm (Fin n)) =>
      permutationPoint C.carrier.hom e η σ.down)
    (fun σ => permutationPoint_base C.carrier.hom e η σ.down)
    (genericKernelPair_bijective_evaluation C point n e)
  intro σ
  rw [permutationPoint_first_assoc, permutationPoint_second_assoc]
  simpa only [Over.comp_left, Category.assoc] using congrArg (fun a => η ≫ a)
    (congrArg CommaMorphism.left (abelianSum_permutation C G φ n σ.down)).symm

/-- The sum coequalizes the whole scheme-theoretic kernel pair.
Generic reducedness, flatness and separatedness extend the generic equality;
no condition is imposed on special divisor fibres. -/
theorem abelianSum_kernelPair (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {H : Over (Spec (.of k))}
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H)
    (G : CommGrp (Over (Spec (.of k)))) [IsSeparated G.X.hom]
    (φ : C.carrier ⟶ G.X) :
    pullback.fst (map C.carrier.hom e).left (map C.carrier.hom e).left ≫
        (abelianSum C G φ n).left =
      pullback.snd (map C.carrier.hom e).left (map C.carrier.hom e).left ≫
        (abelianSum C G φ n).left := by
  letI := curve_product_integral C n
  letI : IsIntegral (∏ᶜ fun _ : Fin n => Over.mk C.carrier.hom).left :=
    curve_product_integral C n
  let P := (∏ᶜ fun _ : Fin n => C.carrier).left
  let q := (map C.carrier.hom e).left
  obtain ⟨_, hflat, _, _, _⟩ := curve_map_properties C n H e
  letI := hflat
  letI : IsReduced (pullback (pullback.fst q q)
      (P.fromSpecStalk (genericPoint P))) := genericKernelPair_isReduced C point n e
  apply ext_of_flat_genericPullback (Y := P) (pullback.fst q q) G.X.hom
  · have hw : (abelianSum C G φ n).left ≫ G.X.hom = q ≫ H.hom :=
      (Over.w (abelianSum C G φ n)).trans (Over.w (map C.carrier.hom e)).symm
    calc
      (pullback.fst q q ≫ (abelianSum C G φ n).left) ≫ G.X.hom =
          pullback.fst q q ≫ q ≫ H.hom := by rw [Category.assoc, hw]
      _ = pullback.snd q q ≫ q ≫ H.hom := pullback.condition_assoc H.hom
      _ = (pullback.snd q q ≫ (abelianSum C G φ n).left) ≫ G.X.hom := by
        rw [Category.assoc, hw]
  · exact abelianSum_genericKernelPair C point n e G φ

/-- The ordered sum descends uniquely to the Hilbert representative. -/
theorem existsUnique_abelianSum_descent (C : Curve k)
    (point : 𝟙_ (Over (Spec (.of k))) ⟶ C.carrier) (n : ℕ)
    {H : Over (Spec (.of k))}
    (e : (hilbertPresheaf C.carrier.hom n).RepresentableBy H)
    (G : CommGrp (Over (Spec (.of k)))) [IsSeparated G.X.hom]
    (φ : C.carrier ⟶ G.X) :
    ∃! d : H ⟶ G.X, map C.carrier.hom e ≫ d = abelianSum C G φ n := by
  let q := (map C.carrier.hom e).left
  let s := (abelianSum C G φ n).left
  obtain ⟨hfin, hflat, _, _, hsurj⟩ := curve_map_properties C n H e
  letI := hfin
  letI := hflat
  letI := hsurj
  have hpair := abelianSum_kernelPair C point n e G φ
  have hcompat : ∀ {T : Scheme.{u}} (a b : T ⟶ (∏ᶜ fun _ : Fin n => C.carrier).left),
      a ≫ q = b ≫ q → a ≫ s = b ≫ s := by
    intro T a b hab
    have h : (pullback.lift a b hab ≫ pullback.fst q q) ≫ s =
        (pullback.lift a b hab ≫ pullback.snd q q) ≫ s := by
      simpa only [Category.assoc] using
        congrArg (fun v => pullback.lift a b hab ≫ v) hpair
    rw [pullback.lift_fst, pullback.lift_snd] at h
    exact h
  let d : H.left ⟶ G.X.left := EffectiveEpi.desc q s hcompat
  have hd : q ≫ d = s := EffectiveEpi.fac q s hcompat
  have hd_base : d ≫ G.X.hom = H.hom := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, hd]
    exact (Over.w (abelianSum C G φ n)).trans (Over.w (map C.carrier.hom e)).symm
  refine ⟨Over.homMk d hd_base, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hd
  · intro d' hd'
    apply Over.OverMorphism.ext
    apply (cancel_epi q).mp
    exact (congrArg CommaMorphism.left hd').trans hd.symm

end Pointed


end AlgebraicGeometry.Hilbert.OrderedDivisors
