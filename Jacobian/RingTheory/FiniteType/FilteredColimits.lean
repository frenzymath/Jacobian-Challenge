import Jacobian.LinearAlgebra.TensorProduct.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Finiteness at a finite stage

Integrality of finitely many generators descends along directed ring colimits.
Consequently a finite type algebra map that becomes finite after base change
to a directed colimit is finite after base change to some finite stage.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u v t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

private theorem integral_at_stage
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (B C : J → Type*) [∀ j, CommRing (B j)] [∀ j, CommRing (C j)]
    {Bcolim Ccolim : Type*} [CommRing Bcolim] [CommRing Ccolim]
    (bmap : ∀ {i j : J}, i ≤ j → B i →+* B j)
    (cmap : ∀ {i j : J}, i ≤ j → C i →+* C j)
    (bι : ∀ j, B j →+* Bcolim) (cι : ∀ j, C j →+* Ccolim)
    (φ : ∀ j, B j →+* C j) (φcolim : Bcolim →+* Ccolim)
    (bcompat : ∀ {i j} (h : i ≤ j) b, bι j (bmap h b) = bι i b)
    (φcompat : ∀ j b, cι j (φ j b) = φcolim (bι j b))
    (φtrans : ∀ {i j} (h : i ≤ j) b, cmap h (φ i b) = φ j (bmap h b))
    (rep : ∀ b : Bcolim, ∃ j, ∃ t : B j, bι j t = b)
    (zero : ∀ j (z : C j), cι j z = 0 → ∃ k, ∃ h : j ≤ k, cmap h z = 0)
    (x : ∀ j, C j) (xcolim : Ccolim)
    (hx : ∀ j, cι j (x j) = xcolim)
    (htrans : ∀ {i j} (h : i ≤ j), cmap h (x i) = x j)
    (hi : φcolim.IsIntegralElem xcolim) : ∃ j, (φ j).IsIntegralElem (x j) := by
  classical
  obtain ⟨p, hp, heval⟩ := hi
  choose stage coeff hcoeff using fun k : Fin p.natDegree ↦ rep (p.coeff k)
  obtain ⟨j, hj⟩ := (Finset.univ.image stage).exists_le
  have hstage (k : Fin p.natDegree) : stage k ≤ j :=
    hj _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  let q : Polynomial (B j) := Polynomial.X ^ p.natDegree +
    ∑ k : Fin p.natDegree, Polynomial.C (bmap (hstage k) (coeff k)) * Polynomial.X ^ (k : ℕ)
  have hq : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hqmap : q.map (bι j) = p := by
    rw [hp.as_sum]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, bcompat, hcoeff]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun k ↦ Polynomial.C (p.coeff k) * Polynomial.X ^ k) p.natDegree
  have hvanish : cι j (q.eval₂ (φ j) (x j)) = 0 := by
    have hcomm : (cι j).comp (φ j) = φcolim.comp (bι j) := by
      ext b
      exact φcompat j b
    rw [Polynomial.hom_eval₂, hcomm, ← Polynomial.eval₂_map, hx, hqmap]
    exact heval
  obtain ⟨k, hjk, hk⟩ := zero j (q.eval₂ (φ j) (x j)) hvanish
  refine ⟨k, q.map (bmap hjk), hq.map _, ?_⟩
  have hcomm : (cmap hjk).comp (φ j) = (φ k).comp (bmap hjk) := by
    ext b
    exact φtrans hjk b
  rw [Polynomial.eval₂_map, ← htrans hjk, ← hcomm, ← Polynomial.hom_eval₂]
  exact hk

/-- Generators integral after tensoring with a directed colimit are integral at one stage. -/
theorem exists_integral_tensor_generators_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (s : Finset C₀) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (∀ x ∈ s,
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom.IsIntegralElem
          ((1 : (colimit F : CommRingCat.{u})) ⊗ₜ[F.obj i₀] x)) →
      ∃ (i : I) (h : i₀ ≤ i),
        letI : Algebra (F.obj i₀) (F.obj i) :=
          (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
        ∀ x ∈ s,
          (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).toRingHom.IsIntegralElem
            ((1 : F.obj i) ⊗ₜ[F.obj i₀] x) := by
  classical
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  intro hint
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let T : J → Type u := fun j ↦ F.obj j.val
  let : ∀ j, CommRing (T j) := fun j ↦ inferInstance
  let : ∀ j, Algebra S (T j) := fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  let trans (i j : J) (h : i ≤ j) : T i →ₐ[S] T j :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f a)
        (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let incl (j : J) : T j →ₐ[S] R :=
    { (colimit.ι F j.val).hom with
      commutes' := fun a ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f a)
        (colimit.w F (homOfLE j.property)) }
  let B (j : J) := T j ⊗[S] B₀
  let C (j : J) := T j ⊗[S] C₀
  let bmap {i j : J} (h : i ≤ j) : B i →+* B j :=
    (Algebra.TensorProduct.map (trans i j h) (AlgHom.id S B₀)).toRingHom
  let cmap {i j : J} (h : i ≤ j) : C i →+* C j :=
    (Algebra.TensorProduct.map (trans i j h) (AlgHom.id S C₀)).toRingHom
  let bι (j : J) : B j →+* (R ⊗[S] B₀) :=
    (Algebra.TensorProduct.map (incl j) (AlgHom.id S B₀)).toRingHom
  let cι (j : J) : C j →+* (R ⊗[S] C₀) :=
    (Algebra.TensorProduct.map (incl j) (AlgHom.id S C₀)).toRingHom
  let φ (j : J) : B j →+* C j :=
    (Algebra.TensorProduct.map (AlgHom.id S (T j)) φ₀).toRingHom
  let φcolim : (R ⊗[S] B₀) →+* (R ⊗[S] C₀) :=
    (Algebra.TensorProduct.map (AlgHom.id S R) φ₀).toRingHom
  have bcompat {i j : J} (h : i ≤ j) (b : B i) :
      bι j (bmap h b) = bι i b := by
    induction b using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul t b =>
      change incl j (trans i j h t) ⊗ₜ[S] b = incl i t ⊗ₜ[S] b
      congr 1
      exact ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) t
    | add x y hx hy => simp only [map_add, hx, hy]
  have φcompat (j : J) (b : B j) : cι j (φ j b) = φcolim (bι j b) := by
    induction b using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul t b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have φtrans {i j : J} (h : i ≤ j) (b : B i) :
      cmap h (φ i b) = φ j (bmap h b) := by
    induction b using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul t b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have rep (b : R ⊗[S] B₀) : ∃ j, ∃ t : B j, bι j t = b := by
    obtain ⟨i, h, t, ht⟩ := (TensorProduct.directedColimitBaseChangeElementwise F i₀ B₀).1 b
    exact ⟨⟨i, h⟩, t, ht⟩
  have zero (j : J) (z : C j) (hz : cι j z = 0) :
      ∃ k, ∃ h : j ≤ k, cmap h z = 0 := by
    obtain ⟨k, h, hk⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ C₀).2 j.val j.property z hz
    exact ⟨⟨k, j.property.trans h⟩, h, hk⟩
  have hsingle (x : C₀) (hx : x ∈ s) :
      ∃ j, (φ j).IsIntegralElem ((1 : T j) ⊗ₜ[S] x) := by
    apply integral_at_stage B C bmap cmap bι cι φ φcolim bcompat φcompat φtrans rep zero
      (fun j ↦ (1 : T j) ⊗ₜ[S] x) ((1 : R) ⊗ₜ[S] x)
    · intro j
      change incl j 1 ⊗ₜ[S] x = (1 : R) ⊗ₜ[S] x
      rw [map_one]
    · intro i j h
      change trans i j h 1 ⊗ₜ[S] x = (1 : T j) ⊗ₜ[S] x
      rw [map_one]
    · exact hint x hx
  choose stage hstage using fun x : s ↦ hsingle x.val x.property
  obtain ⟨j, hj⟩ := (Finset.univ.image stage).exists_le
  refine ⟨j.val, j.property, ?_⟩
  intro x hx
  let x' : s := ⟨x, hx⟩
  have hle : stage x' ≤ j := hj _ (Finset.mem_image.mpr ⟨x', Finset.mem_univ _, rfl⟩)
  have hi := (hstage x').map (cmap hle)
  have heq : (cmap hle).comp (φ (stage x')) = (φ j).comp (bmap hle) := by
    exact RingHom.ext (φtrans hle)
  rw [heq] at hi
  have ht : cmap hle ((1 : T (stage x')) ⊗ₜ[S] x) = (1 : T j) ⊗ₜ[S] x := by
    change trans (stage x') j hle 1 ⊗ₜ[S] x = (1 : T j) ⊗ₜ[S] x
    rw [map_one]
  rw [ht] at hi
  exact hi.of_comp

end RingHom
end

section
universe u v t

open CategoryTheory CategoryTheory.Limits

namespace RingHom

private theorem adjoin_tensor_generators
    {R T B C : Type*} [CommRing R] [CommRing T] [CommRing B] [CommRing C]
    [Algebra R T] [Algebra R B] [Algebra R C] (φ : B →ₐ[R] C)
    (s : Finset C)
    (hs : letI := φ.toRingHom.toAlgebra; Algebra.adjoin B (s : Set C) = ⊤) :
    let ψ := Algebra.TensorProduct.map (AlgHom.id R T) φ
    letI := ψ.toRingHom.toAlgebra
    Algebra.adjoin (TensorProduct R T B)
      ((fun c ↦ TensorProduct.tmul R (1 : T) c) '' (s : Set C)) = ⊤ := by
  let ψ := Algebra.TensorProduct.map (AlgHom.id R T) φ
  let := ψ.toRingHom.toAlgebra
  let D := Algebra.adjoin (TensorProduct R T B)
    ((fun c ↦ TensorProduct.tmul R (1 : T) c) '' (s : Set C))
  have hright (c : C) : TensorProduct.tmul R (1 : T) c ∈ D := by
    let := φ.toRingHom.toAlgebra
    have hc : c ∈ Algebra.adjoin B (s : Set C) := by rw [hs]; trivial
    induction hc using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap b =>
      exact D.algebraMap_mem (TensorProduct.tmul R (1 : T) b)
    | add x y hx hy ihx ihy =>
      simpa only [TensorProduct.tmul_add] using D.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using D.mul_mem ihx ihy
  apply top_unique
  intro z _
  change z ∈ D
  induction z using TensorProduct.inductionOn with
  | tmul t c =>
    have ht : TensorProduct.tmul R t (1 : C) ∈ D := by
      have heq :
          algebraMap (TensorProduct R T B) (TensorProduct R T C)
            (TensorProduct.tmul R t (1 : B)) =
          TensorProduct.tmul R t (1 : C) := by
        change ψ (TensorProduct.tmul R t (1 : B)) = _
        simp only [ψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      rw [← heq]
      exact D.algebraMap_mem _
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using
      D.mul_mem ht (hright c)
  | add x y ihx ihy => exact D.add_mem (ihx trivial) (ihy trivial)

/-- A finite type map becoming finite over a directed colimit is finite at a finite stage. -/
theorem exists_finite_tensorProductMap_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hft : φ₀.FiniteType) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (Algebra.TensorProduct.map
      (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).Finite →
      ∃ (i : I) (h : i₀ ≤ i),
        letI : Algebra (F.obj i₀) (F.obj i) :=
          (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).Finite := by
  classical
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
    (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
  intro hfinite
  let : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  have hint : ∀ x ∈ s,
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom.IsIntegralElem
          (TensorProduct.tmul (F.obj i₀) (1 : (colimit F : CommRingCat.{u})) x) := by
    intro x _
    exact hfinite.to_isIntegral _
  obtain ⟨i, h, hi⟩ := exists_integral_tensor_generators_of_colimit F i₀ B₀ C₀ φ₀ s hint
  refine ⟨i, h, ?_⟩
  let : Algebra (F.obj i₀) (F.obj i) :=
    (CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra
  let ψ := Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀
  let := ψ.toRingHom.toAlgebra
  have hgen := adjoin_tensor_generators (T := F.obj i) φ₀ s hs
  have hm : Module.Finite (TensorProduct (F.obj i₀) (F.obj i) B₀)
      (Algebra.adjoin (TensorProduct (F.obj i₀) (F.obj i) B₀)
        ((fun c ↦ TensorProduct.tmul (F.obj i₀) (1 : F.obj i) c) '' (s : Set C₀))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hi x hx)
  rw [hgen] at hm
  exact Module.Finite.of_surjective (Subalgebra.topEquiv.toLinearMap) (by
    exact Subalgebra.topEquiv.surjective)

end RingHom
end
