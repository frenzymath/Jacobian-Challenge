import Jacobian.AlgebraicGeometry.IdealSheaf.Colon
import Jacobian.AlgebraicGeometry.GlobalSections.Disjoint
import Jacobian.AlgebraicGeometry.FiniteOverField
import Jacobian.RingTheory.Ideal.Quotient.Product

/-!
# Additivity of the length of finite Cartier divisors

Finite closed subschemes over a field decompose into finitely many disjoint
pieces on which Cartier ideals have regular equations. The exact sequence for
a product of regular equations gives additivity of their dimensions of sections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Limits Opposite
open scoped nonZeroDivisors

namespace AlgebraicGeometry

variable {K : Type u} [Field K]


/-- For an affine open `W` of a scheme `Y` over a field `K` and an ideal sheaf `I`, the
`K`-algebra of sections of `V(I)` over the preimage of `W` is `Γ(Y, W) ⧸ I(W)`. -/
lemma Scheme.IdealSheafData.nonempty_algEquiv_sections_preimage {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of K)) (I : Y.IdealSheafData) (W : Y.affineOpens) :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫
      (I.subschemeι ≫ q).appLE ⊤ (I.subschemeι ⁻¹ᵁ W.1) le_top).hom.toAlgebra
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ W.1 le_top).hom.toAlgebra
    Nonempty (Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W.1) ≃ₐ[K] Γ(Y, W.1) ⧸ I.ideal W) := by
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫
    (I.subschemeι ≫ q).appLE ⊤ (I.subschemeι ⁻¹ᵁ W.1) le_top).hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ W.1 le_top).hom.toAlgebra
  have key : (I.subschemeι ≫ q).appLE ⊤ (I.subschemeι ⁻¹ᵁ W.1) le_top =
      q.appLE ⊤ W.1 le_top ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) ≫
        (I.subschemeObjIso W).inv := by
    rw [← subschemeι_app, ← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  refine ⟨AlgEquiv.ofRingEquiv (f := (I.subschemeObjIso W).commRingCatIsoToRingEquiv) ?_⟩
  intro k
  change (I.subschemeObjIso W).hom (((Scheme.ΓSpecIso (.of K)).inv ≫
    (I.subschemeι ≫ q).appLE ⊤ (I.subschemeι ⁻¹ᵁ W.1) le_top) k) =
      Ideal.Quotient.mk _ (((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ W.1 le_top) k)
  rw [key]
  simp

/-- Sections of a finite scheme are finite over the field, using its top-section map. -/
private lemma finite_sections_appLE_top {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K))
    [IsFinite g] :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ le_top).hom.toAlgebra
    Module.Finite K Γ(Z, ⊤) := by
  let P : (K →+* Γ(Z, ⊤)) → Prop := fun φ =>
    letI := φ.toAlgebra
    Module.Finite K Γ(Z, ⊤)
  have hfinite : P (((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom) :=
    finite_globalSections_of_isFinite g
  have hmap : ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ le_top).hom =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  change P ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ le_top).hom
  exact hmap.symm ▸ hfinite

/-- Dimensions add when finite Cartier divisors are added by multiplying their ideals. -/
lemma Scheme.IdealSheafData.finrankΓ_subschemeι_mul_comp {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of K)) {I J : Y.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible)
    [IsFinite (I.subschemeι ≫ q)] [IsFinite (J.subschemeι ≫ q)]
    [IsFinite ((I * J).subschemeι ≫ q)] :
    ((I * J).subschemeι ≫ q).finrankΓ =
      (I.subschemeι ≫ q).finrankΓ + (J.subschemeι ≫ q).finrankΓ := by
  classical
  obtain ⟨hZfin, hZdisc⟩ := finite_and_discreteTopology_of_isFinite ((I * J).subschemeι ≫ q)
  have : Fintype (I * J).subscheme := Fintype.ofFinite _
  set F : Finset Y := Finset.univ.image (I * J).subschemeι
  have hF : (F : Set Y) = ((I * J).support : Set Y) := by
    rw [← range_subschemeι]
    ext y
    simp [F]
  have hFclosed (y : Y) : IsClosed ((F : Set Y) \ {y}) := by
    have e : (F : Set Y) \ {y} = ⋃ z ∈ ((F.erase y : Finset Y) : Set Y), {z} := by
      ext z
      simp [and_comm]
    rw [e]
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun z hz ↦ ?_
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hz)
    rw [← Set.image_singleton]
    exact (I * J).subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_discrete _)
  have hW (y : Y) (hy : y ∈ F) : ∃ W : Y.affineOpens, y ∈ W.1 ∧
      W.1 ≤ ⟨((F : Set Y) \ {y})ᶜ, (hFclosed y).isOpen_compl⟩ ∧
      (I.ideal W).IsRegularPrincipal ∧ (J.ideal W).IsRegularPrincipal :=
    exists_affineOpens_isRegularPrincipal hI hJ (by simp)
  have : Nonempty Y.affineOpens := ⟨⟨⊥, isAffineOpen_bot Y⟩⟩
  choose! W hyW hWF hWI hWJ using hW
  have hdecomp (L : Y.IdealSheafData) (hL : (L.support : Set Y) ⊆ (F : Set Y)) :
      ((F : Set Y).PairwiseDisjoint fun y ↦ L.subschemeι ⁻¹ᵁ (W y).1) ∧
        ⨆ y ∈ F, L.subschemeι ⁻¹ᵁ (W y).1 = ⊤ := by
    have hmem (x : L.subscheme) (y : Y) (hy : y ∈ F) (hx : L.subschemeι x ∈ (W y).1) :
        L.subschemeι x = y := by
      have hxF : L.subschemeι x ∈ (F : Set Y) := hL (by rw [← range_subschemeι]; exact ⟨x, rfl⟩)
      by_contra hne
      exact hWF y hy hx ⟨hxF, hne⟩
    refine ⟨fun y hy y' hy' hne ↦ ?_, ?_⟩
    · rw [Function.onFun, disjoint_iff, eq_bot_iff]
      rintro x ⟨hx, hx'⟩
      exact hne ((hmem x y hy hx).symm.trans (hmem x y' hy' hx'))
    · rw [eq_top_iff]
      rintro x -
      have hxF : L.subschemeι x ∈ F := hL (by rw [← range_subschemeι]; exact ⟨x, rfl⟩)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨L.subschemeι x,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨hxF, hyW _ hxF⟩⟩
  have hsupp (L : Y.IdealSheafData) (hL : L.support ≤ (I * J).support) :
      (L.support : Set Y) ⊆ (F : Set Y) := by
    rw [hF]
    exact hL
  obtain ⟨hfIJ, hrIJ⟩ := finite_and_finrank_sections_iSup ((I * J).subschemeι ≫ q)
    (fun y ↦ (I * J).subschemeι ⁻¹ᵁ (W y).1) F (hdecomp _ (hsupp _ le_rfl)).1 ⊤
    (hdecomp _ (hsupp _ le_rfl)).2 (finite_sections_appLE_top _)
  obtain ⟨hfI, hrI⟩ := finite_and_finrank_sections_iSup (I.subschemeι ≫ q)
    (fun y ↦ I.subschemeι ⁻¹ᵁ (W y).1) F (hdecomp _ (hsupp _ (by simp))).1 ⊤
    (hdecomp _ (hsupp _ (by simp))).2 (finite_sections_appLE_top _)
  obtain ⟨hfJ, hrJ⟩ := finite_and_finrank_sections_iSup (J.subschemeι ≫ q)
    (fun y ↦ J.subschemeι ⁻¹ᵁ (W y).1) F (hdecomp _ (hsupp _ (by simp))).1 ⊤
    (hdecomp _ (hsupp _ (by simp))).2 (finite_sections_appLE_top _)
  simp only [Scheme.Hom.finrankΓ_eq_finrank_appLE]
  rw [hrIJ, hrI, hrJ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  obtain ⟨a, ha, haI⟩ := hWI y hy
  obtain ⟨b, hb, hbJ⟩ := hWJ y hy
  obtain ⟨eIJ⟩ := nonempty_algEquiv_sections_preimage q (I * J) (W y)
  obtain ⟨eI⟩ := nonempty_algEquiv_sections_preimage q I (W y)
  obtain ⟨eJ⟩ := nonempty_algEquiv_sections_preimage q J (W y)
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ (W y).1 le_top).hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ ((I * J).subschemeι ≫ q).appLE ⊤
    ((I * J).subschemeι ⁻¹ᵁ (W y).1) le_top).hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ (I.subschemeι ≫ q).appLE ⊤
    (I.subschemeι ⁻¹ᵁ (W y).1) le_top).hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ (J.subschemeι ≫ q).appLE ⊤
    (J.subschemeι ⁻¹ᵁ (W y).1) le_top).hom.toAlgebra
  have := hfI y hy
  have := hfJ y hy
  have : Module.Finite K (Γ(Y, (W y).1) ⧸ Ideal.span {a}) := by
    rw [← haI]
    exact Module.Finite.equiv eI.toLinearEquiv
  have : Module.Finite K (Γ(Y, (W y).1) ⧸ Ideal.span {b}) := by
    rw [← hbJ]
    exact Module.Finite.equiv eJ.toLinearEquiv
  rw [eIJ.toLinearEquiv.finrank_eq, eI.toLinearEquiv.finrank_eq, eJ.toLinearEquiv.finrank_eq,
    ideal_mul, Pi.mul_apply, haI, hbJ, Ideal.span_singleton_mul_span_singleton]
  exact (Ideal.Quotient.finrank_span_singleton_mul a b ha).2

end AlgebraicGeometry
