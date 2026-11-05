import Jacobian.AlgebraicGeometry.Modules.FreeComplexLocus
import Jacobian.AlgebraicGeometry.Modules.LocallyFree
import Jacobian.AlgebraicGeometry.Modules.RestrictionLimits
import Jacobian.AlgebraicGeometry.Modules.Vanishing
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The single-degree locus of a finite free complex

For a bounded complex of finite free module sheaves, the locus where the derived
fibres have prescribed rank in one degree and vanish in every other degree is
open. After arbitrary base change into this locus, the homology is finite locally
free of that rank in the specified degree and zero elsewhere. In degree zero and
rank one this gives an invertible module with all higher homology zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A complex of finite free module sheaves concentrated in degrees `[0, d]`. -/
structure IsFiniteFreeComplex (P : CochainComplex X.Modules ℤ) (d : ℕ) : Prop where
  isStrictlyGE : P.IsStrictlyGE 0
  isStrictlyLE : P.IsStrictlyLE d
  exists_iso_free (n : ℤ) :
    ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))

/-- A family of module sheaves vanishes except in degree `i`, where it is finite
locally free of rank `r`. -/
structure IsFiniteLocallyFreeInDegree (M : ℕ → X.Modules) (i r : ℕ) : Prop where
  isZero (q : ℕ) (hq : q ≠ i) : IsZero (M q)
  isFiniteLocallyFreeOfRank : (M i).IsFiniteLocallyFreeOfRank r

/-- The single-degree local freeness property is invariant under termwise isomorphisms. -/
theorem IsFiniteLocallyFreeInDegree.of_iso {M N : ℕ → X.Modules} {i r : ℕ}
    (h : IsFiniteLocallyFreeInDegree M i r) (e : ∀ q, M q ≅ N q) :
    IsFiniteLocallyFreeInDegree N i r := by
  letI := h.isFiniteLocallyFreeOfRank
  exact ⟨fun q hq ↦ (h.isZero q hq).of_iso (e q).symm,
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e i)⟩

/-- Rank one in degree zero means invertibility in degree zero and higher vanishing. -/
theorem isFiniteLocallyFreeInDegree_zero_one_iff (M : ℕ → X.Modules) :
    IsFiniteLocallyFreeInDegree M 0 1 ↔
      (∀ q ≠ 0, IsZero (M q)) ∧ SheafOfModules.IsInvertible.{u, u, u} (M 0) :=
  ⟨fun h ↦ ⟨h.isZero, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).2
      h.isFiniteLocallyFreeOfRank⟩,
    fun h ↦ ⟨h.1, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).1 h.2⟩⟩

/-- Choose trivializations whose ranks are zero outside the bounds of the complex. -/
lemma IsFiniteFreeComplex.exists_iso_free_of_rank_eq_zero {P : CochainComplex X.Modules ℤ}
    {d : ℕ} (hP : IsFiniteFreeComplex P d) :
    ∃ r : ℤ → ℕ, (∀ n : ℤ, n < 0 ∨ d < n → r n = 0) ∧
      Nonempty (∀ n, P.X n ≅
        SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r n)))) := by
  classical
  choose r₀ e₀ using hP.exists_iso_free
  have := hP.isStrictlyGE
  have := hP.isStrictlyLE
  refine ⟨fun n ↦ if n < 0 ∨ (d : ℤ) < n then 0 else r₀ n, fun n hn ↦ if_pos hn, ⟨fun n ↦ ?_⟩⟩
  by_cases hn : n < 0 ∨ (d : ℤ) < n
  · have h₁ : IsZero (P.X n) := by
      rcases hn with hn | hn
      · exact CochainComplex.isZero_of_isStrictlyGE P 0 n hn
      · exact CochainComplex.isZero_of_isStrictlyLE P d n hn
    refine h₁.iso ?_
    simp only [if_pos hn]
    exact isZero_free_of_isEmpty _
  · simp only [if_neg hn]
    exact (e₀ n).some

/-- The locus where the derived fibre has dimension `r` in degree `i` and zero
dimension in every other degree. -/
def homologyRankLocus (P : CochainComplex X.Modules ℤ) (i r : ℕ) : Set X :=
  {x | ∀ q : ℤ, Module.finrank (X.residueField x)
    ((moduleSpecΓFunctor (R := .of (X.residueField x))).obj
      ((((Modules.pullback (X.fromSpecResidueField x)).mapHomologicalComplex _).obj P).homology q)) =
        if q = (i : ℤ) then r else 0}

/-- The numerical fibre condition is equivalent to the rank equations for the
matrices of the differentials in any finite free trivialization. -/
lemma mem_homologyRankLocus_iff_rankCondition {P : CochainComplex X.Modules ℤ}
    {rk : ℤ → ℕ}
    (e : ∀ n, P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (rk n))))
    (i r : ℕ) (x : X) :
    x ∈ homologyRankLocus P i r ↔
      Scheme.RankCondition (fun n m ↦ freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom)) i r x := by
  constructor
  · intro hx q
    have hdim := finrank_homology_pullback_add_rank_add_rank e
      (Field.toIsField (X.residueField x)) (X.fromSpecResidueField x) q
    have hxq := hx q
    simp only [Fintype.card_ulift, Fintype.card_fin]
    omega
  · intro hx q
    have hdim := finrank_homology_pullback_add_rank_add_rank e
      (Field.toIsField (X.residueField x)) (X.fromSpecResidueField x) q
    have hxq := hx q
    simp only [Fintype.card_ulift, Fintype.card_fin] at hxq
    omega

/-- The single-degree, fixed-rank derived-fibre locus of a finite free complex is open. -/
theorem IsFiniteFreeComplex.isOpen_homologyRankLocus {P : CochainComplex X.Modules ℤ}
    {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ) :
    IsOpen (homologyRankLocus P i r) := by
  classical
  obtain ⟨rk, hrk, ⟨e⟩⟩ := hP.exists_iso_free_of_rank_eq_zero
  let C : ∀ n m : ℤ, Matrix (ULift.{u} (Fin (rk m))) (ULift.{u} (Fin (rk n))) Γ(X, ⊤) :=
    fun n m ↦ freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom)
  have hC (n m l : ℤ) : C m l * C n m = 0 := by
    dsimp only [C]
    rw [← freeMatrix_comp]
    simp
  have hN (n : ℤ) (hn : n < 0 ∨ d < n) : IsEmpty (ULift.{u} (Fin (rk n))) := by
    rw [hrk n hn]
    infer_instance
  have heq : homologyRankLocus P i r = {x | Scheme.RankCondition C i r x} := by
    ext x
    exact mem_homologyRankLocus_iff_rankCondition e i r x
  rw [heq]
  exact Scheme.isOpen_setOf_rankCondition hC d hN i r

/-- Arbitrary base change into the single-degree fibre locus has finite locally
free homology of the prescribed rank, with every other nonnegative degree zero. -/
theorem IsFiniteFreeComplex.isFiniteLocallyFreeInDegree_of_range_subset
    {P : CochainComplex X.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ)
    {Y : Scheme.{u}} (g : Y ⟶ X) (hg : Set.range g ⊆ homologyRankLocus P i r) :
    IsFiniteLocallyFreeInDegree
      (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r := by
  classical
  obtain ⟨rk, hrk, ⟨e⟩⟩ := hP.exists_iso_free_of_rank_eq_zero
  set C : ∀ n m : ℤ, Matrix (ULift.{u} (Fin (rk m))) (ULift.{u} (Fin (rk n))) Γ(X, ⊤) :=
    fun n m ↦ freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom) with hCdef
  have hC (n m l : ℤ) : C m l * C n m = 0 := by
    simp only [hCdef]
    rw [← freeMatrix_comp]
    simp
  have hN (n : ℤ) (hn : n < 0 ∨ d < n) : IsEmpty (ULift.{u} (Fin (rk n))) := by
    rw [hrk n hn]
    infer_instance
  set Pg := ((Modules.pullback g).mapHomologicalComplex _).obj P
  let eg (n : ℤ) : Pg.X n ≅ SheafOfModules.free (ULift.{u} (Fin (rk n))) :=
    (Modules.pullback g).mapIso (e n) ≪≫ pullbackFreeIso g _
  have hCg (n m : ℤ) {Z : Scheme.{u}} (j : Z ⟶ Y) :
      freeMatrix ((((Modules.pullback j).mapIso (eg n) ≪≫ pullbackFreeIso j _).inv ≫
        (((Modules.pullback j).mapHomologicalComplex _).obj Pg).d n m ≫
        ((Modules.pullback j).mapIso (eg m) ≪≫ pullbackFreeIso j _).hom)) =
        (C n m).map (j ≫ g).appTop := by
    rw [freeMatrix_pullback_d, freeMatrix_pullback_d, map_appTop_comp]
  have hy (y : Y) : Scheme.RankCondition C i r (g y) :=
    (mem_homologyRankLocus_iff_rankCondition e i r (g y)).1 (hg ⟨y, rfl⟩)
  choose W hyW hW using fun y ↦ Scheme.exists_opens_hasSplitHomology hC d hN (hy y)
  let V : Y → Y.Opens := fun y ↦ g ⁻¹ᵁ W y
  have key (y : Y) (q : ℤ) : Nonempty ((Pg.homology q).restrict (V y).ι ≅
      SheafOfModules.free (ULift.{u} (Fin (if q = i then r else 0)))) := by
    let j := (V y).ι
    letI : PreservesFiniteLimits (Modules.pullback j) :=
      preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback j)
    obtain ⟨I, Pm, σ, τ, h₁, h₂, h₃, h₄⟩ :=
      (hW y (j ≫ g) (by rintro _ ⟨z, rfl⟩; exact z.2) q).of_equiv Equiv.ulift.symm
    let E (n : ℤ) := (Modules.pullback j).mapIso (eg n) ≪≫
      pullbackFreeIso j (ULift.{u} (Fin (rk n)))
    obtain ⟨φ⟩ := nonempty_homology_iso_free_of_split
      (((Modules.pullback j).mapHomologicalComplex _).obj Pg) q (E (q - 1)) (E q) (E (q + 1))
      σ τ I Pm h₁ (by rw [hCg]; exact h₂) (by rw [hCg]; exact h₃)
      (by rw [hCg, hCg]; exact h₄)
    exact ⟨(restrictFunctorIsoPullback j).app _ ≪≫
      ((Pg.sc q).mapHomologyIso (Modules.pullback j)).symm ≪≫ φ⟩
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · refine isZero_of_forall_exists_isZero_restrict _ fun y ↦ ⟨V y, hyW y, ?_⟩
    have : IsEmpty (ULift.{u} (Fin (if (q : ℤ) = i then r else 0))) := by
      rw [if_neg (by exact_mod_cast hq)]
      infer_instance
    exact (isZero_free_of_isEmpty _).of_iso (key y q).some
  · have hV : ⨆ y, V y = ⊤ :=
      eq_top_iff.2 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩
    exact isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun y ↦ (V y).ι)
      (by simpa using hV) fun y ↦ ⟨(key y i).some ≪≫ eqToIso (by rw [if_pos rfl])⟩

/-- An open locus defined by fibre homology, with a universal base-change property. -/
theorem IsFiniteFreeComplex.exists_opens_isFiniteLocallyFreeInDegree
    {P : CochainComplex X.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ) :
    ∃ U : X.Opens, (U : Set X) = homologyRankLocus P i r ∧
      ∀ {Y : Scheme.{u}} (g : Y ⟶ X), Set.range g ⊆ U →
        IsFiniteLocallyFreeInDegree
          (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r :=
  ⟨⟨_, hP.isOpen_homologyRankLocus i r⟩, rfl,
    fun g hg ↦ hP.isFiniteLocallyFreeInDegree_of_range_subset i r g hg⟩

/-- On the rank-one degree-zero locus, every base change has invertible zeroth
homology and vanishing higher homology. -/
theorem IsFiniteFreeComplex.exists_opens_invertible_and_higher_vanishing
    {P : CochainComplex X.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) :
    ∃ U : X.Opens, (U : Set X) = homologyRankLocus P 0 1 ∧
      ∀ {Y : Scheme.{u}} (g : Y ⟶ X), Set.range g ⊆ U →
        SheafOfModules.IsInvertible.{u, u, u}
          ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology 0) ∧
        ∀ q : ℕ, q ≠ 0 →
          IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) := by
  obtain ⟨U, hU, h⟩ := hP.exists_opens_isFiniteLocallyFreeInDegree 0 1
  refine ⟨U, hU, fun g hg ↦ ?_⟩
  obtain ⟨hzero, hinv⟩ := (isFiniteLocallyFreeInDegree_zero_one_iff _).1 (h g hg)
  exact ⟨hinv, hzero⟩

end AlgebraicGeometry.Scheme.Modules
