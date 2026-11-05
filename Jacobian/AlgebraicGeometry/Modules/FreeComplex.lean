import Jacobian.Algebra.Category.ModuleCat.RankRange
import Jacobian.Algebra.Homology.ShortComplex.ModuleCat
import Jacobian.AlgebraicGeometry.Field
import Jacobian.AlgebraicGeometry.Modules.Field
import Jacobian.AlgebraicGeometry.Modules.FreeMatrix
import Jacobian.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Fiber homology of finite free complexes

The fiber homology of a termwise finite free complex is finite-dimensional. Its dimension is the middle rank minus the ranks of the two differentials, and is upper semicontinuous, as witnessed by nonvanishing minors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Module SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- **The rank of a matrix of functions is lower semicontinuous.** At a point `g : Spec R ⟶ Y`
with values in a field, the rank of a matrix `A` of global functions on `Y` is at least `ρ` if and
only if the point lies in the non-vanishing locus `D(δ)` of some `ρ × ρ` minor `δ` of `A`. -/
lemma le_rank_map_appTop_iff {m n : Type*} [Finite m] [Fintype n] {R : CommRingCat.{u}}
    (hR : IsField Γ(Spec R, ⊤)) (g : Spec R ⟶ Y) (x : Spec R) (A : Matrix m n Γ(Y, ⊤)) (ρ : ℕ) :
    ρ ≤ (A.map g.appTop).rank ↔
      ∃ (e₁ : Fin ρ → m) (e₂ : Fin ρ → n), g.base x ∈ Y.basicOpen (A.submatrix e₁ e₂).det := by
  let := hR.toField
  simp_rw [← g.appTop_ne_zero_iff_mem_basicOpen hR _ x]
  exact Matrix.le_rank_map_iff A g.appTop.hom ρ

/-- The rank of `Γ(g^* φ)` for a morphism `φ` of free modules of finite rank on `Y` and a point
`g : Spec R ⟶ Y` is the rank of the matrix of `φ` at that point. -/
lemma finrank_range_moduleSpecΓFunctor_map {R : CommRingCat.{u}} (g : Spec R ⟶ Y)
    {M N : (Spec R).Modules} {I J : Type u} [Fintype I] [Finite J] [DecidableEq J]
    (eM : (Modules.pullback g).obj (free (R := Y.ringCatSheaf) I) ≅ M)
    (eN : (Modules.pullback g).obj (free (R := Y.ringCatSheaf) J) ≅ N) (ψ : M ⟶ N)
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J)
    (h : ψ = eM.inv ≫ (Modules.pullback g).map φ ≫ eN.hom) :
    finrank R (LinearMap.range ((moduleSpecΓFunctor (R := R)).map ψ).hom) =
      ((freeMatrix φ).map g.appTop).rank := by
  rw [← freeMatrix_pullback, rank_freeMatrix]
  let D := (pullbackFreeIso g I).inv ≫ (Modules.pullback g).map φ ≫ (pullbackFreeIso g J).hom
  have hψ : ψ = (eM.symm ≪≫ pullbackFreeIso g I).hom ≫ D ≫
      (eN.symm ≪≫ pullbackFreeIso g J).inv := by
    simp [h, D]
  rw [hψ, Functor.map_comp, Functor.map_comp]
  refine (ModuleCat.finrank_range_iso_comp ((moduleSpecΓFunctor (R := R)).mapIso
    (eM.symm ≪≫ pullbackFreeIso g I)) _ ((moduleSpecΓFunctor (R := R)).mapIso
    (eN.symm ≪≫ pullbackFreeIso g J)).symm).trans ?_
  exact finrank_eq_of_coe_eq _ _ _ rfl

/-- Over a field `R`, the global sections of a free module of rank `n` on `Spec R` form an
`n`-dimensional `R`-vector space. -/
lemma finrank_moduleSpecΓFunctor_obj_free {R : CommRingCat.{u}} (hR : IsField R)
    {M : (Spec R).Modules} {J : Type u} [Fintype J]
    (e : M ≅ free (R := (Spec R).ringCatSheaf) J) :
    finrank R ((moduleSpecΓFunctor (R := R)).obj M) = Fintype.card J ∧
      Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  classical
  let := (isField_Γ_Spec hR).toField
  let coordinates : Γ(M, ⊤) ≃ₗ[Γ(Spec R, ⊤)] (J → Γ(Spec R, ⊤)) :=
    (appLinearEquivOfIso e ⊤).trans
      (freeSectionsLinearEquiv (R := (Spec R).ringCatSheaf) J
        (Opposite.op (⊤ : (Spec R).Opens)))
  letI : Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤) := Module.Finite.equiv coordinates.symm
  refine ⟨?_, finite_sections_top_of_finite M⟩
  have scalarRank : finrank R Γ(M, ⊤) = finrank Γ(Spec R, ⊤) Γ(M, ⊤) := by
    simpa only [finrank_top] using finrank_eq_of_coe_eq M ⊤ ⊤ rfl
  calc
    finrank R ((moduleSpecΓFunctor (R := R)).obj M) =
        finrank Γ(Spec R, ⊤) Γ(M, ⊤) := scalarRank
    _ = finrank Γ(Spec R, ⊤) (J → Γ(Spec R, ⊤)) := coordinates.finrank_eq
    _ = Fintype.card J := Module.finrank_fintype_fun_eq_card (Γ(Spec R, ⊤))

/-- Over a field `R`, an `𝒪_{Spec R}`-module with finite dimensional global sections vanishes if
and only if its global sections do. -/
theorem isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero {R : CommRingCat.{u}} (hR : IsField R)
    (M : (Spec R).Modules)
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)] :
    IsZero M ↔ finrank R ((moduleSpecΓFunctor (R := R)).obj M) = 0 := by
  have := isEquivalence_moduleSpecΓFunctor hR
  let := hR.toField
  rw [Module.finrank_zero_iff]
  refine ⟨fun h ↦ ModuleCat.subsingleton_of_isZero ((moduleSpecΓFunctor (R := R)).map_isZero h),
    fun h ↦ ?_⟩
  let F := (moduleSpecΓFunctor (R := R)).asEquivalence
  have : Subsingleton (F.functor.obj M) := h
  exact (F.inverse.map_isZero (ModuleCat.isZero_of_subsingleton (F.functor.obj M))).of_iso
    (F.unitIso.app M)

/-- The fiber dimension of homology plus the ranks of the two differentials is the middle rank. -/
theorem finrank_homology_pullback_add_rank_add_rank {P : CochainComplex Y.Modules ℤ}
    {r : ℤ → ℕ} (e : ∀ n, P.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r n))))
    {R : CommRingCat.{u}} (hR : IsField R) (g : Spec R ⟶ Y) (q : ℤ) :
    finrank R ((moduleSpecΓFunctor (R := R)).obj
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) +
      ((freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)).map g.appTop).rank +
      ((freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)).map g.appTop).rank = r q := by
  have := isEquivalence_moduleSpecΓFunctor hR
  let F := moduleSpecΓFunctor (R := R)
  let Q := ((Modules.pullback g).mapHomologicalComplex _).obj P
  let S := (Q.sc' (q - 1) q (q + 1)).map F
  let E (n : ℤ) : (Modules.pullback g).obj (free (ULift.{u} (Fin (r n)))) ≅ Q.X n :=
    ((Modules.pullback g).mapIso (e n)).symm
  have hd (n m : ℤ) : Q.d n m =
      (E n).inv ≫ (Modules.pullback g).map ((e n).inv ≫ P.d n m ≫ (e m).hom) ≫ (E m).hom := by
    simp [E, Q]
  have h₁ : finrank R (F.obj (Q.homology q)) = finrank R S.homology :=
    (F.mapIso (Q.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)) ≪≫
      ((Q.sc' (q - 1) q (q + 1)).mapHomologyIso F).symm).toLinearEquiv.finrank_eq
  have h₂ := finrank_range_moduleSpecΓFunctor_map g (E q) (E (q + 1)) _ _ (hd q (q + 1))
  have h₃ := finrank_range_moduleSpecΓFunctor_map g (E (q - 1)) (E q) _ _ (hd (q - 1) q)
  obtain ⟨h₄, hfin⟩ := finrank_moduleSpecΓFunctor_obj_free hR
    ((Modules.pullback g).mapIso (e q) ≪≫ pullbackFreeIso g _)
  let := hR.toField
  have : FiniteDimensional R S.X₂ := hfin
  have := S.finrank_homology_add_finrank_range_add_finrank_range
  simp only [Fintype.card_ulift, Fintype.card_fin] at h₄
  change finrank R (F.obj (Q.homology q)) + _ + _ = _
  rw [h₁, ← h₂, ← h₃, ← h₄]
  exact this

/-- The fibre `H^q(g^* P)` of the cohomology of a complex of finite free modules at a point
`g : Spec R ⟶ Y` with values in a field is finite dimensional. -/
theorem finite_moduleSpecΓFunctor_obj_homology_pullback {P : CochainComplex Y.Modules ℤ}
    (hP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    {R : CommRingCat.{u}} (hR : IsField R) (g : Spec R ⟶ Y) (q : ℤ) :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) := by
  have := isEquivalence_moduleSpecΓFunctor hR
  let F := moduleSpecΓFunctor (R := R)
  let Q := ((Modules.pullback g).mapHomologicalComplex _).obj P
  let S := (Q.sc' (q - 1) q (q + 1)).map F
  obtain ⟨r, ⟨e⟩⟩ := hP q
  obtain ⟨-, hfin⟩ := finrank_moduleSpecΓFunctor_obj_free hR
    ((Modules.pullback g).mapIso e ≪≫ pullbackFreeIso g _)
  let := hR.toField
  have : FiniteDimensional R S.X₂ := hfin
  exact Module.Finite.equiv (F.mapIso (Q.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)) ≪≫
    ((Q.sc' (q - 1) q (q + 1)).mapHomologyIso F).symm).toLinearEquiv.symm

/-- **Upper semicontinuity of the fibre cohomology of a complex of finite free modules.** Let `P`
be a complex of `𝒪_Y`-modules whose terms are free of finite rank, and `g : Spec R ⟶ Y` a point
with values in a field. There is an open neighbourhood `V` of the point such that at every point
`g' : Spec R' ⟶ Y` in `V`, `dim_{R'} H^q(g'^* P) ≤ dim_R H^q(g^* P)`.

Take for `V` the non-vanishing locus of a maximal nonvanishing minor at `g` of each of the two
differentials around degree `q`: on `V` their ranks can only be larger
(`AlgebraicGeometry.Scheme.Modules.le_rank_map_appTop_iff`), so the dimension of the cohomology
can only be smaller
(`AlgebraicGeometry.Scheme.Modules.finrank_homology_pullback_add_rank_add_rank`). -/
theorem exists_finrank_homology_pullback_le {P : CochainComplex Y.Modules ℤ}
    (hP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (q : ℤ) {R : CommRingCat.{u}} (hR : IsField R) (g : Spec R ⟶ Y) :
    ∃ V : Y.Opens, Set.range g.base ⊆ V ∧
      ∀ {R' : CommRingCat.{u}} (_ : IsField R') (g' : Spec R' ⟶ Y), Set.range g'.base ⊆ V →
        finrank R' ((moduleSpecΓFunctor (R := R')).obj
          ((((Modules.pullback g').mapHomologicalComplex _).obj P).homology q)) ≤
        finrank R ((moduleSpecΓFunctor (R := R)).obj
          ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) := by
  choose r he using hP
  let e n := (he n).some
  let A₁ := freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)
  let A₂ := freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)
  have hΓ := isField_Γ_Spec hR
  have : Nonempty (Spec R) := by
    let := hR.toField
    infer_instance
  obtain ⟨x⟩ := this
  obtain ⟨a₁, b₁, h₁⟩ := (le_rank_map_appTop_iff hΓ g x A₁ _).1 le_rfl
  obtain ⟨a₂, b₂, h₂⟩ := (le_rank_map_appTop_iff hΓ g x A₂ _).1 le_rfl
  rw [← g.appTop_ne_zero_iff_mem_basicOpen hΓ] at h₁ h₂
  refine ⟨Y.basicOpen (A₁.submatrix a₁ b₁).det ⊓ Y.basicOpen (A₂.submatrix a₂ b₂).det, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(g.appTop_ne_zero_iff_mem_basicOpen hΓ _ y).1 h₁,
      (g.appTop_ne_zero_iff_mem_basicOpen hΓ _ y).1 h₂⟩
  · intro R' hR' g' hg'
    have : Nonempty (Spec R') := by
      let := hR'.toField
      infer_instance
    obtain ⟨x'⟩ := this
    have k₁ := (le_rank_map_appTop_iff (isField_Γ_Spec hR') g' x' A₁ _).2
      ⟨a₁, b₁, (hg' ⟨x', rfl⟩).1⟩
    have k₂ := (le_rank_map_appTop_iff (isField_Γ_Spec hR') g' x' A₂ _).2
      ⟨a₂, b₂, (hg' ⟨x', rfl⟩).2⟩
    have f₁ := finrank_homology_pullback_add_rank_add_rank e hR g q
    have f₂ := finrank_homology_pullback_add_rank_add_rank e hR' g' q
    dsimp only [A₁, A₂] at k₁ k₂
    omega

end AlgebraicGeometry.Scheme.Modules
