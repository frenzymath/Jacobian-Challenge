import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Jacobian.AlgebraicGeometry.Cohomology.Fiber
import Jacobian.AlgebraicGeometry.Modules.FieldRank
import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplex

/-!
# Single-degree loci of fibre cohomology

The fixed-rank perfect locus is defined using the cohomology dimensions of the
actual residue-field fibres. When a finite free complex computes higher direct
images compatibly with base change, its fibre homology detects this locus. The
comparison uses the native linear equivalence between sections of higher direct
images over a field and sheaf cohomology.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- The points where the fibre cohomology dimensions vanish outside degree `i`. -/
def perfectLocus (M : X.Modules) (f : X ⟶ T) (i : ℕ) : Set T :=
  {t | ∀ q ≠ i, M.hFiber f q t = 0}

/-- The single-degree fibre-cohomology locus with prescribed dimension in that degree. -/
def perfectLocusOfRank (M : X.Modules) (f : X ⟶ T) (i r : ℕ) : Set T :=
  {t ∈ M.perfectLocus f i | M.hFiber f i t = r}

@[simp]
theorem mem_perfectLocus (M : X.Modules) (f : X ⟶ T) (i : ℕ) (t : T) :
    t ∈ M.perfectLocus f i ↔ ∀ q ≠ i, M.hFiber f q t = 0 :=
  Iff.rfl

@[simp]
theorem mem_perfectLocusOfRank (M : X.Modules) (f : X ⟶ T) (i r : ℕ) (t : T) :
    t ∈ M.perfectLocusOfRank f i r ↔ t ∈ M.perfectLocus f i ∧ M.hFiber f i t = r :=
  Iff.rfl

theorem perfectLocusOfRank_subset (M : X.Modules) (f : X ⟶ T) (i r : ℕ) :
    M.perfectLocusOfRank f i r ⊆ M.perfectLocus f i :=
  fun _ ht ↦ ht.1

variable (f : X ⟶ T) (M : X.Modules) [QuasiCompact f] [IsSeparated f]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]

/-- A base-change-compatible complex computes the native fibre cohomology dimensions. -/
theorem hFiber_eq_finrank_homology {U : T.Opens} {P : CochainComplex U.toScheme.Modules ℤ}
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj M)))
    {s : T} (g : Spec (T.residueField s) ⟶ U.toScheme)
    (hg : g ≫ U.ι = T.fromSpecResidueField s) (q : ℕ) :
    M.hFiber f q s =
      Module.finrank (T.residueField s) ((moduleSpecΓFunctor (R := .of (T.residueField s))).obj
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) := by
  letI fibreOver : (f.fiber s).Over (Spec (.of (T.residueField s))) :=
    f.fiberOverSpecResidueField s
  letI : IsSeparated (f.fiber s ↘ Spec (.of (T.residueField s))) := by
    change IsSeparated (Limits.pullback.snd f (T.fromSpecResidueField s))
    infer_instance
  have sq : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (g ≫ U.ι) := by
    rw [hg]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨e⟩ := hbc g _ _ sq q
  obtain ⟨comparison⟩ := nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H
    (X := f.fiber s) (ℱ := (Modules.pullback (f.fiberι s)).obj M) (K := T.residueField s) q
  calc
    M.hFiber f q s = Module.finrank (T.residueField s)
        (((Modules.pullback (f.fiberι s)).obj M).H q) := rfl
    _ = Module.finrank (T.residueField s) ((moduleSpecΓFunctor
        (R := .of (T.residueField s))).obj
          ((higherDirectImage (f.fiberToSpecResidueField s) q).obj
            ((Modules.pullback (f.fiberι s)).obj M))) := comparison.finrank_eq.symm
    _ = _ := ((moduleSpecΓFunctor (R := .of (T.residueField s))).mapIso e).toLinearEquiv.finrank_eq.symm

/-- The fibre homology of a finite free model is finite locally free in one
degree exactly at the fixed-rank perfect locus of the actual fibre cohomology. -/
theorem isFiniteLocallyFreeInDegree_homology_pullback_iff {U : T.Opens}
    {P : CochainComplex U.toScheme.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d)
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj M)))
    {s : T} (g : Spec (T.residueField s) ⟶ U.toScheme)
    (hg : g ≫ U.ι = T.fromSpecResidueField s) (i r : ℕ) :
    IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r ↔
      s ∈ M.perfectLocusOfRank f i r := by
  have hκ : IsField (T.residueField s) := Field.toIsField _
  letI (q : ℕ) : Module.Finite (T.residueField s)
      ((moduleSpecΓFunctor (R := .of (T.residueField s))).obj
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :=
    finite_moduleSpecΓFunctor_obj_homology_pullback hP.exists_iso_free hκ g q
  simp only [mem_perfectLocusOfRank, mem_perfectLocus, hFiber_eq_finrank_homology f M hbc g hg]
  refine ⟨fun ⟨hz, hl⟩ ↦ ⟨fun q hq ↦
      (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).1 (hz q hq),
      (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hκ _ r).1 hl⟩,
    fun ⟨hz, hl⟩ ↦ ⟨fun q hq ↦
      (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).2 (hz q hq),
      (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hκ _ r).2 hl⟩⟩

end AlgebraicGeometry.Scheme.Modules
