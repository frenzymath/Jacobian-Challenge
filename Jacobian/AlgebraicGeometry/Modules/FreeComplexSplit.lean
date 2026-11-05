import Jacobian.AlgebraicGeometry.Modules.FreeComplex
import Jacobian.Algebra.Homology.ShortComplex.SplitHomology
import Jacobian.LinearAlgebra.Matrix.SplitFactorization
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Local splitting of complexes of finite free module sheaves

Matrices of differentials are compatible with pullback. A split matrix complex
gives an isomorphism from its homology sheaf to a finite free module, and
residue-field ranks depend only on the image point of a field-valued point.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- A section of a scheme that is invertible at every point of its domain is a unit.
This is the converse of `Scheme.basicOpen_of_isUnit`. -/
theorem isUnit_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens} {f : Γ(X, U)}
    (h : U ≤ X.basicOpen f) : IsUnit f :=
  X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx ↦ (X.mem_basicOpen f x hx).mp (h hx)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- The rank of a matrix of functions at a field-valued point only depends on the image point. -/
lemma rank_map_appTop_eq_of_base_eq {m n : Type*} [Finite m] [Fintype n] {R R' : CommRingCat.{u}}
    (hR : IsField Γ(Spec R, ⊤)) (hR' : IsField Γ(Spec R', ⊤)) (g : Spec R ⟶ Y)
    (g' : Spec R' ⟶ Y) (x : Spec R) (x' : Spec R') (h : g.base x = g'.base x')
    (A : Matrix m n Γ(Y, ⊤)) : (A.map g.appTop).rank = (A.map g'.appTop).rank := by
  refine le_antisymm ?_ ?_
  · obtain ⟨e₁, e₂, he⟩ := (le_rank_map_appTop_iff hR g x A _).1 le_rfl
    exact (le_rank_map_appTop_iff hR' g' x' A _).2 ⟨e₁, e₂, h ▸ he⟩
  · obtain ⟨e₁, e₂, he⟩ := (le_rank_map_appTop_iff hR' g' x' A _).1 le_rfl
    exact (le_rank_map_appTop_iff hR g x A _).2 ⟨e₁, e₂, h.symm ▸ he⟩

/-- The ring of global functions of the spectrum of a residue field is a field. -/
lemma isField_Γ_Spec_residueField (y : Y) : IsField Γ(Spec (Y.residueField y), ⊤) :=
  isField_Γ_Spec (Field.toIsField _)

lemma fromSpecResidueField_base_apply (y : Y) (x : Spec (Y.residueField y)) :
    (Y.fromSpecResidueField y).base x = y :=
  (Scheme.range_fromSpecResidueField y).subset ⟨x, rfl⟩

/-- **Free cohomology of a complex of finite free modules with a split middle term.** Let `Q` be a
cochain complex of `𝒪_Y`-modules with `Q^{q-1} ≅ 𝒪^{(a)}`, `Q^q ≅ 𝒪^{(b)}`, `Q^{q+1} ≅ 𝒪^{(c)}`,
and let `A₁`, `A₂` be the matrices of the differentials into and out of degree `q`. If matrices
`I`, `P`, `σ`, `τ` satisfy `P I = 1`, `A₂ I = 0`, `P A₁ = 0` and `I P + A₁ σ + τ A₂ = 1`, then
`H^q(Q) ≅ 𝒪^{(k)}`. -/
theorem nonempty_homology_iso_free_of_split (Q : CochainComplex Y.Modules ℤ) (q : ℤ)
    {a b c k : Type u} [Fintype a] [Fintype b] [DecidableEq b] [Fintype c]
    [DecidableEq c] [Fintype k] [DecidableEq k]
    (e₀ : Q.X (q - 1) ≅ free (R := Y.ringCatSheaf) a) (e₁ : Q.X q ≅ free (R := Y.ringCatSheaf) b)
    (e₂ : Q.X (q + 1) ≅ free (R := Y.ringCatSheaf) c)
    (σ : Matrix a b Γ(Y, ⊤)) (τ : Matrix b c Γ(Y, ⊤)) (I : Matrix b k Γ(Y, ⊤))
    (P : Matrix k b Γ(Y, ⊤)) (hIP : P * I = 1)
    (hI : freeMatrix (e₁.inv ≫ Q.d q (q + 1) ≫ e₂.hom) * I = 0)
    (hP : P * freeMatrix (e₀.inv ≫ Q.d (q - 1) q ≫ e₁.hom) = 0)
    (hsum : I * P + freeMatrix (e₀.inv ≫ Q.d (q - 1) q ≫ e₁.hom) * σ +
      τ * freeMatrix (e₁.inv ≫ Q.d q (q + 1) ≫ e₂.hom) = 1) :
    Nonempty (Q.homology q ≅ free (R := Y.ringCatSheaf) k) := by
  classical
  set D₁ := e₀.inv ≫ Q.d (q - 1) q ≫ e₁.hom with hD₁
  set D₂ := e₁.inv ≫ Q.d q (q + 1) ≫ e₂.hom with hD₂
  have h₁ : Q.d (q - 1) q = e₀.hom ≫ D₁ ≫ e₁.inv := by simp [hD₁]
  have h₂ : Q.d q (q + 1) = e₁.hom ≫ D₂ ≫ e₂.inv := by simp [hD₂]
  have kIP : freeHomOfMatrix I ≫ freeHomOfMatrix P = 𝟙 _ :=
    freeMatrix_injective (by rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix,
      freeMatrix_freeHomOfMatrix, freeMatrix_id, hIP])
  have kI : freeHomOfMatrix I ≫ D₂ = 0 :=
    freeMatrix_injective (by rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix, hI,
      freeMatrix_zero])
  have kP : D₁ ≫ freeHomOfMatrix P = 0 :=
    freeMatrix_injective (by rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix, hP,
      freeMatrix_zero])
  have ksum : freeHomOfMatrix P ≫ freeHomOfMatrix I + freeHomOfMatrix σ ≫ D₁ +
      D₂ ≫ freeHomOfMatrix τ = 𝟙 _ :=
    freeMatrix_injective (by rw [freeMatrix_add, freeMatrix_add, freeMatrix_comp,
      freeMatrix_comp, freeMatrix_comp, freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix,
      freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix, freeMatrix_id, hsum])
  let S : ShortComplex Y.Modules :=
    ShortComplex.mk (Q.d (q - 1) q) (Q.d q (q + 1)) (Q.d_comp_d _ _ _)
  have eS : Q.sc' (q - 1) q (q + 1) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [S]) (by simp [S])
  refine ⟨Q.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso eS ≪≫ S.homologyIsoOfSplit (e₁.hom ≫ freeHomOfMatrix σ ≫ e₀.inv)
      (e₂.hom ≫ freeHomOfMatrix τ ≫ e₁.inv) (freeHomOfMatrix I ≫ e₁.inv)
      (e₁.hom ≫ freeHomOfMatrix P) ?_ ?_ ?_ ?_⟩
  · simp [kIP]
  · simp [S, h₂, reassoc_of% kI]
  · simp [S, h₁, kP]
  · simp only [S]
    rw [h₁, h₂]
    refine Eq.trans (?_ : _ = e₁.hom ≫ (freeHomOfMatrix P ≫ freeHomOfMatrix I +
      freeHomOfMatrix σ ≫ D₁ + D₂ ≫ freeHomOfMatrix τ) ≫ e₁.inv) ?_
    · simp [Preadditive.add_comp, Preadditive.comp_add]
    · rw [ksum, Category.id_comp, Iso.hom_inv_id]

lemma map_appTop_comp {m n : Type*} {X Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Matrix m n Γ(Z, ⊤)) : A.map (f ≫ g).appTop = (A.map g.appTop).map f.appTop := by
  rw [Scheme.Hom.comp_appTop, Matrix.map_map]
  rfl

/-- The rank of a matrix restricted to an open subscheme, at a point, is its rank at the image
point. -/
lemma rank_map_appTop_restrict {m n : Type*} [Finite m] [Fintype n] (V : Y.Opens) (z : V.toScheme)
    (A : Matrix m n Γ(Y, ⊤)) :
    ((A.map V.ι.appTop).map (V.toScheme.fromSpecResidueField z).appTop).rank =
      (A.map (Y.fromSpecResidueField (V.ι.base z)).appTop).rank := by
  obtain ⟨x⟩ : Nonempty (Spec (V.toScheme.residueField z)) := inferInstance
  obtain ⟨x'⟩ : Nonempty (Spec (Y.residueField (V.ι.base z))) := inferInstance
  rw [← map_appTop_comp]
  refine rank_map_appTop_eq_of_base_eq (isField_Γ_Spec_residueField z)
    (isField_Γ_Spec_residueField _) _ _ x x' ?_ A
  rw [Scheme.Hom.comp_apply, fromSpecResidueField_base_apply,
    fromSpecResidueField_base_apply]

/-- The matrices of the differentials of the pullback of a complex of free modules are the
images of the matrices of the differentials. -/
lemma freeMatrix_pullback_d {Z : Scheme.{u}} (j : Z ⟶ Y) (P : CochainComplex Y.Modules ℤ)
    {I J : Type u} [DecidableEq J] {n n' : ℤ} (eₙ : P.X n ≅ free (R := Y.ringCatSheaf) I)
    (eₙ' : P.X n' ≅ free (R := Y.ringCatSheaf) J) :
    freeMatrix ((((Modules.pullback j).mapIso eₙ ≪≫ pullbackFreeIso j I).inv ≫
        (((Modules.pullback j).mapHomologicalComplex _).obj P).d n n' ≫
        ((Modules.pullback j).mapIso eₙ' ≪≫ pullbackFreeIso j J).hom)) =
      (freeMatrix (eₙ.inv ≫ P.d n n' ≫ eₙ'.hom)).map j.appTop := by
  rw [← freeMatrix_pullback]
  congr 1
  simp

end AlgebraicGeometry.Scheme.Modules
