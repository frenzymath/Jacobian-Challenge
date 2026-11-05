import Jacobian.AlgebraicGeometry.Rigidity
import Jacobian.AlgebraicGeometry.BaseChange.Field
import Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Jacobian.CategoryTheory.Monoidal.ReflectsMonHom
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Pointed morphisms from proper monoid schemes

A pointed morphism from a proper geometrically integral monoid scheme to a
separated locally finite type group scheme is a homomorphism. The defect
of multiplication is constant by rigidity. Faithful extension to an
algebraic closure proves the result over an arbitrary field.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **A pointed morphism of group schemes is a homomorphism** (Milne, *Abelian Varieties*,
I Cor 1.2; Mumford, *Abelian Varieties*, §II.4 p. 44, Corollary 1). Let `K` be an
algebraically closed field, `A` a monoid object of `Over (Spec K)` whose underlying scheme is
proper and geometrically integral over `K`, and `B` a group object whose underlying scheme is
separated and locally of finite type over `K`. If `g : A ⟶ B` is pointed (`η[A] ≫ g = η[B]`),
then `g` is a homomorphism of monoid objects.

For `A` a group object this makes `g` a homomorphism of group objects: a monoid homomorphism
automatically commutes with inversion (`CategoryTheory.inv_hom`). 

-/
theorem isMonHom_of_isProper_of_geometricallyIntegral_of_isAlgClosed
    {A B : Over (Spec (CommRingCat.of K))} [MonObj A] [GrpObj B]
    [IsProper A.hom] [GeometricallyIntegral A.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (g : A ⟶ B) (hg : η[A] ≫ g = η[B]) : IsMonHom g := by
  -- the defect morphism `φ(x, y) = g(x·y) · (g(x)·g(y))⁻¹` in the group `Hom(A ⊗ A, B)`
  set φ : A ⊗ A ⟶ B := (μ[A] ≫ g) / ((fst A A ≫ g) * (snd A A ≫ g)) with hφdef
  -- `φ` contracts the slice `A × {e}` to the unit point of `B`
  have e1 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ μ[A] ≫ g = g := by
    rw [← Category.assoc, MonObj.lift_comp_one_right, Category.id_comp]
  have e2 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ fst A A ≫ g = g := by
    rw [lift_fst_assoc, Category.id_comp]
  have e3 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ snd A A ≫ g = 1 := by
    rw [lift_snd_assoc, Category.assoc, hg, ← Hom.one_def]
  have hslice : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ φ = toUnit A ≫ η[B] := by
    rw [hφdef, GrpObj.comp_div, MonObj.comp_mul, e1, e2, e3, _root_.mul_one, div_self',
      Hom.one_def]
  -- rigidity: `φ` factors through the second projection
  obtain ⟨ψ, hψ, -⟩ := exists_unique_eq_snd_comp_of_isProper_of_geometricallyIntegral
    φ η[A] η[B] hslice
  -- restricting along the slice `{e} × A` identifies the factor with the unit
  have hψ1 : ψ = (1 : A ⟶ B) := by
    have h1 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ φ = ψ := by
      rw [hψ, lift_snd_assoc, Category.id_comp]
    have f1 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ μ[A] ≫ g = g := by
      rw [← Category.assoc, MonObj.lift_comp_one_left, Category.id_comp]
    have f2 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ fst A A ≫ g = 1 := by
      rw [lift_fst_assoc, Category.assoc, hg, ← Hom.one_def]
    have f3 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ snd A A ≫ g = g := by
      rw [lift_snd_assoc, Category.id_comp]
    rw [← h1, hφdef, GrpObj.comp_div, MonObj.comp_mul, f1, f2, f3, _root_.one_mul, div_self']
  -- hence the defect vanishes identically
  have hφ1 : φ = (1 : A ⊗ A ⟶ B) := by rw [hψ, hψ1, MonObj.comp_one]
  rw [hφdef, div_eq_one] at hφ1
  -- and `μ[A] ≫ g = (g ⊗ₘ g) ≫ μ[B]`
  have h2 : (g ⊗ₘ g) ≫ μ[B] = (fst A A ≫ g) * (snd A A ≫ g) := by
    rw [MonObj.mul_eq_mul B, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  exact { one_hom := hg, mul_hom := by rw [hφ1, h2] }

/-- Actual pullback along any extension of fields is faithful. -/
theorem fieldBaseChange_faithful (k L : Type u) [Field k] [Field L] [Algebra k L] :
    (AlgebraicGeometry.baseChange k L).Faithful := by
  letI : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  infer_instance

/-- The pointed-morphism theorem over an arbitrary field, obtained from the
geometric rigidity lemma and actual faithful field base change. -/
theorem isMonHom_of_isProper_of_geometricallyIntegral
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [MonObj A] [GrpObj B] [IsProper A.hom] [GeometricallyIntegral A.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  let L := AlgebraicClosure k
  let q : Spec (.of L) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k L))
  let F := Over.pullback q
  letI : F.Faithful := fieldBaseChange_faithful k L
  letI : IsProper (F.obj A).hom := by
    change IsProper (Limits.pullback.snd A.hom q)
    infer_instance
  letI : GeometricallyIntegral (F.obj A).hom := by
    change GeometricallyIntegral (Limits.pullback.snd A.hom q)
    infer_instance
  letI : IsSeparated (F.obj B).hom := by
    change IsSeparated (Limits.pullback.snd B.hom q)
    infer_instance
  letI : LocallyOfFiniteType (F.obj B).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd B.hom q)
    infer_instance
  have hpointed : η[F.obj A] ≫ F.map f = η[F.obj B] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫ F.map f =
      Functor.LaxMonoidal.ε F ≫ F.map η[B]
    rw [Category.assoc, ← Functor.map_comp, hf]
  letI : IsMonHom (F.map f) :=
    AlgebraicGeometry.isMonHom_of_isProper_of_geometricallyIntegral_of_isAlgClosed (F.map f) hpointed
  exact Functor.isMonHom_of_map F f

/-- A smooth proper geometrically irreducible group scheme over a field is commutative. -/
theorem isCommMonObj_of_isProper_of_smooth_of_geometricallyIrreducible
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IsProper G.hom] [Smooth G.hom] [GeometricallyIrreducible G.hom] : IsCommMonObj G := by
  letI : GeometricallyIntegral G.hom := Smooth.geometricallyIntegral G.hom
  exact isCommMonObj_of_isProper_of_geometricallyIntegral G

end AlgebraicGeometry
