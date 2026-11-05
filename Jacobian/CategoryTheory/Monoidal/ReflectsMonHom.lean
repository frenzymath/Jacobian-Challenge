import Mathlib.CategoryTheory.Monoidal.Mon

/-! A faithful monoidal functor reflects the actual monoid-homomorphism laws.
The proof cancels the invertible unit comparison and tensorator, then uses
faithfulness on the two defining diagrams. Fullness is unnecessary. -/

universe v₁ v₂ u₁ u₂
open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- Faithful monoidal transport reflects both monoid-homomorphism laws. -/
theorem isMonHom_of_map
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    [IsMonHom (F.map f)] : IsMonHom f where
  one_hom := by
    apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    calc
      Functor.LaxMonoidal.ε F ≫ F.map (η[X] ≫ f) =
          η[F.obj X] ≫ F.map f := by
        simp only [Functor.map_comp, Functor.obj.η_def, Category.assoc]
      _ = η[F.obj Y] := IsMonHom.one_hom (F.map f)
      _ = Functor.LaxMonoidal.ε F ≫ F.map η[Y] := rfl
  mul_hom := by
    apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ F X X)).mp
    calc
      Functor.LaxMonoidal.μ F X X ≫ F.map (μ[X] ≫ f) =
          μ[F.obj X] ≫ F.map f := by
        simp only [Functor.map_comp, Functor.obj.μ_def, Category.assoc]
      _ = (F.map f ⊗ₘ F.map f) ≫ μ[F.obj Y] :=
        IsMonHom.mul_hom (F.map f)
      _ = Functor.LaxMonoidal.μ F X X ≫ F.map ((f ⊗ₘ f) ≫ μ[Y]) := by
        rw [Functor.obj.μ_def, ← Category.assoc,
          Functor.LaxMonoidal.μ_natural, Category.assoc, ← Functor.map_comp]

end CategoryTheory.Functor
