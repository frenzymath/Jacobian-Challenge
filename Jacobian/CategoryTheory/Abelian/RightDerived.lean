import Jacobian.Algebra.Homology.HomologicalComplex.Naturality
import Jacobian.CategoryTheory.Abelian.Injective.Resolution

/-!
# Additivity and scalar naturality of right derived functors

Right derived functors of additive functors are additive. Natural endomorphisms
intertwined by the original functor remain intertwined after deriving.
-/

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] (F : C ⥤ D) [F.Additive]

instance : F.rightDerivedToHomotopyCategory.Additive :=
  inferInstanceAs (injectiveResolutions C ⋙ F.mapHomotopyCategory _).Additive

/-- The right derived functors of an additive functor are additive. -/
instance (n : ℕ) : (F.rightDerived n).Additive :=
  inferInstanceAs
    (F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n).Additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `α` and `β` be natural endomorphisms of the identity functors of `C` and `D` which are
intertwined by `F`: `F (α M) = β (F M)`. Then they are intertwined by every right derived
functor of `F`: `R^n F (α M) = β (R^n F M)`. -/
theorem rightDerived_map_app_eq (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ M, F.map (α.app M) = β.app (F.obj M)) (n : ℕ) (M : C) :
    (F.rightDerived n).map (α.app M) = β.app ((F.rightDerived n).obj M) := by
  let P := injectiveResolution M
  let φ : P.cocomplex ⟶ P.cocomplex :=
    { f i := α.app (P.cocomplex.X i)
      comm' i j _ := (α.naturality (P.cocomplex.d i j)).symm }
  have w : P.ι ≫ φ = (CochainComplex.single₀ C).map (α.app M) ≫ P.ι := by
    ext
    simpa [φ, Functor.id_map] using α.naturality (P.ι.f 0)
  rw [F.rightDerived_map_eq n (α.app M) φ w]
  have hφ := HomologicalComplex.homologyMap_eq_app_homology β ((F.mapHomologicalComplex _).map φ)
    (fun i ↦ h _) n
  rw [Functor.comp_map, HomologicalComplex.homologyFunctor_map, hφ]
  rw [← Category.assoc, Iso.comp_inv_eq]
  exact β.naturality (P.isoRightDerivedObj F n).hom

end CategoryTheory.Functor
