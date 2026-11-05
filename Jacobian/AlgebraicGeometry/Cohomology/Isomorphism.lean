import Jacobian.AlgebraicGeometry.Cohomology.Pullback
import Jacobian.Topology.Sheaves.Isomorphism

/-!
# Cohomology under scheme isomorphisms

Pullback along a scheme isomorphism is a bijection on the existing abelian-sheaf
cohomology. For schemes over a field it is linear, so cohomology dimensions and
Euler characteristics are unchanged. No finiteness or quasi-coherence is needed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Direct image along a scheme isomorphism is an equivalence of module categories. -/
def pushforwardEquivalence (e : X ≅ Y) : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.hom) (pushforward e.inv)
    (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫
      pushforwardId X).symm
    (pushforwardComp e.inv e.hom ≪≫ pushforwardCongr e.inv_hom_id ≪≫
      pushforwardId Y)

instance (f : X ⟶ Y) [IsIso f] : (pushforward f).IsEquivalence :=
  (pushforwardEquivalence (asIso f)).isEquivalence_functor

instance (f : X ⟶ Y) [IsIso f] : (abelianInverseImage f).IsEquivalence := by
  have : IsIso f.base := inferInstance
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    f.base).isEquivalence_left_of_isEquivalence_right

instance (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso (adjointCoefficientMap f ((pullbackPushforwardAdjunction f).unit.app M)) := by
  have : IsIso f.base := inferInstance
  dsimp only [adjointCoefficientMap]
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Pullback by a scheme isomorphism is bijective on every cohomology group. -/
theorem H.pullback_bijective (f : X ⟶ Y) [IsIso f] (M : Y.Modules) (q : ℕ) :
    Function.Bijective (H.pullback f M q) := by
  let a := adjointCoefficientMap f ((pullbackPushforwardAdjunction f).unit.app M)
  have ha : Function.Bijective (Sheaf.H.map a q) := by
    let e : Sheaf.H _ q ≃+ Sheaf.H _ q :=
      { toFun := Sheaf.H.map a q
        invFun := Sheaf.H.map (inv a) q
        map_add' := map_add _
        left_inv := fun x ↦ by
          rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id]
          exact Sheaf.H.map_id_apply x
        right_inv := fun x ↦ by
          rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id]
          exact Sheaf.H.map_id_apply x }
    exact e.bijective
  exact ha.comp (Sheaf.H.mapFunctor_bijective (abelianInverseImage f)
    (abelianInverseImageConstantIso f).symm
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) q)

/-- Cohomological pullback is linear for compatible structure morphisms to a field. -/
def H.pullbackLinearMap {k : Type u} [Field k] (f : X ⟶ Y)
    (g : Y ⟶ Spec (.of k)) (M : Y.Modules) (q : ℕ) :
    letI : Y.Over (Spec (.of k)) := ⟨g⟩
    letI : X.Over (Spec (.of k)) := ⟨f ≫ g⟩
    M.H q →ₗ[k] ((Modules.pullback f).obj M).H q := by
  letI : Y.Over (Spec (.of k)) := ⟨g⟩
  letI : X.Over (Spec (.of k)) := ⟨f ≫ g⟩
  refine { (H.pullback f M q).toAddMonoidHom with map_smul' := ?_ }
  intro c x
  change H.pullback f M q (globalSectionsRingHom k (X := Y) c • x) =
    globalSectionsRingHom k (X := X) c • H.pullback f M q x
  have hc : f.appTop (globalSectionsRingHom k (X := Y) c) =
      globalSectionsRingHom k (X := X) c := by
    change f.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) c) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appTop) c)
    rw [Scheme.Hom.comp_appTop]
    rfl
  calc
    _ = f.appTop (globalSectionsRingHom k (X := Y) c) • H.pullback f M q x :=
      (H.pullback f M q).map_smul' _ _
    _ = _ := by rw [hc]

/-- Pullback by an isomorphism identifies cohomology as vector spaces. -/
def H.pullbackLinearEquiv {k : Type u} [Field k] (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Spec (.of k)) (M : Y.Modules) (q : ℕ) :
    letI : Y.Over (Spec (.of k)) := ⟨g⟩
    letI : X.Over (Spec (.of k)) := ⟨f ≫ g⟩
    M.H q ≃ₗ[k] ((Modules.pullback f).obj M).H q :=
  LinearEquiv.ofBijective (H.pullbackLinearMap f g M q) (H.pullback_bijective f M q)

/-- Cohomology dimensions are invariant under a scheme isomorphism over a field. -/
theorem finrankH_pullback_of_isIso {k : Type u} [Field k] (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Spec (.of k)) (M : Y.Modules) (q : ℕ) :
    (letI : X.Over (Spec (.of k)) := ⟨f ≫ g⟩;
      ((Modules.pullback f).obj M).finrankH k q) =
    (letI : Y.Over (Spec (.of k)) := ⟨g⟩; M.finrankH k q) := by
  letI : Y.Over (Spec (.of k)) := ⟨g⟩
  letI : X.Over (Spec (.of k)) := ⟨f ≫ g⟩
  exact (H.pullbackLinearEquiv f g M q).finrank_eq.symm

/-- The Euler characteristic is invariant under a scheme isomorphism over a field. -/
theorem eulerChar_pullback_of_isIso {k : Type u} [Field k] (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Spec (.of k)) (M : Y.Modules) :
    (letI : X.Over (Spec (.of k)) := ⟨f ≫ g⟩;
      ((Modules.pullback f).obj M).eulerChar k) =
    (letI : Y.Over (Spec (.of k)) := ⟨g⟩; M.eulerChar k) := by
  simp only [eulerChar, finrankH_pullback_of_isIso f g M]

end AlgebraicGeometry.Scheme.Modules
