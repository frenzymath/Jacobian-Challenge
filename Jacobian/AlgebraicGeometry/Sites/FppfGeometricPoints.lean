import Jacobian.AlgebraicGeometry.Sites.Fppf
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Geometric points of fppf sheafifications

Over an algebraically closed field, a covering sieve for the fppf topology
contains a morphism with a section. Consequently, every section of a
sheafification over a geometric point lifts to the original presheaf.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Sheafification for the fppf topology is surjective on sections over an
algebraically closed field extension. -/
theorem surjective_toSheafify_app_of_isAlgClosed {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    [IsAlgClosed extensionField]
    (presheaf : (Over (Spec (.of baseField)))ᵒᵖ ⥤ Type (u + 1)) :
    Function.Surjective
      ((toSheafify (fppfTopology.over (Spec (.of baseField))) presheaf).app
        (.op (Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap baseField extensionField)))))) := by
  intro sectionValue
  let topology := fppfTopology.over (Spec (.of baseField))
  let parameter := Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap baseField extensionField)))
  obtain ⟨point⟩ : Nonempty parameter.left :=
    inferInstanceAs (Nonempty (Spec (.of extensionField)))
  obtain ⟨cover, coverMap, ⟨representative, representative_eq⟩, _, _, liftPoint, _⟩ :=
    exists_flat_mem_of_mem_fppfTopology_over
      (Presheaf.imageSieve_mem topology (toSheafify topology presheaf) sectionValue) point
  have : JacobsonSpace cover.left := LocallyOfFiniteType.jacobsonSpace coverMap.left
  obtain ⟨closedPoint, _, isClosedPoint⟩ :=
    nonempty_inter_closedPoints (Z := Set.univ) ⟨liftPoint, trivial⟩
      isClosed_univ.isLocallyClosed
  have closedSingleton : IsClosed ({closedPoint} : Set cover.left) :=
    mem_closedPoints_iff.mp isClosedPoint
  let sectionMap : parameter ⟶ cover :=
    Over.homMk (pointOfClosedPoint coverMap.left closedPoint closedSingleton) (by
      rw [← Over.w coverMap, pointOfClosedPoint_comp_assoc]
      rfl)
  have section_comp : sectionMap ≫ coverMap = 𝟙 parameter := by
    ext1
    exact pointOfClosedPoint_comp coverMap.left closedPoint closedSingleton
  refine ⟨presheaf.map sectionMap.op representative, ?_⟩
  refine (NatTrans.naturality_apply (toSheafify topology presheaf)
    sectionMap.op representative).trans ?_
  rw [representative_eq, ← Functor.map_comp_apply, ← op_comp, section_comp,
    CategoryTheory.op_id]
  exact CategoryTheory.Functor.map_id_apply (sheafify topology presheaf) _ _

end AlgebraicGeometry.Scheme
