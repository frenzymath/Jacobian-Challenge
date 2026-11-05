import Jacobian.RingTheory.Adjoin.FG
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Directed unions as colimits of commutative rings

A nonempty directed family of integer subalgebras with supremum equal to the
ambient ring presents that ring as a colimit. In particular, every commutative
ring is the filtered colimit of its finitely generated integer subalgebras.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe ringUniverse

open CategoryTheory Limits

namespace CommRingCat

variable (ring : Type ringUniverse) [CommRing ring] (predicate : Subalgebra ℤ ring → Prop)

/-- Integer subalgebras satisfying a predicate, with inclusion morphisms. -/
def subalgebraDiagram : {subalgebra : Subalgebra ℤ ring // predicate subalgebra} ⥤
    CommRingCat.{ringUniverse} where
  obj subalgebra := .of subalgebra.1
  map {firstSubalgebra secondSubalgebra} inclusion :=
    ofHom (Subalgebra.inclusion (leOfHom inclusion)).toRingHom

/-- The inclusion cocone from a family of integer subalgebras to the ambient ring. -/
def subalgebraCocone : Cocone (subalgebraDiagram ring predicate) where
  pt := .of ring
  ι := { app subalgebra := ofHom subalgebra.1.val.toRingHom }

variable [Nonempty {subalgebra : Subalgebra ℤ ring // predicate subalgebra}]
  [IsDirectedOrder {subalgebra : Subalgebra ℤ ring // predicate subalgebra}]

private noncomputable def subalgebraDesc
    (exhaustive : ⨆ subalgebra : {subalgebra : Subalgebra ℤ ring // predicate subalgebra},
      subalgebra.1 = ⊤) (cocone : Cocone (subalgebraDiagram ring predicate)) : ring →+* cocone.pt :=
  ((Subalgebra.iSupLift
      (fun subalgebra : {subalgebra : Subalgebra ℤ ring // predicate subalgebra} ↦ subalgebra.1)
      (Subtype.mono_coe _).directed_le
      (fun subalgebra ↦ by exact (cocone.ι.app subalgebra).hom.toIntAlgHom)
      (fun firstSubalgebra secondSubalgebra inclusion ↦ AlgHom.ext fun element ↦
        (ConcreteCategory.congr_hom
          (cocone.w (homOfLE (Subtype.coe_le_coe.mp inclusion))) element).symm)
      ⊤ exhaustive.ge).comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom

private lemma subalgebraDesc_val
    (exhaustive : ⨆ subalgebra : {subalgebra : Subalgebra ℤ ring // predicate subalgebra},
      subalgebra.1 = ⊤) (cocone : Cocone (subalgebraDiagram ring predicate))
    (subalgebra : {subalgebra : Subalgebra ℤ ring // predicate subalgebra})
    (element : subalgebra.1) :
    subalgebraDesc ring predicate exhaustive cocone (subalgebra.1.val element) =
      (cocone.ι.app subalgebra).hom element := by
  have topEquiv_val : Subalgebra.topEquiv.symm.toAlgHom (subalgebra.1.val element) =
      Subalgebra.inclusion (le_top : subalgebra.1 ≤ ⊤) element := Subtype.ext rfl
  simp only [subalgebraDesc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    topEquiv_val, Subalgebra.iSupLift_inclusion]
  rfl

/-- A nonempty directed family of integer subalgebras which exhausts the ring
has that ring as its colimit. -/
noncomputable def isColimitSubalgebraCocone
    (exhaustive : ⨆ subalgebra : {subalgebra : Subalgebra ℤ ring // predicate subalgebra},
      subalgebra.1 = ⊤) : IsColimit (subalgebraCocone ring predicate) where
  desc cocone := ofHom (subalgebraDesc ring predicate exhaustive cocone)
  fac cocone subalgebra := by
    ext element
    exact subalgebraDesc_val ring predicate exhaustive cocone subalgebra element
  uniq cocone candidate compatible := by
    ext element
    have element_mem : element ∈
        ⋃ subalgebra : {subalgebra : Subalgebra ℤ ring // predicate subalgebra},
          (subalgebra.1 : Set ring) := by
      rw [← Subalgebra.coe_iSup_of_directed (Subtype.mono_coe _).directed_le, exhaustive]
      trivial
    obtain ⟨subalgebra, membership⟩ := Set.mem_iUnion.mp element_mem
    exact (ConcreteCategory.congr_hom (compatible subalgebra) ⟨element, membership⟩).trans
      (subalgebraDesc_val ring predicate exhaustive cocone subalgebra ⟨element, membership⟩).symm

/-- The filtered diagram of finitely generated integer subalgebras. -/
abbrev fgSubalgebraDiagram : {subalgebra : Subalgebra ℤ ring // subalgebra.FG} ⥤
    CommRingCat.{ringUniverse} :=
  subalgebraDiagram ring Subalgebra.FG

/-- The inclusion cocone of finitely generated integer subalgebras. -/
abbrev fgSubalgebraCocone : Cocone (fgSubalgebraDiagram ring) :=
  subalgebraCocone ring Subalgebra.FG

/-- A commutative ring is the filtered colimit of its finitely generated integer subalgebras. -/
noncomputable def isColimitFgSubalgebraCocone : IsColimit (fgSubalgebraCocone ring) :=
  isColimitSubalgebraCocone ring Subalgebra.FG (Subalgebra.iSup_val_fg_eq_top ℤ ring)

end CommRingCat
