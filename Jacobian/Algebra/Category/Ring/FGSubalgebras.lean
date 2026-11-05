import Jacobian.Algebra.Category.Ring.Subalgebras

/-!
# A field algebra as a filtered colimit of finite-type subalgebras

The finitely generated subalgebras exhaust the algebra, and their cocone is
colimiting in commutative rings, without requiring morphisms to preserve the base.
-/

set_option backward.isDefEq.respectTransparency false

universe ringUniverse

open CategoryTheory Limits

namespace CommRingCat

variable (baseField algebra : Type ringUniverse) [Field baseField] [CommRing algebra] [Algebra baseField algebra]

/-- The diagram in `CommRingCat` of the finitely generated `baseField`-subalgebras of a `baseField`-algebra `algebra`. -/
@[simps]
def fgSubalgebraDiagramOf : {subalgebra : Subalgebra baseField algebra // subalgebra.FG} ⥤ CommRingCat.{ringUniverse} where
  obj subalgebra := .of subalgebra.1
  map {subalgebra largerSubalgebra} inclusion := ofHom (Subalgebra.inclusion (leOfHom inclusion)).toRingHom

/-- `algebra` as a cocone over its finitely generated `baseField`-subalgebras. -/
@[simps]
def fgSubalgebraCoconeOf : Cocone (fgSubalgebraDiagramOf baseField algebra) where
  pt := .of algebra
  ι := { app subalgebra := ofHom subalgebra.1.val.toRingHom }

lemma iSup_restrictScalars_fg :
    ⨆ subalgebra : {subalgebra : Subalgebra baseField algebra // subalgebra.FG}, subalgebra.1.restrictScalars ℤ = ⊤ := by
  rw [eq_top_iff]
  rintro element -
  let subalgebra : {subalgebra : Subalgebra baseField algebra // subalgebra.FG} :=
    ⟨Algebra.adjoin baseField ↑({element} : Finset algebra), Subalgebra.fg_adjoin_finset _⟩
  have elementMembership : element ∈ subalgebra.1 := Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_singleton_self element))
  exact Algebra.mem_iSup_of_mem (S := fun subalgebra : {subalgebra : Subalgebra baseField algebra // subalgebra.FG} ↦
    subalgebra.1.restrictScalars ℤ) subalgebra elementMembership

lemma directed_restrictScalars :
    Directed (· ≤ ·) fun subalgebra : {subalgebra : Subalgebra baseField algebra // subalgebra.FG} ↦ subalgebra.1.restrictScalars ℤ :=
  Monotone.directed_le fun subalgebra largerSubalgebra compatibility _ elementMembership ↦ (show subalgebra.1 ≤ largerSubalgebra.1 from compatibility) elementMembership

/-- The ring homomorphism induced by a cocone over finite-type subalgebras. -/
noncomputable def fgSubalgebraDescOf (cocone : Cocone (fgSubalgebraDiagramOf baseField algebra)) : algebra →+* cocone.pt :=
  ((Subalgebra.iSupLift (fun subalgebra : {subalgebra : Subalgebra baseField algebra // subalgebra.FG} ↦ subalgebra.1.restrictScalars ℤ)
      (directed_restrictScalars baseField algebra)
      (fun subalgebra ↦ by exact (cocone.ι.app subalgebra).hom.toIntAlgHom)
      (fun subalgebra largerSubalgebra compatibility ↦ AlgHom.ext fun element ↦
        (ConcreteCategory.congr_hom (cocone.w (homOfLE (Subtype.coe_le_coe.mp
          (fun _ membership ↦ compatibility membership)))) element).symm)
      ⊤ (iSup_restrictScalars_fg baseField algebra).ge).comp Subalgebra.topEquiv.symm.toAlgHom).toRingHom

lemma fgSubalgebraDescOf_val (cocone : Cocone (fgSubalgebraDiagramOf baseField algebra))
    (subalgebra : {subalgebra : Subalgebra baseField algebra // subalgebra.FG}) (element : subalgebra.1) :
    fgSubalgebraDescOf baseField algebra cocone (subalgebra.1.val element) = (cocone.ι.app subalgebra).hom element := by
  have compatibility : Subalgebra.topEquiv.symm.toAlgHom (subalgebra.1.val element)
      = Subalgebra.inclusion (le_top : subalgebra.1.restrictScalars ℤ ≤ ⊤) element := Subtype.ext rfl
  simp only [fgSubalgebraDescOf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, compatibility,
    Subalgebra.iSupLift_inclusion]
  rfl

/-- subalgebra `baseField`-algebra is the filtered colimit in `CommRingCat` of its finitely generated
`baseField`-subalgebras. -/
noncomputable def isColimitFGSubalgebraCocone : IsColimit (fgSubalgebraCoconeOf baseField algebra) where
  desc cocone := ofHom (fgSubalgebraDescOf baseField algebra cocone)
  fac cocone subalgebra := by
    ext element
    exact fgSubalgebraDescOf_val baseField algebra cocone subalgebra element
  uniq cocone desc hm := by
    ext element
    have elementMembership : element ∈ (⊤ : Subalgebra ℤ algebra) := trivial
    rw [← iSup_restrictScalars_fg baseField algebra, ← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed
      (directed_restrictScalars baseField algebra)] at elementMembership
    obtain ⟨subalgebra, subalgebraMembership⟩ := Set.mem_iUnion.mp elementMembership
    exact (ConcreteCategory.congr_hom (hm subalgebra) ⟨element, subalgebraMembership⟩).trans
      (fgSubalgebraDescOf_val baseField algebra cocone subalgebra ⟨element, subalgebraMembership⟩).symm


end CommRingCat
