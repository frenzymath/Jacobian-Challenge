import Jacobian.AlgebraicGeometry.Curve.Genus
import Jacobian.AlgebraicGeometry.BaseChange.Field
import Jacobian.AlgebraicGeometry.Curve.AbelJacobiMap
import Jacobian.AlgebraicGeometry.Picard.FieldDescent
import Jacobian.AlgebraicGeometry.Picard.RepresentedFunctor
import Jacobian.AlgebraicGeometry.Picard.FieldExtensionCoherence
import Jacobian.AlgebraicGeometry.Picard.FieldExtensionIdentity
import Jacobian.AlgebraicGeometry.AbelianVariety.Albanese.UniversalProperty
import Jacobian.AlgebraicGeometry.Curve.Albanese

/-!
# Solution to the Jacobian challenge

The constructions here use the mathematical library independently of the
statement target `Challenge`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

private theorem mapIso_of_hom_comp
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [Category targetCategory]
    (F : sourceCategory ⥤ targetCategory) {source middle target : sourceCategory}
    (first : source ≅ middle) (second : middle ≅ target) (composite : source ≅ target)
    (compatibility : first.hom ≫ second.hom = composite.hom) :
    F.mapIso first ≪≫ F.mapIso second = F.mapIso composite := by
  rw [← Functor.mapIso_trans]
  exact congrArg (fun comparison : source ≅ target ↦ F.mapIso comparison)
    (Iso.ext compatibility)

private theorem mapIso_eq_trans_symm_of_hom_comp
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [Category targetCategory]
    (F : sourceCategory ⥤ targetCategory) {source middle target : sourceCategory}
    (first : source ≅ middle) (second : middle ≅ target) (composite : source ≅ target)
    (compatibility : first.hom ≫ second.hom = composite.hom) :
    F.mapIso first = F.mapIso composite ≪≫ F.mapIso second.symm := by
  rw [Functor.mapIso_symm]
  calc
    F.mapIso first = (F.mapIso first ≪≫ F.mapIso second) ≪≫
        (F.mapIso second).symm := by
      rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = F.mapIso composite ≪≫ (F.mapIso second).symm := by
      rw [mapIso_of_hom_comp F first second composite compatibility]

private theorem forget_mapCommGrpNatIso
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [CartesianMonoidalCategory sourceCategory]
    [BraidedCategory sourceCategory]
    [Category targetCategory] [CartesianMonoidalCategory targetCategory]
    [BraidedCategory targetCategory]
    {F G : sourceCategory ⥤ targetCategory} [F.Braided] [G.Braided]
    (comparison : F ≅ G) (group : CommGrp sourceCategory) :
    (CommGrp.forget₂Grp targetCategory).mapIso
        ((Functor.mapCommGrpNatIso comparison).app group) =
      (Functor.mapGrpNatIso comparison).app group.toGrp := by
  apply Iso.ext
  rfl

private theorem forget_mapCommGrpIdIso
    {sourceCategory : Type*} [Category sourceCategory]
    [CartesianMonoidalCategory sourceCategory] [BraidedCategory sourceCategory]
    (group : CommGrp sourceCategory) :
    (CommGrp.forget₂Grp sourceCategory).mapIso
        ((Functor.mapCommGrpIdIso (C := sourceCategory)).app group) =
      (Functor.mapGrpIdIso (C := sourceCategory)).app group.toGrp := by
  apply Iso.ext
  rfl

private theorem forget_mapCommGrpCompIso
    {sourceCategory middleCategory targetCategory : Type*}
    [Category sourceCategory] [CartesianMonoidalCategory sourceCategory]
    [BraidedCategory sourceCategory]
    [Category middleCategory] [CartesianMonoidalCategory middleCategory]
    [BraidedCategory middleCategory]
    [Category targetCategory] [CartesianMonoidalCategory targetCategory]
    [BraidedCategory targetCategory]
    (F : sourceCategory ⥤ middleCategory) [F.Braided]
    (G : middleCategory ⥤ targetCategory) [G.Braided]
    (group : CommGrp sourceCategory) :
    (CommGrp.forget₂Grp targetCategory).mapIso
        ((Functor.mapCommGrpCompIso (F := F) (G := G)).app group) =
      (Functor.mapGrpCompIso (F := F) (G := G)).app group.toGrp := by
  apply Iso.ext
  rfl

private theorem forget_mapCommGrp_mapIso
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [CartesianMonoidalCategory sourceCategory]
    [BraidedCategory sourceCategory]
    [Category targetCategory] [CartesianMonoidalCategory targetCategory]
    [BraidedCategory targetCategory]
    (F : sourceCategory ⥤ targetCategory) [F.Braided]
    {source target : CommGrp sourceCategory} (comparison : source ≅ target) :
    (CommGrp.forget₂Grp targetCategory).mapIso (F.mapCommGrp.mapIso comparison) =
      F.mapGrp.mapIso ((CommGrp.forget₂Grp sourceCategory).mapIso comparison) := by
  apply Iso.ext
  rfl

private theorem forget_identity_comparison
    {sourceCategory : Type*} [Category sourceCategory]
    [CartesianMonoidalCategory sourceCategory] [BraidedCategory sourceCategory]
    (F : sourceCategory ⥤ sourceCategory) [F.Braided]
    (comparison : F ≅ 𝟭 sourceCategory)
    {group extendedGroup : CommGrp sourceCategory}
    (first : F.mapCommGrp.obj group ≅ extendedGroup)
    (second : extendedGroup ≅ group)
    (compatibility : first.hom ≫ second.hom =
      ((Functor.mapCommGrpNatIso comparison).app group ≪≫
        (Functor.mapCommGrpIdIso (C := sourceCategory)).app group).hom) :
    (CommGrp.forget₂Grp sourceCategory).mapIso first =
      (Functor.mapGrpNatIso comparison).app group.toGrp ≪≫
        (Functor.mapGrpIdIso (C := sourceCategory)).app group.toGrp ≪≫
          ((CommGrp.forget₂Grp sourceCategory).mapIso second).symm := by
  have mapped := mapIso_eq_trans_symm_of_hom_comp
    (CommGrp.forget₂Grp sourceCategory) first second
    ((Functor.mapCommGrpNatIso comparison).app group ≪≫
      (Functor.mapCommGrpIdIso (C := sourceCategory)).app group) compatibility
  simpa only [Functor.mapIso_trans, Functor.mapIso_symm, forget_mapCommGrpNatIso,
    forget_mapCommGrpIdIso, Iso.trans_assoc] using mapped

private theorem forget_tower_comparison
    {sourceCategory middleCategory targetCategory : Type*}
    [Category sourceCategory] [CartesianMonoidalCategory sourceCategory]
    [BraidedCategory sourceCategory]
    [Category middleCategory] [CartesianMonoidalCategory middleCategory]
    [BraidedCategory middleCategory]
    [Category targetCategory] [CartesianMonoidalCategory targetCategory]
    [BraidedCategory targetCategory]
    (F : sourceCategory ⥤ middleCategory) [F.Braided]
    (G : middleCategory ⥤ targetCategory) [G.Braided]
    (H : sourceCategory ⥤ targetCategory) [H.Braided]
    (comparison : H ≅ F ⋙ G)
    {group : CommGrp sourceCategory} {middleGroup : CommGrp middleCategory}
    {directGroup iteratedGroup : CommGrp targetCategory}
    (first : F.mapCommGrp.obj group ≅ middleGroup)
    (last : G.mapCommGrp.obj middleGroup ≅ iteratedGroup)
    (direct : H.mapCommGrp.obj group ≅ directGroup)
    (second : directGroup ≅ iteratedGroup)
    (compatibility : direct.hom ≫ second.hom =
      ((Functor.mapCommGrpNatIso comparison).app group ≪≫
        (Functor.mapCommGrpCompIso (F := F) (G := G)).app group ≪≫
        G.mapCommGrp.mapIso first ≪≫ last).hom) :
    (CommGrp.forget₂Grp targetCategory).mapIso direct ≪≫
        (CommGrp.forget₂Grp targetCategory).mapIso second =
      (Functor.mapGrpNatIso comparison).app group.toGrp ≪≫
        (Functor.mapGrpCompIso (F := F) (G := G)).app group.toGrp ≪≫
        G.mapGrp.mapIso ((CommGrp.forget₂Grp middleCategory).mapIso first) ≪≫
          (CommGrp.forget₂Grp targetCategory).mapIso last := by
  have mapped := mapIso_of_hom_comp (CommGrp.forget₂Grp targetCategory)
    direct second
    ((Functor.mapCommGrpNatIso comparison).app group ≪≫
      (Functor.mapCommGrpCompIso (F := F) (G := G)).app group ≪≫
      G.mapCommGrp.mapIso first ≪≫ last) compatibility
  simpa only [Functor.mapIso_trans, forget_mapCommGrpNatIso,
    forget_mapCommGrpCompIso, forget_mapCommGrp_mapIso] using mapped

variable {k : Type u} [Field k]


/-- The genus of a smooth proper geometrically irreducible curve. -/
def genus (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ :=
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  C.left.arithmeticGenus k

private theorem jacobianRepresentationExists (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ∃ (variety : AbelianVariety k)
      (representation : (picardFunctorDegree C.hom 0).obj.RepresentableBy variety.group.X),
      PicardTensorCompatible C.hom variety.group representation ∧
        SmoothOfRelativeDimension (genus C) variety.group.X.hom := by
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  letI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  letI : GeometricallyIntegral C.hom := Smooth.geometricallyIntegral C.hom
  have : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  have : IsProper (C.left ↘ Spec (.of k)) := inferInstanceAs (IsProper C.hom)
  have : GeometricallyIntegral (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral C.hom)
  exact exists_abelianVariety_picardDegreeZero (baseField := k) C.left

private def jacobianVariety (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    AbelianVariety k :=
  (jacobianRepresentationExists C).choose

private def jacobianRepresentation (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    (picardFunctorDegree C.hom 0).obj.RepresentableBy (jacobianVariety C).group.X :=
  (jacobianRepresentationExists C).choose_spec.choose

private theorem jacobianTensorCompatible (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    PicardTensorCompatible C.hom (jacobianVariety C).group (jacobianRepresentation C) :=
  (jacobianRepresentationExists C).choose_spec.choose_spec.1

private theorem jacobianDimension (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    SmoothOfRelativeDimension (genus C) (jacobianVariety C).group.X.hom :=
  (jacobianRepresentationExists C).choose_spec.choose_spec.2

/-- The degree-zero Picard variety of a smooth proper curve. -/
def Jacobian (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Over (Spec (.of k)) :=
  (jacobianVariety C).group.X

namespace Jacobian

variable {C : Over (Spec (.of k))} [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- The tensor-product group law on the degree-zero Picard variety. -/
instance instGrpObj : GrpObj (Jacobian C) :=
  (jacobianVariety C).group.grp

instance : SmoothOfRelativeDimension (genus C) (Jacobian C).hom :=
  jacobianDimension C

instance : IsProper (Jacobian C).hom :=
  (jacobianVariety C).proper

instance : GeometricallyIrreducible (Jacobian C).hom :=
  (jacobianVariety C).geometricallyIrreducible

/-- The classifying map of the diagonal minus the specified constant section. -/
def ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ Jacobian C :=
  Curve.abelJacobiMap ⟨C⟩ P.left (by simpa using Over.w P) (jacobianRepresentation C)

/-- The normalized Abel map sends the marked rational point to the group identity. -/
theorem comp_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ofCurve P = η[Jacobian C] := by
  have native := Curve.abelJacobiMap_point
      (representingGroup := (jacobianVariety C).group)
      ⟨C⟩ P.left (by simpa using Over.w P)
      (jacobianRepresentation C) (jacobianTensorCompatible C)
  change P ≫ ofCurve P = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ Jacobian C) at native
  simpa only [CategoryTheory.Hom.one_def,
    SemiCartesianMonoidalCategory.toUnit_unit, Category.id_comp] using native

/-- Every normalized map to a smooth proper connected group scheme factors
uniquely through the Abel map, among all scheme morphisms. -/
theorem exists_unique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : Jacobian C ⟶ A), f = ofCurve P ≫ g := by
  have albanese : IsAlbanese P (jacobianVariety C) (ofCurve P) :=
    Curve.isAlbanese_abelJacobiMap ⟨C⟩ P (jacobianVariety C)
      (jacobianRepresentation C) (jacobianTensorCompatible C)
  exact albanese.existsUnique_schemeMap f hf

private def commGrpFunctor (k : Type u) [Field k] :
    (Curve k)ᵒᵖ ⥤ CommGrp (Over (Spec (.of k))) :=
  PicardTensorCompatible.representedFunctor
    (fun curve ↦ (jacobianVariety curve.carrier).group)
    (fun curve ↦ jacobianRepresentation curve.carrier)
    (fun curve ↦ jacobianTensorCompatible curve.carrier)

private def commGrpComparison {k : Type u} [Field k] {C C' : Over (Spec (.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsProper C'.hom] [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]
    (e : C ≅ C') : (jacobianVariety C).group ≅ (jacobianVariety C').group := by
  let firstCurve : Curve k := ⟨C⟩
  let secondCurve : Curve k := ⟨C'⟩
  let comparison : firstCurve ≅ secondCurve :=
    { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }
  exact (commGrpFunctor k).mapIso
    (X := .op firstCurve) (Y := .op secondCurve) comparison.symm.op

private theorem commGrpComparison_hom_of_forget_mapIso {k : Type u} [Field k]
    {C C' : Over (Spec (.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsProper C'.hom] [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]
    (e : C ≅ C') (comparison : (⟨C⟩ : Curve k) ≅ ⟨C'⟩)
    (underlying : (Curve.forget k).mapIso comparison = e) :
    (commGrpComparison e).hom =
      PicardTensorCompatible.representedPullback (source := ⟨C'⟩) (target := ⟨C⟩)
        (jacobianTensorCompatible C') (jacobianTensorCompatible C) comparison.inv := by
  have inverse : comparison.inv = e.inv :=
    congrArg (fun isomorphism : C ≅ C' ↦ isomorphism.inv) underlying
  rw [inverse]
  rfl

private theorem commGrpComparison_symm {k : Type u} [Field k]
    {C C' : Over (Spec (.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsProper C'.hom] [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]
    (e : C ≅ C') : commGrpComparison e.symm = (commGrpComparison e).symm := by
  apply Iso.ext
  rfl

/-- Pullback of degree-zero line bundles gives the contravariant Jacobian functor. -/
def functor (k : Type u) [Field k] : (Curve k)ᵒᵖ ⥤ Grp (Over (Spec (.of k))) :=
  commGrpFunctor k ⋙ CommGrp.forget₂Grp _

/-- The curve-isomorphism comparison is induced by the Jacobian functor. -/
def congr {k : Type u} [Field k] {C C' : Over (Spec (.of k))}
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsProper C'.hom] [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]
    (e : C ≅ C') :
    (.mk (Jacobian C) : Grp (Over (Spec (.of k)))) ≅ .mk (Jacobian C') :=
  (CommGrp.forget₂Grp _).mapIso (commGrpComparison e)

/-- The Cartesian comparison of represented Picard groups under field extension. -/
def baseChangeIso (k L : Type u) [Field k] [Field L] [Algebra k L]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    (baseChange k L).mapGrp.obj (.mk (Jacobian C)) ≅
      .mk (Jacobian ((baseChange k L).obj C)) :=
  (CommGrp.forget₂Grp _).mapIso
    (PicardTensorCompatible.baseChangeIso (curve := ⟨C⟩)
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k L).obj C)))

/-- Identity field extension agrees with the canonical group and curve comparisons. -/
theorem baseChangeIso_id (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    baseChangeIso k k C =
      (Functor.mapGrpNatIso (baseChange.idIso k)).app _ ≪≫
        (Functor.mapGrpIdIso (C := Over (Spec (.of k)))).app _ ≪≫
          Jacobian.congr ((baseChange.idIso k).app C).symm := by
  have native := PicardTensorCompatible.baseChangeIso_id (curve := ⟨C⟩)
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k k).obj C))
  rw [← commGrpComparison_hom_of_forget_mapIso ((baseChange.idIso k).app C)
    ((Curve.baseChange.idIso k).app ⟨C⟩)
    (Curve.forget_mapIso_baseChange_idIso_app k ⟨C⟩)] at native
  exact forget_identity_comparison (baseChange k k) (baseChange.idIso k)
    (PicardTensorCompatible.baseChangeIso (baseField := k) (extensionField := k)
      (curve := ⟨C⟩) (sourceGroup := (jacobianVariety C).group)
      (extendedGroup := (jacobianVariety ((baseChange k k).obj C)).group)
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k k).obj C)))
    (commGrpComparison ((baseChange.idIso k).app C))
    native

/-- Direct and iterated field extension induce the same Jacobian comparison. -/
theorem baseChangeIso_comp (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    baseChangeIso k M C ≪≫ Jacobian.congr ((baseChange.compIso k L M).app C) =
      (Functor.mapGrpNatIso (baseChange.compIso k L M)).app _ ≪≫
        (Functor.mapGrpCompIso (F := baseChange k L) (G := baseChange L M)).app _ ≪≫
        (baseChange L M).mapGrp.mapIso (baseChangeIso k L C) ≪≫
          baseChangeIso L M ((baseChange k L).obj C) := by
  have native := PicardTensorCompatible.baseChangeIso_comp (curve := ⟨C⟩)
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k L).obj C))
      (jacobianTensorCompatible ((baseChange k M).obj C))
      (jacobianTensorCompatible ((baseChange k L ⋙ baseChange L M).obj C))
  rw [← commGrpComparison_hom_of_forget_mapIso ((baseChange.compIso k L M).app C)
    ((Curve.baseChange.compIso k L M).app ⟨C⟩)
    (Curve.forget_mapIso_baseChange_compIso_app k L M ⟨C⟩)] at native
  exact forget_tower_comparison (baseChange k L) (baseChange L M) (baseChange k M)
    (baseChange.compIso k L M)
    (PicardTensorCompatible.baseChangeIso (baseField := k) (extensionField := L)
      (curve := ⟨C⟩) (sourceGroup := (jacobianVariety C).group)
      (extendedGroup := (jacobianVariety ((baseChange k L).obj C)).group)
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k L).obj C)))
    (PicardTensorCompatible.baseChangeIso (baseField := L) (extensionField := M)
        (curve := ⟨(baseChange k L).obj C⟩)
        (sourceGroup := (jacobianVariety ((baseChange k L).obj C)).group)
        (extendedGroup := (jacobianVariety ((baseChange k L ⋙ baseChange L M).obj C)).group)
        (jacobianTensorCompatible ((baseChange k L).obj C))
        (jacobianTensorCompatible ((baseChange k L ⋙ baseChange L M).obj C)))
    (PicardTensorCompatible.baseChangeIso (baseField := k) (extensionField := M)
      (curve := ⟨C⟩) (sourceGroup := (jacobianVariety C).group)
      (extendedGroup := (jacobianVariety ((baseChange k M).obj C)).group)
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k M).obj C)))
    (commGrpComparison ((baseChange.compIso k L M).app C))
    native

variable {L : Type u} [Field L] [Algebra k L]

/-- Field extension preserves the normalized Abel–Jacobi map. -/
theorem baseChange_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (baseChange k L).map (ofCurve P) ≫ (baseChangeIso k L C).hom.hom.hom =
      ofCurve (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P) := by
  let curve : Curve k := ⟨C⟩
  have point_over : P.left ≫ C.hom = 𝟙 _ := by simpa using Over.w P
  have native := Curve.abelJacobiMap_baseChange
      (baseField := k) (extensionField := L)
      (sourceGroup := (jacobianVariety C).group)
      (extendedGroup := (jacobianVariety ((baseChange k L).obj C)).group)
      curve P.left point_over (jacobianRepresentation C)
      (jacobianRepresentation ((baseChange k L).obj C))
      (jacobianTensorCompatible C)
      (jacobianTensorCompatible ((baseChange k L).obj C))
  let liftedPoint : 𝟙_ (Over (Spec (.of L))) ⟶ (baseChange k L).obj C :=
    Over.homMk (Curve.baseChangePoint (extensionField := L) curve P.left point_over)
      (Curve.baseChangePoint_over (extensionField := L) curve P.left point_over)
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have unit_snd : (Functor.LaxMonoidal.ε (baseChange k L)).left ≫
      pullback.snd (𝟙 (Spec (.of k))) fieldMap = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε (baseChange k L))
  have unit_fst : (Functor.LaxMonoidal.ε (baseChange k L)).left ≫
      pullback.fst (𝟙 (Spec (.of k))) fieldMap = fieldMap := by
    calc
      _ = ((Functor.LaxMonoidal.ε (baseChange k L)).left ≫
          pullback.snd (𝟙 (Spec (.of k))) fieldMap) ≫ fieldMap := by
        rw [Category.assoc, ← pullback.condition, Category.comp_id]
      _ = fieldMap := by rw [unit_snd, Category.id_comp]
  have point_eq : liftedPoint =
      Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P := by
    apply Over.OverMorphism.ext
    change Curve.baseChangePoint (extensionField := L) curve P.left point_over =
      (Functor.LaxMonoidal.ε (baseChange k L)).left ≫ ((baseChange k L).map P).left
    apply pullback.hom_ext
    · rw [Curve.baseChangePoint, pullback.lift_fst]
      dsimp only [curve]
      simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
      simpa only [Category.assoc, Over.tensorUnit_hom, Over.tensorUnit_left] using
        (congrArg (fun arrow ↦ arrow ≫ P.left) unit_fst).symm
    · rw [Curve.baseChangePoint, pullback.lift_snd]
      exact (Over.w (Functor.LaxMonoidal.ε (baseChange k L) ≫
        (baseChange k L).map P)).symm
  change (baseChange k L).map (ofCurve P) ≫ (baseChangeIso k L C).hom.hom.hom =
    ofCurve liftedPoint at native
  exact native.trans (congrArg (fun point ↦ ofCurve point) point_eq)

end Jacobian

end AlgebraicGeometry
