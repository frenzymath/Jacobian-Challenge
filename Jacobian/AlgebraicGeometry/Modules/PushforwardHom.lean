import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Jacobian.AlgebraicGeometry.Modules.Dual
import Jacobian.AlgebraicGeometry.Modules.LocalIsomorphism
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeAffine
import Jacobian.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# Internal hom and pushforward

A map `traceMap : f_* L ⟶ G` induces `f_* Hom(M,L) ⟶ Hom(f_* M,G)`,
naturally in `M`. For an affine morphism, this comparison is an isomorphism
for every finite locally free `M` if it is one for the structure sheaf.
The reduction uses finite projective splittings on affine opens.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe moduleMorphism

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme targetScheme : Scheme.{moduleMorphism}} (morphism : sourceScheme ⟶ targetScheme) {dualizingSheaf : sourceScheme.Modules} {targetSheaf : targetScheme.Modules}
  (traceMap : (pushforward morphism).obj dualizingSheaf ⟶ targetSheaf) (moduleSheaf : sourceScheme.Modules)

/-- The section `τ ∘ f_* φ : (f_* M)|_V ⟶ G|_V` of `Hom(f_* M, G)` over `V` given by a section
`φ : M|_{f⁻¹V} ⟶ L|_{f⁻¹V}` of `Hom(M, L)` over `f⁻¹V`. -/
noncomputable def pushforwardHomObjComparisonApp (openSubset : targetScheme.Opens)
    (homomorphism : (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj dualizingSheaf.val) :
    (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj ((pushforward morphism).obj moduleSheaf).val ⟶
      (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj targetSheaf.val where
  app overOpen := (ModuleCat.restrictScalars (morphism.app overOpen.unop.left).hom).map
      (homomorphism.app (op (Over.mk ((TopologicalSpace.Opens.map morphism.base).map overOpen.unop.hom)))) ≫
    traceMap.val.app (op overOpen.unop.left)
  naturality {overOpen otherOverOpen} restrictionMap := by
    ext sectionValue
    have h₁ := PresheafOfModules.naturality_apply homomorphism
      (Over.homMk ((TopologicalSpace.Opens.map morphism.base).map restrictionMap.unop.left) (Subsingleton.elim _ _) :
        Over.mk ((TopologicalSpace.Opens.map morphism.base).map otherOverOpen.unop.hom) ⟶
          Over.mk ((TopologicalSpace.Opens.map morphism.base).map overOpen.unop.hom)).op sectionValue
    have h₂ := PresheafOfModules.naturality_apply traceMap.val restrictionMap.unop.left.op
      ((homomorphism.app (op (Over.mk ((TopologicalSpace.Opens.map morphism.base).map overOpen.unop.hom)))).hom sectionValue)
    exact (congrArg (traceMap.val.app (op otherOverOpen.unop.left)) h₁).trans h₂

@[simp]
lemma pushforwardHomObjComparisonApp_app_apply (openSubset : targetScheme.Opens)
    (homomorphism : (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj dualizingSheaf.val)
    (overOpen : (Over openSubset)ᵒᵖ) (sectionValue : Γ(moduleSheaf, morphism ⁻¹ᵁ overOpen.unop.left)) :
    (pushforwardHomObjComparisonApp morphism traceMap moduleSheaf openSubset homomorphism).app overOpen sectionValue = traceMap.val.app (op overOpen.unop.left)
      ((homomorphism.app (op (Over.mk ((TopologicalSpace.Opens.map morphism.base).map overOpen.unop.hom)))).hom sectionValue) :=
  rfl

/-- The morphism `f_* Hom(M, L) ⟶ Hom(f_* M, G)` of sheaves of modules on `Y` sending a section
`φ : M|_{f⁻¹V} ⟶ L|_{f⁻¹V}` to `τ ∘ f_* φ : (f_* M)|_V ⟶ G|_V`. -/
noncomputable def pushforwardHomObjComparison :
    (pushforward morphism).obj (homObj moduleSheaf dualizingSheaf) ⟶ homObj ((pushforward morphism).obj moduleSheaf) targetSheaf where
  val :=
    { app openSubset := ModuleCat.ofHom (X := ((pushforward morphism).obj (homObj moduleSheaf dualizingSheaf)).val.obj openSubset)
        (Y := (homObj ((pushforward morphism).obj moduleSheaf) targetSheaf).val.obj openSubset)
        { toFun := pushforwardHomObjComparisonApp morphism traceMap moduleSheaf openSubset.unop
          map_add' homomorphism otherHomomorphism := by
            refine PresheafOfModules.hom_ext fun overOpen ↦ ?_
            ext sectionValue
            exact map_add (traceMap.val.app (op overOpen.unop.left)).hom _ _
          map_smul' scalar homomorphism := by
            refine PresheafOfModules.hom_ext fun overOpen ↦ ?_
            ext sectionValue
            have splitting := (ConcreteCategory.congr_hom (morphism.naturality overOpen.unop.hom.op) scalar).symm
            let imageSection : Γ(dualizingSheaf, morphism ⁻¹ᵁ overOpen.unop.left) :=
              (homomorphism.app (op (Over.mk ((TopologicalSpace.Opens.map morphism.base).map overOpen.unop.hom)))).hom sectionValue
            exact (congrArg (fun indices : Γ(sourceScheme, morphism ⁻¹ᵁ overOpen.unop.left) ↦ traceMap.app overOpen.unop.left
              (show Γ((pushforward morphism).obj dualizingSheaf, overOpen.unop.left) from indices • imageSection)) splitting).trans
                (traceMap.app_smul (targetScheme.presheaf.map overOpen.unop.hom.op scalar) imageSection) }
      naturality {openSubset V'} restrictionMap := by
        ext homomorphism : 2
        refine PresheafOfModules.hom_ext fun overOpen ↦ ?_
        ext sectionValue
        exact congrArg (traceMap.val.app (op overOpen.unop.left)).hom
          (PresheafOfModules.restrictOver_hom_app_congr homomorphism rfl sectionValue) }

variable {moduleSheaf} in
/-- `f_* Hom(M, L) ⟶ Hom(f_* M, G)` is natural in `M`: for `u : M' ⟶ M` the square
```
  f_* Hom(M, L)  ---> Hom(f_* M, G)
        |                   |
     f_* u^*            (f_* u)^*
        v                   v
  f_* Hom(M', L) ---> Hom(f_* M', G)
```
commutes. -/
@[reassoc]
lemma pushforwardHomObjComparison_naturality {otherModuleSheaf : sourceScheme.Modules} (moduleMorphism : otherModuleSheaf ⟶ moduleSheaf) :
    (pushforward morphism).map (SheafOfModules.homObjMap (R := sourceScheme.sheaf) moduleMorphism (𝟙 dualizingSheaf)) ≫
        pushforwardHomObjComparison morphism traceMap otherModuleSheaf =
      pushforwardHomObjComparison morphism traceMap moduleSheaf ≫
        SheafOfModules.homObjMap (R := targetScheme.sheaf) ((pushforward morphism).map moduleMorphism) (𝟙 targetSheaf) := by
  ext openSubset homomorphism
  rfl

/-- The morphism `f_* Hom(M, L) ⟶ Hom(f_* M, G)`, `φ ↦ τ ∘ f_* φ`, as a natural transformation
in `M`. -/
@[simps]
noncomputable def pushforwardHomObjComparisonNatTrans :
    (SheafOfModules.homFunctor sourceScheme.sheaf).flip.obj dualizingSheaf ⋙ pushforward morphism ⟶
      (pushforward morphism).op ⋙ (SheafOfModules.homFunctor targetScheme.sheaf).flip.obj targetSheaf where
  app moduleSheaf := pushforwardHomObjComparison morphism traceMap moduleSheaf.unop
  naturality _ _ moduleMorphism := pushforwardHomObjComparison_naturality morphism traceMap moduleMorphism.unop

section Retract

variable {morphism traceMap}

/-- `φ ↦ τ ∘ f_* φ` is compatible with composition: `τ ∘ f_*(φ ∘ a) = (τ ∘ f_* φ) ∘ f_* a`. -/
lemma pushforwardHomObjComparisonApp_comp {otherModuleSheaf : sourceScheme.Modules} (openSubset : targetScheme.Opens)
    (precomposition : (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj otherModuleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val)
    (homomorphism : (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj dualizingSheaf.val) :
    pushforwardHomObjComparisonApp morphism traceMap otherModuleSheaf openSubset (precomposition ≫ homomorphism) =
      pushforwardHomObjComparisonApp morphism (𝟙 _) otherModuleSheaf openSubset precomposition ≫
        pushforwardHomObjComparisonApp morphism traceMap moduleSheaf openSubset homomorphism := by
  refine PresheafOfModules.hom_ext fun overOpen ↦ ?_
  ext sectionValue
  rfl

lemma pushforwardHomObjComparisonApp_id (openSubset : targetScheme.Opens) :
    pushforwardHomObjComparisonApp morphism (𝟙 _) moduleSheaf openSubset (𝟙 _) = 𝟙 _ := by
  refine PresheafOfModules.hom_ext fun overOpen ↦ ?_
  ext sectionValue
  rfl

lemma pushforwardHomObjComparisonApp_sum (openSubset : targetScheme.Opens) {indexType : Type*} (indices : Finset indexType)
    (homomorphism : indexType → ((PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj dualizingSheaf.val)) :
    pushforwardHomObjComparisonApp morphism traceMap moduleSheaf openSubset (∑ index ∈ indices, homomorphism index) =
      ∑ index ∈ indices, pushforwardHomObjComparisonApp morphism traceMap moduleSheaf openSubset (homomorphism index) :=
  map_sum ((pushforwardHomObjComparison morphism traceMap moduleSheaf).val.app (op openSubset)).hom homomorphism indices

/-- If `M|_{f⁻¹V}` is a direct summand of a finite direct sum of copies of `N|_{f⁻¹V}`, and
`φ ↦ τ ∘ f_* φ` is bijective over `V` for `N`, then it is bijective over `V` for `M`. -/
lemma bijective_pushforwardHomObjComparisonApp_of_sum_comp_eq_id {summandSheaf : sourceScheme.Modules} (openSubset : targetScheme.Opens)
    {rank : ℕ} (coordinates : Fin rank → ((PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj summandSheaf.val))
    (generators : Fin rank → ((PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj summandSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val))
    (splitting : ∑ index, coordinates index ≫ generators index = 𝟙 _)
    (hN : Function.Bijective (pushforwardHomObjComparisonApp morphism traceMap summandSheaf openSubset)) :
    Function.Bijective (pushforwardHomObjComparisonApp morphism traceMap moduleSheaf openSubset) := by
  have hsum (homomorphism : (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj moduleSheaf.val ⟶
      (PresheafOfModules.restrictOver sourceScheme.sheaf.obj (morphism ⁻¹ᵁ openSubset)).obj dualizingSheaf.val) :
      homomorphism = ∑ index, coordinates index ≫ generators index ≫ homomorphism := by
    simp_rw [← Category.assoc, ← Preadditive.sum_comp, splitting, Category.id_comp]
  refine ⟨fun homomorphism otherHomomorphism hφψ ↦ ?_, fun targetHomomorphism ↦ ?_⟩
  · have hj (index : Fin rank) : generators index ≫ homomorphism = generators index ≫ otherHomomorphism := hN.1 <| by
      rw [pushforwardHomObjComparisonApp_comp, pushforwardHomObjComparisonApp_comp, hφψ]
    rw [hsum homomorphism, hsum otherHomomorphism]
    simp_rw [hj]
  · choose otherHomomorphism hψ using fun index ↦ hN.2 (pushforwardHomObjComparisonApp morphism (𝟙 _) summandSheaf openSubset (generators index) ≫ targetHomomorphism)
    refine ⟨∑ index, coordinates index ≫ otherHomomorphism index, ?_⟩
    rw [pushforwardHomObjComparisonApp_sum]
    simp_rw [pushforwardHomObjComparisonApp_comp, hψ, ← Category.assoc]
    rw [← Preadditive.sum_comp]
    simp_rw [← pushforwardHomObjComparisonApp_comp]
    rw [← pushforwardHomObjComparisonApp_sum, splitting, pushforwardHomObjComparisonApp_id,
      Category.id_comp]

/-- **Reduction to the structure sheaf.** Let `f : X ⟶ Y` be affine and `τ : f_* L ⟶ G`. If
`f_* Hom(𝒪_X, L) ⟶ Hom(f_* 𝒪_X, G)`, `φ ↦ τ ∘ f_* φ`, is an isomorphism, then so is
`f_* Hom(M, L) ⟶ Hom(f_* M, G)` for every finite locally free `M`. Both sides are sheaves, so it
suffices to check bijectivity over affine opens `V ⊆ Y`; there `f⁻¹V` is affine, so `M|_{f⁻¹V}`
is a direct summand of a free module of finite rank
(`AlgebraicGeometry.Scheme.Modules.exists_sum_comp_eq_id_over`), and the comparison for `M` is a
retract of the one for `𝒪_X^n`. -/
theorem isIso_pushforwardHomObjComparison_of_isIso_unit [IsAffineHom morphism]
    (hτ : IsIso (pushforwardHomObjComparison morphism traceMap (SheafOfModules.unit sourceScheme.ringCatSheaf)))
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFiniteLocallyFree] : IsIso (pushforwardHomObjComparison morphism traceMap moduleSheaf) := by
  refine isIso_of_bijective_app_of_isAffineOpen _ fun openSubset hV ↦ ?_
  obtain ⟨rank, coordinates, generators, splitting⟩ := exists_sum_comp_eq_id_over moduleSheaf (hV.preimage morphism)
  have hN : Function.Bijective
      (pushforwardHomObjComparisonApp morphism traceMap (SheafOfModules.unit sourceScheme.ringCatSheaf) openSubset) :=
    ConcreteCategory.bijective_of_isIso
      (Hom.app (pushforwardHomObjComparison morphism traceMap (SheafOfModules.unit sourceScheme.ringCatSheaf)) openSubset)
  have h' := congrArg (fun restrictionMap ↦ (SheafOfModules.forget _).map restrictionMap) splitting
  simp only [Functor.map_sum, Functor.map_comp] at h'
  exact bijective_pushforwardHomObjComparisonApp_of_sum_comp_eq_id moduleSheaf openSubset
    (fun index ↦ (SheafOfModules.forget _).map (coordinates index)) (fun index ↦ (SheafOfModules.forget _).map (generators index))
    h' hN

end Retract

end AlgebraicGeometry.Scheme.Modules
