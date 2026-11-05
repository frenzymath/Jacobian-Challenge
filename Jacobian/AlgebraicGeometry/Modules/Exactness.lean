import Jacobian.Algebra.Category.ModuleCat.Sheaf.Colimits
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Evaluation
import Jacobian.Algebra.Homology.Embedding.Property
import Jacobian.Algebra.Homology.Embedding.Map
import Jacobian.Algebra.Homology.MappingCone.Acyclic
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Abelian

/-!
# Local exactness for sheaves of modules

Exactness and quasi-isomorphisms can be checked on stalks, or on sections over
arbitrarily small neighbourhoods. These criteria do not require quasi-coherent
coefficients or an affine hypothesis.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The stalk at `x` of the underlying abelian sheaf of an `𝒪_X`-module. -/
noncomputable def stalkFunctor (x : X) : X.Modules ⥤ Ab.{u} :=
  SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ TopCat.Sheaf.forget Ab.{u} X ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} x

lemma stalkFunctor_obj (x : X) (M : X.Modules) :
    (stalkFunctor x).obj M = M.presheaf.stalk x :=
  rfl

instance (x : X) : (stalkFunctor x).Additive := by
  have : (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
      X.Modules ⥤ TopCat.Sheaf Ab.{u} X).Additive :=
    inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive
  have : (TopCat.Sheaf.forget Ab.{u} X).Additive := inferInstance
  have : (TopCat.Presheaf.stalkFunctor Ab.{u} x).Additive := inferInstance
  dsimp only [stalkFunctor]
  infer_instance

instance (x : X) : PreservesFiniteLimits (stalkFunctor x) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.forget Ab.{u} X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x) := inferInstance
  exact comp_preservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) _

instance (x : X) : PreservesFiniteColimits (stalkFunctor x) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
      X.Modules ⥤ TopCat.Sheaf Ab.{u} X) :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  dsimp only [stalkFunctor]
  have : PreservesFiniteColimits (TopCat.Sheaf.forget Ab.{u} X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  exact comp_preservesFiniteColimits _ _

/-- **Exactness is stalk-local.** A short complex of `𝒪_X`-modules is exact if and only if its
stalks at all points are exact. -/
theorem exact_iff_stalkFunctor (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, (S.map (stalkFunctor x)).Exact := by
  have : (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
      X.Modules ⥤ TopCat.Sheaf Ab.{u} X).PreservesZeroMorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
      X.Modules ⥤ TopCat.Sheaf Ab.{u} X) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
      X.Modules ⥤ TopCat.Sheaf Ab.{u} X) :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  have : (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
      X.Modules ⥤ TopCat.Sheaf Ab.{u} X).Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Faithful
  rw [← ShortComplex.exact_map_iff_of_faithful S
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf : X.Modules ⥤ TopCat.Sheaf Ab.{u} X),
    TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  rfl

/-- A homological complex of `𝒪_X`-modules is exact in degree `i` if and only if its stalks at
all points are. -/
theorem exactAt_iff_stalkFunctor {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (i : ι) :
    K.ExactAt i ↔ ∀ x : X, (((stalkFunctor x).mapHomologicalComplex c).obj K).ExactAt i := by
  simp only [HomologicalComplex.exactAt_iff]
  exact exact_iff_stalkFunctor (K.sc i)

/-- A homological complex of `𝒪_X`-modules is acyclic if and only if its stalks at all points
are. -/
theorem acyclic_iff_stalkFunctor {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) :
    K.Acyclic ↔ ∀ x : X, (((stalkFunctor x).mapHomologicalComplex c).obj K).Acyclic := by
  simp only [HomologicalComplex.Acyclic, exactAt_iff_stalkFunctor K]
  exact forall_comm

/-- The sections over `W` of an `𝒪_X`-module, as an abelian group. -/
noncomputable abbrev sectionsAb (W : X.Opens) : X.Modules ⥤ Ab.{u} :=
  SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙ forget₂ _ Ab.{u}

instance (W : X.Opens) : (sectionsAb W).Additive where
  map_add := rfl

/-- **Exactness from sections over small opens.** A short complex of `𝒪_X`-modules is exact if
every point has arbitrarily small open neighbourhoods over which its sections are exact. -/
theorem exact_of_exact_sectionsAb (S : ShortComplex X.Modules)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      (S.map (sectionsAb W)).Exact) : S.Exact := by
  rw [exact_iff_stalkFunctor]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.presheaf a
  have ha' : S.X₃.presheaf.germ V x hxV (S.g.app V s) = S.X₃.presheaf.germ V x hxV 0 := by
    rw [map_zero]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV S.g.mapPresheaf s).symm.trans ha
  obtain ⟨V', hxV', i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ ha'
  rw [map_zero] at e
  obtain ⟨W, hxW, hWV', hW⟩ := h x V' hxV'
  rw [ShortComplex.ab_exact_iff] at hW
  obtain ⟨t, ht⟩ := hW (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) (by
    change S.g.app W (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) = 0
    have naturality := ConcreteCategory.congr_hom
      (S.g.mapPresheaf.naturality (homOfLE (hWV'.trans i₁.le)).op) s
    change S.g.app W (S.X₂.presheaf.map (homOfLE (hWV'.trans i₁.le)).op s) =
      S.X₃.presheaf.map (homOfLE (hWV'.trans i₁.le)).op (S.g.app V s) at naturality
    rw [naturality, show S.X₃.presheaf.map (homOfLE (hWV'.trans i₁.le)).op =
      S.X₃.presheaf.map i₁.op ≫ S.X₃.presheaf.map (homOfLE hWV').op by
        rw [← Functor.map_comp]; rfl, ConcreteCategory.comp_apply, e, map_zero])
  refine ⟨S.X₁.presheaf.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor Ab x).map S.f.mapPresheaf _ = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change S.X₂.presheaf.germ W x hxW (S.f.app W t) = _
  rw [show S.f.app W t = _ from ht, TopCat.Presheaf.germ_res_apply]

/-- **Exactness from sections over small opens**, for homological complexes. -/
theorem exactAt_of_exactAt_sectionsAb {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (i : ι)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      (((sectionsAb W).mapHomologicalComplex c).obj K).ExactAt i) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_exact_sectionsAb _ fun x V hxV ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hxV
  exact ⟨W, hxW, hWV, (HomologicalComplex.exactAt_iff _ _).mp hW⟩

/-- **Quasi-isomorphisms from sections**, for complexes indexed by `ℤ`. -/
theorem quasiIso_of_quasiIso_sectionsAb {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      QuasiIso (((sectionsAb W).mapHomologicalComplex _).map φ)) : QuasiIso φ := by
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  intro n
  refine exactAt_of_exactAt_sectionsAb _ n fun x V hx ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hx
  refine ⟨W, hxW, hWV, ?_⟩
  exact ((CochainComplex.mappingCone.quasiIso_iff_acyclic _).1 hW n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ (sectionsAb W)).symm

/-- **Quasi-isomorphisms from sections**, for complexes indexed by `ℕ`. -/
theorem quasiIso_of_quasiIso_sectionsAb_nat {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      QuasiIso (((sectionsAb W).mapHomologicalComplex _).map φ)) : QuasiIso φ := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff φ ComplexShape.embeddingUpNat]
  refine quasiIso_of_quasiIso_sectionsAb _ fun x V hx ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hx
  refine ⟨W, hxW, hWV, ?_⟩
  have hsq : ((sectionsAb W).mapHomologicalComplex _).map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat (sectionsAb W)).hom =
      (K.mapExtendIso ComplexShape.embeddingUpNat (sectionsAb W)).hom ≫
        HomologicalComplex.extendMap (((sectionsAb W).mapHomologicalComplex _).map φ)
          ComplexShape.embeddingUpNat := by
    ext i : 1
    exact HomologicalComplex.mapExtensIso_hom_f_naturality φ _ (sectionsAb W) i
  rw [← quasiIso_iff_comp_right _ (L.mapExtendIso ComplexShape.embeddingUpNat (sectionsAb W)).hom,
    hsq, quasiIso_iff_comp_left, HomologicalComplex.quasiIso_extendMap_iff]
  exact hW


end AlgebraicGeometry.Scheme.Modules
