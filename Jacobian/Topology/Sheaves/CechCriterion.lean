import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.EpiMono
import Jacobian.Topology.Sheaves.Cech

/-!
# Vanishing of Ext cohomology from exactness of Čech complexes on a basis.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe coefficientUniverse indexUniverse

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {scheme : TopCat.{coefficientUniverse}}
  {sequence : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}

/-- The composite of the two maps of a short complex of abelian sheaves vanishes on sections. -/
lemma app_g_app_f (smallerOpen : (Opens scheme)ᵒᵖ) (element : sequence.X₁.obj.obj smallerOpen) :
    sequence.g.hom.app smallerOpen (sequence.f.hom.app smallerOpen element) = 0 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congr_arg (fun coefficientMap ↦ coefficientMap.hom) sequence.zero) smallerOpen) element

/-- In a short exact sequence of abelian sheaves, the first map is injective on sections. -/
lemma injective_app_f (hS : sequence.ShortExact) (smallerOpen : (Opens scheme)ᵒᵖ) :
    Function.Injective (sequence.f.hom.app smallerOpen) := by
  have := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective _).1
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj smallerOpen).map_mono sequence.f)

/-- A short exact sequence of abelian sheaves is left exact on sections. -/
lemma exists_app_f_eq (hS : sequence.ShortExact) (smallerOpen : (Opens scheme)ᵒᵖ) (element : sequence.X₂.obj.obj smallerOpen)
    (hx : sequence.g.hom.app smallerOpen element = 0) : ∃ otherElement, sequence.f.hom.app smallerOpen otherElement = element := by
  have := hS.mono_f
  exact (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj smallerOpen) inferInstance inferInstance) element hx

/-- In a short exact sequence of abelian sheaves, a section of the third sheaf over `V`
lifts locally around every point of `V`. -/
lemma exists_app_g_eq_map (hS : sequence.ShortExact) (openSubset : Opens scheme) (sectionValue : sequence.X₃.obj.obj (op openSubset)) (element : scheme)
    (hx : element ∈ openSubset) : ∃ (smallerOpen : Opens scheme) (compatibility : smallerOpen ≤ openSubset) (liftedSection : sequence.X₂.obj.obj (op smallerOpen)),
      sequence.g.hom.app _ liftedSection = sequence.X₃.obj.map (homOfLE compatibility).op sectionValue ∧ element ∈ smallerOpen := by
  have := hS.epi_g
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology scheme) sequence.g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{coefficientUniverse} sequence.g).2 this
  obtain ⟨smallerOpen, morphism, hf, hxW⟩ :=
    (Opens.mem_grothendieckTopology scheme).1 (Presheaf.imageSieve_mem _ sequence.g.hom sectionValue) element hx
  obtain ⟨liftedSection, ht⟩ := hf
  exact ⟨smallerOpen, morphism.le, liftedSection, ht, hxW⟩

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {scheme : TopCat.{coefficientUniverse}} {indexType : Type indexUniverse} (cover : indexType → Opens scheme)

/-- `TopCat.Presheaf.cechComplex_map_f_apply`, for elements of the objects of the complex. -/
lemma cechComplex_map_f_apply' {presheaf targetPresheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}} (coefficientMap : presheaf ⟶ targetPresheaf) (degree : ℕ)
    (cochain : ((cechComplex cover).obj presheaf).X degree) (otherElement : Fin (degree + 1) → indexType) :
    ((cechComplex cover).map coefficientMap).f degree cochain otherElement = coefficientMap.app _ (cochain otherElement) :=
  cechComplex_map_f_apply cover coefficientMap degree cochain otherElement

/-- The zero Čech cochain vanishes termwise. -/
lemma cechComplex_zero_apply (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) (degree : ℕ)
    (otherElement : Fin (degree + 1) → indexType) : (0 : ((cechComplex cover).obj presheaf).X degree) otherElement = 0 :=
  rfl

/-- `TopCat.Presheaf.exactAt_cechComplex_iff`, for elements of the objects of the complex. -/
lemma exactAt_cechComplex_iff' (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) (cohomologyDegree : ℕ) :
    ((cechComplex cover).obj presheaf).ExactAt (cohomologyDegree + 1) ↔
      ∀ cochain : ((cechComplex cover).obj presheaf).X (cohomologyDegree + 1), ((cechComplex cover).obj presheaf).d (cohomologyDegree + 1) (cohomologyDegree + 2) cochain = 0 →
        ∃ primitive : ((cechComplex cover).obj presheaf).X cohomologyDegree, ((cechComplex cover).obj presheaf).d cohomologyDegree (cohomologyDegree + 1) primitive = cochain :=
  exactAt_cechComplex_iff cover presheaf cohomologyDegree

/-- A morphism of presheaves commutes with the Čech differentials. -/
lemma cechComplex_map_f_d_apply {presheaf targetPresheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}} (coefficientMap : presheaf ⟶ targetPresheaf) (degree : ℕ)
    (cochain : ((cechComplex cover).obj presheaf).X degree) :
    ((cechComplex cover).map coefficientMap).f (degree + 1) (((cechComplex cover).obj presheaf).d degree (degree + 1) cochain) =
      ((cechComplex cover).obj targetPresheaf).d degree (degree + 1) (((cechComplex cover).map coefficientMap).f degree cochain) :=
  (ConcreteCategory.congr_hom (((cechComplex cover).map coefficientMap).comm degree (degree + 1)) cochain).symm

/-- The composite of two Čech differentials vanishes. -/
lemma cechComplex_d_d_apply (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) (degree : ℕ)
    (cochain : ((cechComplex cover).obj presheaf).X degree) :
    ((cechComplex cover).obj presheaf).d (degree + 1) (degree + 2) (((cechComplex cover).obj presheaf).d degree (degree + 1) cochain) = 0 :=
  ConcreteCategory.congr_hom (((cechComplex cover).obj presheaf).d_comp_d degree (degree + 1) (degree + 2)) cochain

/-- A sectionwise injective morphism of presheaves induces injections on Čech cochains. -/
lemma cechComplex_map_f_injective {presheaf targetPresheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}} (morphism : presheaf ⟶ targetPresheaf)
    (hf : ∀ smallerOpen, Function.Injective (morphism.app smallerOpen)) (degree : ℕ) :
    Function.Injective (((cechComplex cover).map morphism).f degree) := fun scalar primitive compatibility ↦ by
  funext otherElement
  exact hf _ (by simpa only [cechComplex_map_f_apply'] using congr_fun compatibility otherElement)

/-- If `P₁ → P₂ → P₃` is sectionwise exact at `P₂`, then so are the Čech cochains. -/
lemma exists_cechComplex_map_f_eq {P₁ P₂ P₃ : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}}
    (morphism : P₁ ⟶ P₂) (sectionFamily : P₂ ⟶ P₃) (hfg : ∀ smallerOpen element, sectionFamily.app smallerOpen element = 0 → ∃ otherElement, morphism.app smallerOpen otherElement = element) (degree : ℕ)
    (scalar : ((cechComplex cover).obj P₂).X degree) (ha : ((cechComplex cover).map sectionFamily).f degree scalar = 0) :
    ∃ isomorphism, ((cechComplex cover).map morphism).f degree isomorphism = scalar := by
  have (otherElement : Fin (degree + 1) → indexType) := hfg _ (scalar otherElement) (by
    simpa only [cechComplex_map_f_apply', cechComplex_zero_apply] using congr_fun ha otherElement)
  choose isomorphism he using this
  exact ⟨isomorphism, funext fun otherElement ↦ (cechComplex_map_f_apply cover morphism degree isomorphism otherElement).trans (he otherElement)⟩

/-- If the composite `P₁ → P₂ → P₃` vanishes sectionwise, then it vanishes on Čech cochains. -/
lemma cechComplex_map_f_map_f_eq_zero {P₁ P₂ P₃ : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}}
    (morphism : P₁ ⟶ P₂) (sectionFamily : P₂ ⟶ P₃) (hfg : ∀ smallerOpen element, sectionFamily.app smallerOpen (morphism.app smallerOpen element) = 0) (degree : ℕ)
    (primitive : ((cechComplex cover).obj P₁).X degree) :
    ((cechComplex cover).map sectionFamily).f degree (((cechComplex cover).map morphism).f degree primitive) = 0 := by
  funext otherElement
  rw [cechComplex_map_f_apply', cechComplex_map_f_apply', cechComplex_zero_apply]
  exact hfg _ _

/-- Let `P₁ → P₂ → P₃` be morphisms of presheaves which are sectionwise left exact, and such
that `P₂ → P₃` is surjective on the sections over the finite intersections of the family `U`.
If the Čech complexes of `P₁` and `P₂` are exact in degrees `q + 2` and `q + 1`, then the Čech
complex of `P₃` is exact in degree `q + 1`. -/
theorem exactAt_cechComplex_of_sectionwise {P₁ P₂ P₃ : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}}
    (morphism : P₁ ⟶ P₂) (sectionFamily : P₂ ⟶ P₃) (hfg : ∀ smallerOpen element, sectionFamily.app smallerOpen (morphism.app smallerOpen element) = 0)
    (hf : ∀ smallerOpen, Function.Injective (morphism.app smallerOpen))
    (hfg' : ∀ smallerOpen element, sectionFamily.app smallerOpen element = 0 → ∃ otherElement, morphism.app smallerOpen otherElement = element)
    (hg : ∀ (degree : ℕ) (otherElement : Fin (degree + 1) → indexType), Function.Surjective (sectionFamily.app (op (⨅ position, cover (otherElement position)))))
    (cohomologyDegree : ℕ) (h₁ : ((cechComplex cover).obj P₁).ExactAt (cohomologyDegree + 2))
    (h₂ : ((cechComplex cover).obj P₂).ExactAt (cohomologyDegree + 1)) :
    ((cechComplex cover).obj P₃).ExactAt (cohomologyDegree + 1) := by
  have hinj := cechComplex_map_f_injective cover morphism hf
  have hker := exists_cechComplex_map_f_eq cover morphism sectionFamily hfg'
  have hzero := cechComplex_map_f_map_f_eq_zero cover morphism sectionFamily hfg
  rw [exactAt_cechComplex_iff'] at h₁ h₂ ⊢
  intro cochain hc
  obtain ⟨scalar, hac⟩ : ∃ scalar : ((cechComplex cover).obj P₂).X (cohomologyDegree + 1),
      ((cechComplex cover).map sectionFamily).f (cohomologyDegree + 1) scalar = cochain := by
    choose scalar ha using fun otherElement ↦ hg (cohomologyDegree + 1) otherElement (cochain otherElement)
    exact ⟨scalar, funext fun otherElement ↦ (cechComplex_map_f_apply cover sectionFamily _ scalar otherElement).trans (ha otherElement)⟩
  obtain ⟨isomorphism, he⟩ := hker _ (((cechComplex cover).obj P₂).d (cohomologyDegree + 1) (cohomologyDegree + 2) scalar) (by
    rw [cechComplex_map_f_d_apply, hac, hc])
  obtain ⟨primitive, hb⟩ := h₁ isomorphism (hinj _ (by
    rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  obtain ⟨scalar', ha'⟩ := h₂ (scalar - ((cechComplex cover).map morphism).f (cohomologyDegree + 1) primitive) (by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self])
  refine ⟨((cechComplex cover).map sectionFamily).f cohomologyDegree scalar', ?_⟩
  rw [← cechComplex_map_f_d_apply, ha', map_sub, hzero, sub_zero, hac]

/-- Subtraction of Čech cochains is termwise. -/
lemma cechComplex_sub_apply (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) (degree : ℕ)
    (scalar primitive : ((cechComplex cover).obj presheaf).X degree) (otherElement : Fin (degree + 1) → indexType) : (scalar - primitive) otherElement = scalar otherElement - primitive otherElement :=
  rfl

/-- The restrictions of the members of a family of sections with equal indices agree. -/
lemma map_homOfLE_apply_of_eq (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) {indexType : Type*}
    (openSubset : indexType → Opens scheme) (liftedSection : ∀ thirdElement, presheaf.obj (op (openSubset thirdElement))) {thirdElement thirdElement' : indexType} (compatibility : thirdElement = thirdElement') {smallerOpen : Opens scheme}
    (h₁ : smallerOpen ≤ openSubset thirdElement) (h₂ : smallerOpen ≤ openSubset thirdElement') :
    presheaf.map (homOfLE h₁).op (liftedSection thirdElement) = presheaf.map (homOfLE h₂).op (liftedSection thirdElement') := by
  subst compatibility
  rfl

/-- The Čech differential of the restrictions of a single section vanishes. -/
lemma cechComplex_d_zero_restrict (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse}) {openSubset : Opens scheme}
    (sectionValue : presheaf.obj (op openSubset)) (compatibility : ∀ thirdElement : Fin 1 → indexType, ⨅ position, cover (thirdElement position) ≤ openSubset) :
    ((cechComplex cover).obj presheaf).d 0 1
      (fun thirdElement ↦ presheaf.map (homOfLE (compatibility thirdElement)).op sectionValue : ((cechComplex cover).obj presheaf).X 0) = 0 := by
  funext otherElement
  refine (cechComplex_d_apply cover presheaf 0 _ otherElement).trans ?_
  simp [Fin.sum_univ_two, map_homOfLE_map_homOfLE_apply, cechComplex_zero_apply]

/-- A Čech `0`-cocycle is compatible: its members agree on the overlaps. -/
lemma map_inf_eq_of_cechComplex_d_zero (presheaf : (Opens scheme)ᵒᵖ ⥤ AddCommGrpCat.{coefficientUniverse})
    (cochain : ((cechComplex cover).obj presheaf).X 0) (hc : ((cechComplex cover).obj presheaf).d 0 1 cochain = 0)
    (thirdElement thirdElement' : Fin 1 → indexType) :
    presheaf.map (homOfLE (inf_le_left : (⨅ position, cover (thirdElement position)) ⊓ ⨅ position, cover (thirdElement' position) ≤ _)).op (cochain thirdElement) =
      presheaf.map (homOfLE (inf_le_right : (⨅ position, cover (thirdElement position)) ⊓ ⨅ position, cover (thirdElement' position) ≤ _)).op (cochain thirdElement') := by
  have hle : (⨅ position, cover (thirdElement position)) ⊓ ⨅ position, cover (thirdElement' position) ≤ ⨅ position, cover (![thirdElement 0, thirdElement' 0] position) := by
    refine le_iInf fun position ↦ ?_
    fin_cases position
    · exact inf_le_left.trans (iInf_le _ 0)
    · exact inf_le_right.trans (iInf_le _ 0)
  have compatibility := congr_arg (presheaf.map (homOfLE hle).op) (congr_fun hc ![thirdElement 0, thirdElement' 0])
  rw [cechComplex_zero_apply, map_zero] at compatibility
  replace compatibility := (congr_arg (presheaf.map (homOfLE hle).op) (cechComplex_d_apply cover presheaf 0 cochain _)).symm.trans compatibility
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_zsmul, add_zero,
    map_homOfLE_map_homOfLE_apply] at compatibility
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, Fin.val_zero,
    zero_add, pow_one, neg_smul, one_smul] at compatibility
  rw [← sub_eq_add_neg, sub_eq_zero] at compatibility
  have h₀ : ![thirdElement 0, thirdElement' 0] ∘ Fin.succ = thirdElement' := by
    funext position
    fin_cases position
    rfl
  have h₁ : ![thirdElement 0, thirdElement' 0] ∘ Fin.succAbove 1 = thirdElement := by
    funext position
    fin_cases position
    rfl
  exact (map_homOfLE_apply_of_eq presheaf (fun thirdElement : Fin 1 → indexType ↦ ⨅ position, cover (thirdElement position)) cochain h₁.symm _ _).trans
    (compatibility.symm.trans (map_homOfLE_apply_of_eq presheaf (fun thirdElement : Fin 1 → indexType ↦ ⨅ position, cover (thirdElement position)) cochain h₀ _ _))

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves and `V` an open subset
such that every open covering of `V` is refined by a finite family `U` covering `V` on which the
first Čech cohomology of `F` vanishes. Then `I(V) → Q(V)` is surjective. -/
theorem surjective_app_of_exactAt_cechComplex_one
    {sequence : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) {openSubset : Opens scheme}
    (hV : ∀ smallerOpen : openSubset → Opens scheme, (∀ element, element.1 ∈ smallerOpen element) → ∃ (size : ℕ) (cover : Fin size → Opens scheme),
      iSup cover = openSubset ∧ (∀ index, ∃ element, cover index ≤ smallerOpen element) ∧ ((cechComplex cover).obj sequence.X₁.obj).ExactAt 1) :
    Function.Surjective (sequence.g.hom.app (op openSubset)) := by
  intro sectionValue
  choose smallerOpen hWV liftedSection ht hxW using TopCat.Sheaf.exists_app_g_eq_map hS openSubset sectionValue
  obtain ⟨otherDegree, cover, hUV, hUW, hU⟩ := hV (fun element ↦ smallerOpen element.1 element.2) (fun element ↦ hxW element.1 element.2)
  choose indexType hι using hUW
  have hW (thirdElement : Fin 1 → Fin otherDegree) : ⨅ position, cover (thirdElement position) ≤ smallerOpen (indexType (thirdElement 0)).1 (indexType (thirdElement 0)).2 :=
    (iInf_le _ 0).trans (hι _)
  have hV' (thirdElement : Fin 1 → Fin otherDegree) : ⨅ position, cover (thirdElement position) ≤ openSubset := (hW thirdElement).trans (hWV _ _)
  let scalar : ((cechComplex cover).obj sequence.X₂.obj).X 0 := fun thirdElement ↦
    sequence.X₂.obj.map (homOfLE (hW thirdElement)).op (liftedSection _ _)
  have ha : ((cechComplex cover).map sequence.g.hom).f 0 scalar =
      fun thirdElement ↦ sequence.X₃.obj.map (homOfLE (hV' thirdElement)).op sectionValue := by
    funext thirdElement
    rw [cechComplex_map_f_apply', NatTrans.naturality_apply, ht, map_homOfLE_map_homOfLE_apply]
  obtain ⟨isomorphism, he⟩ := exists_cechComplex_map_f_eq cover sequence.f.hom sequence.g.hom
    (TopCat.Sheaf.exists_app_f_eq hS) _ (((cechComplex cover).obj sequence.X₂.obj).d 0 1 scalar) (by
      rw [cechComplex_map_f_d_apply, ha, cechComplex_d_zero_restrict])
  obtain ⟨primitive, hb⟩ := (exactAt_cechComplex_iff' cover _ 0).1 hU isomorphism
    (cechComplex_map_f_injective cover _ (TopCat.Sheaf.injective_app_f hS) _ (by
      rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  have hda : ((cechComplex cover).obj sequence.X₂.obj).d 0 1
      (scalar - ((cechComplex cover).map sequence.f.hom).f 0 primitive) = 0 := by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self]
  have hcov : openSubset ≤ iSup fun thirdElement : Fin 1 → Fin otherDegree ↦ ⨅ position, cover (thirdElement position) := by
    rw [← hUV]
    exact iSup_le fun index ↦ (le_iInf fun _ ↦ le_rfl).trans
      (le_iSup (fun thirdElement : Fin 1 → Fin otherDegree ↦ ⨅ position, cover (thirdElement position)) fun _ ↦ index)
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' sequence.X₂
    (fun thirdElement : Fin 1 → Fin otherDegree ↦ ⨅ position, cover (thirdElement position)) openSubset (fun thirdElement ↦ homOfLE (hV' thirdElement)) hcov _
    (map_inf_eq_of_cechComplex_d_zero cover _ _ hda)
  refine ⟨σ, TopCat.Sheaf.eq_of_locally_eq' sequence.X₃ (fun thirdElement : Fin 1 → Fin otherDegree ↦ ⨅ position, cover (thirdElement position)) openSubset
    (fun thirdElement ↦ homOfLE (hV' thirdElement)) hcov _ _ fun thirdElement ↦ ?_⟩
  rw [← NatTrans.naturality_apply, hσ, cechComplex_sub_apply, map_sub, cechComplex_map_f_apply',
    TopCat.Sheaf.app_g_app_f, sub_zero, ← cechComplex_map_f_apply' cover sequence.g.hom]
  exact congr_fun ha thirdElement

end TopCat.Presheaf

namespace TopCat.Sheaf

open Presheaf Abelian

variable {scheme : TopCat.{coefficientUniverse}}

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves with `I` injective. If
the connecting map `H^q(Q) → H^{q + 1}(F)` vanishes, then `H^{q + 1}(F) = 0`. -/
lemma subsingleton_H_succ_of_comp_extClass
    {sequence : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) [Injective sequence.X₂] (cohomologyDegree : ℕ)
    (compatibility : ∀ otherElement : CategoryTheory.Sheaf.H sequence.X₃ cohomologyDegree, otherElement.comp hS.extClass rfl = 0) :
    Subsingleton (CategoryTheory.Sheaf.H sequence.X₁ (cohomologyDegree + 1)) := by
  refine subsingleton_of_forall_eq 0 fun element ↦ ?_
  obtain ⟨otherElement, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS element (Subsingleton.elim _ _) rfl
  exact compatibility otherElement

/-- If `I(X) → Q(X)` is surjective, then the connecting map `H^0(Q) → H^1(F)` vanishes. -/
lemma comp_extClass_eq_zero_of_surjective
    {sequence : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) (compatibility : Function.Surjective (sequence.g.hom.app (op ⊤)))
    (otherElement : CategoryTheory.Sheaf.H sequence.X₃ 0) : otherElement.comp hS.extClass rfl = 0 := by
  obtain ⟨liftedSection, ht⟩ := compatibility (CategoryTheory.Sheaf.H.equiv₀ sequence.X₃ isTerminalTop otherElement)
  obtain rfl : otherElement = CategoryTheory.Sheaf.H.map sequence.g 0
      ((CategoryTheory.Sheaf.H.equiv₀ sequence.X₂ isTerminalTop).symm liftedSection) := by
    rw [CategoryTheory.Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  rw [CategoryTheory.Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
    Ext.comp_zero]

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves. If every open covering
of a member `V` of `B` is refined by a finite family covering `V` on which the first Čech
cohomology of `F` vanishes, then `I(V) → Q(V)` is surjective for every `V` in `B`. -/
lemma surjective_app_of_exactAt_cechComplex
    {sequence : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) (basis : Opens scheme → Prop) (𝒞 : ∀ {size : ℕ}, (Fin size → Opens scheme) → Prop)
    (hcov : ∀ openSubset, basis openSubset → ∀ smallerOpen : openSubset → Opens scheme, (∀ element, element.1 ∈ smallerOpen element) → ∃ (size : ℕ) (cover : Fin size → Opens scheme),
      𝒞 cover ∧ iSup cover = openSubset ∧ ∀ index, ∃ element, cover index ≤ smallerOpen element)
    (hF : ∀ {size : ℕ} (cover : Fin size → Opens scheme), 𝒞 cover → ((cechComplex cover).obj sequence.X₁.obj).ExactAt 1)
    (openSubset : Opens scheme) (hV : basis openSubset) : Function.Surjective (sequence.g.hom.app (op openSubset)) :=
  surjective_app_of_exactAt_cechComplex_one hS fun smallerOpen hW ↦ by
    obtain ⟨size, cover, hU, hUV, hUW⟩ := hcov openSubset hV smallerOpen hW
    exact ⟨size, cover, hUV, hUW, hF cover hU⟩

/-- **The Čech criterion for the vanishing of cohomology.** Let `B` be a class of open subsets of
`X` containing `X` and `𝒞` a class of finite families of open subsets such that the finite
intersections of the members of a family in `𝒞` lie in `B`, and such that every open covering of
a member `V` of `B` is refined by a family in `𝒞` covering `V`. If the Čech complexes of the
abelian sheaf `F` on the families in `𝒞` are exact in positive degrees, then `H^q(X, F) = 0` for
`q > 0`. -/
@[stacks 01EV]
theorem subsingleton_H_succ_of_exactAt_cechComplex
    (sheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})
    (basis : Opens scheme → Prop) (𝒞 : ∀ {size : ℕ}, (Fin size → Opens scheme) → Prop) (hB : basis ⊤)
    (h𝒞 : ∀ {size : ℕ} (cover : Fin size → Opens scheme), 𝒞 cover → ∀ (degree : ℕ) (otherElement : Fin (degree + 1) → Fin size),
      basis (⨅ position, cover (otherElement position)))
    (hcov : ∀ openSubset, basis openSubset → ∀ smallerOpen : openSubset → Opens scheme, (∀ element, element.1 ∈ smallerOpen element) → ∃ (size : ℕ) (cover : Fin size → Opens scheme),
      𝒞 cover ∧ iSup cover = openSubset ∧ ∀ index, ∃ element, cover index ≤ smallerOpen element)
    (hF : ∀ {size : ℕ} (cover : Fin size → Opens scheme), 𝒞 cover → ∀ cohomologyDegree : ℕ,
      ((cechComplex cover).obj sheaf.obj).ExactAt (cohomologyDegree + 1))
    (cohomologyDegree : ℕ) : Subsingleton (CategoryTheory.Sheaf.H sheaf (cohomologyDegree + 1)) := by
  induction cohomologyDegree generalizing sheaf with
  | zero =>
    let sequence := ShortComplex.mk (Injective.ι sheaf) (cokernel.π (Injective.ι sheaf)) (cokernel.condition _)
    have hS : sequence.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    exact subsingleton_H_succ_of_comp_extClass hS 0 (comp_extClass_eq_zero_of_surjective hS
      (surjective_app_of_exactAt_cechComplex hS basis 𝒞 hcov (fun cover hU ↦ hF cover hU 0) ⊤ hB))
  | succ cohomologyDegree ih =>
    let sequence := ShortComplex.mk (Injective.ι sheaf) (cokernel.π (Injective.ι sheaf)) (cokernel.condition _)
    have hS : sequence.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hsurj := surjective_app_of_exactAt_cechComplex hS basis 𝒞 hcov fun cover hU ↦ hF cover hU 0
    have := ih sequence.X₃ fun cover hU cohomologyDegree ↦ exactAt_cechComplex_of_sectionwise cover sequence.f.hom sequence.g.hom
      app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun degree otherElement ↦ hsurj _ (h𝒞 cover hU degree otherElement)) cohomologyDegree (hF cover hU (cohomologyDegree + 1))
      (exactAt_cechComplex_of_injective cover sequence.X₂ cohomologyDegree)
    exact subsingleton_H_succ_of_comp_extClass hS (cohomologyDegree + 1) fun otherElement ↦ by
      rw [Subsingleton.elim otherElement 0, Ext.zero_comp]

end TopCat.Sheaf
