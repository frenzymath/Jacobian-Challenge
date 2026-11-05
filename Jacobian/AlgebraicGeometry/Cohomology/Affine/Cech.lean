import Jacobian.Topology.Sheaves.CechCriterion
import Jacobian.AlgebraicGeometry.Modules.Localization
import Jacobian.AlgebraicGeometry.BasicOpen

/-!
# Exactness of the standard affine Čech complex of a quasi-coherent module sheaf.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe coefficientUniverse
open CategoryTheory Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme : Scheme.{coefficientUniverse}}
section CechCochain

open TopCat.Presheaf

variable {size : ℕ}

/-- A nonempty finite intersection of members of a family contained in `V` is contained in `V`. -/
lemma iInf_le_of_forall_le {degree : ℕ} (cover : Fin size → scheme.Opens) {openSubset : scheme.Opens} (hU : ∀ index, cover index ≤ openSubset)
    (otherElement : Fin (degree + 1) → Fin size) : ⨅ position, cover (otherElement position) ≤ openSubset :=
  (iInf_le _ 0).trans (hU _)

/-- The action of `Γ(X, V)` on the Čech cochains of a family of opens contained in `V`. -/
noncomputable def cechCochainSMul (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens} (cover : Fin size → scheme.Opens)
    (hU : ∀ index, cover index ≤ openSubset) (degree : ℕ) : Γ(scheme, openSubset) →+* AddMonoid.End
    (TopCat.Presheaf.CechCochain cover moduleSheaf.presheaf degree) where
  toFun scalar :=
    { toFun cochain otherElement := scheme.presheaf.map (homOfLE (iInf_le_of_forall_le cover hU otherElement)).op scalar • cochain otherElement
      map_zero' := funext fun _ ↦ smul_zero _
      map_add' _ _ := funext fun _ ↦ smul_add _ _ _ }
  map_one' := AddMonoidHom.ext fun cochain ↦ funext fun otherElement ↦ by
    simp only [map_one, one_smul]
    rfl
  map_mul' scalar primitive := AddMonoidHom.ext fun cochain ↦ funext fun otherElement ↦ by
    simp only [map_mul, mul_smul]
    rfl
  map_zero' := AddMonoidHom.ext fun cochain ↦ funext fun otherElement ↦ by
    simp only [map_zero, zero_smul]
    rfl
  map_add' scalar primitive := AddMonoidHom.ext fun cochain ↦ funext fun otherElement ↦ by
    simp only [map_add, add_smul]
    rfl

@[simp]
lemma cechCochainSMul_apply (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens} (cover : Fin size → scheme.Opens)
    (hU : ∀ index, cover index ≤ openSubset) (degree : ℕ) (scalar : Γ(scheme, openSubset)) (cochain : CechCochain cover moduleSheaf.presheaf degree)
    (otherElement : Fin (degree + 1) → Fin size) :
    cechCochainSMul moduleSheaf cover hU degree scalar cochain otherElement =
      scheme.presheaf.map (homOfLE (iInf_le_of_forall_le cover hU otherElement)).op scalar • cochain otherElement :=
  rfl

/-- The action of `Γ(X, V)` on Čech cochains commutes with the Čech differential. -/
lemma cechComplex_d_cechCochainSMul (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens} (cover : Fin size → scheme.Opens)
    (hU : ∀ index, cover index ≤ openSubset) (degree : ℕ) (scalar : Γ(scheme, openSubset)) (primitive : CechCochain cover moduleSheaf.presheaf degree) :
    ((cechComplex cover).obj moduleSheaf.presheaf).d degree (degree + 1) (cechCochainSMul moduleSheaf cover hU degree scalar primitive) =
      cechCochainSMul moduleSheaf cover hU (degree + 1) scalar (((cechComplex cover).obj moduleSheaf.presheaf).d degree (degree + 1) primitive) := by
  funext (otherElement : Fin (degree + 1 + 1) → Fin size)
  refine Eq.trans ?_ (cechCochainSMul_apply moduleSheaf cover hU (degree + 1) scalar _ otherElement).symm
  simp only [cechComplex_d_apply, cechCochainSMul_apply, Finset.smul_sum,
    Scheme.Modules.map_smul, Scheme.presheaf_map_homOfLE_map_homOfLE_apply]
  exact Finset.sum_congr rfl fun index _ ↦ smul_comm _ _ _

/-- The action of `Γ(X, V)` on Čech cochains commutes with restriction to a smaller family. -/
lemma cechCochainRestrict_cechCochainSMul (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens}
    {cover cover' : Fin size → scheme.Opens} (hU : ∀ index, cover index ≤ openSubset) (compatibility : ∀ index, cover' index ≤ cover index) (degree : ℕ) (scalar : Γ(scheme, openSubset))
    (cochain : CechCochain cover moduleSheaf.presheaf degree) :
    cechCochainRestrict moduleSheaf.presheaf compatibility degree (cechCochainSMul moduleSheaf cover hU degree scalar cochain) =
      cechCochainSMul moduleSheaf cover' (fun index ↦ (compatibility index).trans (hU index)) degree scalar
        (cechCochainRestrict moduleSheaf.presheaf compatibility degree cochain) := by
  funext otherElement
  rw [cechCochainRestrict_apply, cechCochainSMul_apply, Scheme.Modules.map_smul,
    Scheme.presheaf_map_homOfLE_map_homOfLE_apply, cechCochainSMul_apply,
    cechCochainRestrict_apply]

/-- Let `V` be affine, `f : Fin n → Γ(X, V)` and `c` a Čech cocycle of the family of basic
opens `D(f i)` with values in a quasi-coherent module. Then for every `j` some power of `f j`
times `c` is a coboundary: after restricting to `D(f j)` the covering contains the whole space,
so the restriction of `c` is a coboundary, and one clears denominators. -/
lemma exists_pow_smul_eq_cechComplex_d (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] {openSubset : scheme.Opens} (hV : IsAffineOpen openSubset)
    (morphism : Fin size → Γ(scheme, openSubset)) (cohomologyDegree : ℕ) (cochain : CechCochain (fun index ↦ scheme.basicOpen (morphism index)) moduleSheaf.presheaf (cohomologyDegree + 1))
    (hc : ((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).d (cohomologyDegree + 1) (cohomologyDegree + 2) cochain = 0)
    (selectedIndex : Fin size) :
    ∃ (exponent : ℕ) (primitive : CechCochain (fun index ↦ scheme.basicOpen (morphism index)) moduleSheaf.presheaf cohomologyDegree),
      ((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).d cohomologyDegree (cohomologyDegree + 1) primitive =
        cechCochainSMul moduleSheaf _ (fun index ↦ scheme.basicOpen_le (morphism index)) (cohomologyDegree + 1) (morphism selectedIndex ^ exponent) cochain := by
  classical
  have hUV (index : Fin size) : scheme.basicOpen (morphism index) ≤ openSubset := scheme.basicOpen_le (morphism index)
  have hU'U (index : Fin size) : scheme.basicOpen (morphism index) ⊓ scheme.basicOpen (morphism selectedIndex) ≤ scheme.basicOpen (morphism index) :=
    inf_le_left
  have hU'V (index : Fin size) : scheme.basicOpen (morphism index) ⊓ scheme.basicOpen (morphism selectedIndex) ≤ openSubset := inf_le_left.trans (hUV index)
  have hI (degree : ℕ) (otherElement : Fin (degree + 1) → Fin size) : IsAffineOpen (⨅ position, scheme.basicOpen (morphism (otherElement position))) := by
    rw [Scheme.iInf_basicOpen_eq_basicOpen_prod]
    exact hV.basicOpen _
  have hO (degree : ℕ) (otherElement : Fin (degree + 1) → Fin size) :
      scheme.basicOpen (scheme.presheaf.map (homOfLE (iInf_le_of_forall_le _ hUV otherElement)).op (morphism selectedIndex)) =
        ⨅ position, (scheme.basicOpen (morphism (otherElement position)) ⊓ scheme.basicOpen (morphism selectedIndex)) := by
    rw [Scheme.basicOpen_res, iInf_inf]
  have hex := exactAt_cechComplex_of_le (fun index ↦ scheme.basicOpen (morphism index) ⊓ scheme.basicOpen (morphism selectedIndex))
    moduleSheaf.presheaf (selectedIndex := selectedIndex) (fun index ↦ le_inf inf_le_right inf_le_right) cohomologyDegree
  rw [exactAt_cechComplex_iff] at hex
  obtain ⟨primitive', hb'⟩ := hex (cechCochainRestrict moduleSheaf.presheaf hU'U (cohomologyDegree + 1) cochain) (by
    rw [cechComplex_d_cechCochainRestrict, hc]
    exact map_zero _)
  have hlift (otherElement : Fin (cohomologyDegree + 1) → Fin size) : ∀ᶠ exponent in Filter.atTop,
      ∃ liftedSection : Γ(moduleSheaf, ⨅ position, scheme.basicOpen (morphism (otherElement position))),
        moduleSheaf.presheaf.map (homOfLE (iInf_mono fun position ↦ hU'U (otherElement position))).op liftedSection =
          cechCochainSMul moduleSheaf _ hU'V cohomologyDegree (morphism selectedIndex ^ exponent) primitive' otherElement := by
    obtain ⟨N₀, liftedSection, ht⟩ := exists_map_eq_pow_smul_of_basicOpen_eq moduleSheaf (hI cohomologyDegree otherElement) _ (hO cohomologyDegree otherElement)
      (iInf_mono fun position ↦ hU'U (otherElement position)) (primitive' otherElement)
    refine Filter.eventually_atTop.2 ⟨N₀, fun exponent hN ↦ ⟨scheme.presheaf.map
      (homOfLE (iInf_le_of_forall_le _ hUV otherElement)).op (morphism selectedIndex) ^ (exponent - N₀) • liftedSection, ?_⟩⟩
    rw [Scheme.Modules.map_smul, ht, map_pow, Scheme.presheaf_map_homOfLE_map_homOfLE_apply,
      ← mul_smul, ← pow_add, Nat.sub_add_cancel hN, cechCochainSMul_apply, map_pow]
  obtain ⟨exponent, hN⟩ := (Filter.eventually_all.2 hlift).exists
  choose sectionValue hs using hN
  have hz : cechCochainRestrict moduleSheaf.presheaf hU'U (cohomologyDegree + 1)
      (cechCochainSMul moduleSheaf _ hUV (cohomologyDegree + 1) (morphism selectedIndex ^ exponent) cochain) = cechCochainRestrict moduleSheaf.presheaf hU'U (cohomologyDegree + 1)
        (((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).d cohomologyDegree (cohomologyDegree + 1) sectionValue) := by
    have hs' : cechCochainRestrict moduleSheaf.presheaf hU'U cohomologyDegree sectionValue = cechCochainSMul moduleSheaf _ hU'V cohomologyDegree (morphism selectedIndex ^ exponent) primitive' :=
      funext hs
    rw [cechCochainRestrict_cechCochainSMul, ← cechComplex_d_cechCochainRestrict, hs',
      cechComplex_d_cechCochainSMul, hb']
  have hkill (otherElement : Fin (cohomologyDegree + 1 + 1) → Fin size) :
      ∀ᶠ killingExponent : ℕ in Filter.atTop,
      scheme.presheaf.map (homOfLE (iInf_le_of_forall_le _ hUV otherElement)).op
          (morphism selectedIndex) ^ killingExponent •
        (cechCochainSMul moduleSheaf _ hUV (cohomologyDegree + 1) (morphism selectedIndex ^ exponent) cochain otherElement -
          ((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).d cohomologyDegree (cohomologyDegree + 1) sectionValue otherElement) = 0 := by
    obtain ⟨M₀, hM₀⟩ := exists_pow_smul_eq_zero_of_basicOpen_eq moduleSheaf (hI (cohomologyDegree + 1) otherElement) _
      (hO (cohomologyDegree + 1) otherElement) (iInf_mono fun position ↦ hU'U (otherElement position))
      (cechCochainSMul moduleSheaf _ hUV (cohomologyDegree + 1) (morphism selectedIndex ^ exponent) cochain otherElement -
        ((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).d cohomologyDegree (cohomologyDegree + 1) sectionValue otherElement) (by
        rw [map_sub, sub_eq_zero]
        exact congrFun hz otherElement)
    refine Filter.eventually_atTop.2 ⟨M₀, fun killingExponent hM ↦ ?_⟩
    rw [← Nat.sub_add_cancel hM, pow_add, mul_smul, hM₀, smul_zero]
  obtain ⟨killingExponent, hM⟩ := (Filter.eventually_all.2 hkill).exists
  refine ⟨killingExponent + exponent, cechCochainSMul moduleSheaf _ hUV cohomologyDegree
    (morphism selectedIndex ^ killingExponent) sectionValue, ?_⟩
  rw [cechComplex_d_cechCochainSMul, pow_add, map_mul, AddMonoid.End.coe_mul,
    Function.comp_apply]
  funext (otherElement : Fin (cohomologyDegree + 1 + 1) → Fin size)
  have hy := hM otherElement
  rw [smul_sub, sub_eq_zero] at hy
  refine (cechCochainSMul_apply moduleSheaf _ hUV (cohomologyDegree + 1) _ _ otherElement).trans
    ((cechCochainSMul_apply moduleSheaf _ hUV (cohomologyDegree + 1) _ _ otherElement).trans ?_).symm
  rw [map_pow]
  exact hy

end CechCochain

open TopCat.Presheaf in
/-- The Čech complex of a quasi-coherent module on a finite standard affine covering
is exact in positive degrees. Localizing at each covering section gives a contraction;
powers of these sections still generate the unit ideal, so the local coboundaries glue. -/
theorem exactAt_cechComplex_basicOpen (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] {openSubset : scheme.Opens} (hV : IsAffineOpen openSubset)
    {size : ℕ} (morphism : Fin size → Γ(scheme, openSubset)) (hf : ⨆ index, scheme.basicOpen (morphism index) = openSubset) (cohomologyDegree : ℕ) :
    ((TopCat.Presheaf.cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).ExactAt (cohomologyDegree + 1) := by
  rw [exactAt_cechComplex_iff]
  intro cochain hc
  let topology : Ideal Γ(scheme, openSubset) :=
    { carrier := {scalar | ∃ primitive : CechCochain (fun index ↦ scheme.basicOpen (morphism index)) moduleSheaf.presheaf cohomologyDegree,
        ((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj moduleSheaf.presheaf).d cohomologyDegree (cohomologyDegree + 1) primitive =
        cechCochainSMul moduleSheaf _ (fun index ↦ scheme.basicOpen_le (morphism index)) (cohomologyDegree + 1) scalar cochain}
      add_mem' := by
        rintro scalar scalar' ⟨primitive, hb⟩ ⟨primitive', hb'⟩
        refine ⟨primitive + primitive', ((map_add _ primitive primitive').trans (congrArg₂ (· + ·) hb hb')).trans ?_⟩
        rw [map_add]
        rfl
      zero_mem' := ⟨0, by
        refine (map_zero _).trans ?_
        rw [map_zero]
        rfl⟩
      smul_mem' := by
        rintro otherScalar scalar ⟨primitive, hb⟩
        refine ⟨cechCochainSMul moduleSheaf _ (fun index ↦ scheme.basicOpen_le (morphism index)) cohomologyDegree otherScalar primitive, ?_⟩
        rw [cechComplex_d_cechCochainSMul, hb, smul_eq_mul, map_mul, AddMonoid.End.coe_mul,
          Function.comp_apply] }
  obtain ⟨primitive, hb⟩ : (1 : Γ(scheme, openSubset)) ∈ topology := by
    rw [← Ideal.eq_top_iff_one, ← Ideal.radical_eq_top, eq_top_iff,
      ← (hV.self_le_iSup_basicOpen_iff (s := Set.range morphism)).1 ?_, Ideal.span_le]
    · rintro _ ⟨selectedIndex, rfl⟩
      exact exists_pow_smul_eq_cechComplex_d moduleSheaf hV morphism cohomologyDegree cochain hc selectedIndex
    · exact hf.ge.trans (iSup_le fun index ↦ le_iSup_of_le ⟨morphism index, index, rfl⟩ le_rfl)
  refine ⟨primitive, ?_⟩
  rw [hb, map_one, AddMonoid.End.coe_one, id_eq]

end AlgebraicGeometry.Scheme.Modules
