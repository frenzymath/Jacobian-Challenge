import Jacobian.RingTheory.Spectrum.Prime.MinimalPrimes
import Jacobian.Topology.GenericPoints
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties

/-!
# Affine covers containing generic points

Finite sets of generic points of a quasi-separated scheme have disjoint affine
neighbourhoods. A quasi-compact quasi-separated scheme with finitely many
irreducible components consequently has a finite affine cover each of whose
members contains every generic point.
-/

noncomputable section

universe u

open TopologicalSpace Topology
open scoped Function

namespace AlgebraicGeometry

variable {scheme : Scheme.{u}}

lemma IsAffineOpen.primeIdealOf_mem_minimalPrimes {opensFamily : scheme.Opens} (hU : IsAffineOpen opensFamily) {point : scheme}
    (hx : point ∈ genericPoints scheme) (hxU : point ∈ opensFamily) :
    (hU.primeIdealOf ⟨point, hxU⟩).asIdeal ∈ minimalPrimes Γ(scheme, opensFamily) := by
  rw [← PrimeSpectrum.mem_genericPoints_iff]
  have hoe : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have witness : hU.fromSpec.base ⁻¹' closure {point} ∈ irreducibleComponents (Spec Γ(scheme, opensFamily)) :=
    preimage_mem_irreducibleComponents hx hoe
      ⟨point, subset_closure rfl, by rw [hU.range_fromSpec]; exact hxU⟩
  rw [hoe.isOpenMap.preimage_closure_eq_closure_preimage hoe.continuous] at witness
  have : hU.fromSpec.base ⁻¹' {point} = {hU.primeIdealOf ⟨point, hxU⟩} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hU.fromSpec_primeIdealOf ⟨point, hxU⟩, fun otherPoint hy ↦ ?_⟩
    exact hoe.injective (hy.trans (hU.fromSpec_primeIdealOf ⟨point, hxU⟩).symm)
  rwa [this] at witness

/-- Let `opensFamily` be an affine open of `scheme` and let `point ∈ opensFamily` be the generic point of an irreducible
component of `scheme`. Any quasi-compact open `excludedOpen ⊆ opensFamily` not containing `point` can be separated from `point`
by a standard open: there is `localSection ∈ Γ(scheme, opensFamily)` with `point ∈ D(localSection)` and `D(localSection) ∩ excludedOpen = ∅`. -/
@[stacks 00EV]
lemma IsAffineOpen.exists_mem_basicOpen_and_disjoint {opensFamily : scheme.Opens} (hU : IsAffineOpen opensFamily) {point : scheme}
    (hx : point ∈ genericPoints scheme) (hxU : point ∈ opensFamily) {excludedOpen : Set scheme} (hWo : IsOpen excludedOpen) (hWc : IsCompact excludedOpen)
    (hWU : excludedOpen ⊆ (opensFamily : Set scheme)) (hxW : point ∉ excludedOpen) :
    ∃ localSection : Γ(scheme, opensFamily), point ∈ scheme.basicOpen localSection ∧ Disjoint (scheme.basicOpen localSection : Set scheme) excludedOpen := by
  have hoe : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have hrange : Set.range hU.fromSpec.base = (opensFamily : Set scheme) := hU.range_fromSpec
  obtain ⟨localSection, hf, hdisj⟩ := PrimeSpectrum.exists_notMem_and_disjoint_basicOpen_of_mem_minimalPrimes
    (hU.primeIdealOf_mem_minimalPrimes hx hxU) (hWo.preimage hU.fromSpec.continuous)
    (hoe.isInducing.isCompact_preimage' hWc (hrange ▸ hWU))
    (by
      change hU.fromSpec.base (hU.primeIdealOf ⟨point, hxU⟩) ∉ excludedOpen
      rw [hU.fromSpec_primeIdealOf]
      exact hxW)
  have hmem (otherPoint : Spec Γ(scheme, opensFamily)) :
      hU.fromSpec.base otherPoint ∈ scheme.basicOpen localSection ↔ otherPoint ∈ PrimeSpectrum.basicOpen localSection :=
    congr(otherPoint ∈ $(hU.fromSpec_preimage_basicOpen localSection)).to_iff
  refine ⟨localSection, ?_, Set.disjoint_left.mpr fun otherPoint hy hyW ↦ ?_⟩
  · have witness := (hmem (hU.primeIdealOf ⟨point, hxU⟩)).mpr hf
    rwa [hU.fromSpec_primeIdealOf ⟨point, hxU⟩] at witness
  · have hyU : otherPoint ∈ Set.range hU.fromSpec.base := by
      rw [hrange]; exact scheme.basicOpen_le localSection hy
    obtain ⟨testPoint, rfl⟩ := hyU
    exact Set.disjoint_left.mp hdisj ((hmem testPoint).mp hy) hyW

/-- **Disjoint affine neighbourhoods of generic points.** Let `scheme` be a quasi-separated scheme
and let `points` be a finite set of generic points of irreducible components of `scheme`. Then there is a
family of pairwise disjoint affine opens `opensFamily point`, for `point ∈ points`, with `point ∈ opensFamily point`. -/
@[stacks 0200 "Step 1 of the proof"]
theorem exists_isAffineOpen_pairwise_disjoint [QuasiSeparatedSpace scheme] {points : Set scheme}
    (hsf : points.Finite) (hs : points ⊆ genericPoints scheme) :
    ∃ opensFamily : scheme → scheme.Opens, (∀ point ∈ points, IsAffineOpen (opensFamily point)) ∧ (∀ point ∈ points, point ∈ opensFamily point) ∧
      points.Pairwise (Disjoint on opensFamily) := by
  classical
  have hV : ∀ point ∈ points, ∃ neighborhoods : scheme.Opens, IsAffineOpen neighborhoods ∧ point ∈ neighborhoods ∧ ∀ otherPoint ∈ points, otherPoint ≠ point → otherPoint ∉ neighborhoods := by
    intro point hx
    have hΩ : IsOpen ((⋃ otherPoint ∈ points \ {point}, closure ({otherPoint} : Set scheme))ᶜ) :=
      (hsf.sdiff.isClosed_biUnion fun otherPoint _ ↦ isClosed_closure).isOpen_compl
    have hxΩ : point ∈ (⟨_, hΩ⟩ : scheme.Opens) := by
      intro hmem
      obtain ⟨otherPoint, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨hys, hyx⟩ := Set.mem_sdiff_singleton.mp hy
      exact genericPoints.notMem_closure_of_ne (hs hx) (hs hys) (Ne.symm hyx) hxy
    obtain ⟨neighborhoods, hVaff, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset hxΩ
    refine ⟨neighborhoods, hVaff, hxV, fun otherPoint hy hyx hyV ↦ hVsub hyV ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨otherPoint, Set.mem_sdiff_singleton.mpr ⟨hy, hyx⟩, subset_closure rfl⟩
  choose! neighborhoods hVaff hVmem hVnot using hV
  have key : ∀ point ∈ points, ∃ opensFamily : scheme.Opens, IsAffineOpen opensFamily ∧ point ∈ opensFamily ∧ opensFamily ≤ neighborhoods point ∧
      ∀ otherPoint ∈ points, otherPoint ≠ point → Disjoint opensFamily (neighborhoods otherPoint) := by
    intro point hx
    set excludedOpen : Set scheme := ⋃ otherPoint ∈ points \ {point}, ((neighborhoods point : Set scheme) ∩ (neighborhoods otherPoint : Set scheme))
    have hWo : IsOpen excludedOpen := isOpen_biUnion fun otherPoint _ ↦ (neighborhoods point).isOpen.inter (neighborhoods otherPoint).isOpen
    have hWc : IsCompact excludedOpen := hsf.sdiff.isCompact_biUnion fun otherPoint hy ↦
      QuasiSeparatedSpace.inter_isCompact _ _ (neighborhoods point).isOpen (hVaff point hx).isCompact
        (neighborhoods otherPoint).isOpen (hVaff otherPoint (Set.mem_sdiff_singleton.mp hy).1).isCompact
    have hWU : excludedOpen ⊆ (neighborhoods point : Set scheme) := Set.iUnion₂_subset fun otherPoint _ ↦ Set.inter_subset_left
    have hxW : point ∉ excludedOpen := by
      intro hmem
      obtain ⟨otherPoint, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨hys, hyx⟩ := Set.mem_sdiff_singleton.mp hy
      exact hVnot otherPoint hys point hx (Ne.symm hyx) hxy.2
    obtain ⟨localSection, hf, hdisj⟩ := (hVaff point hx).exists_mem_basicOpen_and_disjoint (hs hx)
      (hVmem point hx) hWo hWc hWU hxW
    refine ⟨scheme.basicOpen localSection, (hVaff point hx).basicOpen localSection, hf, scheme.basicOpen_le localSection, fun otherPoint hy hyx ↦ ?_⟩
    rw [← Opens.coe_disjoint]
    refine Set.disjoint_left.mpr fun testPoint hz hzy ↦ Set.disjoint_left.mp hdisj hz ?_
    exact Set.mem_iUnion₂.mpr ⟨otherPoint, Set.mem_sdiff_singleton.mpr ⟨hy, hyx⟩,
      ⟨scheme.basicOpen_le localSection hz, hzy⟩⟩
  choose! opensFamily hUaff hUmem hUle hUdisj using key
  exact ⟨opensFamily, hUaff, hUmem, fun point hx otherPoint hy hxy ↦
    (hUdisj point hx otherPoint hy (Ne.symm hxy)).mono_right (hUle otherPoint hy)⟩

/-- A finite set of generic points of irreducible components of a quasi-separated scheme is
contained in an affine open: the disjoint union of the affine opens provided by
`AlgebraicGeometry.exists_isAffineOpen_pairwise_disjoint` is affine. -/
theorem exists_isAffineOpen_of_subset_genericPoints [QuasiSeparatedSpace scheme] {points : Set scheme}
    (hsf : points.Finite) (hs : points ⊆ genericPoints scheme) :
    ∃ opensFamily : scheme.Opens, IsAffineOpen opensFamily ∧ points ⊆ (opensFamily : Set scheme) := by
  obtain ⟨opensFamily, hUaff, hUmem, hUdisj⟩ := exists_isAffineOpen_pairwise_disjoint hsf hs
  refine ⟨⨆ point ∈ points, opensFamily point, IsAffineOpen.biSup_of_disjoint hsf hUaff hUdisj, fun point hx ↦ ?_⟩
  exact Opens.mem_iSup.mpr ⟨point, Opens.mem_iSup.mpr ⟨hx, hUmem point hx⟩⟩

/-- **An affine open containing a point and all generic points.** Let `scheme` be a quasi-separated
scheme, let `points` be a finite set of generic points of irreducible components of `scheme` and let
`point : scheme`. Then there is an affine open of `scheme` containing `point` and all points of `points`. -/
@[stacks 0200 "Step 1 of the proof"]
theorem exists_isAffineOpen_mem_of_subset_genericPoints [QuasiSeparatedSpace scheme] {points : Set scheme}
    (hsf : points.Finite) (hs : points ⊆ genericPoints scheme) (point : scheme) :
    ∃ opensFamily : scheme.Opens, IsAffineOpen opensFamily ∧ point ∈ opensFamily ∧ points ⊆ (opensFamily : Set scheme) := by
  classical
  set remainingPoints : Set scheme := {otherPoint ∈ points | point ∉ closure ({otherPoint} : Set scheme)}
  have htf : remainingPoints.Finite := hsf.subset fun otherPoint hy ↦ hy.1
  have hts : remainingPoints ⊆ genericPoints scheme := fun otherPoint hy ↦ hs hy.1
  have hΩ : IsOpen ((⋃ otherPoint ∈ remainingPoints, closure ({otherPoint} : Set scheme))ᶜ) :=
    (htf.isClosed_biUnion fun otherPoint _ ↦ isClosed_closure).isOpen_compl
  have hxΩ : point ∈ (⟨_, hΩ⟩ : scheme.Opens) := by
    intro hmem
    obtain ⟨otherPoint, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
    exact hy.2 hxy
  obtain ⟨excludedOpen, hWaff, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset hxΩ
  have hWt : ∀ otherPoint ∈ remainingPoints, otherPoint ∉ excludedOpen := fun otherPoint hy hyW ↦
    hWsub hyW (Set.mem_iUnion₂.mpr ⟨otherPoint, hy, subset_closure rfl⟩)
  have hWs : ∀ otherPoint ∈ points, otherPoint ∉ remainingPoints → otherPoint ∈ excludedOpen := by
    intro otherPoint hy hyt
    have hxy : point ∈ closure ({otherPoint} : Set scheme) := by
      by_contra witness
      exact hyt ⟨hy, witness⟩
    exact ((isGenericPoint_closure (x := otherPoint)).mem_open_set_iff excludedOpen.isOpen).mpr ⟨point, hxy, hxW⟩
  obtain ⟨opensFamily, hUaff, hUmem, hUdisj⟩ := exists_isAffineOpen_pairwise_disjoint htf hts
  have key : ∀ otherPoint ∈ remainingPoints, ∃ opensFamily' : scheme.Opens, IsAffineOpen opensFamily' ∧ otherPoint ∈ opensFamily' ∧ opensFamily' ≤ opensFamily otherPoint ∧ Disjoint opensFamily' excludedOpen := by
    intro otherPoint hy
    obtain ⟨localSection, hf, hdisj⟩ := (hUaff otherPoint hy).exists_mem_basicOpen_and_disjoint (hts hy) (hUmem otherPoint hy)
      (excludedOpen.isOpen.inter (opensFamily otherPoint).isOpen)
      (QuasiSeparatedSpace.inter_isCompact _ _ excludedOpen.isOpen hWaff.isCompact (opensFamily otherPoint).isOpen
        (hUaff otherPoint hy).isCompact) Set.inter_subset_right (fun witness ↦ hWt otherPoint hy witness.1)
    refine ⟨scheme.basicOpen localSection, (hUaff otherPoint hy).basicOpen localSection, hf, scheme.basicOpen_le localSection, ?_⟩
    rw [← Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun testPoint hz hzW ↦
      Set.disjoint_left.mp hdisj hz ⟨hzW, scheme.basicOpen_le localSection hz⟩
  choose! opensFamily' hU'aff hU'mem hU'le hU'disj using key
  refine ⟨excludedOpen ⊔ ⨆ otherPoint ∈ remainingPoints, opensFamily' otherPoint, ?_, Opens.mem_sup.mpr (.inl hxW), fun otherPoint hy ↦ ?_⟩
  · refine hWaff.sup_of_disjoint (IsAffineOpen.biSup_of_disjoint htf hU'aff
      fun otherPoint hy testPoint hz hyz ↦ (hUdisj hy hz hyz).mono (hU'le otherPoint hy) (hU'le testPoint hz)) ?_
    simp only [disjoint_iSup_iff]
    exact fun otherPoint hy ↦ (hU'disj otherPoint hy).symm
  · by_cases hyt : otherPoint ∈ remainingPoints
    · exact Opens.mem_sup.mpr (.inr (Opens.mem_iSup.mpr ⟨otherPoint,
        Opens.mem_iSup.mpr ⟨hyt, hU'mem otherPoint hyt⟩⟩))
    · exact Opens.mem_sup.mpr (.inl (hWs otherPoint hy hyt))

/-- **Affine cover through the generic points.** A quasi-compact and quasi-separated scheme with
finitely many irreducible components admits a finite affine open cover each member of which
contains all the generic points of the irreducible components. -/
@[stacks 0200 "Step 1 of the proof"]
theorem exists_isAffineOpen_cover_genericPoints_subset [CompactSpace scheme] [QuasiSeparatedSpace scheme]
    (hX : (irreducibleComponents scheme).Finite) :
    ∃ (exponent : ℕ) (opensFamily : Fin exponent → scheme.Opens), (∀ index, IsAffineOpen (opensFamily index)) ∧
      (∀ index, genericPoints scheme ⊆ (opensFamily index : Set scheme)) ∧ ⨆ index, opensFamily index = ⊤ := by
  classical
  have witness : ∀ point : scheme, ∃ opensFamily : scheme.Opens, IsAffineOpen opensFamily ∧ point ∈ opensFamily ∧ genericPoints scheme ⊆ (opensFamily : Set scheme) :=
    fun point ↦ exists_isAffineOpen_mem_of_subset_genericPoints (genericPoints.finite hX) le_rfl point
  choose opensFamily hUaff hUmem hUsub using witness
  obtain ⟨coverSet, hc⟩ := isCompact_univ.elim_finite_subcover (fun point : scheme ↦ (opensFamily point : Set scheme))
    (fun point ↦ (opensFamily point).isOpen) fun point _ ↦ Set.mem_iUnion.mpr ⟨point, hUmem point⟩
  refine ⟨coverSet.card, fun index ↦ opensFamily (coverSet.equivFin.symm index), fun index ↦ hUaff _, fun index ↦ hUsub _,
    eq_top_iff.mpr fun point _ ↦ ?_⟩
  obtain ⟨otherPoint, hy, hxy⟩ := Set.mem_iUnion₂.mp (hc (Set.mem_univ point))
  exact Opens.mem_iSup.mpr ⟨coverSet.equivFin ⟨otherPoint, hy⟩, by simpa using hxy⟩

end AlgebraicGeometry
