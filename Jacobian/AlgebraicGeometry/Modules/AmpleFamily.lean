import Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import Jacobian.AlgebraicGeometry.Modules.TensorInvertible
import Mathlib.Topology.JacobsonSpace

/-!
# Ample families of sections

An invertible module with finitely many sections whose nonvanishing loci form
an affine open cover is an ample family. On a quasi-compact Jacobson scheme it
suffices to cover the closed points; compactness then gives a finite family.
-/

noncomputable section
universe schemeUniverse
open CategoryTheory MonoidalCategory

lemma TopologicalSpace.Opens.eq_of_forall_isClosed_singleton {scheme : Type*} [TopologicalSpace scheme]
    [JacobsonSpace scheme] {affineOpen parameterSpace : TopologicalSpace.Opens scheme}
    (compatibility : ∀ point : scheme, IsClosed {point} → (point ∈ affineOpen ↔ point ∈ parameterSpace)) : affineOpen = parameterSpace := by
  have key {affineOpen parameterSpace : TopologicalSpace.Opens scheme} (compatibility : ∀ point : scheme, IsClosed {point} → point ∈ affineOpen → point ∈ parameterSpace) :
      affineOpen ≤ parameterSpace := by
    by_contra hUV
    obtain ⟨point, hxU, hxV⟩ := SetLike.not_le_iff_exists.mp hUV
    obtain ⟨targetPoint, ⟨hyU, hyV⟩, hy⟩ := nonempty_inter_closedPoints (Z := (affineOpen : Set scheme) ∩ (parameterSpace : Set scheme)ᶜ)
      ⟨point, hxU, hxV⟩ ⟨affineOpen, (parameterSpace : Set scheme)ᶜ, affineOpen.isOpen, parameterSpace.isOpen.isClosed_compl, rfl⟩
    exact hyV (compatibility targetPoint hy hyU)
  exact le_antisymm (key fun point hx ↦ (compatibility point hx).mp) (key fun point hx ↦ (compatibility point hx).mpr)

namespace AlgebraicGeometry.Scheme

/-- A single invertible module with finitely many affine nonvanishing loci covering the scheme. -/
def HasAmpleFamily (scheme : Scheme.{schemeUniverse}) : Prop :=
  ∃ (lineBundle : scheme.Modules) (_ : SheafOfModules.IsInvertible.{schemeUniverse, schemeUniverse, schemeUniverse} lineBundle) (ι : Type schemeUniverse) (_ : Finite ι)
    (sectionFamily : ι → (𝟙_ scheme.Modules ⟶ lineBundle)),
    (∀ index, IsAffineOpen (Modules.Hom.zeroLocus (sectionFamily index)).support.compl) ∧
      ⨆ index, (Modules.Hom.zeroLocus (sectionFamily index)).support.compl = ⊤

theorem HasAmpleFamily.of_forall_isClosed {scheme : Scheme.{schemeUniverse}} [CompactSpace scheme] [JacobsonSpace scheme]
    (lineBundle : scheme.Modules) [lineBundle.IsInvertible] {indexType : Type schemeUniverse} (sectionFamily : indexType → (𝟙_ scheme.Modules ⟶ lineBundle))
    (hs : ∀ familyIndex, IsAffineOpen (Modules.Hom.zeroLocus (sectionFamily familyIndex)).support.compl)
    (hcov : ∀ point : scheme, IsClosed {point} → ∃ familyIndex, point ∈ (Modules.Hom.zeroLocus (sectionFamily familyIndex)).support.compl) :
    scheme.HasAmpleFamily := by
  have htop : ⨆ familyIndex, (Modules.Hom.zeroLocus (sectionFamily familyIndex)).support.compl = ⊤ :=
    TopologicalSpace.Opens.eq_of_forall_isClosed_singleton fun point hx ↦
      ⟨fun _ ↦ trivial, fun _ ↦ TopologicalSpace.Opens.mem_iSup.mpr (hcov point hx)⟩
  obtain ⟨finiteSubset, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun familyIndex ↦ ((Modules.Hom.zeroLocus (sectionFamily familyIndex)).support.compl : Set scheme))
    (fun familyIndex ↦ (Modules.Hom.zeroLocus (sectionFamily familyIndex)).support.compl.isOpen) fun point _ ↦ by
      simpa using (SetLike.ext_iff.mp htop point).mpr trivial
  refine ⟨lineBundle, inferInstance, finiteSubset, inferInstance,
    fun familyIndex ↦ sectionFamily familyIndex, fun familyIndex ↦ hs familyIndex, eq_top_iff.mpr fun point _ ↦ ?_⟩
  obtain ⟨familyIndex, ht, hx⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ point))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨familyIndex, ht⟩, hx⟩

end AlgebraicGeometry.Scheme
