import Mathlib.Topology.Sober

/-!
# Generic points and dense intersections

Distinct generic points of irreducible components do not specialize to one another.
A finite intersection of open sets containing all generic points is dense.
-/

variable {space : Type*} [TopologicalSpace space]

/-- If `point` and `otherPoint` are distinct generic points of irreducible components, then `point` does not lie
in the closure of `otherPoint`: otherwise the component of `point` would be contained in the component of
`otherPoint`, hence equal to it by maximality. -/
theorem genericPoints.notMem_closure_of_ne [T0Space space] {point otherPoint : space} (hx : point ∈ genericPoints space)
    (hy : otherPoint ∈ genericPoints space) (hxy : point ≠ otherPoint) : point ∉ _root_.closure ({otherPoint} : Set space) := by
  intro hmem
  have hle : _root_.closure ({point} : Set space) ⊆ _root_.closure ({otherPoint} : Set space) :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  exact hxy (isGenericPoint_closure.eq (hle.antisymm (hx.2 hy.1 hle)).symm)


lemma dense_iInf_of_genericPoints_subset [QuasiSober space] {indexType : Type*}
    [Finite indexType] {opensFamily : indexType → TopologicalSpace.Opens space}
    (containsGenericPoints : ∀ index, genericPoints space ⊆ (opensFamily index : Set space)) :
    Dense ((⨅ index, opensFamily index : TopologicalSpace.Opens space) : Set space) := by
  refine (dense_iff_closure_eq.mpr genericPoints.closure).mono ?_
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.subset_iInter containsGenericPoints
