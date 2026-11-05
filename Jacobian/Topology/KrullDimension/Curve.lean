import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# Complements of opens in irreducible one-dimensional spaces

In an irreducible space of dimension at most one, every point outside a
nonempty open is closed. For a noetherian sober space this complement is finite.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open Order TopologicalSpace
variable {space : Type*} [TopologicalSpace space] [IrreducibleSpace space] [T0Space space]

/-- Points outside a nonempty open of an irreducible one-dimensional space are closed. -/
theorem IsOpen.isClosed_singleton_of_mem_compl (dimension_bound : topologicalKrullDim space ≤ 1) {openSet : Set space}
    (hU : IsOpen openSet) (hne : openSet.Nonempty) {point : space} (hx : point ∉ openSet) : IsClosed {point} := by
  obtain ⟨openPoint, hu⟩ := hne
  by_contra hcl
  obtain ⟨otherPoint, hy, hyx⟩ : ∃ otherPoint ∈ closure {point}, otherPoint ≠ point := by
    by_contra! H
    exact hcl (closure_subset_iff_isClosed.mp fun otherPoint hy ↦ H otherPoint hy)
  let otherSpace : IrreducibleCloseds space := ⟨closure {otherPoint}, isIrreducible_singleton.closure, isClosed_closure⟩
  let thirdSpace : IrreducibleCloseds space := ⟨closure {point}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds space := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ space, isClosed_univ⟩
  have h₁ : otherSpace < thirdSpace := by
    refine lt_of_le_of_ne (show closure {otherPoint} ⊆ closure {point} from
      closure_minimal (by simpa using hy) isClosed_closure) fun dimension_bound ↦ hyx ?_
    exact (inseparable_iff_closure_eq.mpr congr(($dimension_bound : Set space))).eq
  have h₂ : thirdSpace < T := by
    refine lt_of_le_of_ne (show closure {point} ⊆ Set.univ from Set.subset_univ _) fun dimension_bound ↦ hx ?_
    have hu' : openPoint ∈ closure ({point} : Set space) := by
      rw [show closure ({point} : Set space) = Set.univ from congr(($dimension_bound : Set space))]; trivial
    obtain ⟨thirdPoint, hzU, hz⟩ := mem_closure_iff.mp hu' openSet hU hu
    rwa [Set.mem_singleton_iff.mp hz] at hzU
  let q₁ : LTSeries (IrreducibleCloseds space) := (RelSeries.singleton _ otherSpace).snoc thirdSpace h₁
  let chain : LTSeries (IrreducibleCloseds space) :=
    q₁.snoc T (by rw [show q₁.last = thirdSpace from RelSeries.last_snoc _ _ _]; exact h₂)
  have hq : chain.length = 2 := rfl
  have := Order.LTSeries.length_le_krullDim chain
  rw [hq] at this
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := this.trans dimension_bound
  exact absurd h2 (by decide)


/-- A nonempty open of an irreducible noetherian sober curve has finite complement. -/
theorem IsOpen.finite_compl_of_topologicalKrullDim_le_one [QuasiSober space] [NoetherianSpace space]
    (dimension_bound : topologicalKrullDim space ≤ 1) {openSet : Set space} (hU : IsOpen openSet) (hne : openSet.Nonempty) :
    openSetᶜ.Finite := by
  obtain ⟨targetRing, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ closedSet ∈ targetRing, ∃ thirdPoint, closedSet = {thirdPoint} := by
    intro closedSet ht
    obtain ⟨thirdPoint, hz⟩ := QuasiSober.sober (hSi closedSet ht) (hSc closedSet ht)
    have hzU : thirdPoint ∉ openSet := by
      have : thirdPoint ∈ openSetᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨thirdPoint, by rw [← hz.def, (hU.isClosed_singleton_of_mem_compl dimension_bound hne hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun closedSet ht ↦ ?_
  obtain ⟨thirdPoint, rfl⟩ := key closedSet ht
  exact Set.finite_singleton thirdPoint
