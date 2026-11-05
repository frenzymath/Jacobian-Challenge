import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sober

/-!
# Dimension and maps of sober spaces

Surjective specializing maps do not increase dimension in the target.
Continuous maps with incomparable fibers do not decrease dimension in the target.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Topology TopologicalSpace


section Map

open Order

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] [T0Space X]
  [QuasiSober Y] [T0Space Y]

attribute [local instance] specializationOrder

/-- The dimension of a quasi-sober `T₀` space is the Krull dimension of its points, ordered by
specialization. -/
theorem topologicalKrullDim_eq_krullDim_specializationOrder :
    topologicalKrullDim X = krullDim X :=
  krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- A surjective specializing map `f : X ⟶ Y` of quasi-sober `T₀` spaces satisfies
`dim Y ≤ dim X`: a chain of specializations in `Y` lifts to `X`, starting from its generic end.
-/
theorem topologicalKrullDim_le_of_specializingMap {f : X → Y} (hf : SpecializingMap f)
    (hsurj : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder, krullDim_eq_iSup_height,
    krullDim_eq_iSup_height]
  refine iSup_le fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  refine le_trans (WithBot.coe_le_coe.mpr ?_) (le_iSup (fun a : X ↦ (height a : WithBot ℕ∞)) x)
  suffices ∀ (n : ℕ) (p : LTSeries Y) (x : X), p.length = n → p.last = f x → (n : ℕ∞) ≤ height x
    from height_le fun p hp ↦ this _ p x rfl hp
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro p x hn hp
    have hlt : p.eraseLast.last < f x := hp ▸ p.eraseLast_last_rel_last (by omega)
    obtain ⟨x', hxx', hx'⟩ := hf hlt.le
    have hx'x : x' < x := lt_of_le_of_ne hxx' (by rintro rfl; exact hlt.ne hx'.symm)
    have := ih p.eraseLast x' (by simp [hn]) hx'.symm
    calc ((n + 1 : ℕ) : ℕ∞) = n + 1 := by push_cast; rfl
      _ ≤ height x' + 1 := by gcongr
      _ ≤ height x := height_add_one_le hx'x

/-- A continuous map `f : X ⟶ Y` of quasi-sober `T₀` spaces which identifies no two distinct
points `x ⤳ x'` satisfies `dim X ≤ dim Y`. -/
theorem topologicalKrullDim_le_of_continuous {f : X → Y} (hf : Continuous f)
    (hinj : ∀ x x', x ⤳ x' → f x = f x' → x = x') :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder]
  refine krullDim_le_of_strictMono f fun a b hab ↦ lt_of_le_of_ne (hab.le.map hf) fun h ↦ ?_
  exact hab.ne (hinj _ _ hab.le h.symm).symm

end Map
