import Jacobian.AlgebraicGeometry.Cohomology.FlatBaseChange
import Jacobian.AlgebraicGeometry.Curve.Genus
import Jacobian.AlgebraicGeometry.Modules.Invertible

/-!
# Cohomological invariants under field extension

Flat base change identifies cohomology after extension of the ground field with
the scalar extension of the original cohomology. Consequently its dimension,
Euler characteristic, arithmetic genus and cohomological degree are unchanged.
The comparison uses the native abelian-sheaf cohomology and its field actions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- Dimensions of quasi-coherent cohomology are unchanged by field extension. -/
theorem finrankH_pullback [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).finrankH K q =
      M.finrankH k q := by
  let f := X ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := Limits.pullback.fst f g
  let h := Limits.pullback.snd f g
  let A := Γ(Spec (.of k), ⊤)
  let B := Γ(Spec (.of K), ⊤)
  letI : Field A :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  letI : Field B :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  letI : Algebra A B := g.appTop.hom.toAlgebra
  letI : Module A (M.H q) := Module.compHom (M.H q) f.appTop.hom
  letI : Module B (((pullback p).obj M).H q) :=
    Module.compHom (((pullback p).obj M).H q) h.appTop.hom
  obtain ⟨e⟩ := nonempty_H_baseChange_linearEquiv
    (IsPullback.of_hasPullback f g) M rfl q
  have rankSource : M.finrankH k q = Module.finrank A (M.H q) := by
    have eq := rank_eq_of_equiv_equiv (R := k) (R' := A)
      (M := M.H q) (M₁ := M.H q) (Scheme.ΓSpecIso (.of k)).inv.hom
      (AddEquiv.refl _) (ConcreteCategory.bijective_of_isIso _) (fun c x ↦ by rfl)
    exact congrArg Cardinal.toNat eq
  have rankTarget : ((pullback p).obj M).finrankH K q =
      Module.finrank B (((pullback p).obj M).H q) := by
    have eq := rank_eq_of_equiv_equiv (R := K) (R' := B)
      (M := ((pullback p).obj M).H q) (M₁ := ((pullback p).obj M).H q)
      (Scheme.ΓSpecIso (.of K)).inv.hom (AddEquiv.refl _)
      (ConcreteCategory.bijective_of_isIso _) (fun c x ↦ by rfl)
    exact congrArg Cardinal.toNat eq
  exact rankTarget.trans (e.finrank_eq.symm.trans
    (Module.finrank_baseChange.trans rankSource.symm))

/-- Euler characteristic is unchanged by extension of the ground field. -/
theorem eulerChar_pullback [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] :
    ((pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).eulerChar K =
      M.eulerChar k := by
  simp only [eulerChar, finrankH_pullback K M]

/-- The cohomological degree is unchanged by extension of the ground field. -/
theorem degree_pullback [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] :
    ((pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K = M.degree k := by
  simp only [degree]
  rw [eulerChar_pullback K M]
  exact congrArg (M.eulerChar k - ·)
    ((eulerChar_congr K (pullbackObjUnitIso _).symm).trans
      (eulerChar_pullback K (SheafOfModules.unit X.ringCatSheaf)))

end Modules

/-- Arithmetic genus is unchanged by extension of the ground field. -/
theorem arithmeticGenus_pullback {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (K : Type u) [Field K] [Algebra k K] :
    (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).arithmeticGenus K =
      X.arithmeticGenus k := by
  rw [arithmeticGenus, arithmeticGenus, ← Modules.finrankH_pullback K
    (SheafOfModules.unit X.ringCatSheaf) 1]
  exact Modules.finrankH_congr K (Modules.pullbackObjUnitIso _).symm 1

end AlgebraicGeometry.Scheme
