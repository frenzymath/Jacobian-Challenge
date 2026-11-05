import Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import Jacobian.AlgebraicGeometry.Cohomology.FiberField

/-!
# Cohomology of fibers under base change

In a cartesian square of families, the new residue-field fiber is a field
extension of the original one. Flat base change of quasi-coherent cohomology
therefore preserves the fiber dimensions and Euler characteristics. Quasi-compact
and quasi-separated families suffice; no properness or finite presentation is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Cohomology dimensions on residue-field fibers are invariant under base change. -/
theorem hFiber_pullback_of_isPullback {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X)
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) (q : ℕ) (t' : T') :
    ((pullback g').obj M).hFiber f' q t' = M.hFiber f q (g.base t') := by
  let K := T.residueField (g.base t')
  let L := T'.residueField t'
  letI : Algebra K L := (g.residueFieldMap t').hom.toAlgebra
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback sq t'
  letI := f.fiberOverSpecResidueField (g.base t')
  letI := f'.fiberOverSpecResidueField t'
  have : QuasiCompact (f.fiber (g.base t') ↘ Spec (.of K)) := by
    change QuasiCompact (f.fiberToSpecResidueField _)
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiSeparated (f.fiber (g.base t') ↘ Spec (.of K)) := by
    change QuasiSeparated (f.fiberToSpecResidueField _)
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have h := finrankH_pullback (k := K) L ((pullback (f.fiberι (g.base t'))).obj M) q
  let φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hsq' : IsPullback (Limits.pullback.map f' (T'.fromSpecResidueField t') f
      (T.fromSpecResidueField (g.base t')) g' (Spec.map (g.residueFieldMap t')) g
      (by simp [sq.w]) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t').symm)
      (f'.fiberToSpecResidueField t') (f.fiber (g.base t') ↘ Spec (.of K)) φ := hsq
  let e : f'.fiber t' ≅ Limits.pullback (f.fiber (g.base t') ↘ Spec (.of K)) φ :=
    hsq'.isoPullback
  have hcomp : f'.fiberι t' ≫ g' =
      e.hom ≫ Limits.pullback.fst _ _ ≫ f.fiberι (g.base t') := by
    rw [← Category.assoc, hsq'.isoPullback_hom_fst]
    simp [Scheme.Hom.fiberι]
  let N := (pullback (Limits.pullback.fst (f.fiber (g.base t') ↘ Spec (.of K)) φ)).obj
    ((pullback (f.fiberι (g.base t'))).obj M)
  have structureMapEq : e.hom ≫ Limits.pullback.snd _ _ =
      f'.fiberToSpecResidueField t' := hsq'.isoPullback_hom_snd
  have hi : ((pullback e.hom).obj N).finrankH L q = N.finrankH L q := by
    have comparison := finrankH_pullback_of_isIso e.hom (Limits.pullback.snd _ _) N q
    rw [structureMapEq] at comparison
    exact comparison
  change ((pullback (f'.fiberι t')).obj ((pullback g').obj M)).finrankH L q =
    ((pullback (f.fiberι (g.base t'))).obj M).finrankH K q
  rw [← h, ← hi]
  exact finrankH_congr _ ((pullbackComp _ _).app M ≪≫ (pullbackCongr hcomp).app M ≪≫
    ((pullbackComp _ _).app M).symm ≪≫ (pullback e.hom).mapIso
      ((pullbackComp _ _).app M).symm) q

/-- Fiber Euler characteristics of quasi-coherent modules commute with base change. -/
theorem eulerCharFiber_pullback_of_isPullback {T' X' : Scheme.{u}}
    (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f g) (t' : T') :
    ((pullback g').obj M).eulerCharFiber f' t' = M.eulerCharFiber f (g.base t') := by
  simp only [eulerCharFiber, hFiber_pullback_of_isPullback f M g g' f' sq]

end AlgebraicGeometry.Scheme.Modules
