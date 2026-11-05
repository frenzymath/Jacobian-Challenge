import Jacobian.AlgebraicGeometry.Cohomology.Fiber
import Jacobian.AlgebraicGeometry.Curve.Genus
import Jacobian.AlgebraicGeometry.Picard.Presheaf
import Jacobian.AlgebraicGeometry.Picard.Field

/-!
# Degree of Picard classes

The degree of an invertible module sheaf is its Euler characteristic minus
that of the structure sheaf. For a family, the degree is computed on each
residue-field fiber. The representative formulas make this independent of
the chosen representative of an isomorphism class.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Pic

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Cohomological degree of a Picard class over a field. -/
def degree (L : X.Pic) : ℤ :=
  Modules.degree k ((fromSkeleton X.Modules).obj L.val)

/-- The degree of a represented Picard class is the degree of its representative. -/
@[simp]
lemma degree_mk (M : X.Modules) [M.IsInvertible] : degree k (mk M) = M.degree k :=
  Modules.degree_congr k (mkIso M)

set_option backward.isDefEq.respectTransparency false in
/-- The structure-sheaf class has degree zero. -/
@[simp]
lemma degree_mk_unit : degree k (mk (SheafOfModules.unit X.ringCatSheaf)) = 0 := by
  rw [degree_mk, Modules.degree_unit]

end Scheme.Pic

namespace Scheme.Pic

/-- Pullback from the base does not change the restriction of a class to a fiber. -/
lemma map_fiberι_mul_map {Y T : Scheme.{u}} (g : Y ⟶ T) (L : Y.Pic) (N : T.Pic)
    (t : T) : map (g.fiberι t) (L * map g N) = map (g.fiberι t) L := by
  rw [map_mul, ← map_comp, Scheme.Hom.fiber_fac, map_comp,
    Subsingleton.elim (h := subsingleton_spec_field (T.residueField t)) (map _ N) 1,
    map_one, mul_one]

end Scheme.Pic

namespace Scheme.Modules

/-- Equal Picard classes on a fiber have equal fiber Euler characteristics. -/
lemma eulerCharFiber_eq_of_pic_map_fiberι_eq {Y T : Scheme.{u}} (g : Y ⟶ T)
    {L L' : Y.Pic} {t : T} (h : Pic.map (g.fiberι t) L = Pic.map (g.fiberι t) L') :
    eulerCharFiber ((fromSkeleton _).obj L.val) g t =
      eulerCharFiber ((fromSkeleton _).obj L'.val) g t := by
  obtain ⟨e⟩ := Pic.eq_iff_nonempty_iso.1 h
  let := g.fiberOverSpecResidueField t
  refine finsum_congr fun q ↦ ?_
  exact congrArg (fun n : ℕ ↦ (-1) ^ q * (n : ℤ)) (finrankH_congr _
    ((fromSkeletonToSkeletonIso _).symm ≪≫ e ≪≫ fromSkeletonToSkeletonIso _) q)

end Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fiberwise cohomological degree of a class in the relative Picard presheaf. -/
def picardPresheafDegree {T : Over S} (L : (picardPresheaf f).obj (.op T)) (t : T.left) : ℤ :=
  Scheme.Modules.eulerCharFiber
      ((fromSkeleton _).obj (Scheme.Pic.val L)) (pullback.snd f T.hom) t -
    Scheme.Modules.eulerCharFiber (SheafOfModules.unit (pullback f T.hom).ringCatSheaf)
      (pullback.snd f T.hom) t

/-- The fiberwise degree of a represented Picard class is computed from that module sheaf. -/
lemma picardPresheafDegree_mk {T : Over S} (M : (pullback f T.hom).Modules)
    [M.IsInvertible] (t : T.left) :
    picardPresheafDegree f (Scheme.Pic.mk M) t =
      M.eulerCharFiber (pullback.snd f T.hom) t -
        Scheme.Modules.eulerCharFiber (SheafOfModules.unit (pullback f T.hom).ringCatSheaf)
          (pullback.snd f T.hom) t := by
  change _ - _ = _ - _
  rw [Scheme.Modules.eulerCharFiber_congr (Scheme.Pic.mkIso M)]

set_option backward.isDefEq.respectTransparency false in
/-- The trivial Picard class has fiberwise degree zero. -/
@[simp]
lemma picardPresheafDegree_mk_unit (T : Over S) (t : T.left) :
    picardPresheafDegree f (Scheme.Pic.mk
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf)) t = 0 := by
  rw [picardPresheafDegree_mk, sub_self]

/-- Tensoring by a line bundle pulled back from the parameter scheme preserves degree. -/
lemma picardPresheafDegree_mul_map_snd {T : Over S}
    (L : (pullback f T.hom).Pic) (N : T.left.Pic) (t : T.left) :
    picardPresheafDegree f (L * Scheme.Pic.map (pullback.snd f T.hom) N) t =
      picardPresheafDegree f L t := by
  unfold picardPresheafDegree
  rw [Scheme.Modules.eulerCharFiber_eq_of_pic_map_fiberι_eq (pullback.snd f T.hom)
    (Scheme.Pic.map_fiberι_mul_map _ L N t)]

end AlgebraicGeometry
