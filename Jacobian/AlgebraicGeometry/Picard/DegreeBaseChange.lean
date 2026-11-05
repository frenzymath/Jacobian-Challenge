import Jacobian.AlgebraicGeometry.Cohomology.FiberBaseChange
import Jacobian.AlgebraicGeometry.Picard.DegreeSheaf

/-!
# Base change of Picard degrees

Fiberwise degree is natural for quasi-compact quasi-separated families. The
cartesian-square formula permits arbitrary changes of the parameter scheme,
not just canonical chosen pullbacks. Over a field it is the cohomological degree
of the invertible module on that scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Fiberwise Picard degree is natural under a change of the parameter scheme. -/
theorem picardPresheafDegree_map [QuasiCompact f] [QuasiSeparated f] {T T' : Over S}
    (g : T' ⟶ T) (L : (picardPresheaf f).obj (.op T)) (t : T'.left) :
    picardPresheafDegree f ((picardPresheaf f).map g.op L) t =
      picardPresheafDegree f L (g.left t) := by
  have := Pic.isInvertible (scheme := pullback f T.hom) L
  have hsq := isPullback_baseChangeMap f g
  simp only [picardPresheafDegree]
  rw [← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ hsq,
    ← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ hsq,
    Modules.eulerCharFiber_congr (Modules.pullbackObjUnitIso _),
    ← Modules.eulerCharFiber_congr (fromSkeletonToSkeletonIso
      ((Modules.pullback (baseChangeMap f g)).obj ((fromSkeleton _).obj (Pic.val L))))]
  rfl

/-- **The fibrewise degree is compatible with cartesian squares of families.** Let `f' : X' ⟶ S'`
be another morphism, `T'` a scheme over `S'` and `e : X'_{T'} ⟶ X_T` a morphism over
`φ : T' ⟶ T` exhibiting `X'_{T'}` as `X_T ×_T T'`. Then the fibrewise degree of the pullback of
`ℒ ∈ Pic (X_T)` along `e` at `t'` is the fibrewise degree of `ℒ` at `φ(t')`. -/
theorem picardPresheafDegree_pic_map_of_isPullback [QuasiCompact f] [QuasiSeparated f]
    {X' S' : Scheme.{u}} (f' : X' ⟶ S') {T : Over S} {T' : Over S'} (φ : T'.left ⟶ T.left)
    (e : pullback f' T'.hom ⟶ pullback f T.hom)
    (sq : IsPullback e (pullback.snd f' T'.hom) (pullback.snd f T.hom) φ)
    (L : (picardPresheaf f).obj (.op T)) (t : T'.left) :
    picardPresheafDegree f' (Pic.map e L) t = picardPresheafDegree f L (φ t) := by
  have := Pic.isInvertible (scheme := pullback f T.hom) L
  simp only [picardPresheafDegree]
  rw [← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ sq,
    ← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ sq,
    Modules.eulerCharFiber_congr (Modules.pullbackObjUnitIso _),
    ← Modules.eulerCharFiber_congr (fromSkeletonToSkeletonIso
      ((Modules.pullback e).obj ((fromSkeleton _).obj (Pic.val L))))]
  rfl


variable {k : Type u} [Field k]

/-- On a parameter scheme that is the spectrum of a field, the fiber degree
is the cohomological degree over that field. -/
lemma picardPresheafDegree_eq_degree_of_field {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ S)
    (L : (picardPresheaf f).obj (.op (Over.mk t))) (s : Spec (.of K)) :
    picardPresheafDegree f L s =
      (letI : (pullback f t).Over (Spec (.of K)) := ⟨pullback.snd f t⟩
       Pic.degree (X := pullback f t) K L) := by
  letI : (pullback f t).Over (Spec (.of K)) := ⟨pullback.snd f t⟩
  unfold picardPresheafDegree
  rw [Modules.eulerCharFiber_eq_eulerChar, Modules.eulerCharFiber_eq_eulerChar]
  rfl

/-- Pulling a class back to a field-valued point computes its degree on the
residue-field fiber of the image point. -/
lemma picardFibreDegree_eq_picardPresheafDegree {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    {T : Over (Spec (.of k))} (L : (picardPresheaf f).obj (.op T))
    {K : Type u} [Field K] [Algebra k K]
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T)
    (s : Spec (.of K)) :
    picardFibreDegree f L t = picardPresheafDegree f L (t.left s) := by
  exact (picardPresheafDegree_eq_degree_of_field f _
    ((picardPresheaf f).map t.op L) s).symm.trans
      (picardPresheafDegree_map f t L s)

/-- The field-valued definition of the degree part agrees with constant degree
on all residue-field fibers. Every point is detected by its residue-field map. -/
lemma mem_picardSubfunctorDegree_iff {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    {T : Over (Spec (.of k))} (L : (picardPresheaf f).obj (.op T)) (d : ℤ) :
    L ∈ (picardSubfunctorDegree f d).obj (.op T) ↔
      ∀ t : T.left, picardPresheafDegree f L t = d := by
  constructor
  · intro membership t
    letI : Algebra k (T.left.residueField t) :=
      (Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)).hom.toAlgebra
    let point : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap k (T.left.residueField t)))) ⟶ T :=
      Over.homMk (T.left.fromSpecResidueField t) (Spec.map_preimage _).symm
    have degree_eq := picardFibreDegree_eq_picardPresheafDegree f L point
      (IsLocalRing.closedPoint (T.left.residueField t))
    have image_eq : point.left (IsLocalRing.closedPoint (T.left.residueField t)) = t :=
      Scheme.fromSpecResidueField_apply _ _
    rw [image_eq] at degree_eq
    exact degree_eq.symm.trans (membership _ point)
  · intro constantDegree K _ _ point
    rw [picardFibreDegree_eq_picardPresheafDegree f L point
      (IsLocalRing.closedPoint K)]
    exact constantDegree _

/-- Over a field, the residue-fiber degree is the degree of the chosen module. -/
lemma picardPresheafDegree_eq_degree {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {T : Over (Spec (.of k))} (L : (picardPresheaf f).obj (.op T)) (t : T.left) :
    letI := (pullback.snd f T.hom).fiberOverSpecResidueField t
    picardPresheafDegree f L t = Modules.degree (T.left.residueField t)
      ((Modules.pullback ((pullback.snd f T.hom).fiberι t)).obj
        ((fromSkeleton _).obj (Pic.val (scheme := pullback f T.hom) L))) := by
  letI := (pullback.snd f T.hom).fiberOverSpecResidueField t
  refine congrArg (_ - ·) ?_
  exact Modules.eulerChar_congr _ (Modules.pullbackObjUnitIso _)

end AlgebraicGeometry
