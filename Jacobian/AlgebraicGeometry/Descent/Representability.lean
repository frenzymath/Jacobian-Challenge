import Jacobian.CategoryTheory.Comma.Over.DescentRepresentable
import Jacobian.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of representing schemes

An fpqc sheaf represented after a faithfully flat quasi-compact base change is
represented by an actual descended scheme whose canonical point transport is
trivial. Effective epimorphisms supply descent of morphisms; this is not an
assumption of effective descent of arbitrary scheme objects.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe schemeUniverse valueUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{schemeUniverse}} (baseMap : source ⟶ base)
  [Flat baseMap] [Surjective baseMap] [QuasiCompact baseMap]
  {presheaf : (Over base)ᵒᵖ ⥤ Type valueUniverse}

/-- Invariant point transport identifies an actual descended scheme as the representing object. -/
theorem nonempty_representableBy_of_faithfullyFlat
    (sheafCondition : Presheaf.IsSheaf (Scheme.fpqcTopology.over base) presheaf)
    {localObject : Over source}
    (representation : ((Over.map baseMap).op ⋙ presheaf).RepresentableBy localObject)
    (descendedObject : Over base) (projection : localObject.left ⟶ descendedObject.left)
    (cartesian : IsPullback projection localObject.hom descendedObject.hom baseMap)
    (invariant : ∀ {test : Scheme.{schemeUniverse}} (firstMap secondMap : test ⟶ source)
      (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
      (point : Over.mk firstMap ⟶ localObject),
      (representation.overTransport firstMap secondMap equality point).left ≫ projection =
        point.left ≫ projection) :
    Nonempty (presheaf.RepresentableBy descendedObject) := by
  refine Functor.RepresentableBy.nonempty_representableBy_of_descent representation
    projection cartesian invariant (fun parameter ↦ inferInstance) ?_ ?_
  · intro parameter point compatible
    have pointCompatible : ∀ {test : Scheme.{schemeUniverse}}
        (firstMap secondMap : test ⟶ pullback parameter.hom baseMap),
        firstMap ≫ pullback.fst parameter.hom baseMap =
          secondMap ≫ pullback.fst parameter.hom baseMap → firstMap ≫ point = secondMap ≫ point := by
      intro test firstMap secondMap equality
      simpa using congrArg (pullback.lift firstMap secondMap equality ≫ ·) compatible
    exact ⟨EffectiveEpi.desc _ point pointCompatible, EffectiveEpi.fac _ point pointCompatible⟩
  · intro parameter
    have : Flat (Functor.RepresentableBy.descentCoverπ baseMap parameter).left :=
      inferInstanceAs (Flat (pullback.fst _ _))
    have : Surjective (Functor.RepresentableBy.descentCoverπ baseMap parameter).left :=
      inferInstanceAs (Surjective (pullback.fst _ _))
    have : QuasiCompact (Functor.RepresentableBy.descentCoverπ baseMap parameter).left :=
      inferInstanceAs (QuasiCompact (pullback.fst _ _))
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 sheafCondition).isSheafFor _
      (Scheme.singleton_mem_over_fpqcTopology _)

end AlgebraicGeometry
