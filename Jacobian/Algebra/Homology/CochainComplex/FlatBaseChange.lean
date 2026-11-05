import Jacobian.Algebra.Homology.CochainComplex.RestrictScalars
import Jacobian.Algebra.Homology.MappingCone.Flat
import Jacobian.CategoryTheory.Monoidal.Opcycles
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Base change of bounded-above flat complexes

Tensoring with any module preserves quasi-isomorphisms between bounded-above
complexes of flat modules. If such a complex resolves a nonnegative flat
complex, its degree-zero opcycle is flat. Ordinary extension of scalars along
an arbitrary ring homomorphism also preserves these quasi-isomorphisms; the
target ring need not be flat over the source ring.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace Module.Flat

/-- Flat adjacent terms and tensor exactness in the preceding degree imply
flatness of the opcycle. No flatness of the other terms is required. -/
theorem opcycles_of_tensor_exactAt {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (h₁ : Module.Flat R (P.X (a - 1))) (h₂ : Module.Flat R (P.X a))
    (hP : ∀ N : ModuleCat.{u} R,
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    Module.Flat R (P.opcycles a) := by
  apply (Module.Flat.iff_preservesFiniteLimits_tensorLeft (P.opcycles a)).mpr
  exact CategoryTheory.preservesFiniteLimits_tensorLeft_opcycles_of_exactAt P a
    ((Module.Flat.iff_preservesFiniteLimits_tensorLeft (P.X (a - 1))).mp h₁)
    ((Module.Flat.iff_preservesFiniteLimits_tensorLeft (P.X a)).mp h₂) hP

end Module.Flat

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Tensoring with any module preserves a quasi-isomorphism between bounded-above
flat complexes, without a lower bound or a flatness hypothesis on the tensor factor. -/
theorem quasiIso_tensorRight_of_boundedAbove_flat
    {Q C : CochainComplex (ModuleCat.{u} R) ℤ} (e : Q ⟶ C) (b : ℤ)
    [Q.IsStrictlyLE b] [C.IsStrictlyLE b]
    (hQ : ∀ n, Module.Flat R (Q.X n)) (hC : ∀ n, Module.Flat R (C.X n))
    (he : QuasiIso e) (N : ModuleCat.{u} R) :
    QuasiIso (((tensorRight N).mapHomologicalComplex (.up ℤ)).map e) := by
  apply (quasiIso_map_iff_acyclic_map_mappingCone e (tensorRight N)).mpr
  exact tensorRight_mappingCone_exactAt_of_flat e b hQ hC
    ((mappingCone.quasiIso_iff_acyclic e).mp he) N

/-- A bounded-above flat resolution of a nonnegative flat complex has flat
degree-zero opcycle. -/
theorem flat_opcycles_zero_of_quasiIso_boundedAbove_flat
    (C Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [C.IsStrictlyGE 0] [C.IsStrictlyLE b] [Q.IsStrictlyLE b]
    (hC : ∀ n, Module.Flat R (C.X n)) (hQ : ∀ n, Module.Flat R (Q.X n))
    (e : Q ⟶ C) (he : QuasiIso e) : Module.Flat R (Q.opcycles 0) := by
  apply Module.Flat.opcycles_of_tensor_exactAt Q 0 (hQ _) (hQ _)
  intro N
  let F := (tensorRight N).mapHomologicalComplex (.up ℤ)
  letI : QuasiIso (F.map e) := quasiIso_tensorRight_of_boundedAbove_flat e b hQ hC he N
  exact (exactAt_iff_of_quasiIsoAt (F.map e) (0 - 1)).mpr
    (CochainComplex.exactAt_of_isGE (F.obj C) 0 (0 - 1) (by decide))

end CochainComplex

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restricting extension of scalars identifies it with tensoring by the target ring. -/
def extendScalarsRestrictIsoTensorRight :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      tensorRight ((restrictScalars f).obj (ModuleCat.of S S)) :=
  (show extendScalars f ⋙ restrictScalars f ≅
      tensorLeft ((restrictScalars f).obj (ModuleCat.of S S)) from Iso.refl _) ≪≫
    BraidedCategory.tensorLeftIsoTensorRight _

instance additive_extendScalars : (extendScalars.{u, u, u} f).Additive := by
  have : (extendScalars f ⋙ restrictScalars f).Additive :=
    Functor.additive_of_iso (extendScalarsRestrictIsoTensorRight f).symm
  exact Functor.additive_of_comp_faithful (extendScalars f) (restrictScalars f)

/-- Restriction of scalars reflects quasi-isomorphisms of complexes. -/
theorem quasiIso_restrictScalars_iff {Q C : CochainComplex (ModuleCat.{u} S) ℤ}
    (e : Q ⟶ C) :
    QuasiIso (((restrictScalars f).mapHomologicalComplex (.up ℤ)).map e) ↔ QuasiIso e :=
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology e (restrictScalars f)

end ModuleCat

namespace CochainComplex

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars along any ring homomorphism preserves quasi-isomorphisms
between bounded-above flat complexes. -/
theorem quasiIso_extendScalars_of_boundedAbove_flat
    {Q C : CochainComplex (ModuleCat.{u} R) ℤ} (e : Q ⟶ C) (b : ℤ)
    [Q.IsStrictlyLE b] [C.IsStrictlyLE b]
    (hQ : ∀ n, Module.Flat R (Q.X n)) (hC : ∀ n, Module.Flat R (C.X n))
    (he : QuasiIso e) (f : R →+* S) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map e) := by
  let N := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
  let G := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
  let T := (tensorRight N).mapHomologicalComplex (.up ℤ)
  let comparison : E ⋙ G ≅ T :=
    Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsRestrictIsoTensorRight f) (.up ℤ)
  have ht : QuasiIso (T.map e) :=
    quasiIso_tensorRight_of_boundedAbove_flat e b hQ hC he N
  have hr : QuasiIso (G.map (E.map e)) :=
    (quasiIso_iff_of_arrow_mk_iso (G.map (E.map e)) (T.map e)
      (Arrow.isoMk (comparison.app Q) (comparison.app C)
        (comparison.hom.naturality e).symm)).mpr ht
  exact (ModuleCat.quasiIso_restrictScalars_iff f (E.map e)).mp hr

end CochainComplex
