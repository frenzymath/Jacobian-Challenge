import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Relevant
import Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreePart
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Homogeneous fractions as a sheaf of modules

The degree-`m` parts of the localizations at homogeneous primes form a sheaf:
its sections are the dependent functions which are locally homogeneous fractions.
This constructs the presheaf of modules underlying the twisting sheaf `𝒪(m)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ)

namespace ProjectiveSpectrum.Twist

/-- The fibre of the twisting sheaf `𝒪(m)` at a point `x` of `Proj 𝒜`: the degree-`m` part of
the localization of `A` at `x`. -/
abbrev fiber (x : ProjectiveSpectrum 𝒜) :=
  degreePart 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl m

variable {𝒜 m}

/-- The predicate saying that a dependent function on an open `U` is, on all of `U`, the fixed
fraction `a / b` with `a ∈ 𝒜 i`, `b ∈ 𝒜 j`, `i = j + m` and `b` avoiding every point of `U`. -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, fiber 𝒜 m x.1) : Prop :=
  ∃ (i j : ℕ) (h : (i : ℤ) = j + m) (a : 𝒜 i) (b : 𝒜 j)
    (hb : ∀ x : U, (b : A) ∉ x.1.asHomogeneousIdeal.toIdeal),
    ∀ x : U, f x = degreePart.mk a b (hb x) h

variable (𝒜 m)

/-- The predicate `IsFraction` is prelocal: if it holds on `U`, it holds on every open subset
of `U`. -/
def isFractionPrelocal :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ fiber 𝒜 m x where
  pred f := IsFraction f
  res := by
    rintro V U i f ⟨k, l, hkl, a, b, h, w⟩
    exact ⟨k, l, hkl, a, b, (h <| i ·), (w <| i ·)⟩

/-- The sections of the twisting sheaf `𝒪(m)` are the dependent functions which are locally
fractions `a / b` with `deg a = deg b + m`. -/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ fiber 𝒜 m x :=
  (isFractionPrelocal 𝒜 m).sheafify

variable {𝒜 m}

/-- A fixed fraction `a / b` of degree `m` is a section of `𝒪(m)` wherever `b` does not
vanish. -/
theorem isLocallyFraction_mk {i j : ℕ} (h : (i : ℤ) = j + m) (a : 𝒜 i) (b : 𝒜 j)
    {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (hb : ∀ x : U, (b : A) ∉ x.1.asHomogeneousIdeal.toIdeal) :
    (isLocallyFraction 𝒜 m).pred fun x : U ↦ degreePart.mk a b (hb x) h :=
  fun x ↦ ⟨U, x.2, 𝟙 _, i, j, h, a, b, hb, fun _ ↦ rfl⟩

/-- The pointwise product of a section of `𝒪(m)` and a section of `𝒪(n)` is a section of
`𝒪(k)`, for `m + n = k`. -/
theorem isLocallyFraction_mul {n k : ℤ} (h : m + n = k) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {s : ∀ x : U, fiber 𝒜 m x.1} {t : ∀ x : U, fiber 𝒜 n x.1}
    (hs : (isLocallyFraction 𝒜 m).pred s) (ht : (isLocallyFraction 𝒜 n).pred t) :
    (isLocallyFraction 𝒜 k).pred fun x ↦
      ⟨s x * t x, h ▸ mul_mem_degreePart (s x).2 (t x).2⟩ := by
  intro x
  obtain ⟨V₁, m₁, e₁, i₁, j₁, h₁, ⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hw₁, w₁⟩ := hs x
  obtain ⟨V₂, m₂, e₂, i₂, j₂, h₂, ⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩, hw₂, w₂⟩ := ht x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, i₁ + i₂, j₁ + j₂, by omega,
    ⟨a₁ * a₂, SetLike.mul_mem_graded ha₁ ha₂⟩, ⟨b₁ * b₂, SetLike.mul_mem_graded hb₁ hb₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩)
      (hw₂ ⟨y.1, y.2.2⟩), fun y ↦ ?_⟩
  ext
  exact congr($(w₁ ⟨y.1, y.2.1⟩).1 * $(w₂ ⟨y.1, y.2.2⟩).1).trans (Localization.mk_mul _ _ _ _)

/-- The values of a section of the structure sheaf form a section of `𝒪(0)`. -/
theorem isLocallyFraction_zeroEquiv {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s : (Proj 𝒜).ringCatSheaf.obj.obj U) :
    (isLocallyFraction 𝒜 0).pred fun x : U.unop ↦ degreePart.zeroEquiv (s.1 x) := by
  intro x
  obtain ⟨V, hxV, e, i, ⟨r, hr⟩, ⟨q, hq⟩, hw, w⟩ := s.2 x
  refine ⟨V, hxV, e, i, i, by simp, ⟨r, hr⟩, ⟨q, hq⟩, hw, fun y ↦ ?_⟩
  ext
  simp [w y, val_mk]

open ProjectiveSpectrum.StructureSheaf in
/-- The dependent functions into the fibres of `𝒪(m)` on `U` form a module over the sections of
the structure sheaf of `Proj 𝒜` on `U`, by pointwise multiplication. -/
instance modulePi (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, fiber 𝒜 m x.1) :=
  inferInstanceAs (Module ↥(sectionsSubring (𝒜 := 𝒜) U) _)

/-- Sections of the structure sheaf act on dependent functions into the fibres of `𝒪(m)`
pointwise. -/
@[simp]
theorem smul_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (c : (Proj 𝒜).ringCatSheaf.obj.obj U) (s : ∀ x : U.unop, fiber 𝒜 m x.1) (x : U.unop) :
    (c • s) x = c.1 x • s x :=
  rfl

namespace Sections

variable (m) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)

/-- The zero function is a section of `𝒪(m)`. -/
theorem zero_mem' : (isLocallyFraction 𝒜 m).pred (0 : ∀ x : U.unop, fiber 𝒜 m x.1) := by
  intro x
  obtain ⟨j, hj, b, hb, hbx⟩ := x.1.exists_homogeneous_notMem_of_le (-m).toNat
  refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 b, ⟨x.2, hbx⟩, Opens.infLELeft _ _,
    (j + m).toNat, j, by omega, 0, ⟨b, hb⟩, fun y ↦ y.2.2, fun _ ↦ ?_⟩
  ext
  simp [Localization.mk_zero]

variable {m U}

/-- The sum of two sections of `𝒪(m)` is a section of `𝒪(m)`. -/
theorem add_mem' {s t : ∀ x : U.unop, fiber 𝒜 m x.1} (hs : (isLocallyFraction 𝒜 m).pred s)
    (ht : (isLocallyFraction 𝒜 m).pred t) : (isLocallyFraction 𝒜 m).pred (s + t) := by
  intro x
  obtain ⟨V₁, m₁, e₁, i₁, j₁, h₁, ⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hw₁, w₁⟩ := hs x
  obtain ⟨V₂, m₂, e₂, i₂, j₂, h₂, ⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩, hw₂, w₂⟩ := ht x
  refine ⟨V₁ ⊓ V₂, ⟨m₁, m₂⟩, Opens.infLELeft _ _ ≫ e₁, j₁ + i₂, j₁ + j₂, by omega,
    ⟨b₁ * a₂ + b₂ * a₁, add_mem (SetLike.mul_mem_graded hb₁ ha₂) ?_⟩,
    ⟨b₁ * b₂, SetLike.mul_mem_graded hb₁ hb₂⟩,
    fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hw₁ ⟨y.1, y.2.1⟩)
      (hw₂ ⟨y.1, y.2.2⟩), fun y ↦ ?_⟩
  · rw [show j₁ + i₂ = j₂ + i₁ by omega]
    exact SetLike.mul_mem_graded hb₂ ha₁
  · ext
    exact congr($(w₁ ⟨y.1, y.2.1⟩).1 + $(w₂ ⟨y.1, y.2.2⟩).1).trans (Localization.add_mk _ _ _ _)

/-- A section of `𝒪(m)` multiplied by a section of the structure sheaf is a section of
`𝒪(m)`. -/
theorem smul_mem' (c : (Proj 𝒜).ringCatSheaf.obj.obj U) {s : ∀ x : U.unop, fiber 𝒜 m x.1}
    (hs : (isLocallyFraction 𝒜 m).pred s) : (isLocallyFraction 𝒜 m).pred (c • s) :=
  isLocallyFraction_mul (zero_add m) (isLocallyFraction_zeroEquiv c) hs

end Sections

variable (𝒜 m)

/-- The sections of the twisting sheaf `𝒪(m)` on an open set `U`: the dependent functions into
the fibres of `𝒪(m)` that are locally fractions, as a module over the sections of the structure
sheaf. -/
def sections (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Submodule ((Proj 𝒜).ringCatSheaf.obj.obj U) (∀ x : U.unop, fiber 𝒜 m x.1) where
  carrier := {s | (isLocallyFraction 𝒜 m).pred s}
  zero_mem' := Sections.zero_mem' m U
  add_mem' := Sections.add_mem'
  smul_mem' := Sections.smul_mem'

/-- The twisting sheaf `𝒪(m)`, valued in `Type`: the subsheaf of the sheaf of dependent
functions consisting of the local fractions. -/
def sheafInType : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 m)

/-- The sections of `𝒪(m)` form an abelian group. -/
instance addCommGroupSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 m).1.obj U) :=
  inferInstanceAs (AddCommGroup (sections 𝒜 m U))

/-- The twisting presheaf `𝒪(m)`, valued in abelian groups. -/
def presheafInAb : Presheaf Ab (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 m).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 m).1.map i
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- The sections of `𝒪(m)` over `U` form a module over the sections of the structure sheaf
over `U`. -/
instance modulePresheafInAbObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((presheafInAb 𝒜 m).obj U) :=
  inferInstanceAs (Module _ (sections 𝒜 m U))

/-- The `Ab`-valued twisting presheaf agrees with the `Type`-valued one after forgetting. -/
def presheafInAbCompForget : presheafInAb 𝒜 m ⋙ forget Ab ≅ (sheafInType 𝒜 m).1 :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)

/-- The presheaf `𝒪(m)` is a sheaf. -/
theorem isSheaf_presheafInAb : (presheafInAb 𝒜 m).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (presheafInAbCompForget 𝒜 m).symm (sheafInType 𝒜 m).property)

/-- The twisting presheaf `𝒪(m)` as a presheaf of modules over the structure sheaf of
`Proj 𝒜`. -/
def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (presheafInAb 𝒜 m) fun _ _ _ _ _ ↦ rfl

end ProjectiveSpectrum.Twist

end AlgebraicGeometry
