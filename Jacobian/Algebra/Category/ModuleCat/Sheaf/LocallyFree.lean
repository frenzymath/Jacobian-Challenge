import Jacobian.Algebra.Category.ModuleCat.Sheaf.Invertible

/-!
# Finite locally free module sheaves

A finite locally free sheaf has finite local bases, with a rank that may vary
between members of a cover. Fixed rank and local trivializations give equivalent
descriptions. Rank one is exactly invertibility, and finite locally free sheaves
are finitely presented.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

section

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is *finite locally free of rank `r`* if it admits local generators data
which is locally free data (`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`) and whose
family of generators over each member of the covering is indexed by a type with exactly `r`
elements. Such a sheaf of modules is in particular locally free, hence quasi-coherent. -/
class IsFiniteLocallyFreeOfRank (M : SheafOfModules.{u} R) (r : ℕ) : Prop where
  exists_localGeneratorsData : ∃ q : LocalGeneratorsData.{u₁} M, ∃ _ : q.IsLocallyFreeData,
    ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

/-- A finite locally free sheaf of modules is locally free.

This cannot be an instance: the rank `r` does not occur in the goal `M.IsLocallyFree`, so
type-class synthesis has no way to determine it. -/
theorem IsFiniteLocallyFreeOfRank.isLocallyFree (M : SheafOfModules.{u} R)
    (r : ℕ) [h : M.IsFiniteLocallyFreeOfRank r] : M.IsLocallyFree :=
  have := h.exists_localGeneratorsData.choose_spec.choose
  ⟨_, this⟩

theorem IsFiniteLocallyFreeOfRank.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) {r : ℕ}
    [h : M.IsFiniteLocallyFreeOfRank r] : N.IsFiniteLocallyFreeOfRank r := by
  obtain ⟨q, hq, hr⟩ := h.exists_localGeneratorsData
  exact ⟨q.ofIso e, inferInstance, hr⟩

/-- A sheaf of modules is *finite locally free* if it admits local generators data which is
locally free data (`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`) with finitely many
generators over each member of the covering. Unlike `SheafOfModules.IsFiniteLocallyFreeOfRank`,
the rank may vary from one member of the covering to another. -/
class IsFiniteLocallyFree (M : SheafOfModules.{u} R) : Prop where
  exists_localGeneratorsData :
    ∃ q : LocalGeneratorsData.{u₁} M, q.IsLocallyFreeData ∧ q.IsFiniteType

/-- A finite locally free sheaf of modules is locally free, hence quasi-coherent. -/
instance (priority := 100) IsFiniteLocallyFree.isLocallyFree (M : SheafOfModules.{u} R)
    [h : M.IsFiniteLocallyFree] : M.IsLocallyFree :=
  have := h.exists_localGeneratorsData.choose_spec.1
  h.exists_localGeneratorsData.choose.isLocallyFree

variable (R) in
/-- The finite locally free sheaves of modules, as a property of objects. -/
abbrev isFiniteLocallyFree : ObjectProperty (SheafOfModules.{u} R) :=
  fun M ↦ M.IsFiniteLocallyFree

theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (M : SheafOfModules.{u} R) (r : ℕ)
    [h : M.IsFiniteLocallyFreeOfRank r] : M.IsFiniteLocallyFree := by
  obtain ⟨q, hq, hr⟩ := h.exists_localGeneratorsData
  exact ⟨q, hq, ⟨fun i ↦ ⟨Finite.of_equiv _ (hr i).some.symm⟩⟩⟩

theorem IsFiniteLocallyFree.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [h : M.IsFiniteLocallyFree] : N.IsFiniteLocallyFree := by
  obtain ⟨q, hq, hf⟩ := h.exists_localGeneratorsData
  refine ⟨q.ofIso e, inferInstance, ⟨fun i ↦ ?_⟩⟩
  have := hf.isFiniteType i
  exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType

instance (priority := 100) IsInvertible.isFiniteLocallyFree (M : SheafOfModules.{u} R)
    [h : M.IsInvertible] : M.IsFiniteLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertibleData
  refine ⟨q, inferInstance, ⟨fun i ↦ ⟨?_⟩⟩⟩
  have := (hq.nonempty_unique i).some
  infer_instance

/-- A sheaf of modules is invertible if and only if it is finite locally free of rank one. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one (M : SheafOfModules.{u} R) :
    M.IsInvertible ↔ M.IsFiniteLocallyFreeOfRank 1 := by
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨q, inferInstance, fun i ↦ ?_⟩, fun ⟨q, hq, hr⟩ ↦ ⟨q, ?_⟩⟩
  · have := (hq.nonempty_unique i).some
    exact ⟨Equiv.ofUnique _ _⟩
  · exact { toIsLocallyFreeData := hq, nonempty_unique i := ⟨(hr i).some.unique⟩ }


/-- A sheaf of modules is finite locally free of rank `r` if and only if it is isomorphic to the
free module of rank `r` over each object of a family covering the terminal object. -/
theorem isFiniteLocallyFreeOfRank_iff_exists_over_iso_free {M : SheafOfModules.{u} R} {r : ℕ} :
    M.IsFiniteLocallyFreeOfRank r ↔ ∃ (I : Type u₁) (X : I → C), J.CoversTop X ∧
      ∀ i, Nonempty (M.over (X i) ≅ free (ULift.{u} (Fin r))) := by
  constructor
  · rintro ⟨q, hq, hr⟩
    refine ⟨q.I, q.X, q.coversTop, fun i ↦ ⟨?_⟩⟩
    exact (asIso (q.generators i).π).symm ≪≫ freeFunctor.mapIso
      ((hr i).some.trans Equiv.ulift.symm).toIso
  · rintro ⟨I, X, hX, h⟩
    let q : M.LocalGeneratorsData :=
      { I := I
        X := X
        coversTop := hX
        generators i := (free.generatingSections _).ofEpi (h i).some.inv }
    have : q.IsLocallyFreeData := ⟨fun i ↦ by
      dsimp [q]
      rw [GeneratingSections.ofEpi_π]
      infer_instance⟩
    exact ⟨q, this, fun i ↦ ⟨Equiv.ulift⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf of modules which is isomorphic to a free module on a finite type over each object of
a family covering the terminal object is finite locally free. -/
theorem isFiniteLocallyFree_of_exists_over_iso_free {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X) (κ : I → Type u) [∀ i, Finite (κ i)]
    (h : ∀ i, Nonempty (M.over (X i) ≅ free (κ i))) : M.IsFiniteLocallyFree := by
  let q : M.LocalGeneratorsData :=
    { I := I
      X := X
      coversTop := hX
      generators i := (free.generatingSections _).ofEpi (h i).some.inv }
  have : q.IsLocallyFreeData := ⟨fun i ↦ by
    dsimp [q]
    rw [GeneratingSections.ofEpi_π]
    infer_instance⟩
  exact ⟨q, this, ⟨fun i ↦ ⟨inferInstanceAs (Finite (κ i))⟩⟩⟩


end

section

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A finite locally free sheaf of modules is of finite presentation: locally it is free on
finitely many generators, with no relations. -/
instance (priority := 100) IsFiniteLocallyFree.isFinitePresentation (M : SheafOfModules.{u} R)
    [h : M.IsFiniteLocallyFree] : M.IsFinitePresentation := by
  obtain ⟨q, hq, hf⟩ := h.exists_localGeneratorsData
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ?_⟩⟩
  have := hf.isFiniteType i
  exact { isFiniteType_generators := this
          isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift Empty))⟩ }


end

end SheafOfModules
