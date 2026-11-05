import Jacobian.AlgebraicGeometry.Curve.FiniteTraceSections
import Jacobian.AlgebraicGeometry.Modules.HomOfBasis
import Jacobian.AlgebraicGeometry.Modules.PushforwardHomAffine
import Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry

/-!
# Global differential traces along finite flat curve maps

The affine differential traces agree on restrictions and glue on the polynomial
chart basis of the projective line. The resulting module morphism has the
expected trace formula on every nonempty polynomial basic open.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace Polynomial

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))]

/-- `traceSections_restrict` for an open `W` which is equal to a basic open of `V`. -/
lemma traceSections_restrict_of_eq {V W : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (hfree) (hfin) (r : Γ(Y, V)) (hr : W = Y.basicOpen r)
    (hW : IsAffineOpen (f ⁻¹ᵁ W)) (hfree') (hfin') (hWV : W ≤ V)
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V)) :
    f.traceSections W hW hfree' hfin'
        ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE (f.preimage_mono hWV)).op ω) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE hWV).op
        (f.traceSections V hV' hfree hfin ω) := by
  subst hr
  exact traceSections_restrict hV hV' hfree hfin r hW hfree' hfin' ω

/-- **The trace of differentials on sections is compatible with restriction** between affine
opens `V₂ ⊆ V₁`: both sides agree on the opens which are basic in both `V₁` and `V₂`, and these
cover `V₂`. -/
lemma traceSections_restrict_of_le [IsAffineHom f] {V₁ V₂ : Y.Opens} (h₁ : IsAffineOpen V₁)
    (h₂ : IsAffineOpen V₂) (hle : V₂ ≤ V₁) (h₁' : IsAffineOpen (f ⁻¹ᵁ V₁))
    (h₂' : IsAffineOpen (f ⁻¹ᵁ V₂)) (hfree₁) (hfin₁) (hfree₂) (hfin₂)
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V₁)) :
    f.traceSections V₂ h₂' hfree₂ hfin₂
        ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE (f.preimage_mono hle)).op ω) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE hle).op
        (f.traceSections V₁ h₁' hfree₁ hfin₁ ω) := by
  choose r₁ r₂ hr hx using fun x : V₂ ↦ exists_basicOpen_le_affine_inter h₁ h₂ x.1
    ⟨hle x.2, x.2⟩
  have hW₂ (x : V₂) : Y.basicOpen (r₁ x) ≤ V₂ := (hr x).symm ▸ Y.basicOpen_le (r₂ x)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, (Y ↘ Spec (.of k)).relativeDifferentials.isSheaf⟩
    (fun x : V₂ ↦ Y.basicOpen (r₁ x)) V₂ (fun x ↦ homOfLE (hW₂ x))
    (fun x hx' ↦ Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩) _ _ fun x ↦ ?_
  have hW (x : V₂) : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen (r₁ x)) := (h₁.basicOpen (r₁ x)).preimage f
  have hff (x : V₂) := free_finite_basicOpen h₁ h₁' hfree₁ hfin₁ (r₁ x)
  change (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (hW₂ x)).op _ =
    (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (hW₂ x)).op _
  rw [← traceSections_restrict_of_eq h₂ h₂' hfree₂ hfin₂ (r₂ x) (hr x) (hW x) (hff x).1
      (hff x).2 (hW₂ x), Modules.presheaf_map_homOfLE_map_homOfLE,
    Modules.presheaf_map_homOfLE_map_homOfLE,
    ← traceSections_restrict_of_eq h₁ h₁' hfree₁ hfin₁ (r₁ x) rfl (hW x) (hff x).1 (hff x).2]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

open ProjectiveLine Modules

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]

/-- The differential traces of a finite flat map to the projective line glue globally. -/
theorem exists_differentialTrace (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))] [IsFinite morphism] [Flat morphism] :
    ∃ trace : (Modules.pushforward morphism).obj
        (source ↘ Spec (.of baseField)).relativeDifferentials ⟶
          (projectiveLineToSpec baseField).relativeDifferentials,
      ∀ (coordinate : Fin 2) (polynomial : baseField[X]) (nonzero : polynomial ≠ 0)
        (differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
          morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial)),
        trace.app (chartBasicOpen baseField coordinate polynomial) differential =
          morphism.traceSections _
            ((isAffineOpen_chartBasicOpen baseField coordinate polynomial).preimage morphism)
            (morphism.free_finite_chartBasicOpen coordinate polynomial).1
            (morphism.free_finite_chartBasicOpen coordinate polynomial).2 differential := by
  let basisOpen : (Σ _ : Fin 2, {polynomial : baseField[X] // polynomial ≠ 0}) →
      (projectiveLine baseField).Opens :=
    fun index ↦ chartBasicOpen baseField index.1 index.2.1
  have basis : Opens.IsBasis (Set.range basisOpen) := isBasis_chartBasicOpen baseField
  have covers (openSubset : (projectiveLine baseField).Opens) (point) (membership : point ∈ openSubset) :
      ∃ index, point ∈ basisOpen index ∧ basisOpen index ≤ openSubset := by
    obtain ⟨_, ⟨index, rfl⟩, pointMembership, contained⟩ :=
      (Opens.isBasis_iff_nbhd.1 basis) membership
    exact ⟨index, pointMembership, contained⟩
  have affine (index) : IsAffineOpen (basisOpen index) :=
    isAffineOpen_chartBasicOpen baseField index.1 index.2.1
  have affinePreimage (index) : IsAffineOpen (morphism ⁻¹ᵁ basisOpen index) :=
    (affine index).preimage morphism
  have finiteFree (index : Σ _ : Fin 2, {polynomial : baseField[X] // polynomial ≠ 0}) :=
    morphism.free_finite_chartBasicOpen index.1 index.2.1
  let localTrace (index) :
      Γ((Modules.pushforward morphism).obj (source ↘ Spec (.of baseField)).relativeDifferentials,
        basisOpen index) →+
          Γ((projectiveLineToSpec baseField).relativeDifferentials, basisOpen index) :=
    morphism.traceSections (basisOpen index) (affinePreimage index)
      (finiteFree index).1 (finiteFree index).2
  have compatible (index otherIndex) (contained : basisOpen otherIndex ≤ basisOpen index)
      (differential) :
      localTrace otherIndex
        (((Modules.pushforward morphism).obj
          (source ↘ Spec (.of baseField)).relativeDifferentials).presheaf.map
            (homOfLE contained).op differential) =
      (projectiveLineToSpec baseField).relativeDifferentials.presheaf.map
        (homOfLE contained).op (localTrace index differential) :=
    Hom.traceSections_restrict_of_le (affine index) (affine otherIndex) contained
      (affinePreimage index) (affinePreimage otherIndex) _ _ _ _ differential
  have linear (index) (scalar : Γ(projectiveLine baseField, basisOpen index)) (differential) :
      localTrace index (scalar • differential) = scalar • localTrace index differential :=
    (congrArg (localTrace index) (pushforward_smul_def morphism _ _ scalar differential)).trans
      (Hom.traceSections_smul (basisOpen index) (affinePreimage index)
        (finiteFree index).1 (finiteFree index).2 scalar differential)
  refine ⟨homOfBasis covers compatible linear, ?_⟩
  intro coordinate polynomial nonzero differential
  exact homOfBasis_app_basis covers compatible linear ⟨coordinate, polynomial, nonzero⟩ differential

end AlgebraicGeometry.Scheme
