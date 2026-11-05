import Jacobian.AlgebraicGeometry.Curve.SmoothSections
import Jacobian.RingTheory.Kaehler.TraceMap

/-!
# Traces of differential sections

For a morphism of schemes over a field, an affine inverse image with a finite
free ring of sections has a trace map on differentials. It is linear over the
sections of the target and commutes with restriction to basic opens, using the
localized basis of the finite free algebra.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

lemma specStructureMap_comp_app (V : Y.Opens) :
    (Y ↘ Spec (.of k)).specStructureMap V ≫ f.app V =
      (X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V) := by
  rw [specStructureMap, specStructureMap, Category.assoc, app_eq_appLE, appLE_comp_appLE]
  simp only [comp_over]

/-- The **trace of differentials on sections**: for `f⁻¹V` affine and `Γ(X, f⁻¹V)` finite free
over `Γ(Y, V)`, the map `Γ(Ω¹_{X/k}, f⁻¹V) → Γ(Ω¹_{Y/k}, V)`, `c da ↦ Tr(C · dA)`, where `A` and
`C` are the matrices of multiplication by `a` and `c` in a basis of `Γ(X, f⁻¹V)`. -/
def traceSections (V : Y.Opens) (hV : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) :
    Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V) →+
      Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
  letI := (f.app V).hom.toAlgebra
  letI : Algebra k Γ(Y, V) := ((Y ↘ Spec (.of k)).specStructureMap V).hom.toAlgebra
  letI : Algebra k Γ(X, f ⁻¹ᵁ V) :=
    ((X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V)).hom.toAlgebra
  haveI : IsScalarTower k Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := .of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (specStructureMap_comp_app f V)).symm
  letI : Module k Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    Module.compHom _ (algebraMap k Γ(Y, V))
  haveI : IsScalarTower k Γ(Y, V) Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    ⟨fun c r m ↦ by
      change (algebraMap k Γ(Y, V) c * r) • m = algebraMap k Γ(Y, V) c • r • m
      rw [mul_smul]⟩
  (KaehlerDifferential.traceLin
      ((Y ↘ Spec (.of k)).sectionsDerivation V rfl)).toAddMonoidHom.comp
    ((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV).symm.toAddMonoidHom

variable {f}

/-- The trace of differentials on sections is `Γ(Y, V)`-linear. -/
lemma traceSections_smul (V : Y.Opens) (hV : IsAffineOpen (f ⁻¹ᵁ V)) (hfree) (hfin)
    (r : Γ(Y, V)) (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V)) :
    f.traceSections V hV hfree hfin (f.app V r • ω) = r • f.traceSections V hV hfree hfin ω := by
  let := (f.app V).hom.toAlgebra
  let : Algebra k Γ(Y, V) := ((Y ↘ Spec (.of k)).specStructureMap V).hom.toAlgebra
  let : Algebra k Γ(X, f ⁻¹ᵁ V) :=
    ((X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower k Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := .of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (specStructureMap_comp_app f V)).symm
  let : Module k Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    Module.compHom _ (algebraMap k Γ(Y, V))
  have : IsScalarTower k Γ(Y, V) Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    ⟨fun c r m ↦ mul_smul (algebraMap k Γ(Y, V) c) r m⟩
  have h (ω') : f.traceSections V hV hfree hfin ω' =
      KaehlerDifferential.traceLin ((Y ↘ Spec (.of k)).sectionsDerivation V rfl)
        (((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV).symm ω') := rfl
  rw [h, h, LinearEquiv.map_smul]
  exact (congrArg _ (algebraMap_smul (M := Ω[Γ(X, f ⁻¹ᵁ V)⁄k]) Γ(X, f ⁻¹ᵁ V) r _)).trans
    (map_smul _ r _)

/-- For `V` and `f⁻¹V` affine, the restriction of a basis of `Γ(X, f⁻¹V)` over `Γ(Y, V)` is a basis
of `Γ(X, f⁻¹ D(r))` over `Γ(Y, D(r))`: both rings are localizations at `r`. -/
lemma exists_basis_basicOpen {V : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (r : Γ(Y, V)) {ι : Type*}
    (b : letI := (f.app V).hom.toAlgebra; Module.Basis ι Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) :
    letI := (f.app (Y.basicOpen r)).hom.toAlgebra
    ∃ b' : Module.Basis ι Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r),
      ∀ i, b' i = X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op (b i) := by
  let := (f.app V).hom.toAlgebra
  let := (f.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(Y, Y.basicOpen r) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app V ≫ X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (f.naturality _)).symm
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV.isLocalization_basicOpen r
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ V) (Submonoid.powers r))
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hV'.isLocalization_of_eq_basicOpen _ _ (f.preimage_basicOpen r)
  exact ⟨b.localizationLocalization Γ(Y, Y.basicOpen r) (Submonoid.powers r) _,
    b.localizationLocalization_apply _ _ _⟩

/-- Finiteness and freeness of `Γ(X, f⁻¹V)` over `Γ(Y, V)` pass to basic opens of `V`. -/
lemma free_finite_basicOpen {V : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
    (r : Γ(Y, V)) :
    (letI := (f.app (Y.basicOpen r)).hom.toAlgebra;
      Module.Free Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) ∧
    (letI := (f.app (Y.basicOpen r)).hom.toAlgebra;
      Module.Finite Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := by
  let := (f.app V).hom.toAlgebra
  obtain ⟨b', -⟩ := exists_basis_basicOpen hV hV' r (Module.Free.chooseBasis Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
  let := (f.app (Y.basicOpen r)).hom.toAlgebra
  exact ⟨.of_basis b', .of_basis b'⟩

/-- **The trace of differentials on sections is compatible with restriction to basic opens.** -/
lemma traceSections_restrict {V : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree) (hfin) (r : Γ(Y, V)) (hW : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r)) (hfree') (hfin')
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V)) :
    f.traceSections (Y.basicOpen r) hW hfree' hfin'
        ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op ω) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (Y.basicOpen_le r)).op
        (f.traceSections V hV' hfree hfin ω) := by
  let := (f.app V).hom.toAlgebra
  let : Algebra k Γ(Y, V) := ((Y ↘ Spec (.of k)).specStructureMap V).hom.toAlgebra
  let : Algebra k Γ(X, f ⁻¹ᵁ V) :=
    ((X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower k Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := .of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (specStructureMap_comp_app f V)).symm
  let : Module k Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    Module.compHom _ (algebraMap k Γ(Y, V))
  have : IsScalarTower k Γ(Y, V) Γ((Y ↘ Spec (.of k)).relativeDifferentials, V) :=
    ⟨fun c r m ↦ mul_smul (algebraMap k Γ(Y, V) c) r m⟩
  let := (f.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra k Γ(Y, Y.basicOpen r) :=
    ((Y ↘ Spec (.of k)).specStructureMap (Y.basicOpen r)).hom.toAlgebra
  let : Algebra k Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    ((X ↘ Spec (.of k)).specStructureMap (f ⁻¹ᵁ Y.basicOpen r)).hom.toAlgebra
  have : IsScalarTower k Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' <|
    (congrArg CommRingCat.Hom.hom (specStructureMap_comp_app f (Y.basicOpen r))).symm
  let : Module k Γ((Y ↘ Spec (.of k)).relativeDifferentials, Y.basicOpen r) :=
    Module.compHom _ (algebraMap k Γ(Y, Y.basicOpen r))
  have : IsScalarTower k Γ(Y, Y.basicOpen r)
      Γ((Y ↘ Spec (.of k)).relativeDifferentials, Y.basicOpen r) :=
    ⟨fun c s m ↦ mul_smul (algebraMap k Γ(Y, Y.basicOpen r) c) s m⟩
  have h (ω') : f.traceSections V hV' hfree hfin ω' =
      KaehlerDifferential.traceLin ((Y ↘ Spec (.of k)).sectionsDerivation V rfl)
        (((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV').symm ω') := rfl
  have h' (ω') : f.traceSections (Y.basicOpen r) hW hfree' hfin' ω' =
      KaehlerDifferential.traceLin ((Y ↘ Spec (.of k)).sectionsDerivation (Y.basicOpen r) rfl)
        (((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ Y.basicOpen r) rfl hW).symm ω') := rfl
  obtain ⟨b', hb'⟩ :=
    exists_basis_basicOpen hV hV' r (Module.Free.chooseBasis Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
  obtain ⟨η, rfl⟩ := ((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV').surjective ω
  rw [h, h', LinearEquiv.symm_apply_apply]
  have hη : η ∈ Submodule.span Γ(X, f ⁻¹ᵁ V)
      (Set.range (KaehlerDifferential.D k Γ(X, f ⁻¹ᵁ V))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  suffices H : ∀ c : Γ(X, f ⁻¹ᵁ V), KaehlerDifferential.traceLin
      ((Y ↘ Spec (.of k)).sectionsDerivation (Y.basicOpen r) rfl)
        (((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ Y.basicOpen r) rfl hW).symm
          ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
            (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op
            ((X ↘ Spec (.of k)).kaehlerSectionsEquiv (f ⁻¹ᵁ V) rfl hV' (c • η)))) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (Y.basicOpen_le r)).op
        (KaehlerDifferential.traceLin ((Y ↘ Spec (.of k)).sectionsDerivation V rfl) (c • η)) by
    simpa using H 1
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    intro c
    rw [LinearEquiv.map_smul, kaehlerSectionsEquiv_D, Scheme.Modules.map_smul, ← sectionsD_map,
      ← kaehlerSectionsEquiv_D _ _ rfl hW, ← LinearEquiv.map_smul, LinearEquiv.symm_apply_apply,
      KaehlerDifferential.traceLin_smul_D, KaehlerDifferential.traceLin_smul_D]
    refine Algebra.traceDeriv_map _ _ (Module.Free.chooseBasis Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) b'
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom
      (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom
      (fun s ↦ (ConcreteCategory.congr_hom (f.naturality _) s).symm) hb'
      ((Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom
      (fun s m ↦ Scheme.Modules.map_smul _ _ s m) (fun s ↦ ?_) a c
    rw [sectionsDerivation_apply, sectionsDerivation_apply]
    exact (Y ↘ Spec (.of k)).sectionsD_map (Y.basicOpen_le r) s
  | zero => simp
  | add x y _ _ hx hy =>
    intro c
    simp only [smul_add, map_add, hx, hy]
  | smul c' x _ hx =>
    intro c
    rw [smul_smul]
    exact hx _

end AlgebraicGeometry.Scheme.Hom
