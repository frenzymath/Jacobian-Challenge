import Jacobian.AlgebraicGeometry.Modules.Limits
import Jacobian.Algebra.Homology.Cycles
import Jacobian.AlgebraicGeometry.Cohomology.LongExact
import Jacobian.AlgebraicGeometry.Cohomology.Pushforward
import Jacobian.AlgebraicGeometry.Cohomology.InjectiveFlasque

/-!
# Cohomology computed by acyclic resolutions

Dimension shifting through successive cycles computes sheaf cohomology as
the cohomology of global sections of an acyclic resolution. Conversely,
when a complex and its homology sheaves are acyclic, sections of its
homology are the homology of its sections. The identifications are natural.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance : Functor.PreservesZeroMorphisms (C := X.Modules)
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

section Delta

variable {S S' : ShortComplex X.Modules}

/-- **Naturality of the connecting map.** For a morphism `φ : S ⟶ S'` of short exact sequences,
`δ' ∘ H^n(φ₃) = H^{n+1}(φ₁) ∘ δ`. -/
lemma H.δ_naturality (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') (n : ℕ)
    (z : S.X₃.H n) :
    H.δ hS' n (H.map φ.τ₃ n z) = H.map φ.τ₁ (n + 1) (H.δ hS n z) := by
  have h : (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ.τ₁))
      (add_zero 1) =
      (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ.τ₃)).comp (shortExact_map_toSheaf hS').extClass
      (zero_add 1) :=
    have h₁ := shortExact_map_toSheaf hS
    have h₂ := shortExact_map_toSheaf hS'
    let φ' : S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf) ⟶ S'.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := (SheafOfModules.toSheaf.{u} X.ringCatSheaf).mapShortComplex.map φ
    ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ'
  rw [H.δ_apply, H.δ_apply, H.map_apply_eq_comp, H.map_apply_eq_comp,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, h]

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `H^{n+1}(M₂) = H^{n+2}(M₂) = 0`, the
connecting map `δ : H^{n+1}(M₃) ⟶ H^{n+2}(M₁)` is bijective. -/
lemma H.bijective_δ_of_subsingleton (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (S.X₂.H (n + 1))] [Subsingleton (S.X₂.H (n + 2))] :
    Function.Bijective (H.δ hS (n + 1)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ : x ∈ (H.map S.g (n + 1)).range := by
      rw [← H.ker_δ_eq_range_map_g]; exact hx
    rw [Subsingleton.elim z 0, map_zero]
  · have : y ∈ (H.map S.f (n + 2)).ker := by
      rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
    rw [H.ker_map_f_eq_range_δ] at this
    exact this

/-- The connecting map `δ : H^{n+1}(M₃) ≃+ H^{n+2}(M₁)` of a short exact sequence whose middle
term is acyclic in degrees `n + 1` and `n + 2`. -/
noncomputable def H.δAddEquiv (hS : S.ShortExact) (n : ℕ) [Subsingleton (S.X₂.H (n + 1))]
    [Subsingleton (S.X₂.H (n + 2))] : S.X₃.H (n + 1) ≃+ S.X₁.H (n + 2) :=
  AddEquiv.ofBijective (H.δ hS (n + 1)) (H.bijective_δ_of_subsingleton hS n)

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `H¹(M₂) = 0`, the connecting map
`δ : H⁰(M₃) ⟶ H¹(M₁)` is surjective. -/
lemma H.surjective_δ_zero (hS : S.ShortExact) [Subsingleton (S.X₂.H 1)] :
    Function.Surjective (H.δ hS 0) := fun y ↦ by
  have : y ∈ (H.map S.f (0 + 1)).ker := by
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_map_f_eq_range_δ] at this
  exact this

/-- **Left exactness of global sections.** For a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`, the sections of `M₂` killed by `g` are those coming from `M₁`. -/
lemma range_app_f_eq_ker_app_g (hS : S.ShortExact) :
    (S.f.app ⊤).hom.range = (S.g.app ⊤).hom.ker := by
  ext s
  have h := fun x : S.X₂.H 0 ↦ SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f hS 0) x
  constructor
  · rintro ⟨t, rfl⟩
    rw [AddMonoidHom.mem_ker, ← ConcreteCategory.comp_apply, ← Hom.comp_app, S.zero]
    rfl
  · intro hs
    obtain ⟨t, ht⟩ := (h ((H.zeroLinearEquiv _).symm s)).1 (by
      rw [AddMonoidHom.mem_ker]
      refine (H.zeroLinearEquiv _).injective ?_
      rw [H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply, map_zero]
      exact hs)
    refine ⟨H.zeroLinearEquiv _ t, ?_⟩
    have := H.zeroLinearEquiv_map S.f t
    rw [ht, LinearEquiv.apply_symm_apply] at this
    exact this.symm

/-- For a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `H¹(M₁) = 0`, every global section
of `M₃` lifts to `M₂`. -/
lemma surjective_app_g_of_subsingleton (hS : S.ShortExact) [Subsingleton (S.X₁.H 1)] :
    Function.Surjective (S.g.app ⊤).hom := fun s ↦ by
  have hs : (H.zeroLinearEquiv _).symm s ∈ (H.δ hS 0).ker := by
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_δ_eq_range_map_g] at hs
  obtain ⟨t, ht⟩ := hs
  refine ⟨H.zeroLinearEquiv _ t, ?_⟩
  have := H.zeroLinearEquiv_map S.g t
  rw [ht, LinearEquiv.apply_symm_apply] at this
  exact this.symm

end Delta

/-- An isomorphism of `𝒪_X`-modules induces an additive isomorphism on cohomology. -/
noncomputable def H.mapAddEquiv {M N : X.Modules} (e : M ≅ N) (n : ℕ) : M.H n ≃+ N.H n :=
  (H.mapLinearEquiv e n).toAddEquiv

section Shift

variable (K : CochainComplex X.Modules ℕ) (hK : ∀ j, K.ExactAt (j + 1))
  (hacyc : ∀ j m, Subsingleton ((K.X j).H (m + 1)))

include hK in
/-- The short exact sequence `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0` of cycles of `K`. -/
lemma shortExact_cyclesShortComplex (k : ℕ) : (K.cyclesShortComplex k (k + 1)).ShortExact :=
  (hK k).shortExact_cyclesShortComplex rfl

include hK hacyc in
/-- **Dimension shifting.** For a complex `K` exact in positive degrees whose terms are acyclic,
`H^{m+1}(X, Zᵏ) ≅ H¹(X, Zᵏ⁺ᵐ)`, the inverse of a composite of connecting maps of the sequences
`0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0`. -/
noncomputable def H.cyclesShiftAddEquiv : ∀ (m k : ℕ), (K.cycles k).H (m + 1) ≃+
    (K.cycles (k + m)).H 1
  | 0, _ => AddEquiv.refl _
  | m + 1, k =>
    have : Subsingleton ((K.cyclesShortComplex k (k + 1)).X₂.H (m + 1)) := hacyc k m
    have : Subsingleton ((K.cyclesShortComplex k (k + 1)).X₂.H (m + 2)) := hacyc k (m + 1)
    (H.δAddEquiv (shortExact_cyclesShortComplex K hK k) m).symm.trans
      ((H.cyclesShiftAddEquiv m (k + 1)).trans
        (H.mapAddEquiv (eqToIso (by rw [Nat.add_assoc, Nat.add_comm 1 m])) 1))

include hK in
/-- The surjection `Γ(X, Zⁿ⁺¹) ⟶ H¹(X, Zⁿ)` of the sequence `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Zⁿ⁺¹ ⟶ 0`: the
connecting map, which is surjective as `H¹(X, Kⁿ) = 0`, with kernel the sections coming from
`Kⁿ`. -/
noncomputable def H.cyclesδZero (n : ℕ) : Γ(K.cycles (n + 1), ⊤) →+ (K.cycles n).H 1 :=
  (H.δ (shortExact_cyclesShortComplex K hK n) 0).comp
    (H.zeroLinearEquiv (K.cycles (n + 1))).symm.toAddMonoidHom

include hacyc in
lemma H.surjective_cyclesδZero (n : ℕ) : Function.Surjective (H.cyclesδZero K hK n) := by
  have : Subsingleton ((K.cyclesShortComplex n (n + 1)).X₂.H 1) := hacyc n 0
  exact (H.surjective_δ_zero (shortExact_cyclesShortComplex K hK n)).comp
    (H.zeroLinearEquiv (K.cycles (n + 1))).symm.surjective

lemma H.ker_cyclesδZero (n : ℕ) :
    (H.cyclesδZero K hK n).ker =
      ((K.toCycles n (n + 1)).app ⊤).hom.range := by
  ext s
  change H.δ (shortExact_cyclesShortComplex K hK n) 0 ((H.zeroLinearEquiv _).symm s) = 0 ↔ _
  rw [← AddMonoidHom.mem_ker, H.ker_δ_eq_range_map_g]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨H.zeroLinearEquiv _ y, ?_⟩
    have := H.zeroLinearEquiv_map (K.toCycles n (n + 1)) y
    change H.zeroLinearEquiv _ (H.map (K.cyclesShortComplex n (n + 1)).g 0 y) = _ at this
    rw [hy] at this
    simpa using this.symm
  · rintro ⟨y, rfl⟩
    refine ⟨(H.zeroLinearEquiv _).symm y, (H.zeroLinearEquiv _).injective ?_⟩
    change H.zeroLinearEquiv _ (H.map (K.toCycles n (n + 1)) 0 _) = _
    rw [H.zeroLinearEquiv_map]
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- `H¹(X, Zⁿ) ≅ Γ(X, Zⁿ⁺¹) / Γ(X, Kⁿ)` for a complex `K` exact in positive degrees with
acyclic terms. -/
noncomputable def H.cyclesOneAddEquiv (n : ℕ) :
    (K.cycles n).H 1 ≃+ Γ(K.cycles (n + 1), ⊤) ⧸
      ((K.toCycles n (n + 1)).app ⊤).hom.range :=
  ((QuotientAddGroup.quotientAddEquivOfEq (H.ker_cyclesδZero K hK n)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (H.surjective_cyclesδZero K hK hacyc n))).symm

/-- **Cohomology computed by an acyclic resolution.** For a complex `K` exact in positive
degrees with acyclic terms, `H^{n+1}(X, Z⁰) ≅ Γ(X, Zⁿ⁺¹) / Γ(X, Kⁿ)`: the cohomology of `Z⁰`,
the module resolved by `K`, is the cohomology of the complex of global sections of `K`. -/
noncomputable def H.cyclesZeroSuccAddEquiv (n : ℕ) :
    (K.cycles 0).H (n + 1) ≃+ Γ(K.cycles (n + 1), ⊤) ⧸
      ((K.toCycles n (n + 1)).app ⊤).hom.range :=
  ((H.cyclesShiftAddEquiv K hK hacyc n 0).trans
    (H.mapAddEquiv (eqToIso (by rw [Nat.zero_add])) 1)).trans
    (H.cyclesOneAddEquiv K hK hacyc n)

end Shift
/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `Hⁿ(M₁) = Hⁿ(M₃) = 0`, also
`Hⁿ(M₂) = 0`. -/
lemma subsingleton_H_X₂_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (S.X₁.H n)] [Subsingleton (S.X₃.H n)] : Subsingleton (S.X₂.H n) := by
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : S.X₂.H n, z = 0 by rw [h x, h y]
  intro z
  have hz : z ∈ (H.map S.g n).ker := by rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_map_g_eq_range_map_f hS] at hz
  obtain ⟨w, rfl⟩ := hz
  rw [Subsingleton.elim w 0, map_zero]

section CohomologySheaves

variable (L : CochainComplex X.Modules ℕ)

/-- The short complex `Zᵠ ⟶ Lᵠ ⟶ Bᵠ⁺¹` of cycles, terms and boundaries of a complex `L`. -/
noncomputable def cyclesBoundariesShortComplex (q : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (L.iCycles q) (factorThruImage (L.toCycles q (q + 1))) (by
    rw [← cancel_mono (Limits.image.ι (L.toCycles q (q + 1))), Category.assoc, Limits.image.fac,
      ← cancel_mono (L.iCycles (q + 1)), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp, zero_comp])

/-- The sequence `0 ⟶ Zᵠ ⟶ Lᵠ ⟶ Bᵠ⁺¹ ⟶ 0` is short exact. -/
lemma shortExact_cyclesBoundariesShortComplex (q : ℕ) :
    (cyclesBoundariesShortComplex L q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (L.iCycles q)))
    (inferInstanceAs (Epi (factorThruImage _)))
  let φ : cyclesBoundariesShortComplex L q ⟶ ShortComplex.mk _ _ (L.iCycles_d q (q + 1)) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Limits.image.ι (L.toCycles q (q + 1)) ≫ L.iCycles (q + 1)
      comm₂₃ := by simp [cyclesBoundariesShortComplex] }
  have : Mono φ.τ₃ := mono_comp _ _
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ (L.cyclesIsKernel q (q + 1) (by simp))

/-- The short complex `Bᵠ⁺¹ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹` of boundaries, cycles and cohomology of `L`. -/
noncomputable def boundariesHomologyShortComplex (q : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (Limits.image.ι (L.toCycles q (q + 1))) (L.homologyπ (q + 1)) (by
    rw [← cancel_epi (factorThruImage (L.toCycles q (q + 1))), comp_zero, ← Category.assoc,
      Limits.image.fac, HomologicalComplex.toCycles_comp_homologyπ])

/-- The sequence `0 ⟶ Bᵠ⁺¹ ⟶ Zᵠ⁺¹ ⟶ Hᵠ⁺¹ ⟶ 0` is short exact. -/
lemma shortExact_boundariesHomologyShortComplex (q : ℕ) :
    (boundariesHomologyShortComplex L q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (Limits.image.ι _)))
    (inferInstanceAs (Epi (L.homologyπ (q + 1))))
  let φ : ShortComplex.mk _ _ (L.toCycles_comp_homologyπ q (q + 1)) ⟶
      boundariesHomologyShortComplex L q :=
    { τ₁ := factorThruImage (L.toCycles q (q + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [boundariesHomologyShortComplex] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (factorThruImage _))
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_g_is_cokernel _ (L.homologyIsCokernel q (q + 1) (by simp))

variable (hL : ∀ j m, Subsingleton ((L.X j).H (m + 1)))
  (hH : ∀ q m, Subsingleton ((L.homology q).H (m + 1)))

include hL in
/-- If the terms `Lʲ` and the cycles `Zʲ` of `L` are acyclic, then so is the image `Bʲ⁺¹` of the
differential `Lʲ ⟶ Zʲ⁺¹`, by the sequence `0 ⟶ Zʲ ⟶ Lʲ ⟶ Bʲ⁺¹ ⟶ 0`. -/
lemma subsingleton_H_image (j : ℕ) (hZ : ∀ m, Subsingleton ((L.cycles j).H (m + 1))) (m : ℕ) :
    Subsingleton ((Limits.image (L.toCycles j (j + 1))).H (m + 1)) := by
  have hS := shortExact_cyclesBoundariesShortComplex L j
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : (cyclesBoundariesShortComplex L j).X₃.H (m + 1), z = 0 by rw [h x, h y]
  intro z
  have hz : z ∈ (H.δ hS (m + 1)).ker := by
    have : Subsingleton ((cyclesBoundariesShortComplex L j).X₁.H (m + 1 + 1)) := hZ (m + 1)
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _
  rw [H.ker_δ_eq_range_map_g] at hz
  obtain ⟨w, rfl⟩ := hz
  have : Subsingleton ((cyclesBoundariesShortComplex L j).X₂.H (m + 1)) := hL j m
  rw [Subsingleton.elim w 0, map_zero]

include hL hH in
/-- If the terms and the cohomology sheaves of `L` are acyclic, so are its cycles `Zʲ`: by
induction on `j`, using `0 ⟶ Bʲ⁺¹ ⟶ Zʲ⁺¹ ⟶ Hʲ⁺¹ ⟶ 0`. -/
lemma subsingleton_H_cycles : ∀ j m, Subsingleton ((L.cycles j).H (m + 1))
  | 0, m => by
    have := L.isIso_homologyπ 0 0 (by simp) (by simp)
    have := hH 0 m
    exact (H.mapLinearEquiv (asIso (L.homologyπ 0)) (m + 1)).injective.subsingleton
  | j + 1, m => by
    have : Subsingleton ((boundariesHomologyShortComplex L j).X₁.H (m + 1)) :=
      subsingleton_H_image L hL j (subsingleton_H_cycles j) m
    have : Subsingleton ((boundariesHomologyShortComplex L j).X₃.H (m + 1)) := hH (j + 1) m
    exact subsingleton_H_X₂_of_shortExact (shortExact_boundariesHomologyShortComplex L j) (m + 1)

include hL hH in
/-- **Sections of the cohomology sheaves of a complex.** If the terms and the cohomology sheaves
of a complex `L` of `𝒪_X`-modules are acyclic, then `Γ(X, Hᵠ⁺¹(L)) ≅ Γ(X, Zᵠ⁺¹) / Γ(X, Lᵠ)`:
global sections commute with the cohomology of `L`. -/
lemma surjective_app_homologyπ (q : ℕ) : Function.Surjective ((L.homologyπ (q + 1)).app ⊤).hom :=
  have : Subsingleton ((boundariesHomologyShortComplex L q).X₁.H 1) :=
    subsingleton_H_image L hL q (subsingleton_H_cycles L hL hH q) 0
  surjective_app_g_of_subsingleton (shortExact_boundariesHomologyShortComplex L q)

include hL hH in
lemma ker_app_homologyπ (q : ℕ) :
    ((L.homologyπ (q + 1)).app ⊤).hom.ker = ((L.toCycles q (q + 1)).app ⊤).hom.range := by
  refine (range_app_f_eq_ker_app_g (shortExact_boundariesHomologyShortComplex L q)).symm.trans ?_
  have : Subsingleton ((cyclesBoundariesShortComplex L q).X₁.H 1) :=
    subsingleton_H_cycles L hL hH q 0
  have hsurj := surjective_app_g_of_subsingleton (shortExact_cyclesBoundariesShortComplex L q)
  change ((Limits.image.ι (L.toCycles q (q + 1))).app ⊤).hom.range = _
  conv_rhs => rw [← Limits.image.fac (L.toCycles q (q + 1))]
  have hsurj' : Function.Surjective ((factorThruImage (L.toCycles q (q + 1))).app ⊤).hom := hsurj
  rw [Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.range_comp,
    AddMonoidHom.range_eq_top.mpr hsurj', ← AddMonoidHom.range_eq_map]

/-- `Γ(X, Hᵠ⁺¹(L)) ≅ Γ(X, Zᵠ⁺¹) / Γ(X, Lᵠ)` when the terms and the cohomology sheaves of `L` are
acyclic. -/
noncomputable def homologySectionsAddEquiv (q : ℕ) :
    Γ(L.homology (q + 1), ⊤) ≃+ Γ(L.cycles (q + 1), ⊤) ⧸
      ((L.toCycles q (q + 1)).app ⊤).hom.range :=
  ((QuotientAddGroup.quotientAddEquivOfEq (ker_app_homologyπ L hL hH q)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_app_homologyπ L hL hH q))).symm
end CohomologySheaves
/-- The sections of the cycles `Zⁿ⁺¹` of a complex `K` are the global sections of `Kⁿ⁺¹` killed
by the differential. -/
lemma range_app_iCycles (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    ((K.iCycles (n + 1)).app ⊤).hom.range = ((K.d (n + 1) (n + 2)).app ⊤).hom.ker := by
  refine (range_app_f_eq_ker_app_g (shortExact_cyclesBoundariesShortComplex K (n + 1))).trans ?_
  have hd : K.d (n + 1) (n + 2) = factorThruImage (K.toCycles (n + 1) (n + 2)) ≫
      (Limits.image.ι (K.toCycles (n + 1) (n + 2)) ≫ K.iCycles (n + 2)) := by
    rw [← Category.assoc, Limits.image.fac, HomologicalComplex.toCycles_i]
  have : Mono (Limits.image.ι (K.toCycles (n + 1) (n + 2)) ≫ K.iCycles (n + 2)) := mono_comp _ _
  rw [hd, Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.ker_comp_of_injective _ _ (injective_app_of_mono _)]
  rfl
variable (L : CochainComplex X.Modules ℕ)

/-- The cocycles `ker(Γ(Lⁿ⁺¹) ⟶ Γ(Lⁿ⁺²))` of the complex of global sections of `L`. -/
noncomputable abbrev sectionsCycles (n : ℕ) : AddSubgroup Γ(L.X (n + 1), ⊤) :=
  ((L.d (n + 1) (n + 2)).app ⊤).hom.ker

/-- The coboundaries `im(Γ(Lⁿ) ⟶ Γ(Lⁿ⁺¹))` among the cocycles of the complex of global sections of
`L`. -/
noncomputable abbrev sectionsBoundaries (n : ℕ) : AddSubgroup (sectionsCycles L n) :=
  ((L.d n (n + 1)).app ⊤).hom.range.addSubgroupOf (sectionsCycles L n)

/-- `Γ(X, Zⁿ⁺¹) / Γ(X, Lⁿ) ≅ ker Γ(d) / im Γ(d)`: the cycles of `L` have as sections the cocycles of
the complex of global sections. -/
noncomputable def cyclesQuotientAddEquiv (n : ℕ) :
    Γ(L.cycles (n + 1), ⊤) ⧸ ((L.toCycles n (n + 1)).app ⊤).hom.range ≃+
      sectionsCycles L n ⧸ sectionsBoundaries L n :=
  QuotientAddGroup.congr _ _
    ((AddMonoidHom.ofInjective (injective_app_of_mono (L.iCycles (n + 1)))).trans
      (AddEquiv.addSubgroupCongr (range_app_iCycles L n))) (by
    ext ⟨x, hx⟩
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, hz⟩
      refine ⟨z, ?_⟩
      have := congrArg Subtype.val hz
      refine Eq.trans ?_ this
      change _ = ((L.toCycles n (n + 1) ≫ L.iCycles (n + 1)).app ⊤) z
      rw [HomologicalComplex.toCycles_i]
    · rintro ⟨z, hz⟩
      refine ⟨_, ⟨z, rfl⟩, Subtype.ext ?_⟩
      change ((L.toCycles n (n + 1) ≫ L.iCycles (n + 1)).app ⊤) z = x
      rw [HomologicalComplex.toCycles_i]
      exact hz)
section Naturality

variable {K K' : CochainComplex X.Modules ℕ} (ψ : K ⟶ K')

/-- A chain map `ψ : K ⟶ K'` induces a morphism of the sequences `0 ⟶ Zᵏ ⟶ Kᵏ ⟶ Zᵏ⁺¹ ⟶ 0`. -/
@[simps]
noncomputable def cyclesShortComplexMap (k : ℕ) :
    K.cyclesShortComplex k (k + 1) ⟶ K'.cyclesShortComplex k (k + 1) where
  τ₁ := HomologicalComplex.cyclesMap ψ k
  τ₂ := ψ.f k
  τ₃ := HomologicalComplex.cyclesMap ψ (k + 1)
  comm₁₂ := by simp
  comm₂₃ := by
    rw [← cancel_mono (K'.iCycles (k + 1))]
    simp

variable (hK : ∀ j, K.ExactAt (j + 1)) (hacyc : ∀ j m, Subsingleton ((K.X j).H (m + 1)))
  (hK' : ∀ j, K'.ExactAt (j + 1)) (hacyc' : ∀ j m, Subsingleton ((K'.X j).H (m + 1)))

include hK hacyc hK' hacyc' in
/-- **Naturality of dimension shifting** in the complex. -/
lemma H.cyclesShiftAddEquiv_naturality : ∀ (m k : ℕ) (x : (K.cycles k).H (m + 1)),
    H.cyclesShiftAddEquiv K' hK' hacyc' m k
        (H.map (HomologicalComplex.cyclesMap ψ k) (m + 1) x) =
      H.map (HomologicalComplex.cyclesMap ψ (k + m)) 1 (H.cyclesShiftAddEquiv K hK hacyc m k x)
  | 0, _, _ => rfl
  | m + 1, k, x => by
    have : Subsingleton ((K.cyclesShortComplex k (k + 1)).X₂.H (m + 1)) := hacyc k m
    have : Subsingleton ((K.cyclesShortComplex k (k + 1)).X₂.H (m + 2)) := hacyc k (m + 1)
    have : Subsingleton ((K'.cyclesShortComplex k (k + 1)).X₂.H (m + 1)) := hacyc' k m
    have : Subsingleton ((K'.cyclesShortComplex k (k + 1)).X₂.H (m + 2)) := hacyc' k (m + 1)
    set y := (H.δAddEquiv (shortExact_cyclesShortComplex K hK k) m).symm x with hy
    have hx : H.δ (shortExact_cyclesShortComplex K hK k) (m + 1) y = x :=
      (H.δAddEquiv (shortExact_cyclesShortComplex K hK k) m).apply_symm_apply x
    have hδ : (H.δAddEquiv (shortExact_cyclesShortComplex K' hK' k) m).symm
        (H.map (HomologicalComplex.cyclesMap ψ k) (m + 2) x) =
        H.map (HomologicalComplex.cyclesMap ψ (k + 1)) (m + 1) y := by
      rw [AddEquiv.symm_apply_eq, ← hx]
      exact (H.δ_naturality (shortExact_cyclesShortComplex K hK k)
        (shortExact_cyclesShortComplex K' hK' k) (cyclesShortComplexMap ψ k) (m + 1) y).symm
    change H.map _ 1 (H.cyclesShiftAddEquiv K' hK' hacyc' m (k + 1)
        ((H.δAddEquiv (shortExact_cyclesShortComplex K' hK' k) m).symm
          (H.map (HomologicalComplex.cyclesMap ψ k) (m + 2) x))) =
      H.map _ 1 (H.map _ 1 (H.cyclesShiftAddEquiv K hK hacyc m (k + 1) y))
    rw [hδ, H.cyclesShiftAddEquiv_naturality m (k + 1) y, ← H.map_comp_apply,
      ← H.map_comp_apply]
    congr 1
    exact congrArg (H.map · 1)
      (HomologicalComplex.eqToHom_comp_cyclesMap ψ (a := k + 1 + m) (b := k + (m + 1))
        (by omega)).symm

lemma range_app_toCycles_le_comap (n : ℕ) :
    ((K.toCycles n (n + 1)).app ⊤).hom.range ≤
      (((K'.toCycles n (n + 1)).app ⊤).hom.range).comap
        ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom := by
  rintro _ ⟨z, rfl⟩
  refine ⟨(ψ.f n).app ⊤ z, ?_⟩
  change ((ψ.f n ≫ K'.toCycles n (n + 1)).app ⊤) z =
    ((K.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤) z
  rw [HomologicalComplex.toCycles_cyclesMap]

include hK hacyc in
lemma H.cyclesOneAddEquiv_cyclesδZero (n : ℕ) (s : Γ(K.cycles (n + 1), ⊤)) :
    H.cyclesOneAddEquiv K hK hacyc n (H.cyclesδZero K hK n s) = QuotientAddGroup.mk s := by
  rw [H.cyclesOneAddEquiv, AddEquiv.symm_apply_eq, AddEquiv.trans_apply]
  exact (QuotientAddGroup.kerLift_mk (H.cyclesδZero K hK n) s).symm

lemma H.map_cyclesδZero (n : ℕ) (s : Γ(K.cycles (n + 1), ⊤)) :
    H.map (HomologicalComplex.cyclesMap ψ n) 1 (H.cyclesδZero K hK n s) =
      H.cyclesδZero K' hK' n ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤ s) := by
  have h0 : H.map (HomologicalComplex.cyclesMap ψ (n + 1)) 0 ((H.zeroLinearEquiv _).symm s) =
      (H.zeroLinearEquiv _).symm ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤ s) := by
    rw [LinearEquiv.eq_symm_apply, H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply]
  have := H.δ_naturality (shortExact_cyclesShortComplex K hK n)
    (shortExact_cyclesShortComplex K' hK' n) (cyclesShortComplexMap ψ n) 0
    ((H.zeroLinearEquiv _).symm s)
  rw [cyclesShortComplexMap_τ₃, cyclesShortComplexMap_τ₁] at this
  erw [h0] at this
  exact this.symm

include hK hacyc hK' hacyc' in
/-- **Naturality of the cohomology computed by an acyclic resolution.** -/
lemma H.cyclesZeroSuccAddEquiv_naturality (n : ℕ) (w : (K.cycles 0).H (n + 1)) :
    H.cyclesZeroSuccAddEquiv K' hK' hacyc' n
        (H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1) w) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) (H.cyclesZeroSuccAddEquiv K hK hacyc n w) := by
  set v : (K.cycles n).H 1 :=
    H.mapAddEquiv (eqToIso (by rw [Nat.zero_add])) 1 (H.cyclesShiftAddEquiv K hK hacyc n 0 w)
    with hv
  obtain ⟨s, hs⟩ := H.surjective_cyclesδZero K hK hacyc n v
  have hw : H.cyclesZeroSuccAddEquiv K hK hacyc n w = QuotientAddGroup.mk s := by
    change H.cyclesOneAddEquiv K hK hacyc n v = _
    rw [← hs, H.cyclesOneAddEquiv_cyclesδZero]
  rw [hw, QuotientAddGroup.map_mk]
  change H.cyclesOneAddEquiv K' hK' hacyc' n (H.map _ 1 (H.cyclesShiftAddEquiv K' hK' hacyc' n 0
    (H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1) w))) = _
  rw [H.cyclesShiftAddEquiv_naturality ψ hK hacyc hK' hacyc', ← H.map_comp_apply, eqToIso.hom,
    ← HomologicalComplex.eqToHom_comp_cyclesMap ψ (a := 0 + n) (b := n) (by omega),
    H.map_comp_apply]
  change H.cyclesOneAddEquiv K' hK' hacyc' n (H.map (HomologicalComplex.cyclesMap ψ n) 1 v) = _
  rw [← hs, H.map_cyclesδZero ψ hK hK', H.cyclesOneAddEquiv_cyclesδZero]


include hK hacyc hK' hacyc' in
lemma H.cyclesZeroSuccAddEquiv_naturality_symm (n : ℕ)
    (c : Γ(K.cycles (n + 1), ⊤) ⧸ ((K.toCycles n (n + 1)).app ⊤).hom.range) :
    (H.cyclesZeroSuccAddEquiv K' hK' hacyc' n).symm
        (QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
          (range_app_toCycles_le_comap ψ n) c) =
      H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1)
        ((H.cyclesZeroSuccAddEquiv K hK hacyc n).symm c) := by
  rw [AddEquiv.symm_apply_eq, H.cyclesZeroSuccAddEquiv_naturality ψ hK hacyc hK' hacyc',
    AddEquiv.apply_symm_apply]

end Naturality
section NaturalitySections

variable {L L' : CochainComplex X.Modules ℕ} (χ : L ⟶ L')
  (hL : ∀ j m, Subsingleton ((L.X j).H (m + 1)))
  (hH : ∀ q m, Subsingleton ((L.homology q).H (m + 1)))
  (hL' : ∀ j m, Subsingleton ((L'.X j).H (m + 1)))
  (hH' : ∀ q m, Subsingleton ((L'.homology q).H (m + 1)))

lemma homologySectionsAddEquiv_homologyπ (q : ℕ) (z : Γ(L.cycles (q + 1), ⊤)) :
    homologySectionsAddEquiv L hL hH q ((L.homologyπ (q + 1)).app ⊤ z) = QuotientAddGroup.mk z := by
  rw [homologySectionsAddEquiv, AddEquiv.symm_apply_eq, AddEquiv.trans_apply]
  exact (QuotientAddGroup.kerLift_mk _ z).symm

/-- `Γ(X, Hᵠ⁺¹(L)) ≅ Γ(X, Zᵠ⁺¹) / Γ(X, Lᵠ)` is natural in the complex `L`. -/
lemma homologySectionsAddEquiv_naturality (q : ℕ) (y : Γ(L.homology (q + 1), ⊤)) :
    homologySectionsAddEquiv L' hL' hH' q ((HomologicalComplex.homologyMap χ (q + 1)).app ⊤ y) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap χ (q + 1)).app ⊤).hom
        (range_app_toCycles_le_comap χ q) (homologySectionsAddEquiv L hL hH q y) := by
  obtain ⟨z, rfl⟩ := surjective_app_homologyπ L hL hH q y
  rw [homologySectionsAddEquiv_homologyπ, QuotientAddGroup.map_mk]
  have h : ((HomologicalComplex.homologyMap χ (q + 1)).app ⊤) (((L.homologyπ (q + 1)).app ⊤) z) =
      ((L'.homologyπ (q + 1)).app ⊤) (((HomologicalComplex.cyclesMap χ (q + 1)).app ⊤) z) := by
    change ((L.homologyπ (q + 1) ≫ HomologicalComplex.homologyMap χ (q + 1)).app ⊤) z =
      ((HomologicalComplex.cyclesMap χ (q + 1) ≫ L'.homologyπ (q + 1)).app ⊤) z
    rw [HomologicalComplex.homologyπ_naturality]
  rw [h, homologySectionsAddEquiv_homologyπ]

/-- A chain map induces a map on the cocycles of the complexes of global sections. -/
noncomputable def sectionsCyclesMap (n : ℕ) : sectionsCycles L n →+ sectionsCycles L' n :=
  (((χ.f (n + 1)).app ⊤).hom.comp (sectionsCycles L n).subtype).codRestrict _ fun x ↦ by
    obtain ⟨x, hx⟩ := x
    change ((χ.f (n + 1) ≫ L'.d (n + 1) (n + 2)).app ⊤) x = 0
    rw [AddMonoidHom.mem_ker] at hx
    rw [χ.comm, Hom.comp_app, ConcreteCategory.comp_apply]
    erw [hx, map_zero]

lemma sectionsBoundaries_le_comap (n : ℕ) :
    sectionsBoundaries L n ≤ (sectionsBoundaries L' n).comap (sectionsCyclesMap χ n) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨(χ.f n).app ⊤ y, ?_⟩
  change ((χ.f n ≫ L'.d n (n + 1)).app ⊤) y = ((χ.f (n + 1)).app ⊤) x
  rw [χ.comm, Hom.comp_app, ConcreteCategory.comp_apply]
  erw [hy]
  rfl

/-- `Γ(X, Zⁿ⁺¹) / Γ(X, Lⁿ) ≅ ker Γ(d) / im Γ(d)` is natural in the complex `L`. -/
lemma cyclesQuotientAddEquiv_naturality (n : ℕ)
    (a : Γ(L.cycles (n + 1), ⊤) ⧸ ((L.toCycles n (n + 1)).app ⊤).hom.range) :
    cyclesQuotientAddEquiv L' n (QuotientAddGroup.map _ _
        ((HomologicalComplex.cyclesMap χ (n + 1)).app ⊤).hom (range_app_toCycles_le_comap χ n) a) =
      QuotientAddGroup.map _ _ (sectionsCyclesMap χ n) (sectionsBoundaries_le_comap χ n)
        (cyclesQuotientAddEquiv L n a) := by
  induction a using QuotientAddGroup.induction_on with | H z => ?_
  rw [QuotientAddGroup.map_mk]
  change QuotientAddGroup.mk _ = QuotientAddGroup.map _ _ _ _ (QuotientAddGroup.mk _)
  rw [QuotientAddGroup.map_mk]
  congr 1
  refine Subtype.ext ?_
  change ((HomologicalComplex.cyclesMap χ (n + 1) ≫ L'.iCycles (n + 1)).app ⊤) z =
    ((L.iCycles (n + 1) ≫ χ.f (n + 1)).app ⊤) z
  rw [HomologicalComplex.cyclesMap_i]

end NaturalitySections

end AlgebraicGeometry.Scheme.Modules
