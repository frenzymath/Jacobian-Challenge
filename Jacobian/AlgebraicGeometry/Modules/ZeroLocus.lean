import Jacobian.AlgebraicGeometry.IdealSheaf.Integral

/-!
# Zero schemes of morphisms of line bundles

The local coefficients of a line-bundle morphism generate a quasi-coherent ideal independent
of the chosen trivializations. On an integral scheme a nonzero morphism defines an effective
Cartier divisor. A line bundle mapping regularly into the structure module is its ideal module.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Every point `x` of an open `W` has an affine open neighbourhood `U ⊆ W` on which two
invertible modules both have free generators. -/
lemma exists_isFreeGenerator₂ (M N : X.Modules) [M.IsInvertible]
    [N.IsInvertible] {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧ (∃ eM : Γ(M, U.1), IsFreeGenerator eM) ∧
      ∃ eN : Γ(N, U.1), IsFreeGenerator eN := by
  obtain ⟨U, hxU, hUW, eM, hM⟩ := exists_isFreeGenerator M hx
  obtain ⟨U', hxU', hU'U, eN, hN⟩ := exists_isFreeGenerator N hxU
  exact ⟨U', hxU', hU'U.trans hUW, ⟨_, hM.map hU'U⟩, _, hN⟩

/-- Every point of an affine open `W` lies in a basic open of `W` on which two invertible
modules both have free generators. -/
lemma exists_basicOpen_isFreeGenerator (M N : X.Modules)
    [M.IsInvertible] [N.IsInvertible]
    {W : X.Opens} (hW : IsAffineOpen W) {x : X} (hx : x ∈ W) : ∃ g : Γ(X, W),
      x ∈ X.basicOpen g ∧ (∃ eM : Γ(M, X.basicOpen g), IsFreeGenerator eM) ∧
        ∃ eN : Γ(N, X.basicOpen g), IsFreeGenerator eN := by
  obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ := exists_isFreeGenerator₂ M N hx
  obtain ⟨g, hgU, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxU⟩ hx
  exact ⟨g, hxg, ⟨_, hM.map hgU⟩, _, hN.map hgU⟩

/-- If `φ(eM) = b • eN` on `U`, then the same holds for the restrictions to `V ⊆ U`. -/
lemma Hom.app_presheaf_map_of_eq (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) {eM : Γ(M, U)}
    {eN : Γ(N, U)} {b : Γ(X, U)} (hb : φ.app U eM = b • eN) :
    φ.app V (M.presheaf.map i.op eM) = X.presheaf.map i.op b • N.presheaf.map i.op eN := by
  rw [Hom.app_presheaf_map, hb, map_smul]

/-- The coefficient of `φ` with respect to free generators of `M` and `N` is well defined up to
a unit: coefficients with respect to different free generators divide each other. -/
lemma Hom.mem_span_of_isFreeGenerator (φ : M ⟶ N) {U : X.Opens} {eM eM' : Γ(M, U)}
    {eN eN' : Γ(N, U)} (hM : IsFreeGenerator eM) (hM' : IsFreeGenerator eM')
    (hN : IsFreeGenerator eN) (hN' : IsFreeGenerator eN') {b b' : Γ(X, U)}
    (hb : φ.app U eM = b • eN) (hb' : φ.app U eM' = b' • eN') : b ∈ Ideal.span {b'} := by
  obtain ⟨u, rfl⟩ := hM'.exists_unit_smul_eq hM
  obtain ⟨w, rfl⟩ := hN'.exists_unit_smul_eq hN
  have : b * w.1 = u.1 * b' := hN'.smul_left_injective (by
    simp only [mul_smul, ← hb, ← hb', Hom.app_smul])
  rw [Ideal.mem_span_singleton']
  refine ⟨u.1 * w⁻¹.1, ?_⟩
  rw [mul_right_comm, ← this, mul_assoc, Units.mul_inv, mul_one]

/-- Membership in an ideal of the sections over an affine open can be checked locally on
basic opens. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.mem_of_forall_exists_basicOpen {U : X.Opens}
    (hU : IsAffineOpen U) (I : Ideal Γ(X, U)) (a : Γ(X, U))
    (H : ∀ x ∈ U, ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op a ∈
        I.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom) : a ∈ I := by
  let s : Set Γ(X, U) := {g | X.presheaf.map (homOfLE (X.basicOpen_le g)).op a ∈
    I.map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨g, hxg, hg⟩ := H x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem I s hs a fun g ↦ ?_
  have := hU.isLocalization_basicOpen g.1
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers g.1) _ I a).mp g.2
  exact ⟨n, hn⟩

/-- The ideal of coefficients of a morphism of line bundles, checked on simultaneous
local trivializations. -/
def Hom.zeroLocusIdeal (φ : M ⟶ N) (W : X.Opens) [M.IsInvertible] [N.IsInvertible] :
    Ideal Γ(X, W) :=
  ⨅ (V : X.affineOpens) (h : V.1 ≤ W) (eM : Γ(M, V.1)) (_ : IsFreeGenerator eM)
    (eN : Γ(N, V.1)) (_ : IsFreeGenerator eN) (b : Γ(X, V.1)) (_ : φ.app V.1 eM = b • eN),
    (Ideal.span {b}).comap (X.presheaf.map (homOfLE h).op).hom

/-- **The zero scheme of a morphism of invertible modules.** For `φ : M ⟶ N`, the ideal sheaf
`𝓘_{Z(φ)}` which on an affine open `U = Spec A` trivializing `M` and `N`, where `φ` is
multiplication by `b ∈ A`, is the ideal `(b)`; so `Z(φ) ∩ U = Spec(A/(b))`
(`AlgebraicGeometry.Scheme.Modules.Hom.ideal_zeroLocus`).

For a global section `s` of an invertible module `ℳ`, the zero scheme `Z(s)` is
the zero scheme of `s : 𝒪_X ⟶ ℳ`; its ideal is the image of `s^∨ : ℳ^∨ ⟶ 𝒪_X`.
The invertibility hypotheses ensure that simultaneous local trivializations exist. -/
def Hom.zeroLocus (φ : M ⟶ N) [M.IsInvertible] [N.IsInvertible] : X.IdealSheafData :=
  IdealSheafData.ofIdeals fun W ↦ φ.zeroLocusIdeal W.1

variable [M.IsInvertible] [N.IsInvertible]

lemma Hom.mem_zeroLocusIdeal_iff (φ : M ⟶ N) {W : X.Opens} (a : Γ(X, W)) :
    a ∈ φ.zeroLocusIdeal W ↔ ∀ (V : X.affineOpens) (h : V.1 ≤ W) (eM : Γ(M, V.1)),
      IsFreeGenerator eM → ∀ eN : Γ(N, V.1), IsFreeGenerator eN → ∀ b : Γ(X, V.1),
      φ.app V.1 eM = b • eN → X.presheaf.map (homOfLE h).op a ∈ Ideal.span {b} := by
  simp only [Hom.zeroLocusIdeal, Submodule.mem_iInf, Ideal.mem_comap]

/-- On an affine open `U` on which `M` and `N` have free generators, `φ.zeroLocusIdeal U` is
generated by the coefficient of `φ`. -/
lemma Hom.zeroLocusIdeal_eq_span (φ : M ⟶ N) (U : X.affineOpens) {eM : Γ(M, U.1)}
    {eN : Γ(N, U.1)} (hM : IsFreeGenerator eM) (hN : IsFreeGenerator eN) {b : Γ(X, U.1)}
    (hb : φ.app U.1 eM = b • eN) : φ.zeroLocusIdeal U.1 = Ideal.span {b} := by
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.span_le.mpr ?_)
  · simpa only [Scheme.presheaf_map_id_apply] using
      (φ.mem_zeroLocusIdeal_iff a).mp ha U le_rfl eM hM eN hN b hb
  · rintro _ rfl
    rw [SetLike.mem_coe, Hom.mem_zeroLocusIdeal_iff]
    intro V h eM' hM' eN' hN' b' hb'
    exact φ.mem_span_of_isFreeGenerator (hM.map h) hM' (hN.map h) hN'
      (φ.app_presheaf_map_of_eq _ hb) hb'

/-- The restriction of a member of `φ.zeroLocusIdeal W` to `W' ⊆ W` is a member of
`φ.zeroLocusIdeal W'`. -/
lemma Hom.presheaf_map_mem_zeroLocusIdeal (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W)
    {a : Γ(X, W)} (ha : a ∈ φ.zeroLocusIdeal W) :
    X.presheaf.map (homOfLE h).op a ∈ φ.zeroLocusIdeal W' := by
  rw [Hom.mem_zeroLocusIdeal_iff] at ha ⊢
  intro V hV eM hM eN hN b hb
  rw [Scheme.presheaf_map_map_apply]
  exact ha V (hV.trans h) eM hM eN hN b hb

/-- Membership in `φ.zeroLocusIdeal W` is local on `W`. -/
lemma Hom.mem_zeroLocusIdeal_of_forall_exists (φ : M ⟶ N) {W : X.Opens} (a : Γ(X, W))
    (H : ∀ x ∈ W, ∃ (W' : X.Opens) (h : W' ≤ W), x ∈ W' ∧
      X.presheaf.map (homOfLE h).op a ∈ φ.zeroLocusIdeal W') :
    a ∈ φ.zeroLocusIdeal W := by
  rw [Hom.mem_zeroLocusIdeal_iff]
  intro V hV eM hM eN hN b hb
  refine V.2.mem_of_forall_exists_basicOpen _ _ fun x hx ↦ ?_
  obtain ⟨W', hW', hxW', ha⟩ := H x (hV hx)
  obtain ⟨g, hgW', hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW'⟩ hx
  refine ⟨g, hxg, ?_⟩
  have := (φ.mem_zeroLocusIdeal_iff _).mp ha ⟨_, V.2.basicOpen g⟩ hgW' _
    (hM.map (X.basicOpen_le g)) _ (hN.map (X.basicOpen_le g)) _ (φ.app_presheaf_map_of_eq _ hb)
  rw [Scheme.presheaf_map_map_apply] at this
  rw [Scheme.presheaf_map_map_apply, Ideal.map_span, Set.image_singleton]
  exact this

/-- For invertible modules the ideals `φ.zeroLocusIdeal` are quasi-coherent. -/
lemma Hom.map_zeroLocusIdeal_basicOpen (φ : M ⟶ N) (W : X.affineOpens) (f : Γ(X, W.1)) :
    (φ.zeroLocusIdeal W.1).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      φ.zeroLocusIdeal (X.basicOpen f) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha ↦
    φ.presheaf_map_mem_zeroLocusIdeal _ ha) fun c hc ↦ ?_
  have := W.2.isLocalization_basicOpen f
  obtain ⟨a, ⟨_, k, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) c
  refine (IsLocalization.mk'_mem_map_algebraMap_iff (.powers f) _ _ _ _).mpr ?_
  have ha : X.presheaf.map (homOfLE (X.basicOpen_le f)).op a ∈
      φ.zeroLocusIdeal (X.basicOpen f) := by
    have := Ideal.mul_mem_right (algebraMap Γ(X, W.1) Γ(X, X.basicOpen f) (f ^ k)) _ hc
    rwa [IsLocalization.mk'_spec] at this
  let S : Set Γ(X, W.1) := {g | (∃ eM : Γ(M, X.basicOpen g), IsFreeGenerator eM) ∧
    ∃ eN : Γ(N, X.basicOpen g), IsFreeGenerator eN}
  have hS : Ideal.span S = ⊤ := by
    rw [← W.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨g, hxg, hg⟩ := exists_basicOpen_isFreeGenerator M N W.2 hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  have key (g : Γ(X, W.1)) : ∃ n : ℕ, g ∈ S → X.presheaf.map (homOfLE (X.basicOpen_le g)).op
      (f ^ n * a) ∈ φ.zeroLocusIdeal (X.basicOpen g) := by
    by_cases hg : g ∈ S
    · obtain ⟨⟨eM, hM⟩, eN, hN⟩ := hg
      obtain ⟨b, hb⟩ := hN.exists_smul_eq (φ.app _ eM)
      have hU : IsAffineOpen (X.basicOpen g) := W.2.basicOpen g
      rw [φ.zeroLocusIdeal_eq_span ⟨_, hU⟩ hM hN hb.symm]
      let f' := X.presheaf.map (homOfLE (X.basicOpen_le g)).op f
      have := hU.isLocalization_basicOpen f'
      have hle : X.basicOpen f' ≤ X.basicOpen f := by
        rw [Scheme.basicOpen_res]
        exact inf_le_right
      have h1 := φ.presheaf_map_mem_zeroLocusIdeal hle ha
      rw [φ.zeroLocusIdeal_eq_span ⟨_, hU.basicOpen f'⟩ (hM.map (X.basicOpen_le f'))
        (hN.map (X.basicOpen_le f')) (φ.app_presheaf_map_of_eq _ hb.symm)] at h1
      have h2 : algebraMap Γ(X, X.basicOpen g) Γ(X, X.basicOpen f')
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) ∈
          (Ideal.span {b}).map (algebraMap Γ(X, X.basicOpen g) Γ(X, X.basicOpen f')) := by
        rw [Ideal.map_span, Set.image_singleton]
        convert h1 using 2
        exact (Scheme.presheaf_map_map_apply (homOfLE (X.basicOpen_le g))
            (homOfLE (X.basicOpen_le f')) a).trans
            (Scheme.presheaf_map_map_apply (homOfLE (X.basicOpen_le f)) (homOfLE hle) a).symm
      obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (.powers f') _ _ _).mp h2
      refine ⟨n, fun _ ↦ ?_⟩
      rw [map_mul, map_pow]
      exact hn
    · exact ⟨0, fun h ↦ (hg h).elim⟩
  choose n hn using key
  obtain ⟨T, hTS, hT⟩ := (Ideal.span_eq_top_iff_finite S).mp hS
  obtain ⟨m, hm⟩ := Finset.exists_le (T.image n)
  refine ⟨f ^ m, ⟨m, rfl⟩, φ.mem_zeroLocusIdeal_of_forall_exists _ fun x hx ↦ ?_⟩
  obtain ⟨⟨g, hgT⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((W.2.self_le_iSup_basicOpen_iff.mpr hT) hx)
  refine ⟨_, X.basicOpen_le g, hxg, ?_⟩
  rw [← pow_sub_mul_pow f (hm _ (Finset.mem_image_of_mem n hgT)), mul_assoc, map_mul]
  exact Ideal.mul_mem_left _ _ (hn g (hTS hgT))


section Properties

/-- For invertible modules, the sections of the ideal sheaf `Z(φ)` over an affine open `U` are
`φ.zeroLocusIdeal U`. -/
lemma Hom.ideal_zeroLocus_eq (φ : M ⟶ N) (U : X.affineOpens) :
    φ.zeroLocus.ideal U = φ.zeroLocusIdeal U.1 := by
  let I : X.IdealSheafData :=
    ⟨fun U ↦ φ.zeroLocusIdeal U.1, φ.map_zeroLocusIdeal_basicOpen, _, rfl⟩
  exact congr($(IdealSheafData.ofIdeals_ideal I).ideal U)

/-- **The zero scheme is a closed subscheme with the expected local equations.** On an affine
open `U = Spec A` on which `M` and `N` have free generators `eM` and `eN`, with
`φ(eM) = b • eN`, the ideal of the zero scheme `Z(φ)` is `(b)`, i.e. `Z(φ) ∩ U = Spec(A/(b))`.

-/
theorem Hom.ideal_zeroLocus (φ : M ⟶ N) (U : X.affineOpens) {eM : Γ(M, U.1)} {eN : Γ(N, U.1)}
    (hM : IsFreeGenerator eM) (hN : IsFreeGenerator eN) {b : Γ(X, U.1)}
    (hb : φ.app U.1 eM = b • eN) :
    φ.zeroLocus.ideal U = Ideal.span {b} := by
  rw [Hom.ideal_zeroLocus_eq, φ.zeroLocusIdeal_eq_span U hM hN hb]

/-- **The zero scheme is everything exactly for the zero morphism**: `Z(φ) = X`, i.e. its
ideal is `⊥`, if and only if `φ = 0`.

-/
theorem Hom.zeroLocus_eq_bot_iff (φ : M ⟶ N) : φ.zeroLocus = ⊥ ↔ φ = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- `φ` vanishes on every trivializing affine open, hence everywhere.
    have key (x : X) (W : X.Opens) (hx : x ∈ W) : ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
        ∀ m : Γ(M, U.1), φ.app U.1 m = 0 := by
      obtain ⟨U, hxU, hUW, ⟨eM, hM⟩, eN, hN⟩ := exists_isFreeGenerator₂ M N hx
      obtain ⟨b, hb⟩ := hN.exists_smul_eq (φ.app U.1 eM)
      have hb0 : b = 0 := by
        have := φ.ideal_zeroLocus U hM hN hb.symm
        rw [h, IdealSheafData.ideal_bot] at this
        exact Ideal.span_singleton_eq_bot.mp this.symm
      refine ⟨U, hxU, hUW, fun m ↦ ?_⟩
      obtain ⟨r, rfl⟩ := hM.exists_smul_eq m
      rw [Hom.app_smul, ← hb, hb0, zero_smul, smul_zero]
    refine Modules.hom_ext _ _ fun W ↦ ?_
    ext m
    choose U hxU hUW hU using fun x : W ↦ key x.1 W x.2
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun x ↦ (U x).1) W
      (fun x ↦ homOfLE (hUW x))
      (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU _⟩) _ _ fun x ↦ ?_
    simp [← Hom.app_presheaf_map, hU]
  · rintro rfl
    choose U hxU _ hM hN using fun x : X ↦
      exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
    refine le_bot_iff.mp (IdealSheafData.le_of_iSup_eq_top U
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_)
    obtain ⟨eM, hM⟩ := hM x
    obtain ⟨eN, hN⟩ := hN x
    rw [Hom.ideal_zeroLocus (0 : M ⟶ N) (U x) hM hN (b := 0) (by simp)]
    simp

/-- The zero scheme of a morphism of invertible modules is locally principal.

-/
theorem Hom.isLocallyPrincipal_zeroLocus (φ : M ⟶ N) : φ.zeroLocus.IsLocallyPrincipal := by
  intro x
  obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ :=
    exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
  obtain ⟨b, hb⟩ := hN.exists_smul_eq (φ.app U.1 eM)
  exact ⟨U, hxU, ⟨b, φ.ideal_zeroLocus U hM hN hb.symm⟩⟩

/-- The values of a morphism `ψ : L ⟶ 𝒪_X` from an invertible module over an affine open lie in
the ideal of its zero scheme. -/
lemma Hom.app_mem_ideal_zeroLocus {L : X.Modules} [L.IsInvertible]
    (ψ : L ⟶ unit X) (V : X.affineOpens) (m : Γ(L, V.1)) :
    ψ.app V.1 m ∈ ψ.zeroLocus.ideal V := by
  have : (unit X).IsInvertible :=
    inferInstance
  rw [Hom.ideal_zeroLocus_eq, Hom.mem_zeroLocusIdeal_iff]
  intro V' h eL hL e e' b hb
  obtain ⟨r, hr⟩ := hL.exists_smul_eq (L.presheaf.map (homOfLE h).op m)
  let e₀ : Γ(X, V'.1) := e
  have h1 : X.presheaf.map (homOfLE h).op (ψ.app V.1 m) = r * b * e₀ :=
    ((Hom.app_presheaf_map ψ (homOfLE h) m).symm.trans (by rw [← hr, Hom.app_smul, hb])).trans
      (smul_smul r b e)
  rw [h1]
  exact Ideal.mul_mem_right e₀ _ (Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self b))

/-- **An invertible module mapping to `𝒪_X` along an effective Cartier divisor.** If
`ψ : L ⟶ 𝒪_X` is a morphism from an invertible module whose zero scheme `D = Z(ψ)` is an
effective Cartier divisor, then `ψ` identifies `L` with the ideal sheaf `𝒪_X(-D)`: locally `ψ`
sends a free generator of `L` to a non-zerodivisor generating the ideal of `D`. The isomorphism
factors `ψ` through the inclusion `𝒪_X(-D) ⟶ 𝒪_X`. -/
theorem Hom.exists_iso_toModules_zeroLocus {L : X.Modules}
    [L.IsInvertible] (ψ : L ⟶ unit X)
    (hψ : ψ.zeroLocus.IsInvertible) :
    ∃ κ : L ≅ ψ.zeroLocus.toModules, κ.hom ≫ ψ.zeroLocus.toModulesι = ψ := by
  have : (unit X).IsInvertible :=
    inferInstance
  have hzero : ψ ≫ ψ.zeroLocus.toPushforwardSubscheme = 0 := by
    refine Modules.hom_ext _ _ fun W ↦ ?_
    ext m
    have key (x : W) : ∃ V : X.affineOpens, x.1 ∈ V.1 ∧ V.1 ≤ W := by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.2
      exact ⟨⟨V, hV⟩, hxV, hVW⟩
    choose V hxV hVW using key
    let T : X.Modules := (SheafOfModules.pushforward ψ.zeroLocus.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit ψ.zeroLocus.subscheme.ringCatSheaf)
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩ (fun x ↦ (V x).1) W
      (fun x ↦ homOfLE (hVW x))
      (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩) _ _ fun x ↦ ?_
    have h1 := Hom.app_presheaf_map (ψ ≫ ψ.zeroLocus.toPushforwardSubscheme) (homOfLE (hVW x)) m
    have h2 : ψ.zeroLocus.subschemeι.app (V x).1
        (ψ.app (V x).1 (L.presheaf.map (homOfLE (hVW x)).op m)) = 0 := by
      rw [← IdealSheafData.mem_idealOfOpens_iff, IdealSheafData.idealOfOpens_eq_ideal]
      exact ψ.app_mem_ideal_zeroLocus _ _
    refine h1.symm.trans (h2.trans ?_)
    exact (map_zero _).symm
  let κ : L ⟶ ψ.zeroLocus.toModules := kernel.lift _ ψ hzero
  have hκ (U : X.Opens) (m : Γ(L, U)) : ψ.zeroLocus.toModulesι.app U (κ.app U m) = ψ.app U m :=
    congrArg (fun f : L ⟶ unit X ↦ f.app U m) (kernel.lift_ι _ ψ hzero)
  refine ⟨@asIso _ _ _ _ κ (isIso_of_isFreeGenerator κ fun x ↦ ?_), kernel.lift_ι _ ψ hzero⟩
  obtain ⟨U, hxU, -, e, he⟩ := exists_isFreeGenerator L (TopologicalSpace.Opens.mem_top x)
  refine ⟨U.1, e, hxU, he, hψ.isFreeGenerator _ fun V h ↦ ?_⟩
  rw [hκ]
  refine Hom.ideal_zeroLocus ψ V (he.map h) (isFreeGenerator_one V.1) ?_
  exact (Hom.app_presheaf_map ψ (homOfLE h) e).trans
    (mul_one (X.presheaf.map (homOfLE h).op (ψ.app U.1 e))).symm

/-- **An invertible module mapping to `𝒪_X` along an effective Cartier divisor.** If
`ψ : L ⟶ 𝒪_X` is a morphism from an invertible module whose zero scheme `D = Z(ψ)` is an
effective Cartier divisor, then `L` is isomorphic to the ideal sheaf `𝒪_X(-D)`. -/
theorem Hom.nonempty_iso_toModules_zeroLocus {L : X.Modules}
    [L.IsInvertible] (ψ : L ⟶ unit X)
    (hψ : ψ.zeroLocus.IsInvertible) : Nonempty (L ≅ ψ.zeroLocus.toModules) :=
  ⟨(ψ.exists_iso_toModules_zeroLocus hψ).choose⟩


/-- A nonzero morphism of line bundles on an integral scheme defines an effective Cartier divisor. -/
theorem Hom.isInvertible_zeroLocus [IsIntegral X] {φ : M ⟶ N} (hφ : φ ≠ 0) :
    φ.zeroLocus.IsInvertible :=
  (Hom.isLocallyPrincipal_zeroLocus φ).isInvertible fun h ↦
    hφ ((Hom.zeroLocus_eq_bot_iff φ).mp h)

end Properties
end Modules
end AlgebraicGeometry.Scheme
