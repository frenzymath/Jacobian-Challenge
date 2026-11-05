import Jacobian.AlgebraicGeometry.Picard.AffineSpaceRigidity

/-!
# Rigidity of line bundles along a basic open of affine space

A line through two rational points of a basic open in affine space factors through an
open affine line. Rigidity along that line identifies the two pullbacks of a line bundle.
-/

set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory Limits Polynomial

/-- Two `k`-points of a basic open `D(r)` of affine space lie on a line: there is `f : k[t]`
and a `k`-algebra map `k[x]_r ⟶ k[t]_f` through which both points factor via evaluation at
`0` and `1`. -/
theorem MvPolynomial.exists_algHom_localizationAway_polynomial {baseField indexType : Type*} [CommRing baseField]
    (localizer : MvPolynomial indexType baseField) (φp φq : Localization.Away localizer →ₐ[baseField] baseField) :
    ∃ (polynomial : baseField[X]) (Ψ : Localization.Away localizer →ₐ[baseField] Localization.Away polynomial)
      (e₀ e₁ : Localization.Away polynomial →ₐ[baseField] baseField), e₀.comp Ψ = φp ∧ e₁.comp Ψ = φq := by
  let firstCoordinate (index : indexType) := φp (algebraMap (MvPolynomial indexType baseField) (Localization.Away localizer) (MvPolynomial.X index))
  let secondCoordinate (index : indexType) := φq (algebraMap (MvPolynomial indexType baseField) (Localization.Away localizer) (MvPolynomial.X index))
  let interpolation : MvPolynomial indexType baseField →ₐ[baseField] baseField[X] := aeval fun index ↦ Polynomial.C (firstCoordinate index) +
    Polynomial.X * Polynomial.C (secondCoordinate index - firstCoordinate index)
  have h₀ : (Polynomial.aeval 0).comp interpolation =
      φp.comp (IsScalarTower.toAlgHom baseField _ (Localization.Away localizer)) := by
    ext index
    simp [interpolation, firstCoordinate]
  have h₁ : (Polynomial.aeval 1).comp interpolation =
      φq.comp (IsScalarTower.toAlgHom baseField _ (Localization.Away localizer)) := by
    ext index
    simp [interpolation, secondCoordinate]
  have hu (evaluation : Localization.Away localizer →ₐ[baseField] baseField) (value : baseField)
      (compatibility : (Polynomial.aeval value).comp interpolation = evaluation.comp (IsScalarTower.toAlgHom baseField _ _)) :
      ∀ denominator : Submonoid.powers (interpolation localizer), IsUnit (Polynomial.aeval value (denominator : baseField[X])) := by
    rintro ⟨_, exponent, rfl⟩
    have := congr($compatibility localizer)
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [map_pow, this]
    exact ((IsLocalization.Away.algebraMap_isUnit localizer).map evaluation).pow exponent
  refine ⟨interpolation localizer, IsLocalization.Away.mapₐ _ _ interpolation localizer, IsLocalization.liftAlgHom (hu φp 0 h₀),
    IsLocalization.liftAlgHom (hu φq 1 h₁), ?_, ?_⟩
  · refine IsLocalization.algHom_ext (Submonoid.powers localizer) ?_
    ext index
    simpa [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      Algebra.algHom, IsLocalization.lift_eq] using congr($h₀ (MvPolynomial.X index))
  · refine IsLocalization.algHom_ext (Submonoid.powers localizer) ?_
    ext index
    simpa [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      Algebra.algHom, IsLocalization.lift_eq] using congr($h₁ (MvPolynomial.X index))

namespace AlgebraicGeometry
/-- Let `ψ : T' ⟶ T` be a morphism of `S`-schemes and `M` a module on `X ×_S T`. If the pullbacks
of `(𝟙 × ψ)^* M` along the sections `X ⟶ X ×_S T'` given by `p'` and `q'` are isomorphic, then
so are the pullbacks of `M` along the sections `X ⟶ X ×_S T` given by `p' ≫ ψ` and `q' ≫ ψ`. -/
lemma nonempty_iso_pullback_lift_of_comp {scheme baseScheme parameterScheme T' : Scheme.{schemeUniverse}} {sX : scheme ⟶ baseScheme} {sT : parameterScheme ⟶ baseScheme}
    {sT' : T' ⟶ baseScheme} (ψ : T' ⟶ parameterScheme) (hψ : ψ ≫ sT = sT') {p' q' : scheme ⟶ T'}
    (hp' : 𝟙 scheme ≫ sX = p' ≫ sT') (hq' : 𝟙 scheme ≫ sX = q' ≫ sT') {gp gq : scheme ⟶ parameterScheme}
    (hgp : 𝟙 scheme ≫ sX = gp ≫ sT) (hgq : 𝟙 scheme ≫ sX = gq ≫ sT) (hp : p' ≫ ψ = gp)
    (hq : q' ≫ ψ = gq) (lineBundle : (pullback sX sT).Modules)
    (pullbackIso : Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 scheme) p' hp')).obj
        ((Scheme.Modules.pullback (pullback.map sX sT' sX sT (𝟙 scheme) ψ (𝟙 baseScheme) (by simp)
          (by simp [hψ]))).obj lineBundle) ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 scheme) q' hq')).obj
        ((Scheme.Modules.pullback (pullback.map sX sT' sX sT (𝟙 scheme) ψ (𝟙 baseScheme) (by simp)
          (by simp [hψ]))).obj lineBundle))) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 scheme) gp hgp)).obj lineBundle ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 scheme) gq hgq)).obj lineBundle) := by
  subst hp hq
  have compatibility (sectionMap : scheme ⟶ T') (hg : 𝟙 scheme ≫ sX = sectionMap ≫ sT') :
      pullback.lift (𝟙 scheme) (sectionMap ≫ ψ) (by simp [hψ, ← hg]) = pullback.lift (𝟙 scheme) sectionMap hg ≫
        pullback.map sX sT' sX sT (𝟙 scheme) ψ (𝟙 baseScheme) (by simp) (by simp [hψ]) := by
    ext <;> simp
  obtain ⟨evaluationMap⟩ := pullbackIso
  rw [compatibility p' hp', compatibility q' hq']
  exact ⟨(Scheme.Modules.pullbackComp _ _).symm.app lineBundle ≪≫ evaluationMap ≪≫
    (Scheme.Modules.pullbackComp _ _).app lineBundle⟩


/-- A `k`-point of `Spec A` (a section of the structure morphism) as a `k`-algebra map. -/
noncomputable def algHomOfSpecSection {baseField baseAlgebra : Type schemeUniverse} [CommRing baseField] [CommRing baseAlgebra] [Algebra baseField baseAlgebra]
    (firstPoint : Spec (.of baseField) ⟶ Spec (.of baseAlgebra))
    (hp : firstPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra)) = 𝟙 _) : baseAlgebra →ₐ[baseField] baseField where
  __ := (Spec.preimage firstPoint).hom
  commutes' value := by
    have compatibility : CommRingCat.ofHom (algebraMap baseField baseAlgebra) ≫ Spec.preimage firstPoint = 𝟙 _ :=
      Spec.map_injective (by simpa using hp)
    exact congr($compatibility value)

/-- `Spec` of the `k`-algebra map attached to a `k`-point recovers the point. -/
lemma spec_map_algHomOfSpecSection {baseField baseAlgebra : Type schemeUniverse} [CommRing baseField] [CommRing baseAlgebra] [Algebra baseField baseAlgebra]
    (firstPoint : Spec (.of baseField) ⟶ Spec (.of baseAlgebra))
    (hp : firstPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra)) = 𝟙 _) :
    Spec.map (CommRingCat.ofHom (algHomOfSpecSection firstPoint hp).toRingHom) = firstPoint :=
  Spec.map_preimage firstPoint

/-- **Rigidity of invertible modules over a basic open of affine space** (Stacks 0BEH, for a
basic open `D(r)` of affine `d`-space). Let `k` be an algebraically closed field, `X` an integral
`k`-scheme whose local rings are unique factorization domains, and `p`, `q` two `k`-points of
`D(r) = Spec k[x₁, …, x_d]_r`. For every invertible module `ℒ` on `X ×_k D(r)`, the pullbacks of
`ℒ` along the sections `X ⟶ X ×_k D(r)` at `p` and at `q` are isomorphic. -/
@[stacks 0BEH]
theorem nonempty_iso_pullback_lift_of_isAlgClosed_mvPolynomial
    {baseField : Type schemeUniverse} [Field baseField] [IsAlgClosed baseField] (scheme : Scheme.{schemeUniverse}) [IsIntegral scheme]
    (hX : ∀ x : scheme, UniqueFactorizationMonoid (scheme.presheaf.stalk x)) (sX : scheme ⟶ Spec (.of baseField))
    {dimension : ℕ} (localizer : MvPolynomial (Fin dimension) baseField)
    (firstPoint secondPoint : Spec (.of baseField) ⟶ Spec (.of (Localization.Away localizer)))
    (hp : firstPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))) = 𝟙 _)
    (hq : secondPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))) = 𝟙 _)
    (lineBundle : (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))))).Modules)
    [lineBundle.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 scheme) (sX ≫ firstPoint) (by simp [hp]))).obj lineBundle ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 scheme) (sX ≫ secondPoint) (by simp [hq]))).obj lineBundle) := by
  obtain ⟨polynomial, Ψ, e₀, e₁, h₀, h₁⟩ := MvPolynomial.exists_algHom_localizationAway_polynomial localizer
    (algHomOfSpecSection firstPoint hp) (algHomOfSpecSection secondPoint hq)
  have hsec (evaluationMap : Localization.Away polynomial →ₐ[baseField] baseField) :
      Spec.map (CommRingCat.ofHom evaluationMap.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away polynomial))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, evaluationMap.comp_algebraMap]
    exact Spec.map_id _
  have hcomp (evaluationMap : Localization.Away polynomial →ₐ[baseField] baseField) (evaluation : Localization.Away localizer →ₐ[baseField] baseField)
      (compatibility : evaluationMap.comp Ψ = evaluation) : Spec.map (CommRingCat.ofHom evaluationMap.toRingHom) ≫
        Spec.map (CommRingCat.ofHom Ψ.toRingHom) = Spec.map (CommRingCat.ofHom evaluation.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← compatibility]
    rfl
  refine nonempty_iso_pullback_lift_of_comp (Spec.map (CommRingCat.ofHom Ψ.toRingHom))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, Ψ.comp_algebraMap])
    (p' := sX ≫ Spec.map (CommRingCat.ofHom e₀.toRingHom))
    (q' := sX ≫ Spec.map (CommRingCat.ofHom e₁.toRingHom))
    (by rw [Category.assoc, hsec, Category.id_comp, Category.comp_id])
    (by rw [Category.assoc, hsec, Category.id_comp, Category.comp_id])
    _ _ ?_ ?_ lineBundle ?_
  · rw [Category.assoc, hcomp e₀ _ h₀, spec_map_algHomOfSpecSection]
  · rw [Category.assoc, hcomp e₁ _ h₁, spec_map_algHomOfSpecSection]
  · exact nonempty_iso_pullback_lift_of_isAlgClosed scheme hX sX polynomial _ _ (hsec e₀) (hsec e₁) _

end AlgebraicGeometry
