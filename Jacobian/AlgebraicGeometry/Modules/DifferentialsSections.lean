import Jacobian.AlgebraicGeometry.Modules.Differentials

/-!
# Sections of the sheaf of differentials over affine opens

Let `g : X ⟶ Spec R` be a morphism of schemes and `U` an affine open of `X`. Then the sections
`Γ(Ω¹_{X/R}, U)` of the sheaf of relative differentials are the Kähler differentials
`Ω[Γ(X, U)⁄R]`, compatibly with `d` and `D`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Hom.specStructureMap`: the structure map `R ⟶ Γ(X, U)`.
- `AlgebraicGeometry.Scheme.Hom.kaehlerSectionsEquiv`: for `U` affine,
  `Ω[Γ(X, U)⁄R] ≃ Γ(Ω¹_{X/R}, U)`, sending `D b` to `d b`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R)

/-- The structure map `R ⟶ Γ(X, U)` of a scheme `X` over `Spec R`. -/
noncomputable def specStructureMap (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ U le_top

lemma specStructureMap_map {U V : X.Opens} (h : V ≤ U) :
    g.specStructureMap U ≫ X.presheaf.map (homOfLE h).op = g.specStructureMap V := by
  simp [specStructureMap]

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/R}` on sections over `U`. -/
noncomputable def sectionsD (U : X.Opens) : Γ(X, U) →+ Γ(g.relativeDifferentials, U) :=
  g.relativeDifferentialsDerivation.d (X := op U)

lemma sectionsD_mul (U : X.Opens) (a b : Γ(X, U)) :
    g.sectionsD U (a * b) = a • g.sectionsD U b + b • g.sectionsD U a :=
  g.relativeDifferentialsDerivation.d_mul a b

lemma sectionsD_map {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    g.sectionsD V (X.presheaf.map (homOfLE h).op a) =
      g.relativeDifferentials.presheaf.map (homOfLE h).op (g.sectionsD U a) :=
  g.relativeDifferentialsDerivation.d_map _ a

lemma sectionsD_specStructureMap (U : X.Opens) (r : R) :
    g.sectionsD U (g.specStructureMap U r) = 0 := by
  have h := PresheafOfModulesOfCommRing.Derivation'.d_app_app g.relativeDifferentialsDerivation ⊤
    ((Scheme.ΓSpecIso R).inv r)
  have h' := g.sectionsD_map (le_top : U ≤ g ⁻¹ᵁ ⊤) (g.app ⊤ ((Scheme.ΓSpecIso R).inv r))
  have e : g.specStructureMap U r =
      X.presheaf.map (homOfLE (le_top : U ≤ g ⁻¹ᵁ ⊤)).op (g.app ⊤ ((Scheme.ΓSpecIso R).inv r)) := by
    simp [specStructureMap, Scheme.Hom.appLE]
  rw [e, h']
  exact (congrArg (g.relativeDifferentials.presheaf.map _) h).trans (map_zero _)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R) {U : X.Opens}
  (hU : IsAffineOpen U)

include hU in
lemma _root_.AlgebraicGeometry.IsAffineOpen.image_fromSpec_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [image_top_eq_opensRange, hU.opensRange_fromSpec]

lemma fromSpec_comp_eq_specMap : hU.fromSpec ≫ g = Spec.map (g.specStructureMap U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top (Spec R)) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, specStructureMap, Spec.map_comp]

/-- Restricting a section of `𝒪_X` over the affine open `U` to `hU.fromSpec ''ᵁ ⊤ = U` and
transporting it to `Γ(Spec Γ(X, U), ⊤)` is the inverse of `Scheme.ΓSpecIso`. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.map_eqToHom_comp_appIso_hom :
    X.presheaf.map (eqToHom hU.image_fromSpec_top).op ≫ (hU.fromSpec.appIso ⊤).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self,
    Category.assoc, ← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _),
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Elementwise version of `IsAffineOpen.map_eqToHom_comp_appIso_hom`. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.map_eqToHom_apply (a : Γ(X, U)) :
    X.presheaf.map (eqToHom hU.image_fromSpec_top).op a =
      (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a) := by
  rw [← hU.map_eqToHom_comp_appIso_hom, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply]

variable {g} in
/-- `relativeDifferentialsCongr` is compatible with the universal derivations. -/
lemma relativeDifferentialsCongr_hom_app_d {g' : X ⟶ Spec R} (e : g = g') {W : X.Opensᵒᵖ}
    (x : X.presheaf.obj W) :
    (relativeDifferentialsCongr g e).hom.val.app W (g.relativeDifferentialsDerivation.d x) =
      g'.relativeDifferentialsDerivation.d x := by
  subst e
  rw [relativeDifferentialsCongr, eqToIso_refl, Iso.refl_hom]
  rfl

/-- The identity map from the sections over `⊤` of an `𝒪_{Spec A}`-module `N` to the underlying
group of the `A`-module `moduleSpecΓFunctor.obj N`. Stating it for an arbitrary `N` keeps the
unification of the two (definitionally equal) additive structures cheap. -/
private def _root_.AlgebraicGeometry.Scheme.Modules.toModuleSpecΓ {A : CommRingCat.{u}}
    (N : (Spec A).Modules) : N.val.obj (op ⊤) →+ (moduleSpecΓFunctor (R := A)).obj N where
  toFun x := x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `toModuleSpecΓ` turns the action of `Γ(Spec A, ⊤)` into the action of `A`. -/
private lemma _root_.AlgebraicGeometry.Scheme.Modules.toModuleSpecΓ_smul {A : CommRingCat.{u}}
    (N : (Spec A).Modules) (a : A) (x : N.val.obj (op ⊤)) :
    N.toModuleSpecΓ ((Scheme.ΓSpecIso A).inv a • x) = a • N.toModuleSpecΓ x :=
  rfl

/-- `toModuleSpecΓ` is bijective (it is the identity). -/
private lemma _root_.AlgebraicGeometry.Scheme.Modules.toModuleSpecΓ_bijective {A : CommRingCat.{u}}
    (N : (Spec A).Modules) : Function.Bijective N.toModuleSpecΓ :=
  Function.bijective_id

/-- For an isomorphism of sheaves of modules, the maps on sections are bijective. -/
private lemma _root_.AlgebraicGeometry.Scheme.Modules.bijective_val_app {Y : Scheme.{u}}
    {M N : Y.Modules} (e : M ≅ N) (W : Y.Opensᵒᵖ) : Function.Bijective (e.hom.val.app W) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.val.app W, fun x ↦ ?_, fun y ↦ ?_⟩
  · exact congr($(e.hom_inv_id).val.app W x)
  · exact congr($(e.inv_hom_id).val.app W y)

variable {M : X.Modules} {N : (Spec Γ(X, U)).Modules} (θ : M.restrict hU.fromSpec ≅ N)
  {K : ModuleCat Γ(X, U)} (ε : (moduleSpecΓFunctor (R := Γ(X, U))).obj N ≅ K)

/-- Given identifications `θ : M|_{Spec Γ(X, U)} ≅ N` and `ε : Γ(N, ⊤) ≅ K`, the map
`Γ(M, U) → K` obtained by restricting along `hU.fromSpec`. -/
private noncomputable def sectionsMapOfIso (m : Γ(M, U)) : K :=
  ε.hom.hom (N.toModuleSpecΓ (θ.hom.val.app (op ⊤)
    (M.presheaf.map (eqToHom hU.image_fromSpec_top).op m)))

/-- `sectionsMapOfIso` is additive. -/
private lemma sectionsMapOfIso_add (m m' : Γ(M, U)) :
    sectionsMapOfIso hU θ ε (m + m') =
      sectionsMapOfIso hU θ ε m + sectionsMapOfIso hU θ ε m' := by
  simp only [sectionsMapOfIso, map_add]

/-- `sectionsMapOfIso` is `Γ(X, U)`-linear. -/
private lemma sectionsMapOfIso_smul (a : Γ(X, U)) (m : Γ(M, U)) :
    sectionsMapOfIso hU θ ε (a • m) = a • sectionsMapOfIso hU θ ε m := by
  have h1 : M.presheaf.map (eqToHom hU.image_fromSpec_top).op (a • m) =
      (Scheme.ΓSpecIso Γ(X, U)).inv a • (M.restrictAppIso hU.fromSpec ⊤).inv
        (M.presheaf.map (eqToHom hU.image_fromSpec_top).op m) := by
    rw [Scheme.Modules.map_smul, hU.map_eqToHom_apply]
    rfl
  refine (congrArg (fun x ↦ ε.hom.hom (N.toModuleSpecΓ (θ.hom.val.app (op ⊤) x))) h1).trans ?_
  refine (congrArg (fun x ↦ ε.hom.hom (N.toModuleSpecΓ x))
    ((θ.hom.val.app (op ⊤)).hom.map_smul _ _)).trans ?_
  refine (congrArg (fun x ↦ ε.hom.hom x) (N.toModuleSpecΓ_smul _ _)).trans ?_
  exact ε.hom.hom.map_smul _ _

/-- `sectionsMapOfIso` is bijective, as a composite of bijections. -/
private lemma sectionsMapOfIso_bijective : Function.Bijective (sectionsMapOfIso hU θ ε) :=
  ε.toLinearEquiv.bijective.comp ((Scheme.Modules.toModuleSpecΓ_bijective _).comp
    ((Scheme.Modules.bijective_val_app _ _).comp (ConcreteCategory.bijective_of_isIso _)))

/-- Computing `sectionsMapOfIso` for a composite `θ ≪≫ θ'`, given the restriction of `m`. -/
private lemma sectionsMapOfIso_trans_eq {N' : (Spec Γ(X, U)).Modules} (θ' : N ≅ N')
    (ε' : (moduleSpecΓFunctor (R := Γ(X, U))).obj N' ≅ K) (m : Γ(M, U))
    (x : M.val.obj (op (hU.fromSpec ''ᵁ ⊤)))
    (hx : M.presheaf.map (eqToHom hU.image_fromSpec_top).op m = x) :
    sectionsMapOfIso hU (θ ≪≫ θ') ε' m =
      ε'.hom.hom (N'.toModuleSpecΓ (θ'.hom.val.app (op ⊤) (θ.hom.val.app (op ⊤) x))) := by
  subst hx
  rfl

/-- For an isomorphism of sheaves of modules, `e.hom` undoes `e.inv` on sections. -/
private lemma _root_.AlgebraicGeometry.Scheme.Modules.iso_hom_val_app_inv_val_app {Y : Scheme.{u}}
    {M N : Y.Modules} (e : M ≅ N) (W : Y.Opensᵒᵖ) (y : N.val.obj W) :
    e.hom.val.app W (e.inv.val.app W y) = y :=
  congr($(e.inv_hom_id).val.app W y)

/-- The map `Γ(Ω¹_{X/R}, U) → Ω[Γ(X, U)⁄R]` for an affine open `U`, through the sections of
`Ω¹_{Spec Γ(X, U) / Spec R}`. It is additive, `Γ(X, U)`-linear, bijective
(`sectionsToKaehler_bijective`) and sends `d b` to `D b`. -/
noncomputable def sectionsToKaehler (m : Γ(g.relativeDifferentials, U)) :
    CommRingCat.KaehlerDifferential (g.specStructureMap U) :=
  sectionsMapOfIso hU (g.relativeDifferentialsRestrictIso hU.fromSpec ≪≫
    relativeDifferentialsCongr _ (g.fromSpec_comp_eq_specMap hU))
    (relativeDifferentialsSpecΓIso (g.specStructureMap U)) m

/-- `sectionsToKaehler` is additive. -/
lemma sectionsToKaehler_add (m m' : Γ(g.relativeDifferentials, U)) :
    g.sectionsToKaehler hU (m + m') = g.sectionsToKaehler hU m + g.sectionsToKaehler hU m' :=
  sectionsMapOfIso_add hU _ _ m m'

/-- `sectionsToKaehler` is `Γ(X, U)`-linear. -/
lemma sectionsToKaehler_smul (a : Γ(X, U)) (m : Γ(g.relativeDifferentials, U)) :
    g.sectionsToKaehler hU (a • m) = a • g.sectionsToKaehler hU m :=
  sectionsMapOfIso_smul hU _ _ a m

/-- `sectionsToKaehler` is bijective. -/
lemma sectionsToKaehler_bijective : Function.Bijective (g.sectionsToKaehler hU) :=
  sectionsMapOfIso_bijective hU _ _

/-- `sectionsToKaehler` sends `d b` to `D b`. -/
lemma sectionsToKaehler_sectionsD (b : Γ(X, U)) :
    g.sectionsToKaehler hU (g.sectionsD U b) = CommRingCat.KaehlerDifferential.d b := by
  have h1 : g.relativeDifferentials.presheaf.map (eqToHom hU.image_fromSpec_top).op
      (g.sectionsD U b) = g.relativeDifferentialsDerivation.d (X := op (hU.fromSpec ''ᵁ ⊤))
        ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv b)) := by
    rw [← hU.map_eqToHom_apply]
    exact (g.relativeDifferentialsDerivation.d_map _ b).symm
  have h2 : (g.relativeDifferentialsRestrictIso hU.fromSpec).hom.val.app (op ⊤)
      (g.relativeDifferentialsDerivation.d (X := op (hU.fromSpec ''ᵁ ⊤))
        ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv b))) =
      (hU.fromSpec ≫ g).relativeDifferentialsDerivation.d (X := op ⊤)
        ((Scheme.ΓSpecIso Γ(X, U)).inv b) :=
    (congrArg ((g.relativeDifferentialsRestrictIso hU.fromSpec).hom.val.app (op ⊤))
      (g.relativeDifferentialsToRestrict_app_d hU.fromSpec (W := op ⊤) _).symm).trans
      (Scheme.Modules.iso_hom_val_app_inv_val_app _ _ _)
  have h3 : (relativeDifferentialsCongr _ (g.fromSpec_comp_eq_specMap hU)).hom.val.app (op ⊤)
      ((hU.fromSpec ≫ g).relativeDifferentialsDerivation.d (X := op ⊤)
        ((Scheme.ΓSpecIso Γ(X, U)).inv b)) =
      (Spec.map (g.specStructureMap U)).relativeDifferentialsDerivation.d (X := op ⊤)
        ((Scheme.ΓSpecIso Γ(X, U)).inv b) :=
    relativeDifferentialsCongr_hom_app_d _ _
  have h4 : (Spec.map (g.specStructureMap U)).relativeDifferentials.toModuleSpecΓ
      ((Spec.map (g.specStructureMap U)).relativeDifferentialsDerivation.d (X := op ⊤)
        ((Scheme.ΓSpecIso Γ(X, U)).inv b)) =
      relativeDifferentialsSpecΓHom (g.specStructureMap U) (CommRingCat.KaehlerDifferential.d b) :=
    (relativeDifferentialsSpecΓHom_d _ b).symm
  refine (sectionsMapOfIso_trans_eq hU (g.relativeDifferentialsRestrictIso hU.fromSpec)
    (relativeDifferentialsCongr _ (g.fromSpec_comp_eq_specMap hU))
    (relativeDifferentialsSpecΓIso (g.specStructureMap U)) (g.sectionsD U b) _ h1).trans ?_
  refine (congrArg (fun x ↦ (relativeDifferentialsSpecΓIso (g.specStructureMap U)).hom.hom
    ((Spec.map (g.specStructureMap U)).relativeDifferentials.toModuleSpecΓ
      ((relativeDifferentialsCongr _ (g.fromSpec_comp_eq_specMap hU)).hom.val.app (op ⊤) x)))
    h2).trans ?_
  refine (congrArg (fun x ↦ (relativeDifferentialsSpecΓIso (g.specStructureMap U)).hom.hom
    ((Spec.map (g.specStructureMap U)).relativeDifferentials.toModuleSpecΓ x)) h3).trans ?_
  refine (congrArg (relativeDifferentialsSpecΓIso (g.specStructureMap U)).hom.hom h4).trans ?_
  exact (relativeDifferentialsSpecΓIso (g.specStructureMap U)).inv_hom_id_apply _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (g : X ⟶ Spec (.of R)) (U : X.Opens)
  [Algebra R Γ(X, U)]


/-- The universal derivation `d : Γ(X, U) → Γ(Ω¹_{X/R}, U)` as an `R`-derivation, for any
`R`-algebra structure on `Γ(X, U)` given by the structure map and any compatible `R`-module
structure on `Γ(Ω¹_{X/R}, U)`. -/
noncomputable def sectionsDerivation
    (h : algebraMap R Γ(X, U) = (g.specStructureMap U).hom) [Module R Γ(g.relativeDifferentials, U)]
    [IsScalarTower R Γ(X, U) Γ(g.relativeDifferentials, U)] :
    Derivation R Γ(X, U) Γ(g.relativeDifferentials, U) where
  toFun := g.sectionsD U
  map_add' := map_add _
  map_smul' c b := by
    rw [RingHom.id_apply, Algebra.smul_def, sectionsD_mul, h, sectionsD_specStructureMap,
      smul_zero, add_zero, ← h, algebraMap_smul]
  map_one_eq_zero' :=
    (congrArg (g.sectionsD U) (map_one (g.specStructureMap U).hom).symm).trans
      (g.sectionsD_specStructureMap U 1)
  leibniz' := g.sectionsD_mul U

@[simp]
lemma sectionsDerivation_apply
    (h : algebraMap R Γ(X, U) = (g.specStructureMap U).hom) [Module R Γ(g.relativeDifferentials, U)]
    [IsScalarTower R Γ(X, U) Γ(g.relativeDifferentials, U)] (b : Γ(X, U)) :
    g.sectionsDerivation U h b = g.sectionsD U b :=
  rfl

/-- `CommRingCat.KaehlerDifferential.d` is `KaehlerDifferential.D`. -/
lemma _root_.CommRingCat.KaehlerDifferential.d_eq_D {A B : CommRingCat.{u}} (f : A ⟶ B) (b : B) :
    letI := f.hom.toAlgebra
    CommRingCat.KaehlerDifferential.d (f := f) b = KaehlerDifferential.D A B b :=
  rfl

/-- For an affine open `U`, the map `Ω[Γ(X, U)⁄R] → Γ(Ω¹_{X/R}, U)` induced by
`sectionsDerivation` is bijective: composed with the bijection `sectionsToKaehler` it is the
identity. -/
lemma bijective_liftKaehlerDifferential_sectionsDerivation
    (h : algebraMap R Γ(X, U) = (g.specStructureMap U).hom) (hU : IsAffineOpen U)
    [Module R Γ(g.relativeDifferentials, U)]
    [IsScalarTower R Γ(X, U) Γ(g.relativeDifferentials, U)] :
    Function.Bijective (g.sectionsDerivation U h).liftKaehlerDifferential := by
  obtain rfl : ‹Algebra R Γ(X, U)› = (g.specStructureMap U).hom.toAlgebra :=
    Algebra.algebra_ext _ _ (RingHom.congr_fun h)
  let _ : Algebra R Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  let ψ : Γ(g.relativeDifferentials, U) →ₗ[Γ(X, U)] Ω[Γ(X, U)⁄R] :=
    { toFun := g.sectionsToKaehler hU
      map_add' := g.sectionsToKaehler_add hU
      map_smul' := g.sectionsToKaehler_smul hU }
  have hD (b : Γ(X, U)) : ψ ((g.sectionsDerivation U h).liftKaehlerDifferential
      (KaehlerDifferential.D R Γ(X, U) b)) = KaehlerDifferential.D R Γ(X, U) b := by
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact (g.sectionsToKaehler_sectionsD hU b).trans
      (CommRingCat.KaehlerDifferential.d_eq_D (g.specStructureMap U) b)
  have hψ : ψ ∘ₗ (g.sectionsDerivation U h).liftKaehlerDifferential = LinearMap.id :=
    Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext hD)
  have hl : Function.LeftInverse ψ (g.sectionsDerivation U h).liftKaehlerDifferential :=
    LinearMap.congr_fun hψ
  exact ⟨hl.injective, fun m ↦ ⟨ψ m, (g.sectionsToKaehler_bijective hU).1 (hl (ψ m))⟩⟩

/-- **Sections of the sheaf of differentials over an affine open.** For an affine open `U` of a
scheme `X` over `Spec R`, the `Γ(X, U)`-linear map `Ω[Γ(X, U)⁄R] → Γ(Ω¹_{X/R}, U)`,
`D b ↦ d b`, is an isomorphism. -/
noncomputable def kaehlerSectionsEquiv
    (h : algebraMap R Γ(X, U) = (g.specStructureMap U).hom) (hU : IsAffineOpen U) :
    Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X, U)] Γ(g.relativeDifferentials, U) :=
  letI : Module R Γ(g.relativeDifferentials, U) := Module.compHom _ (algebraMap R Γ(X, U))
  haveI : IsScalarTower R Γ(X, U) Γ(g.relativeDifferentials, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  LinearEquiv.ofBijective _ (g.bijective_liftKaehlerDifferential_sectionsDerivation U h hU)

@[simp]
lemma kaehlerSectionsEquiv_D
    (h : algebraMap R Γ(X, U) = (g.specStructureMap U).hom) (hU : IsAffineOpen U) (b : Γ(X, U)) :
    g.kaehlerSectionsEquiv U h hU (KaehlerDifferential.D R Γ(X, U) b) = g.sectionsD U b :=
  letI : Module R Γ(g.relativeDifferentials, U) := Module.compHom _ (algebraMap R Γ(X, U))
  haveI : IsScalarTower R Γ(X, U) Γ(g.relativeDifferentials, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  Derivation.liftKaehlerDifferential_comp_D (g.sectionsDerivation U h) b

end AlgebraicGeometry.Scheme.Hom
