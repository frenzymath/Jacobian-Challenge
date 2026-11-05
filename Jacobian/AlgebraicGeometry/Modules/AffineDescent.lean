import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Jacobian.AlgebraicGeometry.Modules.FaithfullyFlatDescent
import Jacobian.AlgebraicGeometry.Modules.ZariskiDescent

/-!
# Effectivity over finite affine flat coverings

A quasi-coherent module descent datum along a finite affine flat covering is the associated sheaf of its algebraic descent module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TensorProduct CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- The compatibility condition for a family of morphisms between descent data holds over `Y`
if it holds over some `Z` through which `Y` factors. -/
lemma comm_of_factor {D₁ D₂ : F.DescentData f} (κ : ∀ i, D₁.obj i ⟶ D₂.obj i) {Z : C}
    (qZ : Z ⟶ S) {i₁ i₂ : ι} (p₁ : Z ⟶ X i₁) (p₂ : Z ⟶ X i₂) (hp₁ : p₁ ≫ f i₁ = qZ)
    (hp₂ : p₂ ≫ f i₂ = qZ)
    (hZ : (F.map p₁.op.toLoc).toFunctor.map (κ i₁) ≫ D₂.hom qZ p₁ p₂ hp₁ hp₂ =
      D₁.hom qZ p₁ p₂ hp₁ hp₂ ≫ (F.map p₂.op.toLoc).toFunctor.map (κ i₂))
    {Y : C} (q : Y ⟶ S) (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (g : Y ⟶ Z) (hg₁ : g ≫ p₁ = f₁) (hg₂ : g ≫ p₂ = f₂) :
    (F.map f₁.op.toLoc).toFunctor.map (κ i₁) ≫ D₂.hom q f₁ f₂ hf₁ hf₂ =
      D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (κ i₂) := by
  have hq : g ≫ qZ = q := by rw [← hp₁, ← Category.assoc, hg₁, hf₁]
  rw [← D₂.pullHom_hom g qZ q hq p₁ p₂ hp₁ hp₂ f₁ f₂ hg₁ hg₂,
    ← D₁.pullHom_hom g qZ q hq p₁ p₂ hp₁ hp₂ f₁ f₂ hg₁ hg₂]
  dsimp only [pullHom]
  rw [mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, hZ, Functor.map_comp_assoc,
    mapComp'_inv_naturality]
  simp only [Category.assoc]

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry.Scheme.Modules

/-- `pullHom` for `modulesPseudofunctor`, in terms of `pullbackCompOfEq`. -/
lemma modulesPseudofunctor_pullHom_eq_pullbackCompOfEq {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁)
    (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (F := modulesPseudofunctor) φ g gf₁ gf₂ hgf₁ hgf₂ =
      (pullbackCompOfEq g f₁ gf₁ hgf₁ M₁).inv ≫ (pullback g).map φ ≫
        (pullbackCompOfEq g f₂ gf₂ hgf₂ M₂).hom := by
  dsimp only [pullHom]
  rw [modulesPseudofunctor_mapComp'_hom_app_eq f₁ g gf₁ hgf₁,
    modulesPseudofunctor_mapComp'_inv_app_eq f₂ g gf₂ hgf₂]
  rfl

/-- `pullHom` for `modulesPseudofunctor` on global sections in the image of the unit. -/
lemma modulesPseudofunctor_pullHom_app_pullbackΓ {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁)
    (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (m : Γ(M₁, ⊤)) :
    Hom.app (pullHom (F := modulesPseudofunctor) φ g gf₁ gf₂ hgf₁ hgf₂ :
      (pullback gf₁).obj M₁ ⟶ (pullback gf₂).obj M₂) ⊤ (pullbackΓ gf₁ M₁ m) =
      Hom.app (pullbackCompOfEq g f₂ gf₂ hgf₂ M₂).hom ⊤
        (pullbackΓ g _ (φ.app ⊤ (pullbackΓ f₁ M₁ m))) := by
  calc _ = Hom.app ((pullbackCompOfEq g f₁ gf₁ hgf₁ M₁).inv ≫ (pullback g).map φ ≫
        (pullbackCompOfEq g f₂ gf₂ hgf₂ M₂).hom) ⊤ (pullbackΓ gf₁ M₁ m) := by
        rw [modulesPseudofunctor_pullHom_eq_pullbackCompOfEq]
        rfl
    _ = _ := by
        rw [Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply, pullbackCompOfEq_inv_app_pullbackΓ, pullbackΓ_naturality]

/-- The morphisms of a descent datum for `modulesPseudofunctor` on global sections in the image
of the unit, computed by pulling back along `g`. -/
lemma descentData_hom_app_pullbackΓ {ι : Type*} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (D : modulesPseudofunctor.DescentData f) {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q') {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (gf₁ : Y' ⟶ X i₁)
    (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₁' : gf₁ ≫ f i₁ = q') (hgf₂' : gf₂ ≫ f i₂ = q') (m : Γ(D.obj i₁, ⊤)) :
    Hom.app (D.hom q' gf₁ gf₂ hgf₁' hgf₂' :
      (pullback gf₁).obj (D.obj i₁) ⟶ (pullback gf₂).obj (D.obj i₂)) ⊤
        (pullbackΓ gf₁ _ m) =
      Hom.app (pullbackCompOfEq g f₂ gf₂ hgf₂ (D.obj i₂)).hom ⊤
        (pullbackΓ g _ (Hom.app (D.hom q f₁ f₂ hf₁ hf₂ :
          (pullback f₁).obj (D.obj i₁) ⟶ (pullback f₂).obj (D.obj i₂)) ⊤
            (pullbackΓ f₁ _ m))) := by
  rw [← D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  exact modulesPseudofunctor_pullHom_app_pullbackΓ _ g gf₁ gf₂ hgf₁ hgf₂ m

/-- A morphism of quasi-coherent modules on an affine scheme which is bijective on global
sections is an isomorphism. -/
lemma isIso_of_bijective_app_top {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (h : Function.Bijective (φ.app ⊤)) :
    IsIso φ := by
  let e := AddEquiv.ofBijective (φ.app ⊤).hom h
  have he (x : Γ(M, ⊤)) : e x = φ.app ⊤ x := rfl
  have key (r : Γ(Spec R, ⊤)) (n : Γ(N, ⊤)) : e.symm (r • n) = r • e.symm n := by
    apply e.injective
    rw [e.apply_symm_apply, he, Hom.app_smul, ← he, e.apply_symm_apply]
  obtain ⟨ψ, hψ⟩ := exists_hom_app_top_eq' (M := N) (N := M) e.symm.toAddMonoidHom
    (fun a n ↦ key _ n)
  refine ⟨ψ, hom_ext_of_isQuasicoherent_Spec fun m ↦ ?_, hom_ext_of_isQuasicoherent_Spec
    fun n ↦ ?_⟩
  · rw [Hom.comp_app, ConcreteCategory.comp_apply, hψ, Hom.id_app, ConcreteCategory.id_apply]
    exact e.symm_apply_apply m
  · rw [Hom.comp_app, ConcreteCategory.comp_apply, hψ, Hom.id_app, ConcreteCategory.id_apply]
    exact e.apply_symm_apply n

/-- The compatibility condition for morphisms `toDescentData P ⟶ D` in terms of
`pullbackCompOfEq`. -/
lemma toDescentData_comm_of {ι : Type*} {X : Scheme.{u}} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ X}
    (P : X.Modules) (D : modulesPseudofunctor.DescentData u)
    (κ : ∀ i, (pullback (u i)).obj P ⟶ D.obj i) {Y : Scheme.{u}} (q : Y ⟶ X) {i₁ i₂ : ι}
    (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂) (hf₁ : f₁ ≫ u i₁ = q) (hf₂ : f₂ ≫ u i₂ = q)
    (h : (pullback f₁).map (κ i₁) ≫ (D.hom q f₁ f₂ hf₁ hf₂ :
      (pullback f₁).obj (D.obj i₁) ⟶ (pullback f₂).obj (D.obj i₂)) =
      ((pullbackCompOfEq f₁ (u i₁) q hf₁ P).hom ≫ (pullbackCompOfEq f₂ (u i₂) q hf₂ P).inv) ≫
        (pullback f₂).map (κ i₂)) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (κ i₁) ≫ D.hom q f₁ f₂ hf₁ hf₂ =
      ((modulesPseudofunctor.toDescentData u).obj P).hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (κ i₂) := by
  rw [modulesPseudofunctor_toDescentData_obj_hom]
  exact h

end AlgebraicGeometry.Scheme.Modules

namespace TensorProduct

/-- For `A`-algebras `R` and `S` and an `R`-module `M`, the base change of `S ⊗[A] M` along
`R → R ⊗[A] S` identifies `S ⊗[A] M` with `(R ⊗[A] S) ⊗[R] M`. -/
lemma exists_addEquiv_tensor_baseChange (A R S M : Type*) [CommRing A] [CommRing R]
    [CommRing S] [Algebra A R] [Algebra A S] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower A R M] :
    ∃ Ψ : S ⊗[A] M ≃+ (R ⊗[A] S) ⊗[R] M, ∀ s m, Ψ (s ⊗ₜ m) = (1 ⊗ₜ s) ⊗ₜ m :=
  ⟨((TensorProduct.comm A S M).toAddEquiv.trans
    (AlgebraTensorModule.cancelBaseChange A R R M S).symm.toAddEquiv).trans
      (TensorProduct.comm R (R ⊗[A] S) M).symm.toAddEquiv, fun _ _ ↦ rfl⟩

end TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Abstract data of morphisms between affine schemes used in the proof of faithfully flat
descent for quasi-coherent modules along a family `f j : Spec (B j) ⟶ Spec A`: the "double
overlaps" `Spec (C j k)` with projections `p₁, p₂`, the diagonals `δ j`, the "triple
overlaps" `Spec (T j k l)` with their projections, together with the properties of these
morphisms on global sections (semilinearity, base change) which are used in the proof.
Working with abstract morphisms (rather than `Spec.map` of explicit ring maps) keeps the
kernel from unfolding the involved preimages of opens. See `AffineDescentData.ofAlgebra` for
the concrete instance. -/
structure AffineDescentData (A : Type u) [CommRing A] {J : Type u} (B : J → Type u)
    [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)] (C : J → J → Type u)
    [∀ j k, CommRing (C j k)] [∀ j k, Algebra A (C j k)] (T : J → J → J → Type u)
    [∀ j k l, CommRing (T j k l)] where
  /-- The morphisms of the family. -/
  f (j : J) : Spec (.of (B j)) ⟶ Spec (.of A)
  /-- The first projection of the double overlap. -/
  p₁ (j k : J) : Spec (.of (C j k)) ⟶ Spec (.of (B j))
  /-- The second projection of the double overlap. -/
  p₂ (j k : J) : Spec (.of (C j k)) ⟶ Spec (.of (B k))
  /-- The structure morphism of the double overlap. -/
  q (j k : J) : Spec (.of (C j k)) ⟶ Spec (.of A)
  hp₁ (j k : J) : p₁ j k ≫ f j = q j k
  hp₂ (j k : J) : p₂ j k ≫ f k = q j k
  /-- The ring map along which `p₁` is semilinear. -/
  ι (j k : J) : B j →+* C j k
  /-- The diagonal. -/
  δ (j : J) : Spec (.of (B j)) ⟶ Spec (.of (C j j))
  /-- The ring map along which `δ` is semilinear. -/
  μ (j : J) : C j j →+* B j
  /-- A morphism `Spec (B j) ⟶ Spec (B j)` (the identity in practice). -/
  u (j : J) : Spec (.of (B j)) ⟶ Spec (.of (B j))
  hδ₁ (j : J) : δ j ≫ p₁ j j = u j
  hδ₂ (j : J) : δ j ≫ p₂ j j = u j
  hu (j : J) : u j ≫ f j = f j
  hμ (j : J) (b : B j) : μ j (ι j j b) = b
  /-- The projection of the triple overlap to the overlap of the first two factors. -/
  π₁₂ (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of (C j k))
  /-- The projection of the triple overlap to the overlap of the last two factors. -/
  π₂₃ (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of (C k l))
  /-- The projection of the triple overlap to the overlap of the first and last factors. -/
  π₁₃ (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of (C j l))
  /-- The first projection of the triple overlap. -/
  r₁ (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of (B j))
  /-- The second projection of the triple overlap. -/
  r₂ (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of (B k))
  /-- The third projection of the triple overlap. -/
  r₃ (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of (B l))
  /-- The structure morphism of the triple overlap. -/
  Q (j k l : J) : Spec (.of (T j k l)) ⟶ Spec (.of A)
  hπ₁₂₁ (j k l : J) : π₁₂ j k l ≫ p₁ j k = r₁ j k l
  hπ₁₂₂ (j k l : J) : π₁₂ j k l ≫ p₂ j k = r₂ j k l
  hπ₂₃₁ (j k l : J) : π₂₃ j k l ≫ p₁ k l = r₂ j k l
  hπ₂₃₂ (j k l : J) : π₂₃ j k l ≫ p₂ k l = r₃ j k l
  hπ₁₃₁ (j k l : J) : π₁₃ j k l ≫ p₁ j l = r₁ j k l
  hπ₁₃₂ (j k l : J) : π₁₃ j k l ≫ p₂ j l = r₃ j k l
  hr₁ (j k l : J) : r₁ j k l ≫ f j = Q j k l
  hr₂ (j k l : J) : r₂ j k l ≫ f k = Q j k l
  hr₃ (j k l : J) : r₃ j k l ≫ f l = Q j k l
  /-- The ring map along which `π₁₂` is semilinear. -/
  σ₁₂ (j k l : J) : C j k →+* T j k l
  /-- The ring map along which `π₂₃` is semilinear. -/
  σ₂₃ (j k l : J) : C k l →+* T j k l
  /-- The ring map along which `π₁₃` is semilinear. -/
  σ₁₃ (j k l : J) : C j l →+* T j k l
  /-- The ring map `B j → T j k l`. -/
  ρ₁ (j k l : J) : B j →+* T j k l
  /-- The ring map `B k → T j k l`. -/
  ρ₂ (j k l : J) : B k →+* T j k l
  hσ₁₂ (j k l : J) (b : B j) : σ₁₂ j k l (ι j k b) = ρ₁ j k l b
  hσ₂₃ (j k l : J) (b : B k) : σ₂₃ j k l (ι k l b) = ρ₂ j k l b
  hσ₁₃ (j k l : J) (b : B j) : σ₁₃ j k l (ι j l b) = ρ₁ j k l b
  f_smul (j : J) (P : (Spec (.of A)).Modules) (a : A) (x : Γ(P, ⊤)) :
    pullbackΓ (f j) P (a • x) = algebraMap A (B j) a • pullbackΓ (f j) P x
  p₁_smul (j k : J) (P : (Spec (.of (B j))).Modules) (b : B j) (x : Γ(P, ⊤)) :
    pullbackΓ (p₁ j k) P (b • x) = ι j k b • pullbackΓ (p₁ j k) P x
  δ_smul (j : J) (P : (Spec (.of (C j j))).Modules) (c : C j j) (x : Γ(P, ⊤)) :
    pullbackΓ (δ j) P (c • x) = μ j c • pullbackΓ (δ j) P x
  u_smul (j : J) (P : (Spec (.of (B j))).Modules) (b : B j) (x : Γ(P, ⊤)) :
    pullbackΓ (u j) P (b • x) = b • pullbackΓ (u j) P x
  π₁₂_smul (j k l : J) (P : (Spec (.of (C j k))).Modules) (c : C j k) (x : Γ(P, ⊤)) :
    pullbackΓ (π₁₂ j k l) P (c • x) = σ₁₂ j k l c • pullbackΓ (π₁₂ j k l) P x
  π₂₃_smul (j k l : J) (P : (Spec (.of (C k l))).Modules) (c : C k l) (x : Γ(P, ⊤)) :
    pullbackΓ (π₂₃ j k l) P (c • x) = σ₂₃ j k l c • pullbackΓ (π₂₃ j k l) P x
  π₁₃_smul (j k l : J) (P : (Spec (.of (C j l))).Modules) (c : C j l) (x : Γ(P, ⊤)) :
    pullbackΓ (π₁₃ j k l) P (c • x) = σ₁₃ j k l c • pullbackΓ (π₁₃ j k l) P x
  f_base (j : J) (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] :
    ∃ e : B j ⊗[A] Γ(M, ⊤) ≃ₗ[B j] Γ((pullback (f j)).obj M, ⊤),
      ∀ m, e (1 ⊗ₜ m) = pullbackΓ (f j) M m
  q_base (j k : J) (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] :
    ∃ e : C j k ⊗[A] Γ(M, ⊤) ≃ₗ[C j k] Γ((pullback (q j k)).obj M, ⊤),
      ∀ m, e (1 ⊗ₜ m) = pullbackΓ (q j k) M m
  p₂_base (j k : J) (M : (Spec (.of (B k))).Modules) [M.IsQuasicoherent] [Module A Γ(M, ⊤)]
    [IsScalarTower A (B k) Γ(M, ⊤)] :
    ∃ e : B j ⊗[A] Γ(M, ⊤) ≃+ Γ((pullback (p₂ j k)).obj M, ⊤),
      ∀ b m, e (b ⊗ₜ m) = ι j k b • pullbackΓ (p₂ j k) M m
  r₃_base (j k l : J) (M : (Spec (.of (B l))).Modules) [M.IsQuasicoherent]
    [Module A Γ(M, ⊤)] [IsScalarTower A (B l) Γ(M, ⊤)] :
    ∃ e : B j ⊗[A] (B k ⊗[A] Γ(M, ⊤)) ≃+ Γ((pullback (r₃ j k l)).obj M, ⊤),
      ∀ b b' m, e (b ⊗ₜ (b' ⊗ₜ m)) = ρ₁ j k l b • ρ₂ j k l b' • pullbackΓ (r₃ j k l) M m
  u_injective (j : J) (M : (Spec (.of (B j))).Modules) [M.IsQuasicoherent] :
    Function.Injective (pullbackΓ (u j) M)
  exists_lift (j k : J) {Y : Scheme.{u}} (f₁ : Y ⟶ Spec (.of (B j))) (f₂ : Y ⟶ Spec (.of (B k)))
    (h : f₁ ≫ f j = f₂ ≫ f k) : ∃ g : Y ⟶ Spec (.of (C j k)), g ≫ p₁ j k = f₁ ∧ g ≫ p₂ j k = f₂

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.AffineDescentData

variable {A : Type u} [CommRing A] {J : Type u} {B : J → Type u} [∀ j, CommRing (B j)]
  [∀ j, Algebra A (B j)] {C : J → J → Type u} [∀ j k, CommRing (C j k)]
  [∀ j k, Algebra A (C j k)] {T : J → J → J → Type u} [∀ j k l, CommRing (T j k l)]
  (S : AffineDescentData A B C T) {D : modulesPseudofunctor.DescentData S.f}
  [∀ j, Module A Γ(D.obj j, ⊤)] [∀ j, IsScalarTower A (B j) Γ(D.obj j, ⊤)]

/-- The base change identification `B j ⊗[A] Γ(D k) ≃ Γ(p₂^* D k)`. -/
noncomputable def e₂ (hD : ∀ j, (D.obj j).IsQuasicoherent) (j k : J) :
    B j ⊗[A] Γ(D.obj k, ⊤) ≃+ Γ((pullback (S.p₂ j k)).obj (D.obj k), ⊤) :=
  Classical.choose (@S.p₂_base j k (D.obj k) (hD k) _ _)

/-- The value of `e₂` on a pure tensor. -/
lemma e₂_tmul (hD : ∀ j, (D.obj j).IsQuasicoherent) (j k : J) (b : B j) (m : Γ(D.obj k, ⊤)) :
    S.e₂ hD j k (b ⊗ₜ m) = S.ι j k b • pullbackΓ (S.p₂ j k) _ m :=
  Classical.choose_spec (@S.p₂_base j k (D.obj k) (hD k) _ _) b m

/-- `e₂` is semilinear along `ι j k`. -/
lemma e₂_smul (hD : ∀ j, (D.obj j).IsQuasicoherent) (j k : J) (b : B j)
    (t : B j ⊗[A] Γ(D.obj k, ⊤)) : S.e₂ hD j k (b • t) = S.ι j k b • S.e₂ hD j k t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b' m => rw [smul_tmul', smul_eq_mul, e₂_tmul, e₂_tmul, map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The coaction `θ j k : Γ(D j) → B j ⊗[A] Γ(D k)` induced by a descent datum. -/
noncomputable def θ (hD : ∀ j, (D.obj j).IsQuasicoherent) (j k : J) :
    Γ(D.obj j, ⊤) →ₗ[B j] B j ⊗[A] Γ(D.obj k, ⊤) where
  toFun n := (S.e₂ hD j k).symm
    (Hom.app (D.hom (S.q j k) (S.p₁ j k) (S.p₂ j k) (S.hp₁ j k) (S.hp₂ j k) :
      (pullback (S.p₁ j k)).obj (D.obj j) ⟶ (pullback (S.p₂ j k)).obj (D.obj k)) ⊤
        (pullbackΓ (S.p₁ j k) _ n))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' b n := by
    apply (S.e₂ hD j k).injective
    rw [S.p₁_smul, Hom.app_smul_of, RingHom.id_apply, e₂_smul, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]

/-- `e₂ (θ n)` is the gluing morphism applied to the image of `n` under the unit. -/
lemma e₂_θ (hD : ∀ j, (D.obj j).IsQuasicoherent) (j k : J) (n : Γ(D.obj j, ⊤)) :
    S.e₂ hD j k (S.θ hD j k n) =
      Hom.app (D.hom (S.q j k) (S.p₁ j k) (S.p₂ j k) (S.hp₁ j k) (S.hp₂ j k) :
        (pullback (S.p₁ j k)).obj (D.obj j) ⟶ (pullback (S.p₂ j k)).obj (D.obj k)) ⊤
          (pullbackΓ (S.p₁ j k) _ n) :=
  AddEquiv.apply_symm_apply _ _

/-- The unit condition for the coactions `θ`, obtained by pulling back along the diagonal. -/
lemma θ_unit (hD : ∀ j, (D.obj j).IsQuasicoherent) (j : J) (x : Γ(D.obj j, ⊤)) :
    (LinearMap.id : Γ(D.obj j, ⊤) →ₗ[A] Γ(D.obj j, ⊤)).liftBaseChange (B j)
      (S.θ hD j j x) = x := by
  have := hD j
  apply S.u_injective j (D.obj j)
  have hq : S.δ j ≫ S.q j j = S.f j := by
    rw [← S.hp₁ j j, ← Category.assoc, S.hδ₁, S.hu]
  have h1 := descentData_hom_app_pullbackΓ D (S.δ j) (S.q j j) (S.f j) hq (S.p₁ j j) (S.p₂ j j)
    (S.hp₁ j j) (S.hp₂ j j) (S.u j) (S.u j) (S.hδ₁ j) (S.hδ₂ j) (S.hu j) (S.hu j) x
  rw [D.hom_self (S.f j) (S.u j) (S.hu j), Hom.id_app, ConcreteCategory.id_apply] at h1
  rw [h1]
  rw [← S.e₂_θ hD]
  generalize S.θ hD j j x = t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b n =>
    rw [e₂_tmul, S.δ_smul, S.hμ, Hom.app_smul_of, pullbackCompOfEq_hom_app_pullbackΓ,
      LinearMap.liftBaseChange_tmul, LinearMap.id_apply, S.u_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicGeometry.Scheme.Modules.AffineDescentData

namespace AlgebraicGeometry.Scheme.Modules.AffineDescentData

variable {A : Type u} [CommRing A] {J : Type u} {B : J → Type u} [∀ j, CommRing (B j)]
  [∀ j, Algebra A (B j)] {C : J → J → Type u} [∀ j k, CommRing (C j k)]
  [∀ j k, Algebra A (C j k)] {T : J → J → J → Type u} [∀ j k l, CommRing (T j k l)]
  (S : AffineDescentData A B C T) {D : modulesPseudofunctor.DescentData S.f}
  [∀ j, Module A Γ(D.obj j, ⊤)] [∀ j, IsScalarTower A (B j) Γ(D.obj j, ⊤)]

/-- The cocycle condition for the coactions `θ`, obtained by pulling back to the triple overlaps
and using `DescentData.hom_comp`. -/
lemma θ_cocycle (hD : ∀ j, (D.obj j).IsQuasicoherent) (j k l : J) (x : Γ(D.obj j, ⊤)) :
    ((S.θ hD k l).restrictScalars A).lTensor (B j) (S.θ hD j k x) =
      (TensorProduct.mk A (B k) Γ(D.obj l, ⊤) 1).lTensor (B j) (S.θ hD j l x) := by
  have := hD l
  obtain ⟨E₃, hE₃⟩ := S.r₃_base j k l (D.obj l)
  apply E₃.injective
  have hq₁₂ : S.π₁₂ j k l ≫ S.q j k = S.Q j k l := by
    rw [← S.hp₁, ← Category.assoc, S.hπ₁₂₁, S.hr₁]
  have hq₂₃ : S.π₂₃ j k l ≫ S.q k l = S.Q j k l := by
    rw [← S.hp₁, ← Category.assoc, S.hπ₂₃₁, S.hr₂]
  have hq₁₃ : S.π₁₃ j k l ≫ S.q j l = S.Q j k l := by
    rw [← S.hp₁, ← Category.assoc, S.hπ₁₃₁, S.hr₁]
  have h12 := descentData_hom_app_pullbackΓ D (S.π₁₂ j k l) (S.q j k) (S.Q j k l) hq₁₂
    (S.p₁ j k) (S.p₂ j k) (S.hp₁ j k) (S.hp₂ j k) (S.r₁ j k l) (S.r₂ j k l) (S.hπ₁₂₁ j k l)
    (S.hπ₁₂₂ j k l) (S.hr₁ j k l) (S.hr₂ j k l) x
  have h13 := descentData_hom_app_pullbackΓ D (S.π₁₃ j k l) (S.q j l) (S.Q j k l) hq₁₃
    (S.p₁ j l) (S.p₂ j l) (S.hp₁ j l) (S.hp₂ j l) (S.r₁ j k l) (S.r₃ j k l) (S.hπ₁₃₁ j k l)
    (S.hπ₁₃₂ j k l) (S.hr₁ j k l) (S.hr₃ j k l) x
  have h23 (n : Γ(D.obj k, ⊤)) := descentData_hom_app_pullbackΓ D (S.π₂₃ j k l) (S.q k l)
    (S.Q j k l) hq₂₃ (S.p₁ k l) (S.p₂ k l) (S.hp₁ k l) (S.hp₂ k l) (S.r₂ j k l) (S.r₃ j k l)
    (S.hπ₂₃₁ j k l) (S.hπ₂₃₂ j k l) (S.hr₂ j k l) (S.hr₃ j k l) n
  have hcomp (y : Γ((pullback (S.r₁ j k l)).obj (D.obj j), ⊤)) :
      Hom.app (D.hom (S.Q j k l) (S.r₂ j k l) (S.r₃ j k l) (S.hr₂ j k l) (S.hr₃ j k l) :
        (pullback (S.r₂ j k l)).obj (D.obj k) ⟶ (pullback (S.r₃ j k l)).obj (D.obj l)) ⊤
        (Hom.app (D.hom (S.Q j k l) (S.r₁ j k l) (S.r₂ j k l) (S.hr₁ j k l) (S.hr₂ j k l) :
          (pullback (S.r₁ j k l)).obj (D.obj j) ⟶ (pullback (S.r₂ j k l)).obj (D.obj k)) ⊤ y) =
      Hom.app (D.hom (S.Q j k l) (S.r₁ j k l) (S.r₃ j k l) (S.hr₁ j k l) (S.hr₃ j k l) :
        (pullback (S.r₁ j k l)).obj (D.obj j) ⟶ (pullback (S.r₃ j k l)).obj (D.obj l)) ⊤ y := by
    rw [← D.hom_comp (S.Q j k l) (S.r₁ j k l) (S.r₂ j k l) (S.r₃ j k l) (S.hr₁ j k l)
      (S.hr₂ j k l) (S.hr₃ j k l)]
    rfl
  have hR (t : B j ⊗[A] Γ(D.obj l, ⊤)) :
      E₃ ((TensorProduct.mk A (B k) Γ(D.obj l, ⊤) 1).lTensor (B j) t) =
        Hom.app (pullbackCompOfEq (S.π₁₃ j k l) (S.p₂ j l) (S.r₃ j k l) (S.hπ₁₃₂ j k l)
          (D.obj l)).hom ⊤ (pullbackΓ (S.π₁₃ j k l) _ (S.e₂ hD j l t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b n =>
      rw [LinearMap.lTensor_tmul, TensorProduct.mk_apply, hE₃, map_one, one_smul, e₂_tmul,
        S.π₁₃_smul, S.hσ₁₃, Hom.app_smul_of, pullbackCompOfEq_hom_app_pullbackΓ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hL1 (b : B j) (s : B k ⊗[A] Γ(D.obj l, ⊤)) :
      E₃ (b ⊗ₜ s) = S.ρ₁ j k l b •
        Hom.app (pullbackCompOfEq (S.π₂₃ j k l) (S.p₂ k l) (S.r₃ j k l) (S.hπ₂₃₂ j k l)
          (D.obj l)).hom ⊤ (pullbackΓ (S.π₂₃ j k l) _ (S.e₂ hD k l s)) := by
    induction s using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero, smul_zero]
    | tmul b' n =>
      rw [hE₃, e₂_tmul, S.π₂₃_smul, S.hσ₂₃, Hom.app_smul_of, pullbackCompOfEq_hom_app_pullbackΓ]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy, smul_add]
  have hL2 (t : B j ⊗[A] Γ(D.obj k, ⊤)) :
      E₃ (((S.θ hD k l).restrictScalars A).lTensor (B j) t) =
        Hom.app (D.hom (S.Q j k l) (S.r₂ j k l) (S.r₃ j k l) (S.hr₂ j k l) (S.hr₃ j k l) :
          (pullback (S.r₂ j k l)).obj (D.obj k) ⟶ (pullback (S.r₃ j k l)).obj (D.obj l)) ⊤
          (Hom.app (pullbackCompOfEq (S.π₁₂ j k l) (S.p₂ j k) (S.r₂ j k l) (S.hπ₁₂₂ j k l)
            (D.obj k)).hom ⊤ (pullbackΓ (S.π₁₂ j k l) _ (S.e₂ hD j k t))) := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b n =>
      rw [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, hL1, S.e₂_θ, ← h23 n,
        e₂_tmul, S.π₁₂_smul, S.hσ₁₂, Hom.app_smul_of, pullbackCompOfEq_hom_app_pullbackΓ,
        Hom.app_smul_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hL2, hR, S.e₂_θ, S.e₂_θ, ← h12, ← h13, hcomp]

end AlgebraicGeometry.Scheme.Modules.AffineDescentData

namespace AlgebraicGeometry.Scheme.Modules

/-- The global sections of `E^~` on `Spec A` are `E`, as `A`-modules. -/
noncomputable def tildeΓLinearEquiv {A : Type u} [CommRing A] (E : Type u) [AddCommGroup E]
    [Module A E] : Γ(tilde (R := .of A) (ModuleCat.of A E), ⊤) ≃ₗ[A] E where
  toFun := (tilde.isoTop (R := .of A) (ModuleCat.of A E)).inv
  invFun := (tilde.isoTop (R := .of A) (ModuleCat.of A E)).hom
  map_add' := map_add _
  map_smul' a x := (tilde.isoTop (R := .of A) (ModuleCat.of A E)).inv.hom.map_smul a x
  left_inv x := congr($((tilde.isoTop (R := .of A) (ModuleCat.of A E)).inv_hom_id) x)
  right_inv x := congr($((tilde.isoTop (R := .of A) (ModuleCat.of A E)).hom_inv_id) x)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.AffineDescentData

open Pseudofunctor

variable {A : Type u} [CommRing A] {J : Type u} {B : J → Type u} [∀ j, CommRing (B j)]
  [∀ j, Algebra A (B j)] {C : J → J → Type u} [∀ j k, CommRing (C j k)]
  [∀ j k, Algebra A (C j k)] {T : J → J → J → Type u} [∀ j k l, CommRing (T j k l)]
  (S : AffineDescentData A B C T) {D : modulesPseudofunctor.DescentData S.f}
  [∀ j, Module A Γ(D.obj j, ⊤)] [∀ j, IsScalarTower A (B j) Γ(D.obj j, ⊤)]

/-- The compatibility of the comparison morphisms `κ` with the descent data, over the double
overlaps. -/
lemma comm_κ (hD : ∀ j, (D.obj j).IsQuasicoherent) (P : (Spec (.of A)).Modules)
    [P.IsQuasicoherent] (ψ : Γ(P, ⊤) →ₗ[A] TensorProduct.descentSubmodule (S.θ hD))
    (κ : ∀ j, (pullback (S.f j)).obj P ⟶ D.obj j)
    (hκ : ∀ j m, (κ j).app ⊤ (pullbackΓ (S.f j) P m) = (ψ m : ∀ j, Γ(D.obj j, ⊤)) j)
    (i₁ i₂ : J) :
    (pullback (S.p₁ i₁ i₂)).map (κ i₁) ≫
      (D.hom (S.q i₁ i₂) (S.p₁ i₁ i₂) (S.p₂ i₁ i₂) (S.hp₁ i₁ i₂) (S.hp₂ i₁ i₂) :
        (pullback (S.p₁ i₁ i₂)).obj (D.obj i₁) ⟶ (pullback (S.p₂ i₁ i₂)).obj (D.obj i₂)) =
      ((pullbackCompOfEq (S.p₁ i₁ i₂) (S.f i₁) (S.q i₁ i₂) (S.hp₁ i₁ i₂) P).hom ≫
        (pullbackCompOfEq (S.p₂ i₁ i₂) (S.f i₂) (S.q i₁ i₂) (S.hp₂ i₁ i₂) P).inv) ≫
        (pullback (S.p₂ i₁ i₂)).map (κ i₂) := by
  have := hD i₂
  obtain ⟨eq, heq⟩ := S.q_base i₁ i₂ P
  rw [← cancel_epi (pullbackCompOfEq (S.p₁ i₁ i₂) (S.f i₁) (S.q i₁ i₂) (S.hp₁ i₁ i₂) P).inv,
    Category.assoc, Iso.inv_hom_id_assoc]
  refine pullback_hom_ext_of eq heq fun m ↦ ?_
  have hmem := (TensorProduct.mem_descentSubmodule _ _).mp (ψ m).2 i₁ i₂
  have key : Hom.app (D.hom (S.q i₁ i₂) (S.p₁ i₁ i₂) (S.p₂ i₁ i₂) (S.hp₁ i₁ i₂) (S.hp₂ i₁ i₂) :
      (pullback (S.p₁ i₁ i₂)).obj (D.obj i₁) ⟶ (pullback (S.p₂ i₁ i₂)).obj (D.obj i₂)) ⊤
        (pullbackΓ (S.p₁ i₁ i₂) _ ((ψ m : ∀ j, Γ(D.obj j, ⊤)) i₁)) =
      pullbackΓ (S.p₂ i₁ i₂) _ ((ψ m : ∀ j, Γ(D.obj j, ⊤)) i₂) := by
    rw [← S.e₂_θ hD, hmem, e₂_tmul, map_one, one_smul]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackCompOfEq_inv_app_pullbackΓ, pullbackCompOfEq_inv_app_pullbackΓ,
    pullbackΓ_naturality, hκ]
  refine key.trans ?_
  have h2 := pullbackΓ_naturality (S.p₂ i₁ i₂) (κ i₂) (pullbackΓ (S.f i₂) P m)
  rw [hκ] at h2
  exact h2.symm

end AlgebraicGeometry.Scheme.Modules.AffineDescentData

namespace AlgebraicGeometry.Scheme.Modules.AffineDescentData

open Pseudofunctor

variable {A : Type u} [CommRing A] {J : Type u} {B : J → Type u} [∀ j, CommRing (B j)]
  [∀ j, Algebra A (B j)] {C : J → J → Type u} [∀ j k, CommRing (C j k)]
  [∀ j k, Algebra A (C j k)] {T : J → J → J → Type u} [∀ j k l, CommRing (T j k l)]

set_option maxHeartbeats 1000000 in
/-- **Faithfully flat descent of quasi-coherent modules, abstract affine version**: given
`S : AffineDescentData A B C T` with all `B j` flat over `A` and `J` finite, every descent
datum relative to `S.f` with quasi-coherent components is effective. -/
theorem exists_iso_toDescentData (S : AffineDescentData A B C T) [Finite J]
    [∀ j, Module.Flat A (B j)] (D : modulesPseudofunctor.DescentData S.f)
    [∀ j, Module A Γ(D.obj j, ⊤)] [∀ j, IsScalarTower A (B j) Γ(D.obj j, ⊤)]
    (hD : ∀ j, (D.obj j).IsQuasicoherent) :
    ∃ P : (Spec (.of A)).Modules, P.IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData S.f).obj P ≅ D) := by
  obtain ⟨P, hP, ⟨ψ⟩⟩ : ∃ (P : (Spec (.of A)).Modules) (_ : P.IsQuasicoherent),
      Nonempty (Γ(P, ⊤) ≃ₗ[A] TensorProduct.descentSubmodule (S.θ hD)) :=
    ⟨_, inferInstance, ⟨tildeΓLinearEquiv (A := A) (TensorProduct.descentSubmodule (S.θ hD))⟩⟩
  have hκ (j : J) : ∃ κ : (pullback (S.f j)).obj P ⟶ D.obj j, IsIso κ ∧
      ∀ m, κ.app ⊤ (pullbackΓ (S.f j) P m) = (ψ m : ∀ j, Γ(D.obj j, ⊤)) j := by
    have := hD j
    obtain ⟨e, he⟩ := S.f_base j P
    let g : Γ((pullback (S.f j)).obj P, ⊤) →ₗ[B j] Γ(D.obj j, ⊤) :=
      TensorProduct.descentLift (S.θ hD) j ∘ₗ (ψ.baseChange A (B j) _ _).toLinearMap ∘ₗ
        e.symm.toLinearMap
    obtain ⟨κ, hκ⟩ := exists_hom_app_top_eq' (R := .of (B j)) g.toAddMonoidHom
      (fun b y ↦ g.map_smul b y)
    have hg (m : Γ(P, ⊤)) : g (pullbackΓ (S.f j) P m) = (ψ m : ∀ j, Γ(D.obj j, ⊤)) j := by
      simp only [g, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap, ← he,
        LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
        TensorProduct.descentLift_tmul, one_smul]
    refine ⟨κ, isIso_of_bijective_app_top κ ?_, fun m ↦ (hκ _).trans (hg m)⟩
    have hκg : ⇑(κ.app ⊤) = g := funext hκ
    rw [hκg]
    exact ((TensorProduct.bijective_descentLift_of_flat (S.θ hD) (S.θ_unit hD)
      (S.θ_cocycle hD) j).comp (ψ.baseChange A (B j) _ _).bijective).comp e.symm.bijective
  choose κ hκiso hκ using hκ
  refine ⟨P, hP, ⟨DescentData.isoMk (fun j ↦ @asIso _ _ _ _ (κ j) (hκiso j)) ?_⟩⟩
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  obtain ⟨g, hg₁, hg₂⟩ := S.exists_lift i₁ i₂ f₁ f₂ (hf₁.trans hf₂.symm)
  refine DescentData.comm_of_factor (D₁ := (modulesPseudofunctor.toDescentData S.f).obj P)
    (D₂ := D) κ (S.q i₁ i₂) (S.p₁ i₁ i₂) (S.p₂ i₁ i₂)
    (S.hp₁ i₁ i₂) (S.hp₂ i₁ i₂) ?_ q f₁ f₂ hf₁ hf₂ g hg₁ hg₂
  exact toDescentData_comm_of P D κ _ _ _ _ _ (S.comm_κ hD P ψ.toLinearMap κ hκ i₁ i₂)

end AlgebraicGeometry.Scheme.Modules.AffineDescentData

namespace AlgebraicGeometry.Scheme.Modules.AffineDescentData

open Algebra.TensorProduct in
/-- The concrete `AffineDescentData` for a family of `A`-algebras `B j`: the morphisms are
`Spec.map` of the evident ring maps, with double overlaps `Spec (B k ⊗[A] B j)` and triple
overlaps `Spec (B l ⊗[A] (B k ⊗[A] B j))`. -/
noncomputable def ofAlgebra (A : Type u) [CommRing A] {J : Type u} (B : J → Type u)
    [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)] :
    AffineDescentData A B (fun j k ↦ B k ⊗[A] B j) (fun j k l ↦ B l ⊗[A] (B k ⊗[A] B j)) where
  f j := Spec.map (CommRingCat.ofHom (algebraMap A (B j)))
  p₁ j k := Spec.map (CommRingCat.ofHom (includeRight : B j →ₐ[A] B k ⊗[A] B j).toRingHom)
  p₂ j k := Spec.map (CommRingCat.ofHom (algebraMap (B k) (B k ⊗[A] B j)))
  q j k := Spec.map (CommRingCat.ofHom (algebraMap A (B k ⊗[A] B j)))
  hp₁ j k := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (includeRight : B j →ₐ[A] B k ⊗[A] B j).commutes a
  hp₂ j k := by
    rw [← Spec.map_comp]
    congr 1
  ι j k := (includeRight : B j →ₐ[A] B k ⊗[A] B j).toRingHom
  δ j := Spec.map (CommRingCat.ofHom (lmul' A : B j ⊗[A] B j →ₐ[A] B j).toRingHom)
  μ j := (lmul' A : B j ⊗[A] B j →ₐ[A] B j).toRingHom
  u j := Spec.map (CommRingCat.ofHom (algebraMap (B j) (B j)))
  hδ₁ j := by
    rw [← Spec.map_comp]
    congr 1
    ext b
    simp
  hδ₂ j := by
    rw [← Spec.map_comp]
    congr 1
    ext b
    simp
  hu j := by
    rw [← Spec.map_comp]
    congr 1
  hμ j b := by simp
  π₁₂ j k l := Spec.map (CommRingCat.ofHom
    (includeRight : B k ⊗[A] B j →ₐ[A] B l ⊗[A] (B k ⊗[A] B j)).toRingHom)
  π₂₃ j k l := Spec.map (CommRingCat.ofHom
    (map (AlgHom.id A (B l)) (includeLeft : B k →ₐ[A] B k ⊗[A] B j)).toRingHom)
  π₁₃ j k l := Spec.map (CommRingCat.ofHom
    (map (AlgHom.id A (B l)) (includeRight : B j →ₐ[A] B k ⊗[A] B j)).toRingHom)
  r₁ j k l := Spec.map (CommRingCat.ofHom ((includeRight : B k ⊗[A] B j →ₐ[A] _).comp
    (includeRight : B j →ₐ[A] B k ⊗[A] B j) : B j →ₐ[A] B l ⊗[A] (B k ⊗[A] B j)).toRingHom)
  r₂ j k l := Spec.map (CommRingCat.ofHom ((includeRight : B k ⊗[A] B j →ₐ[A] _).comp
    (includeLeft : B k →ₐ[A] B k ⊗[A] B j) : B k →ₐ[A] B l ⊗[A] (B k ⊗[A] B j)).toRingHom)
  r₃ j k l := Spec.map (CommRingCat.ofHom (algebraMap (B l) (B l ⊗[A] (B k ⊗[A] B j))))
  Q j k l := Spec.map (CommRingCat.ofHom (algebraMap A (B l ⊗[A] (B k ⊗[A] B j))))
  hπ₁₂₁ j k l := by
    rw [← Spec.map_comp]
    rfl
  hπ₁₂₂ j k l := by
    rw [← Spec.map_comp]
    congr 1
  hπ₂₃₁ j k l := by
    rw [← Spec.map_comp]
    congr 1
  hπ₂₃₂ j k l := by
    rw [← Spec.map_comp]
    congr 1
  hπ₁₃₁ j k l := by
    rw [← Spec.map_comp]
    congr 1
  hπ₁₃₂ j k l := by
    rw [← Spec.map_comp]
    congr 1
  hr₁ j k l := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp
  hr₂ j k l := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp
  hr₃ j k l := by
    rw [← Spec.map_comp]
    congr 1
  σ₁₂ j k l := (includeRight : B k ⊗[A] B j →ₐ[A] B l ⊗[A] (B k ⊗[A] B j)).toRingHom
  σ₂₃ j k l := (map (AlgHom.id A (B l)) (includeLeft : B k →ₐ[A] B k ⊗[A] B j)).toRingHom
  σ₁₃ j k l := (map (AlgHom.id A (B l)) (includeRight : B j →ₐ[A] B k ⊗[A] B j)).toRingHom
  ρ₁ j k l := ((includeRight : B k ⊗[A] B j →ₐ[A] _).comp
    (includeRight : B j →ₐ[A] B k ⊗[A] B j) : B j →ₐ[A] B l ⊗[A] (B k ⊗[A] B j)).toRingHom
  ρ₂ j k l := ((includeRight : B k ⊗[A] B j →ₐ[A] _).comp
    (includeLeft : B k →ₐ[A] B k ⊗[A] B j) : B k →ₐ[A] B l ⊗[A] (B k ⊗[A] B j)).toRingHom
  hσ₁₂ j k l b := rfl
  hσ₂₃ j k l b := by simp
  hσ₁₃ j k l b := by simp
  f_smul j P a x := pullbackΓ_smul P a x
  p₁_smul j k P b x := pullbackΓ_smul_ringHom _ P b x
  δ_smul j P c x := pullbackΓ_smul_ringHom _ P c x
  u_smul j P b x := pullbackΓ_smul P b x
  π₁₂_smul j k l P c x := pullbackΓ_smul_ringHom _ P c x
  π₂₃_smul j k l P c x := pullbackΓ_smul_ringHom _ P c x
  π₁₃_smul j k l P c x := pullbackΓ_smul_ringHom _ P c x
  f_base j M _ := exists_linearEquiv_pullback_Spec M
  q_base j k M _ := exists_linearEquiv_pullback_Spec M
  p₂_base j k M _ _ _ := by
    obtain ⟨e₀, he₀⟩ := exists_linearEquiv_pullback_Spec (extensionAlgebra := B k ⊗[A] B j) M
    obtain ⟨Ψ, hΨ⟩ := TensorProduct.exists_addEquiv_tensor_baseChange A (B k) (B j) Γ(M, ⊤)
    refine ⟨Ψ.trans e₀.toAddEquiv, fun b m ↦ ?_⟩
    have h1 : (Ψ.trans e₀.toAddEquiv) (b ⊗ₜ m) =
        e₀ ((1 ⊗ₜ[A] b : B k ⊗[A] B j) • (1 ⊗ₜ[B k] m)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← hΨ]
      rfl
    rw [h1, LinearEquiv.map_smul, he₀]
    rfl
  r₃_base j k l M _ _ _ := by
    obtain ⟨e₀, he₀⟩ := exists_linearEquiv_pullback_Spec
      (extensionAlgebra := B l ⊗[A] (B k ⊗[A] B j)) M
    obtain ⟨Ψ, hΨ⟩ := TensorProduct.exists_addEquiv_tensor_baseChange A (B l) (B k ⊗[A] B j)
      Γ(M, ⊤)
    let Φ : B j ⊗[A] (B k ⊗[A] Γ(M, ⊤)) ≃ₗ[A] (B k ⊗[A] B j) ⊗[A] Γ(M, ⊤) :=
      (TensorProduct.assoc A (B j) (B k) Γ(M, ⊤)).symm ≪≫ₗ
        TensorProduct.congr (TensorProduct.comm A (B j) (B k)) (LinearEquiv.refl A _)
    refine ⟨Φ.toAddEquiv.trans (Ψ.trans e₀.toAddEquiv), fun b b' m ↦ ?_⟩
    have h1 : (Φ.toAddEquiv.trans (Ψ.trans e₀.toAddEquiv)) (b ⊗ₜ (b' ⊗ₜ m)) =
        e₀ ((1 ⊗ₜ[A] (b' ⊗ₜ[A] b) : B l ⊗[A] (B k ⊗[A] B j)) • (1 ⊗ₜ[B l] m)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← hΨ]
      rfl
    rw [h1, LinearEquiv.map_smul, he₀, smul_smul]
    congr 1
    simp
  u_injective j M _ := by
    obtain ⟨e, he⟩ := exists_linearEquiv_pullback_Spec
      (baseAlgebra := B j) (extensionAlgebra := B j) M
    intro x y hxy
    rw [← he, ← he] at hxy
    apply (TensorProduct.lid (B j) Γ(M, ⊤)).symm.injective
    rw [TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply]
    exact e.injective hxy
  exists_lift j k Y f₁ f₂ h := by
    refine ⟨Limits.pullback.lift f₂ f₁ h.symm ≫ (pullbackSpecIso A (B k) (B j)).hom, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (Limits.pullback.lift f₂ f₁ h.symm ≫ ·)
        (pullbackSpecIso_hom_snd A (B k) (B j))).trans (Limits.pullback.lift_snd _ _ _))
    · rw [Category.assoc, pullbackSpecIso_hom_fst', Limits.pullback.lift_fst]

end AlgebraicGeometry.Scheme.Modules.AffineDescentData

namespace AlgebraicGeometry.Scheme.Modules

open Pseudofunctor

/-- **Fpqc descent for quasi-coherent modules, affine case**: a descent datum with
quasi-coherent components relative to a finite family of flat morphisms from affine schemes
covering `Spec R` is effective. -/
theorem exists_iso_toDescentData_of_finite_of_isAffine {R : CommRingCat.{u}} {J : Type u}
    [Finite J] {W : J → Scheme.{u}} [∀ j, IsAffine (W j)] (f : ∀ j, W j ⟶ Spec R)
    [∀ j, Flat (f j)] (hf : ⋃ j, Set.range (f j) = Set.univ)
    (D : modulesPseudofunctor.DescentData f)
    (hD : ∀ j, (D.obj j : (W j).Modules).IsQuasicoherent) :
    ∃ P : (Spec R).Modules, P.IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData f).obj P ≅ D) := by
  obtain ⟨A, _, rfl⟩ : ∃ (A : Type u) (_ : CommRing A), CommRingCat.of A = R := ⟨R, _, rfl⟩
  let B : J → Type u := fun j ↦ Γ(W j, ⊤)
  let _ : ∀ j, Algebra A (B j) := fun j ↦
    (Spec.preimage ((W j).isoSpec.inv ≫ f j)).hom.toAlgebra
  have hχ (j : J) : Spec.map (CommRingCat.ofHom (algebraMap A (B j))) = (W j).isoSpec.inv ≫ f j :=
    Spec.map_preimage _
  have hflat (j : J) : Module.Flat A (B j) := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap A (B j)))) := by
      rw [hχ]
      infer_instance
    rw [Flat.SpecMap_iff] at this
    exact RingHom.flat_algebraMap_iff.mp this
  let S := AffineDescentData.ofAlgebra A B
  have w (j : J) : (W j).isoSpec.inv ≫ f j = S.f j ≫ (Iso.refl (Spec (.of A))).hom := by
    rw [Iso.refl_hom, Category.comp_id]
    exact (hχ j).symm
  have w' (j : J) : (W j).isoSpec.hom ≫ S.f j = f j ≫ (Iso.refl (Spec (.of A))).inv := by
    rw [Iso.refl_inv, Category.comp_id]
    exact (congrArg ((W j).isoSpec.hom ≫ ·) (hχ j)).trans (Iso.hom_inv_id_assoc _ _)
  let e := DescentData.pullFunctorEquivalence modulesPseudofunctor (Iso.refl (Spec (.of A)))
    (α := id) (p' := fun j ↦ (W j).isoSpec.inv) w (β := id) (q' := fun j ↦ (W j).isoSpec.hom) w'
  let D' := e.functor.obj D
  have hD' (j : J) : (D'.obj j).IsQuasicoherent :=
    @isQuasicoherent_pullback _ _ (W j).isoSpec.inv _ (hD j)
  let _ (j : J) : Module A Γ(D'.obj j, ⊤) := Module.compHom _ (algebraMap A (B j))
  have (j : J) : IsScalarTower A (B j) Γ(D'.obj j, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨P, hP, ⟨iso⟩⟩ := S.exists_iso_toDescentData D' hD'
  let isoT : modulesPseudofunctor.toDescentData f ⋙ e.functor ≅
      modulesPseudofunctor.toDescentData S.f :=
    DescentData.toDescentDataCompPullFunctorIso _ _ ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (modulesPseudofunctor.mapId _)) _ ≪≫
        Functor.leftUnitor _
  exact ⟨P, hP, ⟨e.fullyFaithfulFunctor.preimageIso (isoT.app P ≪≫ iso)⟩⟩

end AlgebraicGeometry.Scheme.Modules
