import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Affine
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Jacobian.AlgebraicGeometry.Modules.AffinePushforward
import Jacobian.AlgebraicGeometry.Modules.Extension
import Jacobian.AlgebraicGeometry.Modules.LocallySurjective
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Mayer–Vietoris bounds for higher direct images

The pushforwards from two opens and their intersection form a
Mayer–Vietoris sequence. Applying it to injective resolutions propagates
quasi-coherence and cohomological bounds through finite unions. A finite
affine cover therefore gives bounded quasi-coherent higher direct images
for a quasi-compact quasi-separated morphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T)

/-- The functor `M ↦ f_{W,*} (M|_W)` for an open `W` of `X`, with `f_W = W.ι ≫ f`. -/
noncomputable def pushforwardRestrict (W : X.Opens) : X.Modules ⥤ T.Modules :=
  restrictFunctor W.ι ⋙ pushforward (W.ι ≫ f)

instance (W : X.Opens) : (pushforwardRestrict f W).Additive :=
  inferInstanceAs (restrictFunctor W.ι ⋙ pushforward (W.ι ≫ f)).Additive

/-- The open `f⁻¹ V ∩ W` of `X` on which `f_{W,*} (M|_W)` has its sections over `V`. -/
lemma image_preimage_ι_comp (W : X.Opens) (V : T.Opens) :
    W.ι ''ᵁ ((W.ι ≫ f) ⁻¹ᵁ V) = f ⁻¹ᵁ V ⊓ W := by
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm]

/-- The restriction map `f_{W,*} (M|_W) ⟶ f_{W',*} (M|_{W'})` for opens `W' ≤ W` of `X`, built
from the unit of the restriction to `W'` inside `W`. -/
noncomputable def pushforwardRestrictMapApp {W W' : X.Opens} (h : W' ≤ W) (M : X.Modules) :
    (pushforwardRestrict f W).obj M ⟶ (pushforwardRestrict f W').obj M :=
  (pushforward (W.ι ≫ f)).map ((restrictAdjunction (X.homOfLE h)).unit.app (M.restrict W.ι)) ≫
    (pushforwardComp (X.homOfLE h) (W.ι ≫ f)).hom.app _ ≫
    (pushforwardCongr (by rw [← Category.assoc, Scheme.homOfLE_ι])).hom.app _ ≫
    (pushforward (W'.ι ≫ f)).map ((restrictFunctorComp (X.homOfLE h) W.ι).inv.app M ≫
      (restrictFunctorCongr (Scheme.homOfLE_ι X h)).hom.app M)

/-- The open of `f_{W',*}`-sections over `V` is contained in that of `f_{W,*}`-sections. -/
lemma le_of_image_preimage_ι_comp {W W' : X.Opens} (h : W' ≤ W) (V : T.Opens) :
    W'.ι ''ᵁ ((W'.ι ≫ f) ⁻¹ᵁ V) ≤ W.ι ''ᵁ ((W.ι ≫ f) ⁻¹ᵁ V) := by
  rw [image_preimage_ι_comp, image_preimage_ι_comp]
  exact inf_le_inf_left _ h

set_option maxHeartbeats 1000000 in
lemma pushforwardRestrictMapApp_app {W W' : X.Opens} (h : W' ≤ W) (M : X.Modules)
    (V : T.Opens) :
    (pushforwardRestrictMapApp f h M).app V =
      M.presheaf.map (homOfLE (le_of_image_preimage_ι_comp f h V)).op := by
  simp only [pushforwardRestrictMapApp, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app]
  erw [Category.id_comp]
  rw [restrict_map (M.restrict W.ι) (X.homOfLE h), restrict_map M W.ι, restrict_map M W.ι]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The restriction map `f_{W,*} (M|_W) ⟶ f_{W',*} (M|_{W'})` for opens `W' ≤ W` of `X`, as a
natural transformation. -/
noncomputable def pushforwardRestrictMap {W W' : X.Opens} (h : W' ≤ W) :
    pushforwardRestrict f W ⟶ pushforwardRestrict f W' where
  app M := pushforwardRestrictMapApp f h M
  naturality M N φ := by
    refine hom_ext _ _ fun V ↦ ?_
    ext x
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforwardRestrictMapApp_app]
    exact (Hom.app_presheaf_map φ _ x).symm

lemma pushforwardRestrictMap_app_app {W W' : X.Opens} (h : W' ≤ W) (M : X.Modules)
    (V : T.Opens) :
    ((pushforwardRestrictMap f h).app M).app V =
      M.presheaf.map (homOfLE (le_of_image_preimage_ι_comp f h V)).op :=
  pushforwardRestrictMapApp_app f h M V

lemma pushforwardRestrictMap_comp {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') :
    pushforwardRestrictMap f h ≫ pushforwardRestrictMap f h' =
      pushforwardRestrictMap f (h'.trans h) := by
  ext M : 2
  refine hom_ext _ _ fun V ↦ ?_
  simp only [NatTrans.comp_app, Hom.comp_app, pushforwardRestrictMap_app_app, ← Functor.map_comp]
  rfl

section Sections

/-- A morphism of `𝒪_X`-modules which is injective on sections over every open is a
monomorphism. -/
lemma mono_of_forall_injective_app {M N : T.Modules} (φ : M ⟶ N)
    (h : ∀ V, Function.Injective (φ.app V)) : Mono φ where
  right_cancellation a b hab := by
    refine hom_ext _ _ fun V ↦ ?_
    ext x
    exact h V (by simpa using congrArg (fun ψ ↦ ψ.app V x) hab)

/-- A short complex of `𝒪_T`-modules which is injective on the left and exact in the middle on
the sections over every open is exact, with a monomorphism on the left. -/
lemma exact_and_mono_of_forall_app {S : ShortComplex T.Modules}
    (h₁ : ∀ V, Function.Injective (S.f.app V))
    (h₂ : ∀ V y, S.g.app V y = 0 → ∃ x, S.f.app V x = y) : S.Exact ∧ Mono S.f := by
  have := mono_of_forall_injective_app S.f h₁
  refine ⟨?_, this⟩
  rw [S.exact_iff_epi_kernel_lift]
  refine epi_of_forall_surjective_app _ fun V y ↦ ?_
  obtain ⟨x, hx⟩ := h₂ V ((kernel.ι S.g).app V y) (by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, kernel.condition, Hom.zero_app]
    rfl)
  refine ⟨x, injective_app_of_mono (kernel.ι S.g) (U := V) ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, kernel.lift_ι, hx]

/-- Sections of a binary biproduct of `𝒪_T`-modules are determined by their components. -/
lemma biprod_app_ext {A B : T.Modules} {V : T.Opens} {z z' : Γ(A ⊞ B, V)}
    (h₁ : (biprod.fst : A ⊞ B ⟶ A).app V z = (biprod.fst : A ⊞ B ⟶ A).app V z')
    (h₂ : (biprod.snd : A ⊞ B ⟶ B).app V z = (biprod.snd : A ⊞ B ⟶ B).app V z') : z = z' := by
  have h (w : Γ(A ⊞ B, V)) :
      w = (biprod.inl : A ⟶ A ⊞ B).app V ((biprod.fst : A ⊞ B ⟶ A).app V w) +
      (biprod.inr : B ⟶ A ⊞ B).app V ((biprod.snd : A ⊞ B ⟶ B).app V w) := by
    have := congrArg (fun φ ↦ φ.app V w) (biprod.total (X := A) (Y := B))
    simp only [Hom.add_app, Hom.comp_app, Hom.id_app] at this
    exact this.symm
  rw [h z, h z', h₁, h₂]

/-- Evaluating the negative of a morphism of `𝒪_T`-modules on a section. -/
lemma Hom.neg_app_apply {M N : T.Modules} (φ : M ⟶ N) (V : T.Opens) (x : Γ(M, V)) :
    (-φ).app V x = -φ.app V x :=
  rfl

/-- The sheaf condition of an `𝒪_X`-module for two opens. -/
lemma sheafCondition_mayerVietorisSquare (M : X.Modules) {A B C D : X.Opens} (hD : D = B ⊔ C)
    (hA : A = B ⊓ C) :
    (Opens.mayerVietorisSquare' (T := X)
      { X₁ := A
        X₂ := B
        X₃ := C
        X₄ := D
        f₁₂ := homOfLE (hA ▸ inf_le_left)
        f₁₃ := homOfLE (hA ▸ inf_le_right)
        f₂₄ := homOfLE (hD ▸ le_sup_left)
        f₃₄ := homOfLE (hD ▸ le_sup_right)
        fac := Subsingleton.elim _ _ } hD hA).SheafCondition
      (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf _
    ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u})).obj ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M))

end Sections

section MayerVietoris

variable (U V : X.Opens)

/-- The Mayer–Vietoris short complex
`f_{U ∪ V,*} M ⟶ f_{U,*} M ⊕ f_{V,*} M ⟶ f_{U ∩ V,*} M` of an `𝒪_X`-module `M`. -/
noncomputable def mvShortComplex (M : X.Modules) : ShortComplex T.Modules :=
  ShortComplex.mk
    (biprod.lift ((pushforwardRestrictMap f (le_sup_left : U ≤ U ⊔ V)).app M)
      ((pushforwardRestrictMap f (le_sup_right : V ≤ U ⊔ V)).app M))
    (biprod.desc ((pushforwardRestrictMap f (inf_le_left : U ⊓ V ≤ U)).app M)
      (-(pushforwardRestrictMap f (inf_le_right : U ⊓ V ≤ V)).app M)) (by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← NatTrans.comp_app, ← NatTrans.comp_app,
      pushforwardRestrictMap_comp, pushforwardRestrictMap_comp, add_neg_cancel])

lemma mvShortComplex_f_fst (M : X.Modules) (W : T.Opens)
    (x : Γ((mvShortComplex f U V M).X₁, W)) :
    (biprod.fst : _ ⟶ (pushforwardRestrict f U).obj M).app W
      ((mvShortComplex f U V M).f.app W x) =
      M.presheaf.map
        (homOfLE (le_of_image_preimage_ι_comp f (le_sup_left : U ≤ U ⊔ V) W)).op x := by
  have := congrArg (fun φ ↦ Hom.app φ W x)
    (biprod.lift_fst ((pushforwardRestrictMap f (le_sup_left : U ≤ U ⊔ V)).app M)
      ((pushforwardRestrictMap f (le_sup_right : V ≤ U ⊔ V)).app M))
  rw [pushforwardRestrictMap_app_app] at this
  exact this

lemma mvShortComplex_f_snd (M : X.Modules) (W : T.Opens)
    (x : Γ((mvShortComplex f U V M).X₁, W)) :
    (biprod.snd : _ ⟶ (pushforwardRestrict f V).obj M).app W
      ((mvShortComplex f U V M).f.app W x) =
      M.presheaf.map
        (homOfLE (le_of_image_preimage_ι_comp f (le_sup_right : V ≤ U ⊔ V) W)).op x := by
  have := congrArg (fun φ ↦ Hom.app φ W x)
    (biprod.lift_snd ((pushforwardRestrictMap f (le_sup_left : U ≤ U ⊔ V)).app M)
      ((pushforwardRestrictMap f (le_sup_right : V ≤ U ⊔ V)).app M))
  rw [pushforwardRestrictMap_app_app] at this
  exact this

lemma mvShortComplex_app_injective (M : X.Modules) (W : T.Opens) :
    Function.Injective ((mvShortComplex f U V M).f.app W) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h₁ := congrArg ((biprod.fst : _ ⟶ (pushforwardRestrict f U).obj M).app W) hx
  have h₂ := congrArg ((biprod.snd : _ ⟶ (pushforwardRestrict f V).obj M).app W) hx
  simp only [mvShortComplex, ← ConcreteCategory.comp_apply, ← Hom.comp_app, biprod.lift_fst,
    biprod.lift_snd, map_zero, pushforwardRestrictMap_app_app] at h₁ h₂
  have hs := sheafCondition_mayerVietorisSquare M
    (A := (U ⊓ V).ι ''ᵁ (((U ⊓ V).ι ≫ f) ⁻¹ᵁ W)) (B := U.ι ''ᵁ ((U.ι ≫ f) ⁻¹ᵁ W))
    (C := V.ι ''ᵁ ((V.ι ≫ f) ⁻¹ᵁ W)) (D := (U ⊔ V).ι ''ᵁ (((U ⊔ V).ι ≫ f) ⁻¹ᵁ W))
    (by simp only [image_preimage_ι_comp]; exact inf_sup_left _ _ _)
    (by simp only [image_preimage_ι_comp]; exact inf_inf_distrib_left _ _ _)
  refine hs.ext (y := 0) ?_ ?_
  · change (M.presheaf.map _) x = (M.presheaf.map _) 0
    rw [map_zero]
    exact h₁
  · change (M.presheaf.map _) x = (M.presheaf.map _) 0
    rw [map_zero]
    exact h₂

lemma mvShortComplex_app_exact (M : X.Modules) (W : T.Opens)
    (y : Γ((mvShortComplex f U V M).X₂, W)) (hy : (mvShortComplex f U V M).g.app W y = 0) :
    ∃ x, (mvShortComplex f U V M).f.app W x = y := by
  have hs := sheafCondition_mayerVietorisSquare M
    (A := (U ⊓ V).ι ''ᵁ (((U ⊓ V).ι ≫ f) ⁻¹ᵁ W)) (B := U.ι ''ᵁ ((U.ι ≫ f) ⁻¹ᵁ W))
    (C := V.ι ''ᵁ ((V.ι ≫ f) ⁻¹ᵁ W)) (D := (U ⊔ V).ι ''ᵁ (((U ⊔ V).ι ≫ f) ⁻¹ᵁ W))
    (by simp only [image_preimage_ι_comp]; exact inf_sup_left _ _ _)
    (by simp only [image_preimage_ι_comp]; exact inf_inf_distrib_left _ _ _)
  rw [show (mvShortComplex f U V M).g = biprod.fst ≫ (pushforwardRestrictMap f
      (inf_le_left : U ⊓ V ≤ U)).app M + biprod.snd ≫ (-(pushforwardRestrictMap f
      (inf_le_right : U ⊓ V ≤ V)).app M) from biprod.desc_eq] at hy
  rw [Hom.add_app, AddCommGrpCat.hom_add_apply, Hom.comp_app, Hom.comp_app,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Hom.neg_app_apply, add_neg_eq_zero,
    pushforwardRestrictMap_app_app, pushforwardRestrictMap_app_app] at hy
  refine ⟨hs.glue _ _ hy, biprod_app_ext ?_ ?_⟩
  · exact (mvShortComplex_f_fst f U V M W _).trans (hs.map_f₂₄_op_glue _ _ hy)
  · exact (mvShortComplex_f_snd f U V M W _).trans (hs.map_f₃₄_op_glue _ _ hy)

lemma mvShortComplex_app_surjective (M : X.Modules)
    [TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M).obj] (W : T.Opens) :
    Function.Surjective ((mvShortComplex f U V M).g.app W) := by
  intro c
  obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (TopCat.Presheaf.IsFlasque.epi (F := ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M).obj)
      (homOfLE (le_of_image_preimage_ι_comp f (inf_le_right : U ⊓ V ≤ V) W)).op) c
  refine ⟨(biprod.inr : _ ⟶ (mvShortComplex f U V M).X₂).app W (-b), ?_⟩
  have h := congrArg (fun φ ↦ φ.app W (-b))
    (biprod.inr_desc ((pushforwardRestrictMap f (inf_le_left : U ⊓ V ≤ U)).app M)
      (-(pushforwardRestrictMap f (inf_le_right : U ⊓ V ≤ V)).app M))
  simp only [Hom.comp_app] at h
  refine h.trans ?_
  rw [Hom.neg_app_apply, map_neg, neg_neg, pushforwardRestrictMap_app_app]
  exact hb

/-- The Mayer–Vietoris short complex of an `𝒪_X`-module is exact, with a monomorphism on the
left: this is the sheaf condition for the cover of `f⁻¹ W ∩ (U ∪ V)` by `f⁻¹ W ∩ U` and
`f⁻¹ W ∩ V`. -/
lemma mvShortComplex_exact_and_mono (M : X.Modules) :
    (mvShortComplex f U V M).Exact ∧ Mono (mvShortComplex f U V M).f :=
  exact_and_mono_of_forall_app (mvShortComplex_app_injective f U V M)
    (mvShortComplex_app_exact f U V M)

/-- The Mayer–Vietoris short complex of a flasque `𝒪_X`-module is short exact. -/
lemma mvShortComplex_shortExact (M : X.Modules)
    [TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M).obj] : (mvShortComplex f U V M).ShortExact :=
  have := (mvShortComplex_exact_and_mono f U V M).2
  have := epi_of_forall_surjective_app _ (mvShortComplex_app_surjective f U V M)
  .mk' (mvShortComplex_exact_and_mono f U V M).1 inferInstance inferInstance

/-- The complex `f_{W,*} (K|_W)` of a complex `K` of `𝒪_X`-modules. -/
noncomputable abbrev mvComplex (W : X.Opens) (K : CochainComplex X.Modules ℕ) :
    CochainComplex T.Modules ℕ :=
  ((pushforwardRestrict f W).mapHomologicalComplex _).obj K

/-- The restriction map `f_{W,*} (K|_W) ⟶ f_{W',*} (K|_{W'})` of complexes. -/
noncomputable abbrev mvComplexMap {W W' : X.Opens} (h : W' ≤ W) (K : CochainComplex X.Modules ℕ) :
    mvComplex f W K ⟶ mvComplex f W' K :=
  (NatTrans.mapHomologicalComplex (pushforwardRestrictMap f h) _).app K

/-- The Mayer–Vietoris short complex of complexes
`f_{U ∪ V,*} K ⟶ f_{U,*} K ⊕ f_{V,*} K ⟶ f_{U ∩ V,*} K`. -/
noncomputable def mvComplexShortComplex (K : CochainComplex X.Modules ℕ) :
    ShortComplex (CochainComplex T.Modules ℕ) :=
  ShortComplex.mk
    (biprod.lift (mvComplexMap f (le_sup_left : U ≤ U ⊔ V) K)
      (mvComplexMap f (le_sup_right : V ≤ U ⊔ V) K))
    (biprod.desc (mvComplexMap f (inf_le_left : U ⊓ V ≤ U) K)
      (-mvComplexMap f (inf_le_right : U ⊓ V ≤ V) K)) (by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, ← NatTrans.mapHomologicalComplex_comp,
      pushforwardRestrictMap_comp, pushforwardRestrictMap_comp, add_neg_cancel])

/-- In each degree, the Mayer–Vietoris short complex of complexes is the Mayer–Vietoris short
complex of the term. -/
noncomputable def mvComplexShortComplexEvalIso (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    mvShortComplex f U V (K.X n) ≅
      (mvComplexShortComplex f U V K).map (HomologicalComplex.eval _ _ n) :=
  ShortComplex.isoMk (Iso.refl _)
    ((HomologicalComplex.eval _ _ n).mapBiprod (mvComplex f U K) (mvComplex f V K)).symm
    (Iso.refl _) (by
      rw [Iso.symm_hom, ← cancel_mono ((HomologicalComplex.eval _ _ n).mapBiprod
        (mvComplex f U K) (mvComplex f V K)).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply biprod.hom_ext
      · simp only [Iso.refl_hom, ShortComplex.map_f, HomologicalComplex.eval_map,
          biprod.uniqueUpToIso_hom, Functor.mapBinaryBicone_fst, BinaryBiproduct.bicone_fst,
          Category.id_comp, Category.assoc, biprod.lift_fst, mvShortComplex, mvComplexShortComplex,
          ← HomologicalComplex.comp_f]
        exact (biprod.lift_fst _ _).symm
      · simp only [Iso.refl_hom, ShortComplex.map_f, HomologicalComplex.eval_map,
          biprod.uniqueUpToIso_hom, Functor.mapBinaryBicone_snd, BinaryBiproduct.bicone_snd,
          Category.id_comp, Category.assoc, biprod.lift_snd, mvShortComplex, mvComplexShortComplex,
          ← HomologicalComplex.comp_f]
        exact (biprod.lift_snd _ _).symm) (by
      apply biprod.hom_ext' <;>
        simp [mvShortComplex, mvComplexShortComplex, ← HomologicalComplex.comp_f])

/-- The Mayer–Vietoris short complex of a complex of flasque modules is short exact. -/
lemma mvComplexShortComplex_shortExact (K : CochainComplex X.Modules ℕ)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (K.X n)).obj) :
    (mvComplexShortComplex f U V K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    have := hK n
    ShortComplex.shortExact_of_iso (mvComplexShortComplexEvalIso f U V K n)
      (mvShortComplex_shortExact f U V (K.X n))

end MayerVietoris

section AffineCovers

/-- Two affine opens contained in an affine open meet in an affine open. -/
lemma isAffineOpen_inf_of_le {A V₁ V₂ : X.Opens} (hA : IsAffineOpen A) (hV₁ : IsAffineOpen V₁)
    (hV₂ : IsAffineOpen V₂) (h₁ : V₁ ≤ A) (h₂ : V₂ ≤ A) : IsAffineOpen (V₁ ⊓ V₂) :=
  have : IsIso (pullback.diagonal (𝟙 X)) := (pullback.isIso_diagonal_iff (𝟙 X)).mpr inferInstance
  (isAffineHom_diagonal_iff (f := 𝟙 X)).mp inferInstance A hA V₁ (by simpa using h₁) V₂
    (by simpa using h₂) hV₁ hV₂

/-- A quasi-compact open of a scheme is the union of a nonempty finite family of affine opens. -/
lemma exists_finset_affineOpens_sup_eq {W : X.Opens} (hW : IsCompact (W : Set X)) :
    ∃ t : Finset X.affineOpens, t.Nonempty ∧ t.sup (fun V ↦ (V : X.Opens)) = W := by
  classical
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun V : {V : X.affineOpens // (V : X.Opens) ≤ W} ↦ ((V.1 : X.Opens) : Set X))
    (fun V ↦ (V.1 : X.Opens).isOpen) (fun x hx ↦ by
      obtain ⟨V, hV, hxV, hVW⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
      exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩)
  refine ⟨insert ⟨⊥, isAffineOpen_bot X⟩ (t.map (Function.Embedding.subtype _)),
    Finset.insert_nonempty _ _, le_antisymm (Finset.sup_le fun V hV ↦ ?_) fun x hx ↦ ?_⟩
  · obtain rfl | hV := Finset.mem_insert.1 hV
    · exact bot_le
    obtain ⟨V', -, rfl⟩ := Finset.mem_map.1 hV
    exact V'.2
  · obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact (Finset.le_sup (f := fun V : X.affineOpens ↦ (V : X.Opens))
      (Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hV))) hxV

/-- Preimages commute with finite unions of opens. -/
lemma preimage_finset_sup {Y Z : Scheme.{u}} (φ : Y ⟶ Z) {ι : Type*} (s : Finset ι)
    (U : ι → Z.Opens) : φ ⁻¹ᵁ s.sup U = s.sup fun i ↦ φ ⁻¹ᵁ U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sup_insert, Finset.sup_insert, Scheme.Hom.preimage_sup, ih]

end AffineCovers

section Derived

variable [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)

/-- The property of an open `W` of `X` that the higher direct images `R^p f_{W,*} (ℱ|_W)` are
quasi-coherent for all `p`, and vanish for `p ≥ n`. They are written as the right derived
functors of `M ↦ f_{W,*} (M|_W)` at `ℱ`. -/
def HigherDirectImageBound (W : X.Opens) (n : ℕ) : Prop :=
  (∀ p, SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
    (((pushforwardRestrict f W).rightDerived p).obj ℱ)) ∧
  ∀ p ≥ n, IsZero (((pushforwardRestrict f W).rightDerived p).obj ℱ)

variable {f ℱ}

lemma HigherDirectImageBound.mono {W : X.Opens} {n m : ℕ} (h : HigherDirectImageBound f ℱ W n)
    (hnm : n ≤ m) : HigherDirectImageBound f ℱ W m :=
  ⟨h.1, fun p hp ↦ h.2 p (hnm.trans hp)⟩

instance (W : X.Opens) : PreservesFiniteLimits (pushforwardRestrict f W) :=
  have := (pullbackPushforwardAdjunction (W.ι ≫ f)).rightAdjoint_preservesLimits.{0, 0}
  comp_preservesFiniteLimits _ _

variable (f ℱ) in
/-- **The Mayer–Vietoris step.** If the higher direct images on `U`, `V` and `U ∩ V` are
quasi-coherent and vanish in degrees `≥ a`, `≥ b`, `≥ c`, then those on `U ∪ V` are
quasi-coherent and vanish in degrees `≥ max a b` and `≥ c + 1`. -/
theorem HigherDirectImageBound.sup {U V : X.Opens} {a b c : ℕ}
    (hU : HigherDirectImageBound f ℱ U a) (hV : HigherDirectImageBound f ℱ V b)
    (hUV : HigherDirectImageBound f ℱ (U ⊓ V) c) :
    HigherDirectImageBound f ℱ (U ⊔ V) (max (max a b) (c + 1)) := by
  let I := injectiveResolution ℱ
  have hK (n : ℕ) : TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (I.cocomplex.X n)).obj :=
    isFlasque_of_injective _
  let S := mvComplexShortComplex f U V I.cocomplex
  have hS : S.ShortExact := mvComplexShortComplex_shortExact f U V _ hK
  let e (W : X.Opens) (p : ℕ) := I.isoRightDerivedObj (pushforwardRestrict f W) p
  have (p : ℕ) : PreservesBinaryBiproducts
      (HomologicalComplex.homologyFunctor T.Modules (ComplexShape.up ℕ) p) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e₂ (p : ℕ) : S.X₂.homology p ≅ (mvComplex f U I.cocomplex).homology p ⊞
      (mvComplex f V I.cocomplex).homology p :=
    (HomologicalComplex.homologyFunctor _ _ p).mapBiprod _ _
  have hqc (W : X.Opens) (p : ℕ)
      (h : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
        (((pushforwardRestrict f W).rightDerived p).obj ℱ)) :
      SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
        ((mvComplex f W I.cocomplex).homology p) :=
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (e W p) h
  have hqc₂ (p : ℕ) : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf) (S.X₂.homology p) :=
    have := hqc U p (hU.1 p)
    have := hqc V p (hV.1 p)
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (e₂ p).symm
      (isQuasicoherent_biprod _ _)
  refine ⟨fun p ↦ ?_, fun p hp ↦ ?_⟩
  · cases p with
    | zero =>
      have h := mvShortComplex_exact_and_mono f U V ℱ
      have := h.2
      let z (W : X.Opens) := (pushforwardRestrict f W).rightDerivedZeroIsoSelf.app ℱ
      have : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
          ((pushforwardRestrict f U).obj ℱ) :=
        (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (z U) (hU.1 0)
      have : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
          ((pushforwardRestrict f V).obj ℱ) :=
        (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (z V) (hV.1 0)
      have : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
          (mvShortComplex f U V ℱ).X₃ :=
        (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (z (U ⊓ V)) (hUV.1 0)
      have : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
          (mvShortComplex f U V ℱ).X₂ :=
        isQuasicoherent_biprod _ _
      exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
        ((IsLimit.conePointUniqueUpToIso h.1.fIsKernel (kernelIsKernel _)).symm ≪≫
          (z (U ⊔ V)).symm) (isQuasicoherent_kernel (mvShortComplex f U V ℱ).g)
    | succ q =>
      refine (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
        (e (U ⊔ V) (q + 1)).symm ?_
      have := hqc₂ q
      have := hqc₂ (q + 1)
      have : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf) (S.X₃.homology q) :=
        hqc (U ⊓ V) q (hUV.1 q)
      have : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf) (S.X₃.homology (q + 1)) :=
        hqc (U ⊓ V) (q + 1) (hUV.1 (q + 1))
      exact isQuasicoherent_of_exact (hS.homology_exact₃ q (q + 1) rfl)
        (hS.homology_exact₁ q (q + 1) rfl) (hS.homology_exact₂ (q + 1))
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    refine IsZero.of_iso ?_ (e (U ⊔ V) (q + 1))
    refine (hS.homology_exact₁ q (q + 1) rfl).isZero_X₂
      (IsZero.eq_of_src (IsZero.of_iso (hUV.2 q (by omega)) (e (U ⊓ V) q).symm) _ _)
      (IsZero.eq_of_tgt (IsZero.of_iso ?_ (e₂ (q + 1))) _ _)
    exact (biprod_isZero_iff _ _).2
      ⟨IsZero.of_iso (hU.2 (q + 1) (by omega)) (e U (q + 1)).symm,
        IsZero.of_iso (hV.2 (q + 1) (by omega)) (e V (q + 1)).symm⟩

variable (f ℱ) in
/-- **The affine case.** If `f_W : W ⟶ T` is affine and `ℱ` is quasi-coherent, then
`f_{W,*} ℱ|_W` is quasi-coherent and `R^p f_{W,*} (ℱ|_W) = 0` for `p > 0`. -/
theorem higherDirectImageBound_of_isAffineHom (W : X.Opens) [IsAffineHom (W.ι ≫ f)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    HigherDirectImageBound f ℱ W 1 := by
  have := isGrothendieckAbelian (W : Scheme.{u})
  have hE (I : X.Modules) [Injective I] :
      (pushforward (W.ι ≫ f)).rightAcyclic ((restrictFunctor W.ι).obj I) :=
    rightAcyclic_pushforward_of_isFlasque _ _
      (isFlasque_restrict W.ι _ (isFlasque_of_injective I))
  let e (p : ℕ) : ((pushforwardRestrict f W).rightDerived p).obj ℱ ≅
      (higherDirectImage (W.ι ≫ f) p).obj (ℱ.restrict W.ι) :=
    Functor.compRightDerivedObjIso (restrictFunctor W.ι) (pushforward (W.ι ≫ f)) hE p ℱ
  refine ⟨fun p ↦ ?_, fun p hp ↦
    IsZero.of_iso (isZero_higherDirectImage_of_isAffineHom _ _ (by omega)) (e p)⟩
  cases p with
  | zero =>
    exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
      ((pushforwardRestrict f W).rightDerivedZeroIsoSelf.app ℱ).symm
      (isQuasicoherent_pushforward_of_isAffineHom (W.ι ≫ f) (ℱ.restrict W.ι))
  | succ q =>
    exact isQuasicoherent_of_isZero
      (IsZero.of_iso (isZero_higherDirectImage_of_isAffineHom _ _ (by omega)) (e (q + 1)))

variable (f) in
/-- The comparison `f_* M ⟶ f_{X,*} (M|_X)` for the open `⊤` of `X`. -/
noncomputable def pushforwardToPushforwardRestrictTop :
    pushforward f ⟶ pushforwardRestrict f ⊤ :=
  Functor.whiskerRight (restrictAdjunction (⊤ : X.Opens).ι).unit (pushforward f) ≫
    Functor.whiskerLeft (restrictFunctor (⊤ : X.Opens).ι) (pushforwardComp (⊤ : X.Opens).ι f).hom

instance : IsIso (pushforwardToPushforwardRestrictTop f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [Hom.isIso_iff_isIso_app]
  intro V
  simp only [pushforwardToPushforwardRestrictTop, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    pushforwardComp_hom_app_app]
  exact isIso_presheaf_map_of_le M _ (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, top_inf_eq])

/-- The bound on the open `⊤` is a bound for the higher direct images `R^p f_* ℱ`. -/
theorem HigherDirectImageBound.higherDirectImage {n : ℕ} (h : HigherDirectImageBound f ℱ ⊤ n) :
    (∀ p, SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf)
      ((higherDirectImage f p).obj ℱ)) ∧
    ∀ p ≥ n, IsZero ((higherDirectImage f p).obj ℱ) :=
  let e (p : ℕ) := Functor.rightDerivedObjIsoOfIso (asIso (pushforwardToPushforwardRestrictTop f))
    p ℱ
  ⟨fun p ↦ (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (e p).symm (h.1 p),
    fun p hp ↦ IsZero.of_iso (h.2 p hp) (e p)⟩

variable (f ℱ) in
/-- **Mayer–Vietoris induction.** Let `B` be a class of opens of `X` stable under binary
intersections, on whose members the higher direct images of `ℱ` are quasi-coherent and vanish in
degrees `≥ N`. Then on the union of `k ≥ 1` members of `B` they are quasi-coherent and vanish in
degrees `≥ N + k - 1`. -/
theorem higherDirectImageBound_finsetSup (B : X.Opens → Prop)
    (hB : ∀ U V, B U → B V → B (U ⊓ V)) {N : ℕ}
    (hN : ∀ U, B U → HigherDirectImageBound f ℱ U N) {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) :
    ∀ (U : ι → X.Opens), (∀ i ∈ s, B (U i)) →
      HigherDirectImageBound f ℱ (s.sup U) (N + s.card - 1) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro U hU
    simpa using hN _ (hU a (Finset.mem_singleton_self a))
  | cons a s ha hs ih =>
    intro U hU
    rw [Finset.sup_cons, Finset.card_cons]
    have h₁ := hN _ (hU a (Finset.mem_cons_self a s))
    have h₂ := ih U (fun i hi ↦ hU i (Finset.mem_cons_of_mem hi))
    have h₃ := ih (fun i ↦ U a ⊓ U i)
      (fun i hi ↦ hB _ _ (hU a (Finset.mem_cons_self a s)) (hU i (Finset.mem_cons_of_mem hi)))
    rw [← Finset.sup_inf_distrib_left] at h₃
    refine (HigherDirectImageBound.sup f ℱ h₁ h₂ h₃).mono ?_
    have := hs.card_pos
    omega

variable (f ℱ) [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- Over an affine base, the higher direct images on an affine open `W` are quasi-coherent and
vanish in positive degrees. -/
theorem higherDirectImageBound_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) :
    HigherDirectImageBound f ℱ W 1 :=
  have : IsAffine W := hW
  higherDirectImageBound_of_isAffineHom f ℱ W

/-- **Vanishing above the size of an affine cover.** Let `T` be affine and let `U i`, `i ∈ s`,
be affine opens of `X`, each intersection `U i ∩ U j` being covered by at most `m` affine opens.
Then the higher direct images of `ℱ` on `⋃ U i` are quasi-coherent and vanish in degrees
`≥ #s * m + 2`. -/
theorem higherDirectImageBound_of_affineCover {ι κ : Type*} (s : Finset ι) (hs : s.Nonempty)
    (U : ι → X.Opens) (hU : ∀ i ∈ s, IsAffineOpen (U i)) (t : ι → ι → Finset κ)
    (V : κ → X.Opens) (hV : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ t i j, IsAffineOpen (V k))
    (hUV : ∀ i ∈ s, ∀ j ∈ s, (t i j).sup V = U i ⊓ U j) (m : ℕ)
    (hm : ∀ i ∈ s, ∀ j ∈ s, (t i j).card ≤ m) :
    HigherDirectImageBound f ℱ (s.sup U) (s.card * m + 2) := by
  classical
  suffices h : ∀ s' ⊆ s, s'.Nonempty →
      HigherDirectImageBound f ℱ (s'.sup U) (s'.card * m + 2) from h s subset_rfl hs
  intro s' hs' hne
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using (higherDirectImageBound_of_isAffineOpen f ℱ
      (hU a (hs' (Finset.mem_singleton_self a)))).mono (by omega)
  | cons a s' ha hne ih =>
    have has : a ∈ s := hs' (Finset.mem_cons_self a s')
    have hs's : s' ⊆ s := (Finset.subset_cons ha).trans hs'
    rw [Finset.sup_cons, Finset.card_cons]
    let F : Finset (Option κ) := insert none ((s'.biUnion (t a)).map Function.Embedding.some)
    let V' : Option κ → X.Opens := fun o ↦ o.elim ⊥ V
    have hF : F.sup V' = U a ⊓ s'.sup U := by
      rw [Finset.sup_insert, Finset.sup_map, Finset.sup_inf_distrib_left, Finset.sup_biUnion]
      simp only [Option.elim_none, bot_sup_eq, V']
      exact Finset.sup_congr rfl fun i hi ↦ hUV a has i (hs's hi)
    have hFcard : F.card ≤ s'.card * m + 1 := by
      have h₁ : (s'.biUnion (t a)).card ≤ s'.card * m := by
        refine Finset.card_biUnion_le.trans ?_
        simpa using Finset.sum_le_card_nsmul s' _ m fun i hi ↦ hm a has i (hs's hi)
      have h₂ : F.card ≤ ((s'.biUnion (t a)).map Function.Embedding.some).card + 1 :=
        Finset.card_insert_le _ _
      rw [Finset.card_map] at h₂
      omega
    have h₃ := higherDirectImageBound_finsetSup f ℱ
      (fun W ↦ IsAffineOpen W ∧ W ≤ U a)
      (fun W₁ W₂ h₁ h₂ ↦ ⟨isAffineOpen_inf_of_le (hU a has) h₁.1 h₂.1 h₁.2 h₂.2,
        inf_le_left.trans h₁.2⟩)
      (fun W hW ↦ higherDirectImageBound_of_isAffineOpen f ℱ hW.1) F
      (Finset.insert_nonempty _ _) V' (fun o ho ↦ ?_)
    · rw [hF] at h₃
      refine (HigherDirectImageBound.sup f ℱ (higherDirectImageBound_of_isAffineOpen f ℱ
        (hU a has)) (ih hs's) h₃).mono ?_
      have : (s'.card + 1) * m + 2 = s'.card * m + m + 2 := by ring
      omega
    · rcases Finset.mem_insert.1 ho with rfl | ho
      · exact ⟨isAffineOpen_bot X, bot_le⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 ho
        obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.1 hk
        refine ⟨hV a has i (hs's hi) k hk, ?_⟩
        exact (Finset.le_sup (f := V) hk).trans
          ((hUV a has i (hs's hi)).le.trans inf_le_left)

/-- **Vanishing in high degrees over an affine base.** Over an affine base `T`, for `f`
quasi-compact and quasi-separated, the higher direct images of a quasi-coherent module are
quasi-coherent and vanish in high degrees. -/
theorem exists_higherDirectImageBound_top [QuasiCompact f] [QuasiSeparated f] :
    ∃ n, HigherDirectImageBound f ℱ ⊤ n := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨s, hs, hcov⟩ := exists_finset_isAffineOpen_sup_eq_top (scheme := X)
  have (i j : X.affineOpens) : ∃ t : Finset X.affineOpens,
      t.sup (fun V ↦ (V : X.Opens)) = (i : X.Opens) ⊓ j :=
    (exists_finset_affineOpens_sup_eq (QuasiSeparatedSpace.inter_isCompact _ _ i.1.isOpen
      i.2.isCompact j.1.isOpen j.2.isCompact)).imp fun _ h ↦ h.2
  choose t ht using this
  refine ⟨_, hcov ▸ higherDirectImageBound_of_affineCover f ℱ s hs (fun i ↦ i) (fun i _ ↦ i.2) t
    (fun V ↦ V) (fun _ _ _ _ V _ ↦ V.2) (fun i _ j _ ↦ ht i j)
    ((s ×ˢ s).sup fun p ↦ (t p.1 p.2).card) fun i hi j hj ↦
      Finset.le_sup (f := fun p : X.affineOpens × X.affineOpens ↦ (t p.1 p.2).card)
        (b := (i, j)) (Finset.mem_product.2 ⟨hi, hj⟩)⟩

end Derived

end AlgebraicGeometry.Scheme.Modules
