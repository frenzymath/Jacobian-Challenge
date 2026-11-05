import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
import Jacobian.AlgebraicGeometry.Modules.FaithfullyFlatDescent
import Jacobian.AlgebraicGeometry.Modules.ZariskiDescent
import Jacobian.CategoryTheory.Sites.SigmaPresheaf

/-!
# Fpqc descent of quasi-coherent module morphisms

Zariski and affine faithfully flat descent imply full faithfulness for quasi-coherent modules on the fpqc site.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe w u

open CategoryTheory Opposite

namespace CategoryTheory

/-- The sheaf condition for the family `Over.homMk (u i) : Over.mk (u i ≫ y) ⟶ Over.mk y` only
depends on `y` up to equality. -/
lemma Over.isSheafFor_ofArrows_homMk_congr {C : Type*} [Category* C] {Z : C}
    (P : (Over Z)ᵒᵖ ⥤ Type*) {Y : C} {ι : Type*} {U : ι → C} (u : ∀ i, U i ⟶ Y)
    {y y' : Y ⟶ Z} (h : y = y') :
    (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ y))
      (fun i ↦ (Over.homMk (u i) rfl : Over.mk (u i ≫ y) ⟶ Over.mk y))).IsSheafFor P ↔
    (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ y))
      (fun i ↦ (Over.homMk (u i) (by simp [h]) : Over.mk (u i ≫ y) ⟶ Over.mk y'))).IsSheafFor
        P := by
  subst h
  rfl

/-- `F.presheafHom M N` is a sheaf for the family `Over.homMk (u i) : Over.mk (u i ≫ y) ⟶
Over.mk y` if and only if `F.toDescentData u` is bijective on morphisms between the pullbacks
of `M` and `N` along `y`. -/
lemma Pseudofunctor.isSheafFor_presheafHom_ofArrows_iff {C : Type*} [Category* C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat) {Z Y : C} (y : Y ⟶ Z) {ι : Type*}
    {U : ι → C} (u : ∀ i, U i ⟶ Y) (M N : F.obj (.mk (op Z))) :
    (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ y))
      (fun i ↦ (Over.homMk (u i) rfl : Over.mk (u i ≫ y) ⟶ Over.mk y))).IsSheafFor
        (F.presheafHom M N) ↔
    Function.Bijective ((F.toDescentData u).map :
      ((F.map (.toLoc y.op)).toFunctor.obj M ⟶ (F.map (.toLoc y.op)).toFunctor.obj N) → _) := by
  rw [Pseudofunctor.bijective_toDescentData_map_iff,
    ← Presieve.isSheafFor_iff_of_iso (F.overMapCompPresheafHomIso M N y),
    Presieve.isSheafFor_over_map_op_comp_ofArrows_iff,
    Over.isSheafFor_ofArrows_homMk_congr _ u (Category.id_comp y).symm]
  rfl

end CategoryTheory

namespace AlgebraicGeometry

/-- Descent of morphisms of quasi-coherent modules along `Spec.map φ` for `φ` flat and
surjective on spectra. -/
lemma Scheme.Modules.bijective_toDescentData_map_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Flat (Spec.map φ)) (hs : Surjective (Spec.map φ)) (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective ((modulesPseudofunctor.toDescentData
      (fun _ : Unit ↦ Spec.map φ)).map : (M ⟶ N) → _) := by
  have hff := (flat_and_surjective_SpecMap_iff φ).1 ⟨hφ, hs⟩

  obtain ⟨A, _, rfl⟩ : ∃ (A : Type u) (_ : CommRing A), CommRingCat.of A = R := ⟨R, _, rfl⟩
  obtain ⟨B, _, rfl⟩ : ∃ (B : Type u) (_ : CommRing B), CommRingCat.of B = S := ⟨S, _, rfl⟩
  obtain ⟨f, rfl⟩ : ∃ f : A →+* B, CommRingCat.ofHom f = φ := ⟨φ.hom, rfl⟩
  algebraize [f]
  have e : CommRingCat.ofHom f = CommRingCat.ofHom (algebraMap A B) := rfl
  rw [e]
  exact bijective_toDescentData_map_Spec (A := A) (B := B) M N

/-- The presheaf of morphisms between two sheaves of modules is a sheaf for (the family over
`y : Y ⟶ T` induced by) an open cover of `Y`. -/
lemma isSheafFor_presheafHom_ofArrows_openCover {T : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op T))) {Y : Scheme.{u}} (𝒰 : Y.OpenCover)
    (y : Y ⟶ T) :
    (Presieve.ofArrows (fun i ↦ Over.mk (𝒰.f i ≫ y))
      (fun i ↦ (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ y) ⟶ Over.mk y))).IsSheafFor
        (modulesPseudofunctor.presheafHom M N) := by
  rw [Pseudofunctor.isSheafFor_presheafHom_ofArrows_iff]
  exact bijective_toDescentData_map_of_isOpenImmersion _ 𝒰.iSup_opensRange _ _

/-- The presheaf of morphisms between two quasi-coherent modules is a sheaf for (the family
over `y : Spec R ⟶ T` induced by) `Spec.map φ`, for `φ` flat and surjective on spectra. -/
lemma isSheafFor_presheafHom_ofArrows_SpecMap {T : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op T)))
    (hM : (M : T.Modules).IsQuasicoherent) (hN : (N : T.Modules).IsQuasicoherent)
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Flat (Spec.map φ))
    (hs : Surjective (Spec.map φ)) (y : Spec R ⟶ T) :
    (Presieve.ofArrows (fun _ : Unit ↦ Over.mk (Spec.map φ ≫ y))
      (fun _ ↦ (Over.homMk (Spec.map φ) rfl :
        Over.mk (Spec.map φ ≫ y) ⟶ Over.mk y))).IsSheafFor
          (modulesPseudofunctor.presheafHom M N) := by
  rw [Pseudofunctor.isSheafFor_presheafHom_ofArrows_iff]
  exact @Scheme.Modules.bijective_toDescentData_map_SpecMap _ _ φ hφ hs _ _
    (@Scheme.Modules.isQuasicoherent_pullback _ _ y M hM)
    (@Scheme.Modules.isQuasicoherent_pullback _ _ y N hN)

set_option backward.isDefEq.respectTransparency.types false in
/-- For quasi-coherent `M` and `N` on `T`, the presheaf on schemes
`Y ↦ Σ (y : Y ⟶ T), (y^* M ⟶ y^* N)` is a sheaf for the fpqc topology. -/
lemma isSheaf_sigmaPresheaf_presheafHom {T : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op T)))
    (hM : (M : T.Modules).IsQuasicoherent) (hN : (N : T.Modules).IsQuasicoherent) :
    Presieve.IsSheaf Scheme.fpqcTopology
      (Over.sigmaPresheaf (modulesPseudofunctor.presheafHom M N)) := by
  have hT := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fpqcTopology) (yoneda.obj T)
  rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff] at hT ⊢
  obtain ⟨hTz, hTs⟩ := hT
  refine ⟨?_, fun {R S} φ hφ hs ↦ ?_⟩
  · rw [Scheme.zariskiTopology_eq, Presieve.isSheaf_pretopology] at hTz ⊢
    intro Y R hR
    obtain ⟨𝒰, rfl⟩ := Scheme.exists_cover_of_mem_pretopology hR
    exact Over.isSheafFor_sigmaPresheaf _ 𝒰.f (hTz _ hR)
      fun y ↦ isSheafFor_presheafHom_ofArrows_openCover M N 𝒰 y
  · have hT' := hTs φ hφ hs
    rw [← Presieve.ofArrows_pUnit] at hT' ⊢
    exact Over.isSheafFor_sigmaPresheaf _ _ hT'
      fun y ↦ isSheafFor_presheafHom_ofArrows_SpecMap M N hM hN φ hφ hs y

/-- **Fpqc descent of morphisms of quasi-coherent modules.** -/
theorem bijective_toDescentData_map_of_mem_fpqcTopology {T : Scheme.{u}} {ι : Type w}
    {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T) (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (M N : modulesPseudofunctor.obj (.mk (op T)))
    (hM : (M : T.Modules).IsQuasicoherent) (hN : (N : T.Modules).IsQuasicoherent) :
    Function.Bijective ((modulesPseudofunctor.toDescentData g).map : (M ⟶ N) → _) := by
  rw [Pseudofunctor.bijective_toDescentData_map_iff]
  refine Over.isSheafFor_ofArrows_of_sigmaPresheaf _ (W := fun i ↦ Over.mk (g i))
    (fun i ↦ (Over.homMk (g i) : Over.mk (g i) ⟶ Over.mk (𝟙 T))) ?_ ?_
  · rw [Presieve.isSheafFor_iff_generate]
    exact isSheaf_sigmaPresheaf_presheafHom M N hM hN _ hg
  · rw [Presieve.isSeparatedFor_iff_generate]
    exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fpqcTopology) (yoneda.obj T) _ hg).isSeparatedFor

end AlgebraicGeometry
