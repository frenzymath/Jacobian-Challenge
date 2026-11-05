import Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import Jacobian.AlgebraicGeometry.Modules.Sections

/-!
# Zariski descent of module morphisms

Morphisms of module sheaves glue uniquely over jointly surjective families of
open immersions. In particular, the functor from modules to descent data is fully
faithful for such a family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe w u

open CategoryTheory Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The inverse of `pullbackCompOfEq` on the image of the unit, over an arbitrary open:
`(pullbackCompOfEq g f fg h M)⁻¹ (η_fg m) = η_g (η_f m)`. -/
lemma pullbackCompOfEq_inv_app_pullbackUnit (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (m : Γ(M, U)) :
    ((pullbackCompOfEq g f (g ≫ f) rfl M).inv).app ((g ≫ f) ⁻¹ᵁ U) (pullbackUnitApp (g ≫ f) M U m) =
      pullbackUnitApp g ((pullback f).obj M) (f ⁻¹ᵁ U) (pullbackUnitApp f M U m) := by
  rw [← modulesPseudofunctor_mapComp'_hom_app_eq f g (g ≫ f) rfl]
  exact modulesPseudofunctor_mapComp'_hom_app_pullbackUnit f g M U m

/-- Naturality of the unit of `pullback g ⊣ pushforward g` on sections over `f ⁻¹ᵁ U`, with
the open written as `(g ≫ f) ⁻¹ᵁ U`. -/
lemma pullback_map_app_comp_preimage_pullbackUnitApp (g : Z ⟶ Y) (f : Y ⟶ X)
    {M N : Y.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, f ⁻¹ᵁ U)) :
    ((pullback g).map φ).app ((g ≫ f) ⁻¹ᵁ U) (pullbackUnitApp g M (f ⁻¹ᵁ U) x) =
      pullbackUnitApp g N (f ⁻¹ᵁ U) (φ.app (f ⁻¹ᵁ U) x) :=
  pullbackUnit_naturality_apply g φ (f ⁻¹ᵁ U) x

/-- If `φ : f^* M ⟶ f^* N` sends `η_f m` to `η_f n`, then its pullback along `g`, transported
along `pullbackCompOfEq`, sends `η_fg m` to `η_fg n`. -/
lemma pullbackCompOfEq_conj_app_pullbackUnit (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) {M N : X.Modules} (φ : (pullback f).obj M ⟶ (pullback f).obj N)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U))
    (hmn : pullbackUnitApp f N U n = φ.app (f ⁻¹ᵁ U) (pullbackUnitApp f M U m)) :
    ((pullbackCompOfEq g f fg h M).inv ≫ (pullback g).map φ ≫
      (pullbackCompOfEq g f fg h N).hom).app (fg ⁻¹ᵁ U) (pullbackUnitApp fg M U m) =
      pullbackUnitApp fg N U n := by
  subst h
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackCompOfEq_inv_app_pullbackUnit, pullback_map_app_comp_preimage_pullbackUnitApp,
    ← hmn, ← pullbackCompOfEq_inv_app_pullbackUnit]
  exact congr($((pullbackCompOfEq g (f) (g ≫ f) rfl N).inv_hom_id).app _ _)

/-- Two sections `n₁, n₂` of `N` over an open `W` contained in the range of an open immersion
`q = f₁ ≫ u₁ = f₂ ≫ u₂` agree if `n₁` (resp. `n₂`) is the image of `m` under `φ₁` (resp. `φ₂`)
after pulling back along `u₁` (resp. `u₂`), and `φ₁`, `φ₂` agree after pulling back to `q`. -/
lemma eq_of_pullbackCompOfEq_conj_eq {X₁ X₂ : Scheme.{u}} (q : Y ⟶ X) [IsOpenImmersion q]
    {u₁ : X₁ ⟶ X} {u₂ : X₂ ⟶ X} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (hf₁ : f₁ ≫ u₁ = q)
    (hf₂ : f₂ ≫ u₂ = q) {M N : X.Modules} (φ₁ : (pullback u₁).obj M ⟶ (pullback u₁).obj N)
    (φ₂ : (pullback u₂).obj M ⟶ (pullback u₂).obj N)
    (hcomm : (pullbackCompOfEq f₁ u₁ q hf₁ M).inv ≫ (pullback f₁).map φ₁ ≫
        (pullbackCompOfEq f₁ u₁ q hf₁ N).hom =
      (pullbackCompOfEq f₂ u₂ q hf₂ M).inv ≫ (pullback f₂).map φ₂ ≫
        (pullbackCompOfEq f₂ u₂ q hf₂ N).hom)
    {W : X.Opens} (hW : W ≤ q.opensRange) (m : Γ(M, W)) (n₁ n₂ : Γ(N, W))
    (h₁ : pullbackUnitApp u₁ N W n₁ = φ₁.app (u₁ ⁻¹ᵁ W) (pullbackUnitApp u₁ M W m))
    (h₂ : pullbackUnitApp u₂ N W n₂ = φ₂.app (u₂ ⁻¹ᵁ W) (pullbackUnitApp u₂ M W m)) :
    n₁ = n₂ := by
  refine (bijective_pullbackUnit_app_of_isOpenImmersion q N hW).1
    ((pullbackCompOfEq_conj_app_pullbackUnit f₁ u₁ q hf₁ φ₁ W m n₁ h₁).symm.trans ?_)
  rw [hcomm]
  exact pullbackCompOfEq_conj_app_pullbackUnit f₂ u₂ q hf₂ φ₂ W m n₂ h₂

variable {ι : Type w} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X)

/-- The descent data `modulesPseudofunctor.toDescentData u` of a module, in terms of
`pullbackCompOfEq`. -/
lemma modulesPseudofunctor_toDescentData_obj_hom (P : X.Modules) (q : Y ⟶ X) {i₁ i₂ : ι}
    (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂) (hf₁ : f₁ ≫ u i₁ = q) (hf₂ : f₂ ≫ u i₂ = q) :
    ((modulesPseudofunctor.toDescentData u).obj P).hom q f₁ f₂ hf₁ hf₂ =
      (pullbackCompOfEq f₁ (u i₁) q hf₁ P).hom ≫ (pullbackCompOfEq f₂ (u i₂) q hf₂ P).inv := by
  rw [← modulesPseudofunctor_mapComp'_inv_app_eq (u i₁) f₁ q hf₁,
    ← modulesPseudofunctor_mapComp'_hom_app_eq (u i₂) f₂ q hf₂]
  rfl

/-- The compatibility of a morphism `ψ` of descent data for `modulesPseudofunctor`, with
components `φ i`, in terms of `pullbackCompOfEq`. -/
lemma pullbackCompOfEq_conj_eq_of_descentData {M N : X.Modules}
    (ψ : (modulesPseudofunctor.toDescentData u).obj M ⟶
      (modulesPseudofunctor.toDescentData u).obj N)
    (φ : ∀ i, (pullback (u i)).obj M ⟶ (pullback (u i)).obj N) (hφ : ∀ i, ψ.hom i = φ i)
    (q : Y ⟶ X) {i j : ι} (f₁ : Y ⟶ U i) (f₂ : Y ⟶ U j) (hf₁ : f₁ ≫ u i = q)
    (hf₂ : f₂ ≫ u j = q) :
    (pullbackCompOfEq f₁ (u i) q hf₁ M).inv ≫ (pullback f₁).map (φ i) ≫
        (pullbackCompOfEq f₁ (u i) q hf₁ N).hom =
      (pullbackCompOfEq f₂ (u j) q hf₂ M).inv ≫ (pullback f₂).map (φ j) ≫
        (pullbackCompOfEq f₂ (u j) q hf₂ N).hom := by
  have hc := ψ.comm q f₁ f₂ hf₁ hf₂
  rw [hφ, hφ, modulesPseudofunctor_toDescentData_obj_hom,
    modulesPseudofunctor_toDescentData_obj_hom] at hc
  have hc' : (pullback f₁).map (φ i) ≫ (pullbackCompOfEq f₁ (u i) q hf₁ N).hom ≫
      (pullbackCompOfEq f₂ (u j) q hf₂ N).inv = ((pullbackCompOfEq f₁ (u i) q hf₁ M).hom ≫
      (pullbackCompOfEq f₂ (u j) q hf₂ M).inv) ≫ (pullback f₂).map (φ j) := hc
  rw [← cancel_mono (pullbackCompOfEq f₂ (u j) q hf₂ N).inv]
  simp only [Category.assoc]
  rw [hc', Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The unit of `pullback f ⊣ pushforward f` commutes with restriction of sections. -/
lemma pullbackUnitApp_presheaf_map (f : Y ⟶ X) (M : X.Modules) {V V' : X.Opens} (i : V' ⟶ V)
    (m : Γ(M, V)) :
    pullbackUnitApp f M V' (M.presheaf.map i.op m) =
      ((pullback f).obj M).presheaf.map (homOfLE (f.preimage_mono i.le)).op
        (pullbackUnitApp f M V m) :=
  Hom.app_presheaf_map _ _ _

/-- The unit of `pullback f ⊣ pushforward f` is semilinear on sections. -/
lemma pullbackUnitApp_smul (f : Y ⟶ X) (M : X.Modules) {V : X.Opens} (r : Γ(X, V))
    (m : Γ(M, V)) :
    pullbackUnitApp f M V (r • m) = f.app V r • pullbackUnitApp f M V m :=
  Hom.app_smul _ r m

/-- Restriction of sections along an inclusion of equal opens is injective. -/
lemma injective_presheaf_map_of_le (M : X.Modules) {V V' : X.Opens} (i : V' ⟶ V) (h : V ≤ V') :
    Function.Injective (M.presheaf.map i.op) := by
  obtain rfl : V' = V := le_antisymm i.le h
  rw [Subsingleton.elim i (𝟙 V'), op_id, CategoryTheory.Functor.map_id]
  exact fun _ _ h ↦ h

/-- The opens `V ⊓ (u i).opensRange` cover `V` if the ranges of the `u i` cover `X`. -/
lemma le_iSup_inf_opensRange {ι : Type w} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ X}
    [∀ i, IsOpenImmersion (u i)] (hu : ⨆ i, (u i).opensRange = ⊤) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ (u i).opensRange := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hu.ge (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- `n` is a value at `m` of `φ : f^* M ⟶ f^* N`: `φ (η_f m) = η_f n`. -/
def IsPullbackValue (f : Y ⟶ X) {M N : X.Modules} (φ : (pullback f).obj M ⟶ (pullback f).obj N)
    {V : X.Opens} (m : Γ(M, V)) (n : Γ(N, V)) : Prop :=
  pullbackUnitApp f N V n = φ.app (f ⁻¹ᵁ V) (pullbackUnitApp f M V m)

/-- Values of `φ : f^* M ⟶ f^* N` restrict to smaller opens. -/
lemma IsPullbackValue.map {f : Y ⟶ X} {M N : X.Modules}
    {φ : (pullback f).obj M ⟶ (pullback f).obj N} {V V' : X.Opens} (i : V' ⟶ V)
    {m : Γ(M, V)} {n : Γ(N, V)} (h : IsPullbackValue f φ m n) :
    IsPullbackValue f φ (M.presheaf.map i.op m) (N.presheaf.map i.op n) := by
  rw [IsPullbackValue, pullbackUnitApp_presheaf_map, pullbackUnitApp_presheaf_map, h]
  exact (Hom.app_presheaf_map φ _ _).symm

section Descent

variable {ι : Type w} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) {M N : X.Modules}
  (φ : ∀ i, (pullback (u i)).obj M ⟶ (pullback (u i)).obj N)

/-- `n` is a value at `m` of the family `φ i : (u i)^* M ⟶ (u i)^* N`: for all `i`,
`φ i (η m) = η n`. -/
def IsDescentValue {V : X.Opens} (m : Γ(M, V)) (n : Γ(N, V)) : Prop :=
  ∀ i, IsPullbackValue (u i) (φ i) m n

variable {u φ}

/-- Values of a family `φ i` along open immersions covering `X` are unique. -/
lemma IsDescentValue.unique [∀ i, IsOpenImmersion (u i)] (hu : ⨆ i, (u i).opensRange = ⊤)
    {V : X.Opens} {m : Γ(M, V)} {n n' : Γ(N, V)} (hn : IsDescentValue u φ m n)
    (hn' : IsDescentValue u φ m n') : n = n' := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ (u i).opensRange) V (fun _ ↦ homOfLE inf_le_left)
    (le_iSup_inf_opensRange hu V) n n' fun i ↦ ?_
  have h₁ := (hn i).map (homOfLE (inf_le_left : V ⊓ (u i).opensRange ≤ V))
  have h₂ := (hn' i).map (homOfLE (inf_le_left : V ⊓ (u i).opensRange ≤ V))
  exact (bijective_pullbackUnit_app_of_isOpenImmersion (u i) N inf_le_right).1 (h₁.trans h₂.symm)

/-- `α m` is the value at `m` of the family of pullbacks `(u i)^* α`. -/
lemma isDescentValue_app (α : M ⟶ N) {V : X.Opens} (m : Γ(M, V)) :
    IsDescentValue u (fun i ↦ (pullback (u i)).map α) m (α.app V m) :=
  fun i ↦ (pullbackUnit_naturality_apply (u i) α V m).symm

/-- Values of a family `φ i` restrict to smaller opens. -/
lemma IsDescentValue.map {V V' : X.Opens} (i : V' ⟶ V) {m : Γ(M, V)} {n : Γ(N, V)}
    (h : IsDescentValue u φ m n) :
    IsDescentValue u φ (M.presheaf.map i.op m) (N.presheaf.map i.op n) :=
  fun j ↦ (h j).map i

/-- `0` is the value at `0` of a family `φ i`. -/
lemma isDescentValue_zero {V : X.Opens} : IsDescentValue u φ (0 : Γ(M, V)) (0 : Γ(N, V)) := by
  intro i
  rw [IsPullbackValue, map_zero, map_zero, map_zero]

/-- Values of a family `φ i` are additive. -/
lemma IsDescentValue.add {V : X.Opens} {m m' : Γ(M, V)} {n n' : Γ(N, V)}
    (h : IsDescentValue u φ m n) (h' : IsDescentValue u φ m' n') :
    IsDescentValue u φ (m + m') (n + n') := by
  intro i
  rw [IsPullbackValue, map_add, map_add, map_add, h i, h' i]

/-- Values of a family `φ i` are compatible with scalar multiplication. -/
lemma IsDescentValue.smul {V : X.Opens} {m : Γ(M, V)} {n : Γ(N, V)}
    (h : IsDescentValue u φ m n) (r : Γ(X, V)) : IsDescentValue u φ (r • m) (r • n) := by
  intro i
  rw [IsPullbackValue, pullbackUnitApp_smul, pullbackUnitApp_smul, h i, Hom.app_smul]

/-- A family `φ i` along open immersions covering `X` which is compatible on overlaps has a
value at every section of `M`: the values over the opens `V ⊓ (u i).opensRange` glue. -/
lemma exists_isDescentValue [∀ i, IsOpenImmersion (u i)] (hu : ⨆ i, (u i).opensRange = ⊤)
    (hc : ∀ i j (W : X.Opens), W ≤ (u i).opensRange → W ≤ (u j).opensRange →
      ∀ (m : Γ(M, W)) (n₁ n₂ : Γ(N, W)), IsPullbackValue (u i) (φ i) m n₁ →
        IsPullbackValue (u j) (φ j) m n₂ → n₁ = n₂)
    {V : X.Opens} (m : Γ(M, V)) : ∃ n, IsDescentValue u φ m n := by
  have hb (i : ι) := bijective_pullbackUnit_app_of_isOpenImmersion (u i) N
    (inf_le_right : V ⊓ (u i).opensRange ≤ _)
  let sf (i : ι) : Γ(N, V ⊓ (u i).opensRange) := Function.surjInv (hb i).2
    ((φ i).app _ (pullbackUnitApp (u i) M _ (M.presheaf.map (homOfLE inf_le_left).op m)))
  have hsf (i : ι) : IsPullbackValue (u i) (φ i) (M.presheaf.map (homOfLE inf_le_left).op m)
      (sf i) :=
    Function.surjInv_eq (hb i).2 _
  have hcomp : TopCat.Presheaf.IsCompatible N.presheaf (fun i ↦ V ⊓ (u i).opensRange) sf := by
    intro i j
    refine hc i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      (M.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op m) _ _ ?_ ?_
    · have := (hsf i).map
        (TopologicalSpace.Opens.infLELeft (V ⊓ (u i).opensRange) (V ⊓ (u j).opensRange))
      rwa [presheaf_map_map_apply] at this
    · have := (hsf j).map
        (TopologicalSpace.Opens.infLERight (V ⊓ (u i).opensRange) (V ⊓ (u j).opensRange))
      rwa [presheaf_map_map_apply] at this
  obtain ⟨n, hn, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ (u i).opensRange) V (fun _ ↦ homOfLE inf_le_left)
    (le_iSup_inf_opensRange hu V) sf hcomp
  refine ⟨n, fun i ↦ injective_presheaf_map_of_le _
    (homOfLE ((u i).preimage_mono (inf_le_left : V ⊓ (u i).opensRange ≤ V)))
    (fun x hx ↦ ⟨hx, x, rfl⟩) ?_⟩
  rw [← pullbackUnitApp_presheaf_map, ← Hom.app_presheaf_map, ← pullbackUnitApp_presheaf_map]
  exact (hn i).symm ▸ hsf i

variable [∀ i, IsOpenImmersion (u i)] (hu : ⨆ i, (u i).opensRange = ⊤)
  (hc : ∀ i j (W : X.Opens), W ≤ (u i).opensRange → W ≤ (u j).opensRange →
    ∀ (m : Γ(M, W)) (n₁ n₂ : Γ(N, W)), IsPullbackValue (u i) (φ i) m n₁ →
      IsPullbackValue (u j) (φ j) m n₂ → n₁ = n₂)

/-- The morphism `M ⟶ N` obtained by gluing a compatible family of morphisms
`φ i : (u i)^* M ⟶ (u i)^* N` along open immersions `u i` covering `X`. -/
noncomputable def descentHom : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun m := (exists_isDescentValue hu hc (V := V.unop) m).choose
          map_zero' := ((exists_isDescentValue hu hc _).choose_spec).unique hu
            isDescentValue_zero
          map_add' m m' := ((exists_isDescentValue hu hc _).choose_spec).unique hu
            (((exists_isDescentValue hu hc m).choose_spec).add
              (exists_isDescentValue hu hc m').choose_spec) }
      naturality V V' i := by
        ext m
        exact ((exists_isDescentValue hu hc _).choose_spec).unique hu
          (((exists_isDescentValue hu hc m).choose_spec).map i.unop) }
    fun V r m ↦ ((exists_isDescentValue hu hc _).choose_spec).unique hu
      (((exists_isDescentValue hu hc m).choose_spec).smul r)⟩

/-- `descentHom` sends a section `m` to the value of the family `φ i` at `m`. -/
lemma isDescentValue_descentHom_app {V : X.Opens} (m : Γ(M, V)) :
    IsDescentValue u φ m ((descentHom hu hc).app V m) :=
  (exists_isDescentValue hu hc m).choose_spec

end Descent

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

/-- **Morphisms of sheaves of modules glue along open covers.** For a family of open immersions
covering `X`, `modulesPseudofunctor.toDescentData` is fully faithful. -/
theorem bijective_toDescentData_map_of_isOpenImmersion {X : Scheme.{u}} {ι : Type w}
    {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (u i)]
    (hu : ⨆ i, (u i).opensRange = ⊤) (M N : modulesPseudofunctor.obj (.mk (op X))) :
    Function.Bijective ((modulesPseudofunctor.toDescentData u).map : (M ⟶ N) → _) := by
  refine ⟨fun α β hαβ ↦ ?_, fun ψ ↦ ?_⟩
  · have e : (fun i ↦ (pullback (u i)).map α) = fun i ↦ (pullback (u i)).map β :=
      funext fun i ↦ congr_arg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ i) hαβ
    refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
    ext m
    refine (isDescentValue_app (u := u) α m).unique hu ?_
    rw [e]
    exact isDescentValue_app (u := u) β m
  · obtain ⟨φ, hφ⟩ : ∃ φ : ∀ i, (pullback (u i)).obj M ⟶ (pullback (u i)).obj N,
        ∀ i, ψ.hom i = φ i :=
      ⟨ψ.hom, fun _ ↦ rfl⟩
    have hc (i j : ι) (W : X.Opens) (hi : W ≤ (u i).opensRange) (hj : W ≤ (u j).opensRange)
        (m : Γ(M, W)) (n₁ n₂ : Γ(N, W)) (h₁ : IsPullbackValue (u i) (φ i) m n₁)
        (h₂ : IsPullbackValue (u j) (φ j) m n₂) : n₁ = n₂ := by
      have hi' : Set.range W.ι ⊆ Set.range (u i) := by
        rw [Scheme.Opens.range_ι]
        exact hi
      have hj' : Set.range W.ι ⊆ Set.range (u j) := by
        rw [Scheme.Opens.range_ι]
        exact hj
      exact eq_of_pullbackCompOfEq_conj_eq W.ι _ _ (IsOpenImmersion.lift_fac _ _ hi')
        (IsOpenImmersion.lift_fac _ _ hj') (φ i) (φ j)
        (pullbackCompOfEq_conj_eq_of_descentData u ψ φ hφ _ _ _ _ _)
        (Scheme.Opens.opensRange_ι W).ge m n₁ n₂ h₁ h₂
    refine ⟨descentHom hu hc, Pseudofunctor.DescentData.hom_ext fun i ↦ ?_⟩
    rw [hφ]
    refine pullback_hom_ext (u i) fun V m ↦ ?_
    exact (pullbackUnit_naturality_apply (u i) (descentHom hu hc) V m).trans
      (isDescentValue_descentHom_app hu hc m i)

end AlgebraicGeometry
