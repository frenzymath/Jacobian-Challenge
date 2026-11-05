import Jacobian.AlgebraicGeometry.Modules.AffineDescent
import Jacobian.AlgebraicGeometry.Modules.DescentGlue
import Jacobian.AlgebraicGeometry.Modules.FpqcSectionDescent
import Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.LocalIsomorphism
import Jacobian.AlgebraicGeometry.Sites.Fpqc
import Jacobian.CategoryTheory.Sites.Descent.Restrict
import Jacobian.CategoryTheory.Sites.Descent.Refinement

/-!
# Effective fpqc descent of quasi-coherent modules

Affine faithfully flat effectivity and Zariski gluing construct a quasi-coherent module realizing every quasi-coherent fpqc descent datum.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe w u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat Bicategory

namespace AlgebraicGeometry.Scheme.Modules

section PullSec

variable {X Y Z Z' : Scheme.{u}}

/-- The pullback along `y : Z ⟶ X` of a section `s` of `N` over `V`, restricted to an open
`O ≤ y ⁻¹ᵁ V`. -/
noncomputable def pullSec (y : Z ⟶ X) {N : X.Modules} {V : X.Opens} (s : Γ(N, V))
    {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) : Γ((pullback y).obj N, O) :=
  ((pullback y).obj N).presheaf.map (homOfLE hO).op (pullbackUnitApp y N V s)

lemma pullSec_le_rfl (y : Z ⟶ X) {N : X.Modules} {V : X.Opens} (s : Γ(N, V)) :
    pullSec y s (le_refl (y ⁻¹ᵁ V)) = pullbackUnitApp y N V s :=
  presheaf_map_id_apply _ _

lemma presheaf_map_pullSec (y : Z ⟶ X) {N : X.Modules} {V : X.Opens} (s : Γ(N, V))
    {O O' : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) (i : O' ⟶ O) :
    ((pullback y).obj N).presheaf.map i.op (pullSec y s hO) = pullSec y s (i.le.trans hO) := by
  rw [pullSec, presheaf_map_map_apply]
  rfl

lemma pullSec_presheaf_map (y : Z ⟶ X) {N : X.Modules} {V V' : X.Opens} (s : Γ(N, V))
    (i : V' ⟶ V) {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V') :
    pullSec y (N.presheaf.map i.op s) hO = pullSec y s (hO.trans (y.preimage_mono i.le)) := by
  rw [pullSec, pullbackUnitApp_presheaf_map, presheaf_map_map_apply]
  rfl

lemma app_pullSec (y : Z ⟶ X) {M N : X.Modules} (φ : M ⟶ N) {V : X.Opens} (s : Γ(M, V))
    {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) :
    ((pullback y).map φ).app O (pullSec y s hO) = pullSec y (φ.app V s) hO := by
  rw [pullSec, Hom.app_presheaf_map]
  exact congrArg _ (pullbackUnit_naturality_apply y φ V s)

lemma pullSec_add (y : Z ⟶ X) {N : X.Modules} {V : X.Opens} (s t : Γ(N, V))
    {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) :
    pullSec y (s + t) hO = pullSec y s hO + pullSec y t hO := by
  simp only [pullSec, map_add]

lemma pullSec_zero (y : Z ⟶ X) {N : X.Modules} {V : X.Opens}
    {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) :
    pullSec y (0 : Γ(N, V)) hO = 0 := by
  simp only [pullSec, map_zero]

lemma pullSec_neg (y : Z ⟶ X) {N : X.Modules} {V : X.Opens} (s : Γ(N, V))
    {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) :
    pullSec y (-s) hO = -pullSec y s hO := by
  simp only [pullSec, map_neg]

/-- Pulling back sections twice is pulling back along the composite, up to `pullbackComp`. -/
lemma pullbackComp_hom_app_pullSec (g : Z' ⟶ Z) (y : Z ⟶ X) {N : X.Modules} {V : X.Opens}
    (s : Γ(N, V)) {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ V) {O' : Z'.Opens} (hO' : O' ≤ g ⁻¹ᵁ O) :
    ((pullbackComp g y).hom.app N).app O' (pullSec g (pullSec y s hO) hO') =
      pullSec (g ≫ y) s (hO'.trans (g.preimage_mono hO)) := by
  simp only [pullSec]
  rw [pullbackUnitApp_presheaf_map, presheaf_map_map_apply]
  have h := pullbackUnit_comp_app_apply g y N V s
  erw [← h]
  erw [← Hom.app_presheaf_map ((pullbackComp g y).inv.app N)]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id_app, Hom.id_app]
  rfl

end PullSec

section DescentDataHom

variable {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  (D : modulesPseudofunctor.DescentData f)

/-- The pullback along `g` of `D.hom q f₁ f₂` is `D.hom (g ≫ q) (g ≫ f₁) (g ≫ f₂)`, on pulled
back sections. -/
lemma descentData_hom_app_pullSec {Y Y' : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (g : Y' ⟶ Y)
    {O : Y.Opens} (x : Γ((pullback f₁).obj (D.obj i₁ : (X i₁).Modules), O)) {O' : Y'.Opens}
    (hO' : O' ≤ g ⁻¹ᵁ O) :
    (D.hom (g ≫ q) (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, hf₁])
        (by rw [Category.assoc, hf₂])).app O'
        (((pullbackComp g f₁).hom.app _).app O' (pullSec g x hO')) =
      ((pullbackComp g f₂).hom.app _).app O'
        (pullSec g ((D.hom q f₁ f₂ hf₁ hf₂).app O x) hO') := by
  have h₁ := D.pullHom_hom g q (g ≫ q) rfl f₁ f₂ hf₁ hf₂ (g ≫ f₁) (g ≫ f₂) rfl rfl
  have h₂ := modulesPseudofunctor_pullHom_eq (M₁ := (D.obj i₁ : (X i₁).Modules))
    (M₂ := (D.obj i₂ : (X i₂).Modules)) (f₁ := f₁) (f₂ := f₂) (D.hom q f₁ f₂ hf₁ hf₂) g
  have key := h₁.symm.trans h₂
  rw [key,  Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have e : ((pullbackComp g f₁).inv.app (D.obj i₁ : (X i₁).Modules)).app O'
      (((pullbackComp g f₁).hom.app (D.obj i₁ : (X i₁).Modules)).app O' (pullSec g x hO')) =
      pullSec g x hO' := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app]
    rfl
  erw [e, app_pullSec]
  rfl

/-- `D.hom q f₂ f₁` inverts `D.hom q f₁ f₂` on sections. -/
lemma descentData_hom_app_hom_app {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) {O : Y.Opens}
    (x : Γ((pullback f₁).obj (D.obj i₁ : (X i₁).Modules), O)) :
    (D.hom q f₂ f₁ hf₂ hf₁).app O ((D.hom q f₁ f₂ hf₁ hf₂).app O x) = x := by
  have h := D.hom_comp q f₁ f₂ f₁ hf₁ hf₂ hf₁
  rw [D.hom_self q f₁ hf₁] at h
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app]
  erw [h]
  rfl

lemma descentData_hom_app_injective {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (O : Y.Opens) :
    Function.Injective ((D.hom q f₁ f₂ hf₁ hf₂).app O) := fun x x' h ↦ by
  rw [← descentData_hom_app_hom_app D q f₁ f₂ hf₁ hf₂ x,
    ← descentData_hom_app_hom_app D q f₁ f₂ hf₁ hf₂ x', h]

/-- `D.hom q f₁ f₂` only depends on `q` through the proofs. -/
lemma descentData_hom_eq {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom (f₁ ≫ f i₁) f₁ f₂ rfl (hf₂.trans hf₁.symm) := by
  subst hf₁
  rfl

end DescentDataHom

section Extension

variable {S : Scheme.{u}} {J : Type u} {W : J → Scheme.{u}} {f : ∀ a, W a ⟶ S}
  {D : modulesPseudofunctor.DescentData f}

variable (f) in
/-- The sieve on `W b` of the morphisms which factor, over `S`, through a member `f (β k)` of a
subfamily. -/
def subfamilySieve {K : Type*} (β : K → J) (b : J) : Sieve (W b) where
  arrows Z y := ∃ (k : K) (z : Z ⟶ W (β k)), y ≫ f b = z ≫ f (β k)
  downward_closed := by
    rintro Z Z' y ⟨k, z, h⟩ g
    exact ⟨k, g ≫ z, by rw [Category.assoc, h, Category.assoc]⟩

/-- If the subfamily `f ∘ β` covers `V`, then the subfamily sieve covers every open of a scheme
over `W b` mapping into the preimage of `V`. -/
lemma pullback_subfamilySieve_mem {K : Type*} (β : K → J) {V : S.Opens}
    (hβ : Sieve.pullback V.ι (Sieve.ofArrows (fun k ↦ W (β k)) (fun k ↦ f (β k))) ∈
      Scheme.fpqcTopology V.toScheme)
    {b : J} {Y : Scheme.{u}} (y : Y ⟶ W b) {O : Y.Opens} (hO : O ≤ y ⁻¹ᵁ f b ⁻¹ᵁ V) :
    Sieve.pullback O.ι (Sieve.pullback y (subfamilySieve f β b)) ∈
      Scheme.fpqcTopology O.toScheme := by
  refine Scheme.fpqcTopology.superset_covering ?_
    (Scheme.fpqcTopology.pullback_stable ((y ≫ f b).resLE V O hO) hβ)
  rintro Z h hh
  obtain ⟨k, z, hz⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  refine ⟨k, z, ?_⟩
  have e : (y ≫ f b).resLE V O hO ≫ V.ι = O.ι ≫ y ≫ f b := Scheme.Hom.resLE_comp_ι _ _
  rw [← hz]
  simp only [Category.assoc, e]

lemma preimage_le_of_comp_eq {Z : Scheme.{u}} {a b : J} (y : Z ⟶ W a) (z : Z ⟶ W b)
    (h : y ≫ f a = z ≫ f b) (V : S.Opens) : y ⁻¹ᵁ f a ⁻¹ᵁ V ≤ z ⁻¹ᵁ f b ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]

variable {K : Type*} {β : K → J} {V : S.Opens} (e : ∀ k, Γ(descentObj D (β k), f (β k) ⁻¹ᵁ V))

variable (D) in
/-- The value at `y : Z ⟶ W b` of the extension of a family of sections `e` over a subfamily,
computed with a factorization `y ≫ f b = z ≫ f (β k)`. -/
noncomputable def extVal {b : J} {Z : Scheme.{u}} (y : Z ⟶ W b) {k : K} (z : Z ⟶ W (β k))
    (hyz : y ≫ f b = z ≫ f (β k)) {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ f b ⁻¹ᵁ V) :
    Γ((pullback y).obj (descentObj D b), O) :=
  (D.hom (y ≫ f b) z y hyz.symm rfl).app O
    (pullSec z (e k) (hO.trans (preimage_le_of_comp_eq y z hyz V)))

variable {e}

lemma extVal_indep (he : ∀ k k', DescentCompat D V (e k) (e k')) {b : J} {Z : Scheme.{u}}
    (y : Z ⟶ W b) {k k' : K} (z : Z ⟶ W (β k)) (z' : Z ⟶ W (β k'))
    (hyz : y ≫ f b = z ≫ f (β k)) (hyz' : y ≫ f b = z' ≫ f (β k')) {O : Z.Opens}
    (hO : O ≤ y ⁻¹ᵁ f b ⁻¹ᵁ V) :
    extVal D e y z hyz hO = extVal D e y z' hyz' hO := by
  have hc := he k k' z z' (hyz.symm.trans hyz') O
    (hO.trans (preimage_le_of_comp_eq y z hyz V)) (hO.trans (preimage_le_of_comp_eq y z' hyz' V))
  have hcomp := D.hom_comp (y ≫ f b) z z' y hyz.symm hyz'.symm rfl
  rw [extVal, extVal, ← hcomp, Hom.comp_app, ConcreteCategory.comp_apply]
  congr 1
  rw [descentData_hom_eq D (y ≫ f b) z z' hyz.symm hyz'.symm]
  exact hc

lemma extVal_presheaf_map {b : J} {Z : Scheme.{u}} (y : Z ⟶ W b) {k : K} (z : Z ⟶ W (β k))
    (hyz : y ≫ f b = z ≫ f (β k)) {O O' : Z.Opens} (hO : O ≤ y ⁻¹ᵁ f b ⁻¹ᵁ V) (i : O' ⟶ O) :
    ((pullback y).obj (descentObj D b)).presheaf.map i.op (extVal D e y z hyz hO) =
      extVal D e y z hyz (i.le.trans hO) := by
  rw [extVal, extVal]
  erw [← Hom.app_presheaf_map, presheaf_map_pullSec]
  rfl

lemma extVal_pull {b : J} {Z Z' : Scheme.{u}} (y : Z ⟶ W b) {k : K} (z : Z ⟶ W (β k))
    (hyz : y ≫ f b = z ≫ f (β k)) {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ f b ⁻¹ᵁ V) (g : Z' ⟶ Z)
    {O' : Z'.Opens} (hO' : O' ≤ g ⁻¹ᵁ O) :
    ((pullbackComp g y).hom.app (descentObj D b)).app O' (pullSec g (extVal D e y z hyz hO) hO') =
      extVal D e (g ≫ y) (g ≫ z) (by rw [Category.assoc, hyz, Category.assoc])
        (hO'.trans (g.preimage_mono hO)) := by
  rw [extVal, ← descentData_hom_app_pullSec D (y ≫ f b) z y hyz.symm rfl g _ hO',
    pullbackComp_hom_app_pullSec, extVal, descentData_hom_eq D (g ≫ y ≫ f b),
    descentData_hom_eq D ((g ≫ y) ≫ f b)]

lemma extVal_hom {b c : J} {Z : Scheme.{u}} (y₁ : Z ⟶ W b) (y₂ : Z ⟶ W c)
    (h : y₁ ≫ f b = y₂ ≫ f c) {k : K} (z : Z ⟶ W (β k)) (hyz : y₁ ≫ f b = z ≫ f (β k))
    {O : Z.Opens} (h₁ : O ≤ y₁ ⁻¹ᵁ f b ⁻¹ᵁ V) (h₂ : O ≤ y₂ ⁻¹ᵁ f c ⁻¹ᵁ V) :
    (D.hom (y₁ ≫ f b) y₁ y₂ rfl h.symm).app O (extVal D e y₁ z hyz h₁) =
      extVal D e y₂ z (h.symm.trans hyz) h₂ := by
  have hcomp := D.hom_comp (y₁ ≫ f b) z y₁ y₂ hyz.symm rfl h.symm
  rw [extVal, ← ConcreteCategory.comp_apply, ← Hom.comp_app]
  erw [hcomp]
  rw [extVal, descentData_hom_eq D (y₁ ≫ f b), descentData_hom_eq D (y₂ ≫ f c)]

lemma extVal_self (he : ∀ k k', DescentCompat D V (e k) (e k')) {k₀ : K} {Z : Scheme.{u}}
    (y : Z ⟶ W (β k₀)) {k : K} (z : Z ⟶ W (β k)) (hyz : y ≫ f (β k₀) = z ≫ f (β k))
    {O : Z.Opens} (hO : O ≤ y ⁻¹ᵁ f (β k₀) ⁻¹ᵁ V) :
    extVal D e y z hyz hO = pullSec y (e k₀) hO := by
  rw [extVal_indep he y z y hyz rfl hO, extVal]
  erw [D.hom_self (y ≫ f (β k₀)) y rfl]
  rfl

lemma pullbackComp_hom_app_inv_app_apply {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (y : Y ⟶ X)
    (N : X.Modules) (O : Z.Opens) (x : Γ((pullback (g ≫ y)).obj N, O)) :
    ((pullbackComp g y).hom.app N).app O (((pullbackComp g y).inv.app N).app O x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id_app, Hom.id_app]
  rfl

lemma pullbackComp_hom_app_injective {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (y : Y ⟶ X)
    (N : X.Modules) (O : Z.Opens) :
    Function.Injective (((pullbackComp g y).hom.app N).app O) := fun a a' h ↦ by
  have e (x) : ((pullbackComp g y).inv.app N).app O (((pullbackComp g y).hom.app N).app O x) =
      x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app]
    rfl
  rw [← e a, ← e a', h]

variable (hD : ∀ a, (D.obj a : (W a).Modules).IsQuasicoherent)
  (hβ : Sieve.pullback V.ι (Sieve.ofArrows (fun k ↦ W (β k)) (fun k ↦ f (β k))) ∈
      Scheme.fpqcTopology V.toScheme)

include hβ in
lemma subfamilySieve_mem (b : J) :
    Sieve.pullback (f b ⁻¹ᵁ V).ι (subfamilySieve f β b) ∈
      Scheme.fpqcTopology (f b ⁻¹ᵁ V).toScheme := by
  simpa using pullback_subfamilySieve_mem β hβ (𝟙 (W b)) (O := f b ⁻¹ᵁ V) le_rfl

include hD hβ in
/-- Sections of `descentGlue D` are determined by their components along a subfamily covering
the open. -/
theorem glueVal_ext_of_subfamily {s t : Γ(descentGlue D, V)}
    (h : ∀ k, glueVal D (β k) s = glueVal D (β k) t) : s = t := by
  refine glueVal_ext fun b ↦ ?_
  have := hD b
  refine sections_ext_of_mem_fpqcTopology (descentObj D b) (subfamilySieve f β b)
    (subfamilySieve_mem hβ b) ?_
  rintro Z y ⟨k, z, hyz⟩
  have hs := glueVal_compat s b (β k) y z hyz _ le_rfl (preimage_le_of_comp_eq y z hyz V)
  have ht := glueVal_compat t b (β k) y z hyz _ le_rfl (preimage_le_of_comp_eq y z hyz V)
  rw [h k] at hs
  have := descentData_hom_app_injective D _ y z rfl hyz.symm _ (hs.trans ht.symm)
  rw [← pullSec_le_rfl, ← pullSec_le_rfl]
  exact this

include hD hβ in
/-- **Extension of compatible sections from a covering subfamily.** A compatible family of
sections of `D` along a subfamily `f ∘ β` covering the open `V` is the restriction of a section
of `descentGlue D` over `V`. -/
theorem exists_glueVal_eq_of_subfamily (e : ∀ k, Γ(descentObj D (β k), f (β k) ⁻¹ᵁ V))
    (he : ∀ k k', DescentCompat D V (e k) (e k')) :
    ∃ s : Γ(descentGlue D, V), ∀ k, glueVal D (β k) s = e k := by
  have hext (b : J) : ∃ s : Γ(descentObj D b, f b ⁻¹ᵁ V), ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ W b)
      (k : K) (z : Z ⟶ W (β k)) (hyz : y ≫ f b = z ≫ f (β k)),
      pullbackUnitApp y _ _ s = extVal D e y z hyz le_rfl := by
    have := hD b
    obtain ⟨s, hs⟩ := exists_sections_of_mem_fpqcTopology (descentObj D b) (subfamilySieve f β b)
      (subfamilySieve_mem hβ b)
      (fun Z y hy ↦ extVal D e y hy.choose_spec.choose hy.choose_spec.choose_spec le_rfl)
      (fun Z Z' y hy g ↦ by
        rw [← pullSec_le_rfl g]
        erw [extVal_pull]
        exact extVal_indep he _ _ _ _ _ _)
    exact ⟨s, fun Z y k z hyz ↦ (hs y ⟨k, z, hyz⟩).trans (extVal_indep he y _ _ _ _ _)⟩
  choose s hs using hext
  have hcompat (b c : J) : DescentCompat D V (s b) (s c) := by
    intro Y y₁ y₂ h O h₁ h₂
    have := hD c
    refine sections_ext_of_mem_fpqcTopology ((pullback y₂).obj (descentObj D c))
      (Sieve.pullback y₂ (subfamilySieve f β c)) (pullback_subfamilySieve_mem β hβ y₂ h₂) ?_
    rintro Z g ⟨k, z, hz⟩
    change pullbackUnitApp g _ O ((D.hom (y₁ ≫ f b) y₁ y₂ rfl h.symm).app O
      (pullSec y₁ (s b) h₁)) = pullbackUnitApp g _ O (pullSec y₂ (s c) h₂)
    rw [← pullSec_le_rfl g, ← pullSec_le_rfl g]
    apply pullbackComp_hom_app_injective g y₂
    rw [pullbackComp_hom_app_pullSec]
    erw [← descentData_hom_app_pullSec D (y₁ ≫ f b) y₁ y₂ rfl h.symm g _ le_rfl]
    rw [pullbackComp_hom_app_pullSec]
    have hz₁ : (g ≫ y₁) ≫ f b = z ≫ f (β k) := by rw [Category.assoc, h, ← Category.assoc, hz]
    have e₁ : pullSec (g ≫ y₁) (s b) (le_rfl.trans (g.preimage_mono h₁)) =
        extVal D e (g ≫ y₁) z hz₁ (le_rfl.trans (g.preimage_mono h₁)) := by
      rw [pullSec, hs b (g ≫ y₁) k z hz₁, extVal_presheaf_map]
    have e₂ : pullSec (g ≫ y₂) (s c) (le_rfl.trans (g.preimage_mono h₂)) =
        extVal D e (g ≫ y₂) z hz (le_rfl.trans (g.preimage_mono h₂)) := by
      rw [pullSec, hs c (g ≫ y₂) k z hz, extVal_presheaf_map]
    rw [e₁, e₂, descentData_hom_eq D (g ≫ y₁ ≫ f b)]
    exact extVal_hom (g ≫ y₁) (g ≫ y₂) (by rw [Category.assoc, h, Category.assoc]) z hz₁ _ _
  obtain ⟨t, ht⟩ := exists_glueVal_eq s hcompat
  refine ⟨t, fun k ↦ ?_⟩
  rw [ht]
  have := hD (β k)
  refine sections_ext_of_mem_fpqcTopology (descentObj D (β k)) (subfamilySieve f β (β k))
    (subfamilySieve_mem hβ (β k)) ?_
  rintro Z y ⟨k', z, hyz⟩
  rw [hs (β k) y k' z hyz, extVal_self he, pullSec_le_rfl]

end Extension

section PullbackCompOfEq

variable {X Y Z : Scheme.{u}}

lemma pullbackCompOfEq_hom_app_pullSec (g : Z ⟶ Y) (y : Y ⟶ X) (fg : Z ⟶ X) (hfg : g ≫ y = fg)
    {N : X.Modules} {V : X.Opens} (s : Γ(N, V)) {O : Y.Opens} (hO : O ≤ y ⁻¹ᵁ V)
    {O' : Z.Opens} (hO' : O' ≤ g ⁻¹ᵁ O) :
    ((pullbackCompOfEq g y fg hfg N).hom).app O' (pullSec g (pullSec y s hO) hO') =
      pullSec fg s (by subst hfg; exact hO'.trans (g.preimage_mono hO)) := by
  subst hfg
  rw [← pullbackComp_hom_app_pullSec g y s hO hO']
  simp [pullbackCompOfEq, pullbackCongr]

lemma pullbackCompOfEq_hom_app_injective (g : Z ⟶ Y) (y : Y ⟶ X) (fg : Z ⟶ X)
    (hfg : g ≫ y = fg) (N : X.Modules) (O : Z.Opens) :
    Function.Injective (((pullbackCompOfEq g y fg hfg N).hom).app O) := fun a a' h ↦ by
  have e (x) : ((pullbackCompOfEq g y fg hfg N).inv).app O
      (((pullbackCompOfEq g y fg hfg N).hom).app O x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
    rfl
  rw [← e a, ← e a', h]

end PullbackCompOfEq

section GlueIso

variable {S : Scheme.{u}} {J : Type u} {W : J → Scheme.{u}} {f : ∀ a, W a ⟶ S}
  {D : modulesPseudofunctor.DescentData f}

variable (f) in
/-- The family `f` augmented by the identity of `S`, indexed by `Option J`. -/
def augmentedFamily : ∀ o : Option J, o.elim S W ⟶ S
  | none => 𝟙 S
  | some a => f a

lemma pullbackUnitApp_injective_id {X : Scheme.{u}} (N : X.Modules) (V : X.Opens) :
    Function.Injective (pullbackUnitApp (𝟙 X) N V) :=
  (bijective_pullbackUnit_app_of_isOpenImmersion (𝟙 X) N (fun x _ ↦ ⟨x, rfl⟩)).1

lemma pullbackUnitApp_eq_of_pullbackCompOfEq {X Y : Scheme.{u}} (y : Y ⟶ X) (N : X.Modules)
    (q : Y ⟶ X) (h₁ : y ≫ 𝟙 X = q) (h₂ : 𝟙 Y ≫ y = q) {V : X.Opens} (p : Γ(N, V))
    (x : Γ((pullback y).obj N, y ⁻¹ᵁ V))
    (hc : ((pullbackCompOfEq y (𝟙 X) q h₁ N).hom ≫ (pullbackCompOfEq (𝟙 Y) y q h₂ N).inv).app
      (y ⁻¹ᵁ V) (pullSec y (pullbackUnitApp (𝟙 X) N V p) le_rfl) = pullSec (𝟙 Y) x le_rfl) :
    pullbackUnitApp y N V p = x := by
  have h₃ := congrArg ((pullbackCompOfEq (𝟙 Y) y q h₂ N).hom.app (y ⁻¹ᵁ V)) hc
  have e (z) : (pullbackCompOfEq (𝟙 Y) y q h₂ N).hom.app (y ⁻¹ᵁ V)
      ((pullbackCompOfEq (𝟙 Y) y q h₂ N).inv.app (y ⁻¹ᵁ V) z) = z := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]
    rfl
  rw [Hom.comp_app, ConcreteCategory.comp_apply, e, ← pullSec_le_rfl (𝟙 X) p,
    pullbackCompOfEq_hom_app_pullSec,
    ← pullbackCompOfEq_hom_app_pullSec (𝟙 Y) y q h₂ p le_rfl le_rfl] at h₃
  have h₄ := pullbackCompOfEq_hom_app_injective _ _ _ _ _ _ h₃
  rw [pullSec_le_rfl, pullSec_le_rfl] at h₄
  exact pullbackUnitApp_injective_id _ _ (h₄.trans (pullSec_le_rfl (𝟙 Y) x))

/-- **A quasi-coherent module is the module of compatible sections of its descent datum.** For a
family `f` generating an fpqc covering sieve and an isomorphism of descent data
`κ : (toDescentData f).obj P ≅ D` with `P` quasi-coherent, the induced morphism
`P ⟶ descentGlue D` is an isomorphism. -/
theorem isIso_toGlue (hf : Sieve.ofArrows W f ∈ Scheme.fpqcTopology S) {P : S.Modules}
    [P.IsQuasicoherent] (κ : (modulesPseudofunctor.toDescentData f).obj P ≅ D) :
    IsIso (toGlue κ.hom) := by
  have hinv (a : J) {O : (W a).Opens} (x : Γ((pullback (f a)).obj P, O)) :
      (κ.inv.hom a).app O ((κ.hom.hom a).app O x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app]
    erw [← Pseudofunctor.DescentData.comp_hom, κ.hom_inv_id]
    rfl
  have hinv' (a : J) {O : (W a).Opens} (x : Γ(descentObj D a, O)) :
      (κ.hom.hom a).app O ((κ.inv.hom a).app O x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app]
    erw [← Pseudofunctor.DescentData.comp_hom, κ.inv_hom_id]
    rfl
  refine Hom.isIso_of_forall_bijective_app _ fun x ↦ ⟨⊤, trivial, fun V _ ↦ ⟨?_, ?_⟩⟩
  · intro p p' hpp'
    have hV := Scheme.fpqcTopology.pullback_stable V.ι hf
    refine sections_ext_of_mem_fpqcTopology P (Sieve.ofArrows W f) hV ?_
    rintro Z y hy
    obtain ⟨a, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hy
    have h₁ : pullbackUnitApp (f a) P V p = pullbackUnitApp (f a) P V p' := by
      have := congrArg (glueVal D a) hpp'
      rw [glueVal_toGlue_app, glueVal_toGlue_app] at this
      rw [← hinv a (pullbackUnitApp (f a) P V p), this, hinv]
    have key (q : Γ(P, V)) : pullbackUnitApp (k ≫ f a) P V q =
        ((pullbackComp k (f a)).hom.app P).app _
          (pullbackUnitApp k _ _ (pullbackUnitApp (f a) P V q)) := by
      erw [← pullbackUnit_comp_app_apply k (f a) P V q, pullbackComp_hom_app_inv_app_apply]
      rfl
    rw [key p, key p', h₁]
  · intro s
    have hV := Scheme.fpqcTopology.pullback_stable V.ι hf
    let D' := (modulesPseudofunctor.toDescentData (augmentedFamily f)).obj P
    have hD' (o : Option J) : (D'.obj o : (o.elim S W).Modules).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_pullback (moduleSheaf := P) _
    let e : ∀ a, Γ(descentObj D' (some a), augmentedFamily f (some a) ⁻¹ᵁ V) :=
      fun a ↦ (κ.inv.hom a).app _ (glueVal D a s)
    have he (a a' : J) : DescentCompat D' V (e a) (e a') := by
      intro Y y₁ y₂ h O h₁ h₂
      have hc := κ.inv.comm (y₁ ≫ f a) y₁ y₂ rfl h.symm
      change ((((modulesPseudofunctor.toDescentData f).obj P).hom (y₁ ≫ f a) y₁ y₂ rfl
        h.symm).app O (pullSec y₁ ((κ.inv.hom a).app _ (glueVal D a s)) h₁)) =
          pullSec y₂ ((κ.inv.hom a').app _ (glueVal D a' s)) h₂
      erw [← app_pullSec y₁ (κ.inv.hom a), ← ConcreteCategory.comp_apply, ← Hom.comp_app, hc,
        Hom.comp_app, ConcreteCategory.comp_apply]
      erw [glueVal_compat s a a' y₁ y₂ h O h₁ h₂, app_pullSec]
      rfl
    obtain ⟨t, ht⟩ := exists_glueVal_eq_of_subfamily (β := some) hD' hV e he
    obtain ⟨p, hp⟩ := (bijective_pullbackUnit_app_of_isOpenImmersion (𝟙 S) P
      (openSubset := V) (fun x _ ↦ ⟨x, rfl⟩)).2 (glueVal D' none t)
    refine ⟨p, glueVal_ext fun a ↦ ?_⟩
    rw [glueVal_toGlue_app]
    suffices hpa : pullbackUnitApp (f a) P V p = e a by
      rw [hpa]
      exact hinv' a _
    have hc := glueVal_compat t none (some a) (Y := W a) (f a) (𝟙 (W a))
      (by simp [augmentedFamily]) (f a ⁻¹ᵁ V) le_rfl le_rfl
    rw [ht a, modulesPseudofunctor_toDescentData_obj_hom] at hc
    rw [← hp] at hc
    exact pullbackUnitApp_eq_of_pullbackCompOfEq (f a) P _ _ _ p (e a) hc

end GlueIso

section Restrict

variable {S : Scheme.{u}} {I : Type u} {Y : I → Scheme.{u}} (ι : ∀ U, Y U ⟶ S)
  [∀ U, IsOpenImmersion (ι U)] {κ : I → Type u} {W : ∀ U, κ U → Scheme.{u}}
  (w : ∀ U j, W U j ⟶ Y U)
  {D : modulesPseudofunctor.DescentData (fun a : Σ U, κ U ↦ w a.1 a.2 ≫ ι a.1)}

variable (D) in
/-- The restriction of `D` to the members of the family lying over `Y U`, as a descent datum
relative to the family `w U` over `Y U`. -/
noncomputable abbrev restrictDescentData (U : I) :
    modulesPseudofunctor.DescentData (w U) :=
  D.restrict (ι U) (Sigma.mk U) (w U) (fun _ ↦ rfl)

lemma descentCompat_restrict_iff (U : I) {V : S.Opens} {j j' : κ U}
    (s : Γ(descentObj D ⟨U, j⟩, (w U j ≫ ι U) ⁻¹ᵁ V))
    (t : Γ(descentObj D ⟨U, j'⟩, (w U j' ≫ ι U) ⁻¹ᵁ V)) :
    DescentCompat (restrictDescentData ι w D U) (ι U ⁻¹ᵁ V) (a := j) (b := j') s t ↔
      DescentCompat D V (a := ⟨U, j⟩) (b := ⟨U, j'⟩) s t := by
  constructor
  · intro hc Z y₁ y₂ h O h₁ h₂
    have h₀ : y₁ ≫ w U j = y₂ ≫ w U j' := by
      rw [← cancel_mono (ι U), Category.assoc, Category.assoc]
      exact h
    have := hc y₁ y₂ h₀ O h₁ h₂
    rw [Pseudofunctor.DescentData.restrict_hom, descentData_hom_eq D] at this
    rw [descentData_hom_eq D]
    exact this
  · intro hc Z y₁ y₂ h O h₁ h₂
    have h' : y₁ ≫ w U j ≫ ι U = y₂ ≫ w U j' ≫ ι U := by
      rw [← Category.assoc, h, Category.assoc]
    have := hc y₁ y₂ h' O h₁ h₂
    rw [Pseudofunctor.DescentData.restrict_hom, descentData_hom_eq D]
    rw [descentData_hom_eq D] at this
    exact this

lemma exists_restrictGlue (U : I) {V : S.Opens} (s : Γ(descentGlue D, V)) :
    ∃ t : Γ(descentGlue (restrictDescentData ι w D U), ι U ⁻¹ᵁ V),
      ∀ j, glueVal _ j t = glueVal D ⟨U, j⟩ s :=
  exists_glueVal_eq _ fun _ _ ↦ (descentCompat_restrict_iff ι w U _ _).2 (glueVal_compat s _ _)

/-- The sections over `ι U ⁻¹ᵁ V` of the module of compatible sections of the restriction of `D`
to `Y U` determined by a section of `descentGlue D` over `V`. -/
noncomputable def restrictGlueSections (U : I) (V : S.Opens) :
    Γ(descentGlue D, V) →+ Γ(descentGlue (restrictDescentData ι w D U), ι U ⁻¹ᵁ V) where
  toFun s := (exists_restrictGlue ι w U s).choose
  map_zero' := glueVal_ext fun j ↦ by
    rw [(exists_restrictGlue ι w U 0).choose_spec, map_zero, map_zero]
  map_add' s t := glueVal_ext fun j ↦ by
    rw [(exists_restrictGlue ι w U _).choose_spec, map_add, map_add,
      (exists_restrictGlue ι w U _).choose_spec, (exists_restrictGlue ι w U _).choose_spec]

lemma glueVal_restrictGlueSections (U : I) {V : S.Opens} (s : Γ(descentGlue D, V)) (j : κ U) :
    glueVal _ j (restrictGlueSections ι w U V s) = glueVal D ⟨U, j⟩ s :=
  (exists_restrictGlue ι w U s).choose_spec j

lemma restrictGlueSections_smul (U : I) {V : S.Opens} (r : Γ(S, V)) (s : Γ(descentGlue D, V)) :
    restrictGlueSections ι w U V (r • s) = (ι U).app V r • restrictGlueSections ι w U V s := by
  refine glueVal_ext fun j ↦ ?_
  rw [glueVal_restrictGlueSections, glueVal_smul, glueVal_smul, glueVal_restrictGlueSections,
    Scheme.Hom.comp_app]
  rfl

lemma restrictGlueSections_presheaf_map (U : I) {V V' : S.Opens} (i : V' ⟶ V)
    (s : Γ(descentGlue D, V)) :
    restrictGlueSections ι w U V' ((descentGlue D).presheaf.map i.op s) =
      (descentGlue (restrictDescentData ι w D U)).presheaf.map
        (homOfLE ((ι U).preimage_mono i.le)).op (restrictGlueSections ι w U V s) := by
  refine glueVal_ext fun j ↦ ?_
  rw [glueVal_restrictGlueSections, glueVal_presheaf_map, glueVal_presheaf_map,
    glueVal_restrictGlueSections]
  rfl

variable (D) in
/-- The morphism from `descentGlue D` to the pushforward along `ι U` of the module of compatible
sections of the restriction of `D` to `Y U`. -/
noncomputable def restrictGlue (U : I) :
    descentGlue D ⟶ (pushforward (ι U)).obj (descentGlue (restrictDescentData ι w D U)) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (restrictGlueSections ι w U V.unop)
      naturality V V' i := by
        ext s
        exact restrictGlueSections_presheaf_map ι w U i.unop s }
    fun V r s ↦ restrictGlueSections_smul ι w U r s⟩

lemma restrictGlue_app (U : I) {V : S.Opens} (s : Γ(descentGlue D, V)) :
    (restrictGlue ι w D U).app V s = restrictGlueSections ι w U V s :=
  rfl

variable (D) in
/-- The comparison morphism from the restriction to `Y U` of `descentGlue D` to the module of
compatible sections of the restriction of `D` to `Y U`. -/
noncomputable def restrictGlueHom (U : I) :
    (pullback (ι U)).obj (descentGlue D) ⟶ descentGlue (restrictDescentData ι w D U) :=
  ((pullbackPushforwardAdjunction (ι U)).homEquiv _ _).symm (restrictGlue ι w D U)

lemma restrictGlueHom_app_pullbackUnitApp (U : I) {V : S.Opens} (s : Γ(descentGlue D, V)) :
    (restrictGlueHom ι w D U).app (ι U ⁻¹ᵁ V) (pullbackUnitApp (ι U) _ V s) =
      restrictGlueSections ι w U V s := by
  have e := congr(Hom.app
    $(((pullbackPushforwardAdjunction (ι U)).homEquiv _ _).apply_symm_apply
      (restrictGlue ι w D U)) V s)
  rw [Adjunction.homEquiv_unit, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at e
  exact e

lemma glueCounit_eq_restrictGlueHom (U : I) (j : κ U) :
    glueCounit D ⟨U, j⟩ = (pullbackComp (w U j) (ι U)).inv.app (descentGlue D) ≫
      (pullback (w U j)).map (restrictGlueHom ι w D U) ≫
        glueCounit (restrictDescentData ι w D U) j := by
  refine pullback_hom_ext (w U j ≫ ι U) fun V s ↦ ?_
  have h₁ := glueCounit_app_pullbackUnitApp (D := D) ⟨U, j⟩ s
  dsimp only at h₁
  have h₂ : ((pullbackComp (w U j) (ι U)).inv.app (descentGlue D)).app ((w U j ≫ ι U) ⁻¹ᵁ V)
      (pullbackUnitApp (w U j ≫ ι U) _ V s) =
      pullbackUnitApp (w U j) _ _ (pullbackUnitApp (ι U) _ V s) :=
    pullbackUnit_comp_app_apply _ _ _ _ _
  have h₃ : ((pullback (w U j)).map (restrictGlueHom ι w D U)).app (w U j ⁻¹ᵁ ι U ⁻¹ᵁ V)
      (pullbackUnitApp (w U j) _ _ (pullbackUnitApp (ι U) _ V s)) =
      pullbackUnitApp (w U j) _ _ ((restrictGlueHom ι w D U).app _
        (pullbackUnitApp (ι U) _ V s)) :=
    pullbackUnit_naturality_apply _ _ _ _
  erw [h₁]
  rw [Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have h₄ := restrictGlueHom_app_pullbackUnitApp ι w (D := D) U s
  have h₅ := glueCounit_app_pullbackUnitApp (D := restrictDescentData ι w D U) j
    (restrictGlueSections ι w U V s)
  simp only [pullbackUnitApp] at h₂ h₃ h₄ h₅ ⊢
  erw [h₂, h₃, h₄]
  exact (h₅.trans (glueVal_restrictGlueSections ι w U s j)).symm

include w in
lemma pullback_ofArrows_comp_mem {U : I}
    (hU : Sieve.ofArrows (W U) (w U) ∈ Scheme.fpqcTopology (Y U)) {V : S.Opens}
    (hV : V ≤ (ι U).opensRange) :
    Sieve.pullback V.ι (Sieve.ofArrows (fun j ↦ W U j) (fun j ↦ w U j ≫ ι U)) ∈
      Scheme.fpqcTopology V.toScheme := by
  have hr : Set.range V.ι ⊆ Set.range (ι U) := by
    rw [Scheme.Opens.range_ι]
    exact hV
  refine Scheme.fpqcTopology.superset_covering ?_
    (Scheme.fpqcTopology.pullback_stable (IsOpenImmersion.lift (ι U) V.ι hr) hU)
  rintro Z h hh
  obtain ⟨j, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, k, ?_⟩
  rw [← IsOpenImmersion.lift_fac (ι U) V.ι hr, ← Category.assoc, hk, Category.assoc]

include w in
lemma isIso_restrictGlueHom
    (hD : ∀ a : Σ U, κ U, (D.obj a : (W a.1 a.2).Modules).IsQuasicoherent) (U : I)
    (hU : Sieve.ofArrows (W U) (w U) ∈ Scheme.fpqcTopology (Y U)) :
    IsIso (restrictGlueHom ι w D U) := by
  refine Hom.isIso_of_forall_bijective_app _ fun x ↦ ⟨⊤, trivial, fun O _ ↦ ?_⟩
  rw [← (ι U).preimage_image_eq O]
  have hV : (ι U) ''ᵁ O ≤ (ι U).opensRange := (ι U).image_le_opensRange O
  have hβ := pullback_ofArrows_comp_mem ι w hU hV
  have hβ' : Sieve.pullback ((ι U) ''ᵁ O).ι (Sieve.ofArrows (fun k : κ U ↦ W (Sigma.mk U k).1
      (Sigma.mk U k).2) (fun k ↦ w (Sigma.mk U k).1 (Sigma.mk U k).2 ≫ ι (Sigma.mk U k).1)) ∈
      Scheme.fpqcTopology ((ι U) ''ᵁ O).toScheme := hβ
  have hb : Function.Bijective (restrictGlueSections ι w (D := D) U ((ι U) ''ᵁ O)) :=
    ⟨fun s t hst ↦ glueVal_ext_of_subfamily (β := Sigma.mk U) hD hβ' fun j ↦ by
      rw [← glueVal_restrictGlueSections ι w U s j, hst, glueVal_restrictGlueSections],
    fun t ↦ by
      let e : ∀ j : κ U, Γ(descentObj D ⟨U, j⟩, (w U j ≫ ι U) ⁻¹ᵁ ((ι U) ''ᵁ O)) :=
        fun j ↦ glueVal (restrictDescentData ι w D U) j t
      have he (j j' : κ U) : DescentCompat D ((ι U) ''ᵁ O) (a := ⟨U, j⟩) (b := ⟨U, j'⟩) (e j)
          (e j') :=
        (descentCompat_restrict_iff ι w U (e j) (e j')).1 (glueVal_compat t j j')
      obtain ⟨s, hs⟩ := exists_glueVal_eq_of_subfamily (β := Sigma.mk U) hD hβ' e he
      exact ⟨s, glueVal_ext fun j ↦ by rw [glueVal_restrictGlueSections, hs]⟩⟩
  have hη := bijective_pullbackUnit_app_of_isOpenImmersion (ι U) (descentGlue D) hV
  have hc (s : Γ(descentGlue D, (ι U) ''ᵁ O)) :=
    restrictGlueHom_app_pullbackUnitApp ι w (D := D) U s
  refine ⟨fun x y hxy ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hη.2 x
    obtain ⟨b, rfl⟩ := hη.2 y
    erw [hc, hc] at hxy
    rw [hb.1 hxy]
  · obtain ⟨a, rfl⟩ := hb.2 t
    exact ⟨_, hc a⟩

end Restrict

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

/-- Quasi-coherence is invariant under isomorphisms. -/
lemma isQuasicoherent_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) [M.IsQuasicoherent] :
    N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e ‹M.IsQuasicoherent›

/-- A family of open immersions covering `X` generates an fpqc covering sieve. -/
lemma ofArrows_mem_fpqcTopology_of_isOpenImmersion {X : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (u i)]
    (hu : ⨆ i, (u i).opensRange = ⊤) : Sieve.ofArrows U u ∈ Scheme.fpqcTopology X := by
  apply Scheme.zariskiTopology_le_fpqcTopology
  rw [Scheme.mem_grothendieckTopology_iff]
  have hc (x : X) : ∃ i y, u i y = x := by
    obtain ⟨i, y, rfl⟩ : ∃ i, x ∈ (u i).opensRange :=
      TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
    exact ⟨i, y, rfl⟩
  refine ⟨Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι U u hc, ?_⟩
  rintro _ _ ⟨j⟩
  exact Sieve.ofArrows_mk _ _ j

/-- **Fpqc descent for quasi-coherent modules: effectivity.** -/
theorem exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology {T : Scheme.{u}}
    {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsQuasicoherent) :
    ∃ M : modulesPseudofunctor.obj (.mk (op T)), (M : T.Modules).IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D) := by
  choose κ Wf w hfin haff hflat hS hcov using fun U : T.affineOpens ↦
    Scheme.exists_finite_affine_flat_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable U.2.fromSpec hg)
  choose i k hk using fun a : Σ U, κ U ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hS a.1 a.2)
  let ιU : ∀ U : T.affineOpens, Spec Γ(T, U.1) ⟶ T := fun U ↦ U.2.fromSpec
  let F : ∀ a : Σ U, κ U, Wf a.1 a.2 ⟶ T := fun a ↦ w a.1 a.2 ≫ ιU a.1
  have hF : Sieve.ofArrows _ F ∈ Scheme.fpqcTopology T := by
    have hZ := ofArrows_mem_fpqcTopology_of_isOpenImmersion ιU (by
      simpa only [ιU, IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top T)
    refine Scheme.fpqcTopology.transitive hZ _ fun Y h hh ↦ ?_
    obtain ⟨U, m, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
    refine Scheme.fpqcTopology.superset_covering ?_
      (Scheme.fpqcTopology.pullback_stable m (hcov U))
    rintro Z h' hh'
    obtain ⟨j, n, hn⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh'
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨U, j⟩, n, ?_⟩
    simp only [F, ← Category.assoc, ← hn]
  have hw (a : Σ U, κ U) : k a ≫ g (i a) = F a := (hk a).symm
  let D' := (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor (f := g) (p := 𝟙 T)
    (f' := F) (p' := k) (by cat_disch)).obj D
  have hD' (a : Σ U, κ U) : (D'.obj a : (Wf a.1 a.2).Modules).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback (moduleSheaf := (D.obj (i a) : (T' (i a)).Modules)) (k a)
  have hloc (U : T.affineOpens) :
      (descentGlue (restrictDescentData ιU w D' U)).IsQuasicoherent ∧
        ∀ j, IsIso (glueCounit (restrictDescentData ιU w D' U) j) := by
    have := hfin U
    have := haff U
    have := hflat U
    have hsurj : ⋃ j, Set.range (w U j) = Set.univ := by
      refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology (hcov U) x
      obtain ⟨j, k', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
      exact Set.mem_iUnion.2 ⟨j, k' y, rfl⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := exists_iso_toDescentData_of_finite_of_isAffine (w U) hsurj
      (restrictDescentData ιU w D' U) (fun j ↦ hD' ⟨U, j⟩)
    have := isIso_toGlue (hcov U) eP
    refine ⟨isQuasicoherent_of_iso (asIso (toGlue eP.hom)), fun j ↦ ?_⟩
    have h := pullback_map_toGlue_comp_glueCounit eP.hom j
    have : IsIso (eP.hom.hom j) := ⟨eP.inv.hom j,
      congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ j) eP.hom_inv_id,
      congrArg (fun φ ↦ Pseudofunctor.DescentData.Hom.hom φ j) eP.inv_hom_id⟩
    rw [← IsIso.eq_inv_comp] at h
    rw [h]
    infer_instance
  have hτ (U : T.affineOpens) := isIso_restrictGlueHom ιU w hD' U (hcov U)
  have hc (a : Σ U, κ U) : IsIso (glueCounit D' a) := by
    obtain ⟨U, j⟩ := a
    rw [glueCounit_eq_restrictGlueHom ιU w U j]
    have := (hloc U).2 j
    infer_instance
  have hMq : (descentGlue D').IsQuasicoherent := by
    refine isQuasicoherent_of_iSup_opensRange_eq_top (descentGlue D') ιU
      (by simpa only [ιU, IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top T)
      fun U ↦ ?_
    have := (hloc U).1
    exact (presentationOfIsIsoFromTildeΓ (descentGlue (restrictDescentData ιU w D' U))).ofIsIso
      (inv ((restrictFunctorIsoPullback (ιU U)).hom.app (descentGlue D') ≫
        restrictGlueHom ιU w D' U))
  let M' : modulesPseudofunctor.obj (.mk (op T)) := descentGlue D'
  have : ∀ a, IsIso ((glueToDescentData D').hom a) := fun a ↦ by
    rw [glueToDescentData_hom]
    exact hc a
  have := Pseudofunctor.DescentData.isIso_of_isIso_hom (glueToDescentData D')
  let e' : (modulesPseudofunctor.toDescentData F).obj M' ≅ D' := asIso (glueToDescentData D')
  let e₁ := (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor
    (f := g) (p := 𝟙 T) (f' := F) (p' := k) (by cat_disch)).app M'
  let e₂ := (modulesPseudofunctor.toDescentData F).mapIso
    ((Cat.Hom.toNatIso (modulesPseudofunctor.mapId _)).app M')
  refine ⟨M', hMq, Pseudofunctor.DescentData.nonempty_iso_of_pullFunctor_obj_iso
    modulesPseudofunctor (J := Scheme.fpqcTopology) hw hF ?_ ?_ ?_ ?_ (e₁ ≪≫ e₂ ≪≫ e')⟩
  all_goals intro j; apply isSheaf_presheafHom <;>
    first
    | exact Scheme.Modules.isQuasicoherent_pullback (moduleSheaf := (M' : T.Modules)) _
    | exact hD j

end AlgebraicGeometry
