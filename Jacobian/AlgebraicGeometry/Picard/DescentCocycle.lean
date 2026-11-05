import Jacobian.AlgebraicGeometry.Picard.NormalizedDescent.DescentDataModules

/-!
# Scalar cocycles and module descent

Scalar cocycles twist module descent data; ratios of transition maps and base change describe the resulting twists.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w w' u
open CategoryTheory Limits Opposite Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry
open Scheme

section SmulHom

variable {Y : Scheme.{u}}

/-- Multiplication by a global function `a`, as an endomorphism of an object of
`modulesPseudofunctor.obj (.mk (op Y))`; this is `AlgebraicGeometry.Scheme.Modules.smulHom`, seen
in the category of the pseudofunctor so that it composes with descent data. -/
noncomputable def pseudofunctorSmulHom (M : modulesPseudofunctor.obj (.mk (op Y)))
    (a : Γ(Y, ⊤)) : M ⟶ M :=
  Modules.smulHom (X := Y) M a

@[simp]
lemma pseudofunctorSmulHom_one (M : modulesPseudofunctor.obj (.mk (op Y))) :
    pseudofunctorSmulHom M 1 = 𝟙 M :=
  Modules.smulHom_one (X := Y) M

lemma pseudofunctorSmulHom_mul (M : modulesPseudofunctor.obj (.mk (op Y))) (a b : Γ(Y, ⊤)) :
    pseudofunctorSmulHom M (a * b) = pseudofunctorSmulHom M b ≫ pseudofunctorSmulHom M a :=
  Modules.smulHom_mul (X := Y) M a b

@[reassoc]
lemma pseudofunctorSmulHom_naturality {M N : modulesPseudofunctor.obj (.mk (op Y))}
    (φ : M ⟶ N) (a : Γ(Y, ⊤)) :
    pseudofunctorSmulHom M a ≫ φ = φ ≫ pseudofunctorSmulHom N a :=
  Modules.smulHom_naturality (X := Y) φ a

lemma pullHom_pseudofunctorSmulHom {Y' Z : Scheme.{u}}
    (M : modulesPseudofunctor.obj (.mk (op Z))) (f₁ : Y ⟶ Z) (b : Y' ⟶ Y) (bf : Y' ⟶ Z)
    (h : b ≫ f₁ = bf) (a : Γ(Y, ⊤)) :
    pullHom (pseudofunctorSmulHom ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj M) a)
      b bf bf h h =
      pseudofunctorSmulHom ((modulesPseudofunctor.map bf.op.toLoc).toFunctor.obj M)
        (b.appTop a) :=
  pullHom_smulHom M f₁ b bf h a

/-- Pulling back a morphism followed by multiplication by `a`. (Proved by a term rather than by
`rw`, whose motives are slow to type check here.) -/
lemma pullHom_comp_pseudofunctorSmulHom {Y' Z₁ Z₂ : Scheme.{u}}
    {M₁ : modulesPseudofunctor.obj (.mk (op Z₁))} {M₂ : modulesPseudofunctor.obj (.mk (op Z₂))}
    {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    (φ : (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂) (a : Γ(Y, ⊤))
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (φ ≫ pseudofunctorSmulHom _ a) g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pseudofunctorSmulHom _ (g.appTop a) :=
  (pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂).trans
    (congrArg _ (pullHom_pseudofunctorSmulHom _ _ _ _ hgf₂ _))

lemma comp_comp_pseudofunctorSmulHom_comp {A B C D : modulesPseudofunctor.obj (.mk (op Y))}
    (x : A ⟶ B) (y : B ⟶ C) (z : C ⟶ D) (a : Γ(Y, ⊤)) :
    x ≫ (y ≫ pseudofunctorSmulHom C a) ≫ z = (x ≫ y ≫ z) ≫ pseudofunctorSmulHom D a := by
  simp only [Category.assoc, pseudofunctorSmulHom_naturality]

/-- An invertible module on which multiplication by `a` and by `b` agree has `a = b`. -/
lemma eq_of_pseudofunctorSmulHom_eq (M : modulesPseudofunctor.obj (.mk (op Y)))
    [M.IsInvertible] {a b : Γ(Y, ⊤)}
    (h : pseudofunctorSmulHom M a = pseudofunctorSmulHom M b) : a = b :=
  Modules.eq_of_smulHom_eq (scheme := Y) M h

/-- Every endomorphism of an invertible module is multiplication by a global function. -/
lemma exists_eq_pseudofunctorSmulHom (M : modulesPseudofunctor.obj (.mk (op Y)))
    [M.IsInvertible] (φ : M ⟶ M) : ∃ a, φ = pseudofunctorSmulHom M a :=
  Modules.exists_eq_smulHom (scheme := Y) M φ

end SmulHom

section Cocycle

variable {S : Scheme.{u}} {ι : Type w} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- A cocycle of global functions relative to a family of morphisms `f i : X i ⟶ S`: a global
function `c q f₁ f₂` on every scheme `Y` with two morphisms `f₁ : Y ⟶ X i₁`, `f₂ : Y ⟶ X i₂`
over `q : Y ⟶ S`, compatible with pullbacks, trivial on the diagonal and multiplicative. -/
@[ext]
structure DescentCocycle where
  /-- The global function attached to `Y` and the morphisms `f₁` and `f₂`. -/
  c ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) : Γ(Y, ⊤)
  appTop_c ⦃Y' Y : Scheme.{u}⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    g.appTop (c q f₁ f₂ hf₁ hf₂) =
      c q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq])
  c_self ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    c q g g hg hg = 1
  c_mul ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    c q f₁ f₂ hf₁ hf₂ * c q f₂ f₃ hf₂ hf₃ = c q f₁ f₃ hf₁ hf₃

namespace DescentCocycle

variable {f} (c : DescentCocycle f)

/-- The twist of a descent datum of modules by a cocycle `c`: the gluing morphisms are composed
with multiplication by `c`. -/
@[simps]
noncomputable def twist (D : modulesPseudofunctor.DescentData f) :
    modulesPseudofunctor.DescentData f where
  obj := D.obj
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    D.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (c.c q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    (pullHom_comp_pseudofunctorSmulHom _ _ g gf₁ gf₂ hgf₁ hgf₂).trans
      (congrArg₂ (· ≫ ·) (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
        (congrArg _ (c.appTop_c g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)))
  hom_self Y q i g hg := by
    rw [D.hom_self q g hg, c.c_self, pseudofunctorSmulHom_one, Category.comp_id]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [Category.assoc, pseudofunctorSmulHom_naturality_assoc, D.hom_comp_assoc,
      ← pseudofunctorSmulHom_mul, mul_comm, c.c_mul]

lemma twist_comm {D₁ D₂ : modulesPseudofunctor.DescentData f} (φ : D₁ ⟶ D₂) ⦃Y : Scheme.{u}⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫
        D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (c.c q f₁ f₂ hf₁ hf₂) =
      (D₁.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (c.c q f₁ f₂ hf₁ hf₂)) ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  rw [reassoc_of% (φ.comm q f₁ f₂ hf₁ hf₂), Category.assoc, pseudofunctorSmulHom_naturality]

/-- Twisting by a cocycle, as a functor. -/
noncomputable def twistFunctor :
    modulesPseudofunctor.DescentData f ⥤ modulesPseudofunctor.DescentData f where
  obj D := c.twist D
  map {D₁ D₂} φ :=
    { hom i := φ.hom i
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        exact c.twist_comm φ q f₁ f₂ hf₁ hf₂ }

@[simp]
lemma twistFunctor_obj (D : modulesPseudofunctor.DescentData f) :
    c.twistFunctor.obj D = c.twist D :=
  rfl

@[simp]
lemma twistFunctor_map_hom {D₁ D₂ : modulesPseudofunctor.DescentData f} (φ : D₁ ⟶ D₂) (i : ι) :
    (c.twistFunctor.map φ).hom i = φ.hom i :=
  rfl

section Ratio

variable {D₁ D₂ : modulesPseudofunctor.DescentData f}
  [hD₂ : ∀ i, (D₂.obj i).IsInvertible] (e : ∀ i, D₁.obj i ≅ D₂.obj i)

include hD₂ in
lemma exists_ratio ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ∃ a : Γ(Y, ⊤), D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ a =
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by
  letI : (D₂.obj i₂).IsInvertible := hD₂ i₂
  have : SheafOfModules.IsInvertible.{u, u, u}
      (((modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj (D₂.obj i₂)) : Y.Modules) :=
    inferInstanceAs ((Modules.pullback f₂).obj (D₂.obj i₂)).IsInvertible
  obtain ⟨a, ha⟩ := exists_eq_pseudofunctorSmulHom _
    (inv (D₂.hom q f₁ f₂ hf₁ hf₂) ≫
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫
        D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom)
  exact ⟨a, by rw [← ha, IsIso.hom_inv_id_assoc]⟩

/-- The global function by which the gluing morphisms of `D₁` and `D₂`, compared through the
isomorphisms `e i`, differ. -/
noncomputable def ratio ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) : Γ(Y, ⊤) :=
  (exists_ratio e q f₁ f₂ hf₁ hf₂).choose

lemma hom_comp_ratio ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (ratio e q f₁ f₂ hf₁ hf₂) =
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom :=
  (exists_ratio e q f₁ f₂ hf₁ hf₂).choose_spec

include hD₂ in
lemma ratio_eq ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) {a : Γ(Y, ⊤)}
    (h : D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ a =
      (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).inv ≫ D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom) :
    ratio e q f₁ f₂ hf₁ hf₂ = a := by
  letI : (D₂.obj i₂).IsInvertible := hD₂ i₂
  have : SheafOfModules.IsInvertible.{u, u, u}
      (((modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj (D₂.obj i₂)) : Y.Modules) :=
    inferInstanceAs ((Modules.pullback f₂).obj (D₂.obj i₂)).IsInvertible
  exact eq_of_pseudofunctorSmulHom_eq _ (by rw [← cancel_epi (D₂.hom q f₁ f₂ hf₁ hf₂),
    hom_comp_ratio, h])

include hD₂ in
lemma appTop_ratio ⦃Y' Y : Scheme.{u}⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    g.appTop (ratio e q f₁ f₂ hf₁ hf₂) =
      ratio e q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) := by
  refine (ratio_eq e _ _ _ _ _ ?_).symm
  exact ((pullHom_comp_pseudofunctorSmulHom _ _ g gf₁ gf₂ hgf₁ hgf₂).trans
    (congrArg (· ≫ _) (D₂.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂))).symm.trans <|
    (congrArg (pullHom · g gf₁ gf₂ hgf₁ hgf₂) (hom_comp_ratio e q f₁ f₂ hf₁ hf₂)).trans <|
    (pullHom_comp _ _ g gf₁ gf₁ gf₂ hgf₁ hgf₁ hgf₂).trans <|
    congrArg₂ (· ≫ ·) (pullHom_map _ _ _ _ hgf₁) <|
    (pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂).trans <|
    congrArg₂ (· ≫ ·) (D₁.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
      (pullHom_map _ _ _ _ hgf₂)

include hD₂ in
lemma ratio_self ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    ratio e q g g hg hg = 1 := by
  refine ratio_eq e _ _ _ _ _ ?_
  rw [D₂.hom_self q g hg, D₁.hom_self q g hg, pseudofunctorSmulHom_one, Category.id_comp,
    Category.id_comp, Iso.map_inv_hom_id]

include hD₂ in
lemma ratio_mul ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    ratio e q f₁ f₂ hf₁ hf₂ * ratio e q f₂ f₃ hf₂ hf₃ = ratio e q f₁ f₃ hf₁ hf₃ := by
  refine (ratio_eq e q f₁ f₃ hf₁ hf₃ ?_).symm
  rw [← D₂.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃, ← D₁.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃,
    pseudofunctorSmulHom_mul, Category.assoc, ← Category.assoc _ _ (pseudofunctorSmulHom _ _),
    ← pseudofunctorSmulHom_naturality, ← Category.assoc, hom_comp_ratio, Category.assoc,
    hom_comp_ratio]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc]

/-- The cocycle by which two descent data with isomorphic invertible components differ. -/
noncomputable def ratioCocycle : DescentCocycle f where
  c := ratio e
  appTop_c := appTop_ratio e
  c_self := ratio_self e
  c_mul := ratio_mul e

lemma map_hom_comp_twist_hom ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
        D₂.hom q f₁ f₂ hf₁ hf₂ ≫ pseudofunctorSmulHom _ (ratio e q f₁ f₂ hf₁ hf₂) =
      D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by
  rw [hom_comp_ratio, Iso.map_hom_inv_id_assoc]

/-- A descent datum whose components are isomorphic to the invertible components of `D₂` is
isomorphic to the twist of `D₂` by `DescentCocycle.ratioCocycle`. -/
noncomputable def isoTwistRatioCocycle : D₁ ≅ (ratioCocycle e).twist D₂ :=
  DescentData.isoMk e fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ map_hom_comp_twist_hom e q f₁ f₂ hf₁ hf₂

include hD₂ in
/-- **Descent data with isomorphic invertible components differ by a twist.** -/
theorem exists_iso_twist (h : ∀ i, Nonempty (D₁.obj i ≅ D₂.obj i)) :
    ∃ c : DescentCocycle f, Nonempty (D₁ ≅ c.twist D₂) :=
  ⟨ratioCocycle fun i ↦ (h i).some, ⟨isoTwistRatioCocycle fun i ↦ (h i).some⟩⟩

end Ratio

section Pull

variable {S' : Scheme.{u}} {p : S' ⟶ S} {ι' : Type w'} {X' : ι' → Scheme.{u}}
  {f' : ∀ j, X' j ⟶ S'} {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
  (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

/-- The pullback of a cocycle along a morphism of families. -/
def pull : DescentCocycle f' where
  c Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := c.c (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
    (by rw [Category.assoc, w, reassoc_of% hf₁]) (by rw [Category.assoc, w, reassoc_of% hf₂])
  appTop_c Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    c.appTop_c g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq]) _ _ _ _ (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by rw [reassoc_of% hgf₁]) (by rw [reassoc_of% hgf₂])
  c_self Y q j g hg := c.c_self _ _ _
  c_mul Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := c.c_mul _ _ _ _ _ _ _

lemma pullFunctorObjHom_twist (D : modulesPseudofunctor.DescentData f) ⦃Y : Scheme.{u}⦄
    (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂) (hf₁ : f₁ ≫ f' j₁ = q)
    (hf₂ : f₂ ≫ f' j₂ = q) :
    DescentData.pullFunctorObjHom w (c.twist D) q f₁ f₂ hf₁ hf₂ =
      DescentData.pullFunctorObjHom w D q f₁ f₂ hf₁ hf₂ ≫
        pseudofunctorSmulHom _ ((c.pull w).c q f₁ f₂ hf₁ hf₂) := by
  exact comp_comp_pseudofunctorSmulHom_comp _ _ _ _

/-- **Twisting commutes with base change.** -/
lemma pullFunctor_obj_twist (D : modulesPseudofunctor.DescentData f) :
    (DescentData.pullFunctor modulesPseudofunctor w).obj (c.twist D) =
      (c.pull w).twist ((DescentData.pullFunctor modulesPseudofunctor w).obj D) := by
  change DescentData.pullFunctorObj w (c.twist D) =
    (c.pull w).twist (DescentData.pullFunctorObj w D)
  unfold DescentData.pullFunctorObj twist
  congr 1
  funext Y q j₁ j₂ f₁ f₂ hf₁ hf₂
  subst hf₁
  exact pullFunctorObjHom_twist c w D _ f₁ f₂ rfl hf₂

end Pull

end DescentCocycle

end Cocycle

section BaseChange

/-- The base change map `X_{T'} ⟶ X_T` commutes with the projections to `X`. -/
@[reassoc]
lemma baseChangeMap_fst {X S : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) :
    baseChangeMap f φ ≫ pullback.fst f T.hom = pullback.fst f T'.hom := by
  exact pullback.lift_fst _ _ _

/-- The base change map `X_{T'} ⟶ X_T` lies over `T' ⟶ T`. -/
@[reassoc]
lemma baseChangeMap_snd {X S : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) :
    baseChangeMap f φ ≫ pullback.snd f T.hom = pullback.snd f T'.hom ≫ φ.left :=
  pullback.lift_snd _ _ _

variable {X S : Scheme.{u}} (f : X ⟶ S) {T : Over S} {ι : Type w} {T' : ι → Over S}
  (g : ∀ i, T' i ⟶ T)
  (hbij : ∀ Y : Over S, Function.Bijective (pullback.snd f Y.hom).appTop)

namespace DescentCocycle

variable {f g} (c : DescentCocycle fun i ↦ baseChangeMap f (g i))

/-- The value of the descended cocycle `DescentCocycle.ofBaseChange` at `Y`, `f₁` and `f₂`: the
unique function on `Y` whose pullback to `X_Y` is the value of `c` at the base changes of `f₁` and
`f₂`. -/
noncomputable def ofBaseChangeAux ⦃Y : Scheme.{u}⦄ (q : Y ⟶ T.left) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ (T' i₁).left) (f₂ : Y ⟶ (T' i₂).left) (hf₁ : f₁ ≫ (g i₁).left = q)
    (hf₂ : f₂ ≫ (g i₂).left = q) : Γ(Y, ⊤) :=
  (Equiv.ofBijective _ (hbij (Over.mk (q ≫ T.hom)))).symm
    (c.c (baseChangeMap f (Over.homMk q : Over.mk (q ≫ T.hom) ⟶ T))
      (baseChangeMap f (Over.homMk f₁ (by rw [← Over.w (g i₁), reassoc_of% hf₁]; rfl) :
        Over.mk (q ≫ T.hom) ⟶ T' i₁))
      (baseChangeMap f (Over.homMk f₂ (by rw [← Over.w (g i₂), reassoc_of% hf₂]; rfl) :
        Over.mk (q ≫ T.hom) ⟶ T' i₂))
      (by rw [← baseChangeMap_comp]; congr 1; ext; exact hf₁)
      (by rw [← baseChangeMap_comp]; congr 1; ext; exact hf₂))

lemma appTop_ofBaseChangeAux ⦃Y : Scheme.{u}⦄ (q : Y ⟶ T.left) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ (T' i₁).left) (f₂ : Y ⟶ (T' i₂).left) (hf₁ : f₁ ≫ (g i₁).left = q)
    (hf₂ : f₂ ≫ (g i₂).left = q) :
    (pullback.snd f (Over.mk (q ≫ T.hom)).hom).appTop (c.ofBaseChangeAux hbij q f₁ f₂ hf₁ hf₂) =
      c.c (baseChangeMap f (Over.homMk q : Over.mk (q ≫ T.hom) ⟶ T))
        (baseChangeMap f (Over.homMk f₁ (by rw [← Over.w (g i₁), reassoc_of% hf₁]; rfl) :
          Over.mk (q ≫ T.hom) ⟶ T' i₁))
        (baseChangeMap f (Over.homMk f₂ (by rw [← Over.w (g i₂), reassoc_of% hf₂]; rfl) :
          Over.mk (q ≫ T.hom) ⟶ T' i₂))
        (by rw [← baseChangeMap_comp]; congr 1; ext; exact hf₁)
        (by rw [← baseChangeMap_comp]; congr 1; ext; exact hf₂) :=
  (Equiv.ofBijective _ (hbij (Over.mk (q ≫ T.hom)))).apply_symm_apply _

/-- **Descending a cocycle along `X_T ⟶ T`.** If `Γ(Y, 𝒪_Y) ⟶ Γ(X_Y, 𝒪_{X_Y})` is bijective for
every `Y` over `S`, a cocycle relative to the family `X_{T i} ⟶ X_T` comes from a cocycle relative
to the family `T i ⟶ T` (`DescentCocycle.pull_ofBaseChange`). -/
noncomputable def ofBaseChange : DescentCocycle fun i ↦ (g i).left where
  c := c.ofBaseChangeAux hbij
  appTop_c Y' Y h q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    apply (hbij (Over.mk (q' ≫ T.hom))).1
    let ho : Over.mk (q' ≫ T.hom) ⟶ Over.mk (q ≫ T.hom) :=
      Over.homMk h (by rw [← hq]; simp)
    have key : pullback.snd f (Over.mk (q' ≫ T.hom)).hom ≫ h =
        baseChangeMap f ho ≫ pullback.snd f (Over.mk (q ≫ T.hom)).hom :=
      (baseChangeMap_snd f ho).symm
    have key' (a : Γ(Y, ⊤)) : (pullback.snd f (Over.mk (q' ≫ T.hom)).hom).appTop (h.appTop a) =
        (baseChangeMap f ho).appTop ((pullback.snd f (Over.mk (q ≫ T.hom)).hom).appTop a) := by
      change (h.appTop ≫ _) a = (_ ≫ (baseChangeMap f ho).appTop) a
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, key]
    rw [appTop_ofBaseChangeAux, key', appTop_ofBaseChangeAux]
    exact c.appTop_c (baseChangeMap f ho) _ _
      (by rw [← baseChangeMap_comp]; congr 1; ext; exact hq) _ _ _ _ _ _
      (by rw [← baseChangeMap_comp]; congr 1; ext; exact hgf₁)
      (by rw [← baseChangeMap_comp]; congr 1; ext; exact hgf₂)
  c_self Y q i a ha := by
    apply (hbij (Over.mk (q ≫ T.hom))).1
    rw [appTop_ofBaseChangeAux, c.c_self, map_one]
  c_mul Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    apply (hbij (Over.mk (q ≫ T.hom))).1
    rw [map_mul, appTop_ofBaseChangeAux, appTop_ofBaseChangeAux, appTop_ofBaseChangeAux,
      c.c_mul]

/-- The cocycle `DescentCocycle.ofBaseChange` pulls back to the cocycle it was built from. -/
lemma pull_ofBaseChange :
    (c.ofBaseChange hbij).pull (p := pullback.snd f T.hom) (α := id)
      (p' := fun i ↦ pullback.snd f (T' i).hom) (fun i ↦ (baseChangeMap_snd f (g i)).symm) =
      c := by
  ext Y q j₁ j₂ f₁ f₂ hf₁ hf₂
  let s : Y ⟶ pullback f (Over.mk ((q ≫ pullback.snd f T.hom) ≫ T.hom)).hom :=
    pullback.lift (q ≫ pullback.fst f T.hom) (𝟙 Y)
      (by rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition]; rfl)
  have hs : s ≫ pullback.snd f _ = 𝟙 Y := pullback.lift_snd _ _ _
  have hsf : s ≫ pullback.fst f _ = q ≫ pullback.fst f T.hom := pullback.lift_fst _ _ _
  have w (j : ι) (fj : Y ⟶ pullback f (T' j).hom) (hfj : fj ≫ baseChangeMap f (g j) = q) :
      (fj ≫ pullback.snd f (T' j).hom) ≫ (g j).left = q ≫ pullback.snd f T.hom := by
    rw [Category.assoc, ← baseChangeMap_snd, ← Category.assoc, hfj]
  have e (j : ι) (fj : Y ⟶ pullback f (T' j).hom) (hfj : fj ≫ baseChangeMap f (g j) = q) :
      s ≫ baseChangeMap f (Over.homMk (fj ≫ pullback.snd f (T' j).hom)
        (((Category.assoc _ _ _).trans
          (congrArg (fj ≫ pullback.snd f (T' j).hom ≫ ·) (Over.w (g j)).symm)).trans
            (by simp only [← Category.assoc]; rw [w j fj hfj]; rfl)) :
          Over.mk ((q ≫ pullback.snd f T.hom) ≫ T.hom) ⟶ T' j) = fj := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeMap_fst, hsf, ← hfj, Category.assoc, baseChangeMap_fst]
    · rw [Category.assoc, baseChangeMap_snd, ← Category.assoc, hs, Category.id_comp]
      rfl
  change c.ofBaseChangeAux hbij _ _ _ (w j₁ f₁ hf₁) (w j₂ f₂ hf₂) = _
  calc _ = s.appTop ((pullback.snd f _).appTop (c.ofBaseChangeAux hbij
        (q ≫ pullback.snd f T.hom) (f₁ ≫ pullback.snd f (T' j₁).hom)
        (f₂ ≫ pullback.snd f (T' j₂).hom) (w j₁ f₁ hf₁) (w j₂ f₂ hf₂))) := by
        change _ = (_ ≫ s.appTop) _
        rw [← Scheme.Hom.comp_appTop, hs]
        simp
    _ = _ := by
        rw [appTop_ofBaseChangeAux]
        refine c.appTop_c s _ q ?_ _ _ _ _ f₁ f₂ (e j₁ f₁ hf₁) (e j₂ f₂ hf₂)
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, baseChangeMap_fst, hsf]
        · rw [Category.assoc, baseChangeMap_snd, ← Category.assoc, hs, Category.id_comp]
          rfl

end DescentCocycle

end BaseChange

end AlgebraicGeometry
