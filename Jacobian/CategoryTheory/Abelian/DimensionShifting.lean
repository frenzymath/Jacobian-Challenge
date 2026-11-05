import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Comparing two cohomology theories by dimension shifting

Let `C` be an abelian category with enough injectives and `P` a property of objects of `C` such
that for every `X` with `P X`, the chosen injective object `I = Injective.under X` and the
cokernel `Q` of `X ⟶ I` again satisfy `P`. Let `T q` and `T' q` (`q : ℕ`) be two families of
functors `C ⥤ Ab`, each with connecting maps `T^q(X₃) ⟶ T^{q + 1}(X₁)` for the short exact
sequences `0 → X₁ → X₂ → X₃ → 0` with `P X₁`, which are natural and such that
`T^q(X₂) → T^q(X₃) → T^{q + 1}(X₁) → 0` is exact when `X₂` is injective.
Then a natural isomorphism `T 0 ≅ T' 0` on the objects satisfying `P` propagates to natural
isomorphisms `T q ≅ T' q` on these objects for all `q`: both `T^{q + 1}(X)` and `T'^{q + 1}(X)`
are the cokernel of the map induced by `I → Q` in degree `q`.

This is the uniqueness part of the theory of universal δ-functors, in the form used to compare
Čech cohomology and the cohomology of a pushforward with sheaf cohomology.

## Main statements

- `CategoryTheory.ObjectProperty.nonempty_iso_of_connecting`: the comparison theorem.
-/

noncomputable section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The short exact sequence `0 → X → I → Q → 0` given by the chosen injective object `I` under
`X` and the cokernel `Q` of `X ⟶ I`. -/
noncomputable abbrev injectiveShortComplex (X : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι X) (cokernel.π (Injective.ι X)) (cokernel.condition _)

lemma shortExact_injectiveShortComplex (X : C) : (injectiveShortComplex X).ShortExact :=
  .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- A morphism `X ⟶ Y` extends to a morphism between the short exact sequences
`0 → X → I → Q → 0` and `0 → Y → J → R → 0` given by the chosen injective objects. -/
noncomputable def injectiveShortComplexMap {X Y : C} (f : X ⟶ Y) :
    injectiveShortComplex X ⟶ injectiveShortComplex Y where
  τ₁ := f
  τ₂ := Injective.factorThru (f ≫ Injective.ι Y) (Injective.ι X)
  τ₃ := cokernel.desc _ (Injective.factorThru (f ≫ Injective.ι Y) (Injective.ι X) ≫
    cokernel.π _) (by rw [← Category.assoc, Injective.comp_factorThru, Category.assoc,
      cokernel.condition, Limits.comp_zero])
  comm₁₂ := (Injective.comp_factorThru _ _).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

variable (P : ObjectProperty C)

section Step

variable {P} (hP : ∀ X, P X → P (Injective.under X) ∧ P (cokernel (Injective.ι X)))
  {T T' : ℕ → C ⥤ AddCommGrpCat.{w}}
  (δ : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → ∀ q,
    (T q).obj S.X₃ ⟶ (T (q + 1)).obj S.X₁)
  (δ' : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → ∀ q,
    (T' q).obj S.X₃ ⟶ (T' (q + 1)).obj S.X₁)
  (hδ : ∀ {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (p₁ : P S₁.X₁) (p₂ : P S₂.X₁) (q : ℕ),
    δ S₁ h₁ p₁ q ≫ (T (q + 1)).map φ.τ₁ = (T q).map φ.τ₃ ≫ δ S₂ h₂ p₂ q)
  (hδ' : ∀ {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (p₁ : P S₁.X₁) (p₂ : P S₂.X₁) (q : ℕ),
    δ' S₁ h₁ p₁ q ≫ (T' (q + 1)).map φ.τ₁ = (T' q).map φ.τ₃ ≫ δ' S₂ h₂ p₂ q)
  (hexact : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ) (x),
    δ S hS h q x = 0 ↔ x ∈ ((T q).map S.g).hom.range)
  (hexact' : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ) (x),
    δ' S hS h q x = 0 ↔ x ∈ ((T' q).map S.g).hom.range)
  (hsurj : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ), Injective S.X₂ →
    Function.Surjective (δ S hS h q))
  (hsurj' : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ), Injective S.X₂ →
    Function.Surjective (δ' S hS h q))
  {q : ℕ} (e : P.ι ⋙ T q ≅ P.ι ⋙ T' q)

/-- The object `Q`, cokernel of `X ⟶ I`, as an object of the full subcategory. -/
noncomputable abbrev cokernelObj (X : P.FullSubcategory) : P.FullSubcategory :=
  ⟨cokernel (Injective.ι X.obj), (hP _ X.property).2⟩

/-- The map `I ⟶ Q`, as a morphism of the full subcategory. -/
noncomputable abbrev toCokernelObj (X : P.FullSubcategory) :
    (⟨Injective.under X.obj, (hP _ X.property).1⟩ : P.FullSubcategory) ⟶ cokernelObj hP X :=
  ObjectProperty.homMk (cokernel.π (Injective.ι X.obj))

/-- The comparison `e` at the cokernel `Q` of `X ⟶ I`, as an additive equivalence. -/
noncomputable abbrev cokernelAddEquiv (X : P.FullSubcategory) :
    (T q).obj (injectiveShortComplex X.obj).X₃ ≃+ (T' q).obj (injectiveShortComplex X.obj).X₃ :=
  (e.app (cokernelObj hP X)).addCommGroupIsoToAddEquiv

include hexact hexact' in
lemma map_ker_connecting (X : P.FullSubcategory) :
    (δ _ (shortExact_injectiveShortComplex X.obj) X.property q).hom.ker.map
      (cokernelAddEquiv hP e X : (T q).obj (injectiveShortComplex X.obj).X₃ →+
        (T' q).obj (injectiveShortComplex X.obj).X₃) =
      (δ' _ (shortExact_injectiveShortComplex X.obj) X.property q).hom.ker := by
  ext z
  rw [AddSubgroup.mem_map, AddMonoidHom.mem_ker]
  refine Iff.trans ?_ (hexact' _ _ _ _ z).symm
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := ((hexact _ _ _ _ x).1 hx)
    refine ⟨(e.app ⟨_, (hP _ X.property).1⟩).hom y, ?_⟩
    exact (ConcreteCategory.congr_hom (e.hom.naturality (toCokernelObj hP X)) y).symm
  · rintro ⟨y, rfl⟩
    refine ⟨(T q).map (cokernel.π _) ((e.app ⟨_, (hP _ X.property).1⟩).inv y),
      (hexact _ _ _ _ _).2 ⟨_, rfl⟩, ?_⟩
    have h := ConcreteCategory.congr_hom (e.hom.naturality (toCokernelObj hP X))
      ((e.app ⟨_, (hP _ X.property).1⟩).inv y)
    exact h.trans (congrArg _ ((e.app ⟨_, (hP _ X.property).1⟩).inv_hom_id_apply y))

/-- The comparison in degree `q + 1`, deduced from the comparison `e` in degree `q`: both sides
are the quotients of `T^q(Q)`, resp. `T'^q(Q)`, by the kernel of the connecting map. -/
noncomputable def connectingAddEquiv (X : P.FullSubcategory) :
    (T (q + 1)).obj X.obj ≃+ (T' (q + 1)).obj X.obj :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _
    (hsurj _ (shortExact_injectiveShortComplex X.obj) X.property q
      (inferInstanceAs (Injective (Injective.under X.obj))))).symm.trans <|
    (QuotientAddGroup.congr _ _ _ (map_ker_connecting hP δ δ' hexact hexact' e X)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _
        (hsurj' _ (shortExact_injectiveShortComplex X.obj) X.property q
          (inferInstanceAs (Injective (Injective.under X.obj)))))

lemma connectingAddEquiv_apply (X : P.FullSubcategory) (y) :
    connectingAddEquiv hP δ δ' hexact hexact' hsurj hsurj' e X
      (δ _ (shortExact_injectiveShortComplex X.obj) X.property q y) =
      δ' _ (shortExact_injectiveShortComplex X.obj) X.property q
        ((e.app (cokernelObj hP X)).hom y) := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (hsurj _ (shortExact_injectiveShortComplex X.obj) X.property q
        (inferInstanceAs (Injective (Injective.under X.obj))))).symm
      (δ _ (shortExact_injectiveShortComplex X.obj) X.property q y) = (y : _ ⧸ _) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  simp only [connectingAddEquiv, AddEquiv.trans_apply, h]
  rfl

include hδ hδ' in
lemma connectingAddEquiv_naturality {X Y : P.FullSubcategory} (f : X ⟶ Y) (x) :
    connectingAddEquiv hP δ δ' hexact hexact' hsurj hsurj' e Y ((T (q + 1)).map f.hom x) =
      (T' (q + 1)).map f.hom (connectingAddEquiv hP δ δ' hexact hexact' hsurj hsurj' e X x) := by
  obtain ⟨y, rfl⟩ := hsurj _ (shortExact_injectiveShortComplex X.obj) X.property q
    (inferInstanceAs (Injective (Injective.under X.obj))) x
  let φ := injectiveShortComplexMap f.hom
  have h₁ := ConcreteCategory.congr_hom (hδ φ (shortExact_injectiveShortComplex X.obj)
    (shortExact_injectiveShortComplex Y.obj) X.property Y.property q) y
  have h₂ := ConcreteCategory.congr_hom (e.hom.naturality
    (ObjectProperty.homMk φ.τ₃ : cokernelObj hP X ⟶ cokernelObj hP Y)) y
  have h₃ := ConcreteCategory.congr_hom (hδ' φ (shortExact_injectiveShortComplex X.obj)
    (shortExact_injectiveShortComplex Y.obj) X.property Y.property q)
    ((e.app (cokernelObj hP X)).hom y)
  simp only [ConcreteCategory.comp_apply] at h₁ h₂ h₃
  have hτ : φ.τ₁ = f.hom := rfl
  rw [hτ] at h₁ h₃
  rw [h₁, connectingAddEquiv_apply, connectingAddEquiv_apply, h₃]
  exact congrArg _ h₂

/-- The natural isomorphism in degree `q + 1` deduced from one in degree `q`. -/
noncomputable def connectingIso : P.ι ⋙ T (q + 1) ≅ P.ι ⋙ T' (q + 1) :=
  NatIso.ofComponents
    (fun X ↦ (connectingAddEquiv hP δ δ' hexact hexact' hsurj hsurj' e X).toAddCommGrpIso)
    fun f ↦ by
      ext x
      exact connectingAddEquiv_naturality hP δ δ' hδ hδ' hexact hexact' hsurj hsurj' e f x

end Step

/-- **Comparison of cohomology theories by dimension shifting.** Let `P` be a property of objects
of an abelian category with enough injectives, stable under passing from `X` to the chosen
injective object `I` under `X` and to the cokernel of `X ⟶ I`. Let `T q` and `T' q` be functors
to abelian groups with connecting maps for the short exact sequences `0 → X₁ → X₂ → X₃ → 0`
with `P X₁`, natural in the short exact sequence, such that `T^q(X₂) → T^q(X₃) → T^{q + 1}(X₁)`
is exact, and whose connecting map is surjective when `X₂` is injective. Then a natural
isomorphism between `T 0` and `T' 0` on the objects satisfying `P` gives natural isomorphisms
between `T q` and `T' q` on these objects for all `q`. -/
theorem nonempty_iso_of_connecting
    (hP : ∀ X, P X → P (Injective.under X) ∧ P (cokernel (Injective.ι X)))
    (T T' : ℕ → C ⥤ AddCommGrpCat.{w})
    (δ : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → ∀ q,
      (T q).obj S.X₃ ⟶ (T (q + 1)).obj S.X₁)
    (δ' : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → ∀ q,
      (T' q).obj S.X₃ ⟶ (T' (q + 1)).obj S.X₁)
    (hδ : ∀ {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
      (p₁ : P S₁.X₁) (p₂ : P S₂.X₁) (q : ℕ),
      δ S₁ h₁ p₁ q ≫ (T (q + 1)).map φ.τ₁ = (T q).map φ.τ₃ ≫ δ S₂ h₂ p₂ q)
    (hδ' : ∀ {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
      (p₁ : P S₁.X₁) (p₂ : P S₂.X₁) (q : ℕ),
      δ' S₁ h₁ p₁ q ≫ (T' (q + 1)).map φ.τ₁ = (T' q).map φ.τ₃ ≫ δ' S₂ h₂ p₂ q)
    (hexact : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ) (x),
      δ S hS h q x = 0 ↔ x ∈ ((T q).map S.g).hom.range)
    (hexact' : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ) (x),
      δ' S hS h q x = 0 ↔ x ∈ ((T' q).map S.g).hom.range)
    (hsurj : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ), Injective S.X₂ →
      Function.Surjective (δ S hS h q))
    (hsurj' : ∀ (S : ShortComplex C) (hS : S.ShortExact) (h : P S.X₁) (q : ℕ), Injective S.X₂ →
      Function.Surjective (δ' S hS h q))
    (e₀ : P.ι ⋙ T 0 ≅ P.ι ⋙ T' 0) (q : ℕ) :
    Nonempty (P.ι ⋙ T q ≅ P.ι ⋙ T' q) := by
  induction q with
  | zero => exact ⟨e₀⟩
  | succ q ih =>
    obtain ⟨e⟩ := ih
    exact ⟨connectingIso hP δ δ' hδ hδ' hexact hexact' hsurj hsurj' e⟩

end CategoryTheory.ObjectProperty
