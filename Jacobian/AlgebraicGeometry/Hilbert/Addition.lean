import Jacobian.AlgebraicGeometry.Hilbert.Points
import Jacobian.AlgebraicGeometry.Hilbert.RelativeDivisorOperations

/-!
# The finite flat addition morphism on Hilbert schemes

For a smooth separated relative curve, adding the graph of a section gives a
finite flat map `H_d × X → H_(d+1)` of degree `d + 1`. Colon subtraction identifies
the source with the universal divisor over `H_(d+1)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped nonZeroDivisors

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Adding a section to a degree-`d` family is finite flat of degree `d + 1`. -/
theorem exists_addition_hilbertPresheaf [IsSeparated f] [SmoothOfRelativeDimension 1 f] (d : ℕ)
    (H H' : Over S) (e : (hilbertPresheaf f d).RepresentableBy H)
    (e' : (hilbertPresheaf f (d + 1)).RepresentableBy H') :
    ∃ a : pullback H.hom f ⟶ H'.left, a ≫ H'.hom = pullback.snd H.hom f ≫ f ∧
      IsFinite a ∧ Flat a ∧ LocallyOfFinitePresentation a ∧ (∀ t, a.finrank t = d + 1) ∧
      ∀ (T : Over S) (z : T ⟶ H) (x : T.left ⟶ X) (hx : x ≫ f = T.hom) (t : T ⟶ H'),
        t.left = pullback.lift z.left x (by rw [Over.w z, hx]) ≫ a →
          (e'.homEquiv t).1 = (e.homEquiv z).1 *
            (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker := by
  let P : Over S := Over.mk (pullback.snd H.hom f ≫ f)
  let z₀ : P ⟶ H := Over.homMk (pullback.fst H.hom f) (by simp [P, pullback.condition])
  let x₀ : P.left ⟶ X := pullback.snd H.hom f
  have hx₀ : x₀ ≫ f = P.hom := rfl
  have hΓ₀ := isHilbertSubscheme_ker_lift_id f (test := P) x₀ hx₀
  let u : (hilbertPresheaf f (d + 1)).obj (op P) :=
    ⟨_, IsHilbertSubscheme.mul f (e.homEquiv z₀).2 hΓ₀⟩
  let aP := e'.homEquiv.symm u
  have haP : e'.homEquiv aP = u := Equiv.apply_symm_apply _ _
  have hnat (T : Over S) (z : T ⟶ H) (x : T.left ⟶ X) (hx : x ≫ f = T.hom) (t : T ⟶ H')
      (ht : t.left = pullback.lift z.left x (by rw [Over.w z, hx]) ≫ aP.left) :
      (e'.homEquiv t).1 = (e.homEquiv z).1 *
        (pullback.lift x (𝟙 T.left) (by simp [hx]) : T.left ⟶ pullback f T.hom).ker := by
    let w : T ⟶ P := Over.homMk (pullback.lift z.left x (by rw [Over.w z, hx])) (by simp [P, hx])
    obtain rfl : t = w ≫ aP := by
      ext1
      exact ht
    have hz : z = w ≫ z₀ := by
      ext1
      simp [w, z₀]
    rw [hilbertPresheaf_homEquiv_comp_val, haP]
    dsimp only [u]
    rw [Scheme.IdealSheafData.comap_mul,
      ← hilbertPresheaf_homEquiv_comp_val, ← hz,
      ker_lift_id_comap_baseChangeMap f w x₀ hx₀ x hx (by simp [w, x₀])]
  have hDu := (e'.homEquiv (𝟙 H')).2
  have hrank := hDu.2.2.2
  set Du := (e'.homEquiv (𝟙 H')).1
  have hcomap {T : Over S} (y : T ⟶ H') :
      (e'.homEquiv y).1 = Du.comap (baseChangeMap f y) := by
    simpa using hilbertPresheaf_homEquiv_comp_val f e' y (𝟙 H')
  let g : P.left ⟶ pullback f H'.hom := pullback.lift x₀ aP.left (by rw [hx₀, Over.w aP])
  have hg : (pullback.lift x₀ (𝟙 P.left) (by rw [hx₀, Category.id_comp]) :
      P.left ⟶ pullback f P.hom) ≫ baseChangeMap f aP = g := by
    apply pullback.hom_ext
    · simp [g]
    · simp only [g, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact Category.id_comp _
  have hle : Du.subschemeι.ker ≤ g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hg, ← Scheme.IdealSheafData.map_ker,
      Scheme.IdealSheafData.le_map_iff_comap_le, ← hcomap, haP]
    exact fun U ↦ Ideal.mul_le_right
  let φ : P.left ⟶ Du.subscheme := IsClosedImmersion.lift Du.subschemeι g hle
  have hφ : φ ≫ Du.subschemeι = g := IsClosedImmersion.lift_fac _ _ _
  have hφq : φ ≫ Du.subschemeι ≫ pullback.snd f H'.hom = aP.left := by
    rw [← Category.assoc, hφ, pullback.lift_snd]
  let T₁ : Over S := Over.mk (Du.subschemeι ≫ pullback.snd f H'.hom ≫ H'.hom)
  let y : T₁ ⟶ H' := Over.homMk (Du.subschemeι ≫ pullback.snd f H'.hom)
  let x₁ : T₁.left ⟶ X := Du.subschemeι ≫ pullback.fst f H'.hom
  have hx₁ : x₁ ≫ f = T₁.hom := by simp [x₁, T₁, pullback.condition]
  have hy : (pullback.lift x₁ (𝟙 T₁.left) (by rw [hx₁, Category.id_comp]) :
      T₁.left ⟶ pullback f T₁.hom) ≫ baseChangeMap f y = Du.subschemeι := by
    apply pullback.hom_ext
    · simp [x₁, y]
    · simp only [y, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Over.homMk_left]
      exact Category.id_comp _
  have hDT : (e'.homEquiv y).1 ≤ (pullback.lift x₁ (𝟙 T₁.left)
      (by rw [hx₁, Category.id_comp]) : T₁.left ⟶ pullback f T₁.hom).ker := by
    rw [hcomap, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, hy,
      Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨D', hD', hDeq⟩ := IsHilbertSubscheme.exists_eq_mul (d₁ := d) (d₂ := 1)
    (e'.homEquiv y).2 (isHilbertSubscheme_ker_lift_id f (test := T₁) x₁ hx₁) hDT
  let z₁ : T₁ ⟶ H := e.homEquiv.symm ⟨D', hD'⟩
  have hz₁ : (e.homEquiv z₁).1 = D' := by rw [Equiv.apply_symm_apply]
  let ψ : Du.subscheme ⟶ P.left := pullback.lift z₁.left x₁ (by rw [Over.w z₁, hx₁])
  have hψa : ψ ≫ aP.left = Du.subschemeι ≫ pullback.snd f H'.hom := by
    have h := hnat T₁ z₁ x₁ hx₁ (Over.homMk (ψ ≫ aP.left) (by
      rw [Category.assoc, Over.w aP]
      simpa [P, ψ] using hx₁))
      (by simp [ψ])
    rw [hz₁, ← hDeq] at h
    exact congr_arg CommaMorphism.left (e'.homEquiv.injective (Subtype.ext h))
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono Du.subschemeι, Category.assoc, hφ, Category.id_comp]
    apply pullback.hom_ext
    · simp [g, ψ, x₀, x₁]
    · simpa [g] using hψa
  have hφx₁ : φ ≫ x₁ = x₀ := by
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    let w : P ⟶ T₁ := Over.homMk φ (by
      rw [← Over.w aP, ← hφq]
      rfl)
    have hwy : w ≫ y = aP := by
      ext1
      exact hφq
    have hwz : w ≫ z₁ = z₀ := by
      refine e.homEquiv.injective (Subtype.ext ?_)
      refine Scheme.IdealSheafData.IsInvertible.mul_right_cancel hΓ₀.isInvertible ?_
      rw [hilbertPresheaf_homEquiv_comp_val, hz₁]
      conv_lhs => rw [← ker_lift_id_comap_baseChangeMap f w x₁ hx₁ x₀ hx₀ hφx₁.symm,
        ← Scheme.IdealSheafData.comap_mul, ← hDeq, ← hilbertPresheaf_homEquiv_comp_val, hwy, haP]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact congr_arg CommaMorphism.left hwz
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact hφx₁
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have : IsFinite (Du.subschemeι ≫ pullback.snd f H'.hom) := hDu.1
  have : Flat (Du.subschemeι ≫ pullback.snd f H'.hom) := hDu.2.1
  have : LocallyOfFinitePresentation (Du.subschemeι ≫ pullback.snd f H'.hom) := hDu.2.2.1
  have ha : aP.left = φ ≫ Du.subschemeι ≫ pullback.snd f H'.hom := hφq.symm
  refine ⟨aP.left, Over.w aP, ?_, ?_, ?_, fun t ↦ ?_, hnat⟩
  · rw [ha]
    infer_instance
  · rw [ha]
    infer_instance
  · rw [ha]
    infer_instance
  · rw [ha, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrank t

end AlgebraicGeometry
