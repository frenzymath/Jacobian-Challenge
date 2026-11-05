import Jacobian.CategoryTheory.Abelian.DimensionShifting
import Jacobian.CategoryTheory.Sites.SheafCohomology.ExactSequence
import Jacobian.Topology.Sheaves.CechCriterion
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Čech cohomology and sheaf cohomology

Čech cohomology of an open cover agrees with sheaf cohomology on a class of
sheaves stable under injective dimension shifting, provided short exact
sequences are surjective on sections over the finite intersections. The
comparison is natural in the coefficient sheaf.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

open Presheaf

variable {X : TopCat.{max u v}} {ι : Type v} (U : ι → Opens X)

/-- The Čech complex `Č(U, F)` of an abelian sheaf, as a functor of the sheaf. -/
noncomputable abbrev cechComplexFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⥤
      CochainComplex AddCommGrpCat.{max u v} ℕ :=
  sheafToPresheaf _ _ ⋙ cechComplex U

/-- The Čech cohomology `Ȟ^q(U, F)` of an abelian sheaf, as a functor of the sheaf. -/
noncomputable abbrev cechCohomologyFunctor (q : ℕ) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⥤
      AddCommGrpCat.{max u v} :=
  cechComplexFunctor U ⋙ HomologicalComplex.homologyFunctor _ _ q

variable {U}

/-- A short exact sequence of abelian sheaves which is surjective on the sections over the
finite intersections of the family `U` induces a short exact sequence of Čech complexes. -/
lemma shortExact_cechComplex
    {S : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Function.Surjective (S.g.hom.app (op (⨅ l, U (y l))))) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k ↦ ?_
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    exact exists_cechComplex_map_f_eq U S.f.hom S.g.hom (exists_app_f_eq hS) k
  · exact (AddCommGrpCat.mono_iff_injective _).2
      (cechComplex_map_f_injective U _ (injective_app_f hS) k)
  · refine (AddCommGrpCat.epi_iff_surjective _).2 fun c ↦ ?_
    choose a ha using fun y ↦ hg k y (c y)
    exact ⟨a, funext fun y ↦ (cechComplex_map_f_apply U S.g.hom k a y).trans (ha y)⟩

variable (U)

/-- The connecting homomorphism `Ȟ^q(U, S.X₃) → Ȟ^{q+1}(U, S.X₁)` of a short exact sequence
of abelian sheaves which is surjective on the sections over the finite intersections of `U`. -/
noncomputable abbrev cechδ
    {S : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Function.Surjective (S.g.hom.app (op (⨅ l, U (y l)))))
    (q : ℕ) : (cechCohomologyFunctor U q).obj S.X₃ ⟶ (cechCohomologyFunctor U (q + 1)).obj S.X₁ :=
  (shortExact_cechComplex hS hg).δ q (q + 1) rfl

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The connecting homomorphism of Čech cohomology is natural in the short exact sequence. -/
lemma cechδ_naturality
    {S₁ S₂ : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})}
    (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (hg₁ : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (S₁.g.hom.app (op (⨅ l, U (y l)))))
    (hg₂ : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (S₂.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ) :
    cechδ U h₁ hg₁ q ≫ (cechCohomologyFunctor U (q + 1)).map φ.τ₁ =
      (cechCohomologyFunctor U q).map φ.τ₃ ≫ cechδ U h₂ hg₂ q :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cechComplexFunctor U).mapShortComplex.map φ)
    (shortExact_cechComplex h₁ hg₁) (shortExact_cechComplex h₂ hg₂) q (q + 1) rfl

/-- The long exact sequence of Čech cohomology is exact at `Ȟ^q(U, S.X₃)`. -/
lemma cechδ_eq_zero_iff
    {S : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Function.Surjective (S.g.hom.app (op (⨅ l, U (y l)))))
    (q : ℕ) (x : (cechCohomologyFunctor U q).obj S.X₃) :
    cechδ U hS hg q x = 0 ↔ x ∈ ((cechCohomologyFunctor U q).map S.g).hom.range := by
  have h := (shortExact_cechComplex hS hg).homology_exact₃ q (q + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h x

/-- The connecting homomorphism `Ȟ^q(U, S.X₃) → Ȟ^{q+1}(U, S.X₁)` is surjective when `S.X₂` is
injective, the Čech complex of an injective sheaf being exact in positive degrees. -/
lemma cechδ_surjective
    {S : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})}
    (hS : S.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Function.Surjective (S.g.hom.app (op (⨅ l, U (y l)))))
    (q : ℕ) [Injective S.X₂] : Function.Surjective (cechδ U hS hg q) := by
  have h := (shortExact_cechComplex hS hg).homology_exact₁ q (q + 1) rfl
  have hz : IsZero ((S.map (cechComplexFunctor U)).X₂.homology (q + 1)) :=
    (exactAt_cechComplex_of_injective U S.X₂ q).isZero_homology
  have := h.epi_f (hz.eq_of_tgt _ _)
  exact (AddCommGrpCat.epi_iff_surjective _).1 this

/-- The Čech `0`-cochain given by the restrictions of a global section. -/
noncomputable def toCechCochainZero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    F.obj.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj F).X 0 :=
  AddCommGrpCat.ofHom
    { toFun s _ := F.obj.map (homOfLE le_top).op s
      map_zero' := funext fun _ ↦ map_zero _
      map_add' _ _ := funext fun _ ↦ map_add _ _ _ }

@[simp]
lemma toCechCochainZero_apply
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (s : F.obj.obj (op ⊤)) (z : Fin 1 → ι) :
    toCechCochainZero U F s z = F.obj.map (homOfLE le_top).op s :=
  rfl

/-- The restrictions of a global section form a Čech `0`-cocycle. -/
lemma toCechCochainZero_d
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    toCechCochainZero U F ≫ ((cechComplexFunctor U).obj F).d 0 1 = 0 := by
  ext s
  exact cechComplex_d_zero_restrict U F.obj s fun _ ↦ le_top

/-- The map from global sections to the zeroth Čech cohomology, sending a section to the class
of the cocycle of its restrictions. -/
noncomputable def toCechCohomologyZero :
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤) ⟶ cechCohomologyFunctor U 0 where
  app F := ((cechComplexFunctor U).obj F).liftCycles (toCechCochainZero U F) 1 (by simp)
      (toCechCochainZero_d U F) ≫ ((cechComplexFunctor U).obj F).homologyπ 0
  naturality F G φ := by
    have h : toCechCochainZero U F ≫ ((cechComplex U).map ((sheafToPresheaf _ _).map φ)).f 0 =
        ((evaluation _ _).obj (op ⊤)).map ((sheafToPresheaf _ _).map φ) ≫
          toCechCochainZero U G := by
      ext s
      funext z
      exact NatTrans.naturality_apply φ.hom (homOfLE (le_top (a := ⨅ l, U (z l)))).op s
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Category.assoc,
      HomologicalComplex.homologyπ_naturality, HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
      HomologicalComplex.comp_liftCycles_assoc]
    simp only [h]

variable {U}

/-- The members of an open covering are the intersections indexed by the `1`-tuples. -/
lemma top_le_iSup_iInf_fin_one (hU : iSup U = ⊤) :
    ⊤ ≤ iSup fun z : Fin 1 → ι ↦ ⨅ l, U (z l) := by
  rw [← hU]
  exact iSup_le fun i ↦ le_iSup_of_le (fun _ ↦ i) (le_iInf fun _ ↦ le_rfl)

/-- For an open covering, the zeroth Čech cohomology of a sheaf is its group of global sections:
the cocycles of degree `0` are the compatible families of sections. -/
lemma isIso_toCechCohomologyZero_app (hU : iSup U = ⊤)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    IsIso ((toCechCohomologyZero U).app F) := by
  set K := (cechComplexFunctor U).obj F
  haveI : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by simp)
  suffices IsIso (K.liftCycles (toCechCochainZero U F) 1 (by simp) (toCechCochainZero_d U F)) from
    IsIso.comp_isIso
  rw [ConcreteCategory.isIso_iff_bijective]
  have hi : Function.Injective (K.iCycles 0) := (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hli (s : F.obj.obj (op ⊤)) :
      K.iCycles 0 (K.liftCycles (toCechCochainZero U F) 1 (by simp) (toCechCochainZero_d U F) s) =
        toCechCochainZero U F s :=
    ConcreteCategory.congr_hom (K.liftCycles_i _ _ _ _) s
  constructor
  · intro s t hst
    have h := congrArg (K.iCycles 0) hst
    rw [hli, hli] at h
    exact eq_of_locally_eq' F (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) ⊤ (fun _ ↦ homOfLE le_top)
      (top_le_iSup_iInf_fin_one hU) s t fun z ↦ congr_fun h z
  · intro c
    have hd : K.d 0 1 (K.iCycles 0 c) = 0 := ConcreteCategory.congr_hom (K.iCycles_d 0 1) c
    obtain ⟨σ, hσ, -⟩ := existsUnique_gluing' F (fun z : Fin 1 → ι ↦ ⨅ l, U (z l)) ⊤
      (fun _ ↦ homOfLE le_top) (top_le_iSup_iInf_fin_one hU) _
      (map_inf_eq_of_cechComplex_d_zero U _ _ hd)
    exact ⟨σ, hi ((hli σ).trans (funext hσ))⟩

variable (U) in
/-- **Čech cohomology in degree `0`.** For an open covering `U`, the zeroth Čech cohomology of
an abelian sheaf is its group of global sections. -/
noncomputable def cechCohomologyZeroIso (hU : iSup U = ⊤) :
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤) ≅ cechCohomologyFunctor U 0 :=
  haveI (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
      IsIso ((toCechCohomologyZero U).app F) :=
    isIso_toCechCohomologyZero_app hU F
  haveI := NatIso.isIso_of_isIso_app (toCechCohomologyZero U)
  asIso (toCechCohomologyZero U)

variable (U)

/-- **Čech cohomology computes sheaf cohomology on acyclic sheaves.** Let `U` be an open
covering of `X` and `P` a property of abelian sheaves, stable under passing from `F` to the
chosen injective sheaf `I` under `F` and to the cokernel of `F ⟶ I`, such that every short
exact sequence `0 → F → G → H → 0` with `P F` is surjective on the sections over the finite
intersections of the members of `U`. Then `Ȟ^q(U, F) ≅ H^q(X, F)`, naturally in the sheaves
`F` with `P F`. -/
theorem nonempty_cechCohomologyFunctor_iso_functorH (hU : iSup U = ⊤)
    (P : ObjectProperty
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))
    (hP : ∀ F, P F → P (Injective.under F) ∧ P (cokernel (Injective.ι F)))
    (hg : ∀ S : ShortComplex
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}), S.ShortExact →
        P S.X₁ → ∀ (k : ℕ) (y : Fin (k + 1) → ι),
        Function.Surjective (S.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ) :
    Nonempty (P.ι ⋙ cechCohomologyFunctor U q ≅
      P.ι ⋙ CategoryTheory.Sheaf.functorH.{max u v} (Opens.grothendieckTopology X) q) := by
  refine P.nonempty_iso_of_connecting hP (cechCohomologyFunctor U)
    (CategoryTheory.Sheaf.functorH.{max u v} (Opens.grothendieckTopology X))
    (fun S hS h q ↦ cechδ U hS (hg S hS h) q)
    (fun S hS _ q ↦ CategoryTheory.Sheaf.functorHδ hS q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ q
  · intro S₁ S₂ φ h₁ h₂ p₁ p₂ q
    exact cechδ_naturality U φ h₁ h₂ _ _ q
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    exact CategoryTheory.Sheaf.functorHδ_naturality.{max u v} h₁ q h₂ φ
  · intro S hS _ q x
    exact cechδ_eq_zero_iff U hS _ q x
  · intro S hS _ q x
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{max u v} hS q x
  · intro S hS _ q _
    exact cechδ_surjective U hS _ q
  · intro S hS _ q _
    exact CategoryTheory.Sheaf.functorHδ_surjective.{max u v} hS q
  · exact Functor.isoWhiskerLeft P.ι ((cechCohomologyZeroIso U hU).symm ≪≫
      (CategoryTheory.Sheaf.functorHZeroIso.{max u v} _ isTerminalTop).symm)

end TopCat.Sheaf
