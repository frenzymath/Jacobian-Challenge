import Jacobian.AlgebraicGeometry.Modules.FpqcFullyFaithful

/-!
# Fpqc sheaves of module morphisms

The presheaf of morphisms between pullbacks of two quasi-coherent modules is an fpqc sheaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
lemma isSheafFor_presheafHom_of_mem_fpqcTopology {S : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op S)))
    (hM : (M : S.Modules).IsQuasicoherent) (hN : (N : S.Modules).IsQuasicoherent)
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S) :
    Presieve.IsSheafFor (modulesPseudofunctor.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  have h := bijective_toDescentData_map_of_mem_fpqcTopology
    (fun (i : R.arrows.category) ↦ i.obj.hom)
    (by rwa [Sieve.ofArrows_category', Sieve.generate_sieve]) M N hM hN
  rw [Pseudofunctor.bijective_toDescentData_map_iff] at h
  convert! h
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.mk_surjective X
    obtain rfl : f = Over.homMk g := by ext; simpa using Over.w f
    exact Presieve.ofArrows.mk (ι := R.arrows.category) ⟨Over.mk g, hf⟩
  · rintro _ _ ⟨_, h⟩
    exact h

set_option backward.isDefEq.respectTransparency false in
lemma isSheafFor_presheafHom_of_mem_over {S₀ : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op S₀)))
    (hM : (M : S₀.Modules).IsQuasicoherent) (hN : (N : S₀.Modules).IsQuasicoherent)
    {U : Over S₀} (R : Sieve U) (hR : R ∈ (Scheme.fpqcTopology.over S₀) U) :
    Presieve.IsSheafFor (modulesPseudofunctor.presheafHom M N) R.arrows := by
  obtain ⟨S, a, rfl⟩ := U.mk_surjective
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨R, rfl⟩ := (Sieve.overEquiv (Over.mk a)).symm.surjective R
  rw [OrderIso.apply_symm_apply] at hR
  have h := isSheafFor_presheafHom_of_mem_fpqcTopology
    ((modulesPseudofunctor.map a.op.toLoc).toFunctor.obj M)
    ((modulesPseudofunctor.map a.op.toLoc).toFunctor.obj N)
    (Scheme.Modules.isQuasicoherent_pullback (moduleSheaf := (M : S₀.Modules)) a)
    (Scheme.Modules.isQuasicoherent_pullback (moduleSheaf := (N : S₀.Modules)) a) _ hR
  rw [← Presieve.isSheafFor_iff_of_iso (modulesPseudofunctor.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert! h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    change b.left ≫ 𝟙 _ = _ at fac
    rw [Category.comp_id] at fac
    change R.arrows b.left
    simpa [fac] using R.downward_closed h d.left

/-- For quasi-coherent `M` and `N` on `S`, the presheaf `Hom(- ^* M, - ^* N)` on schemes over `S`
is a sheaf for the fpqc topology. -/
lemma isSheaf_presheafHom {S : Scheme.{u}} (M N : modulesPseudofunctor.obj (.mk (op S)))
    (hM : (M : S.Modules).IsQuasicoherent) (hN : (N : S.Modules).IsQuasicoherent) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (modulesPseudofunctor.presheafHom M N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR
  exact isSheafFor_presheafHom_of_mem_over M N hM hN R hR

end AlgebraicGeometry
