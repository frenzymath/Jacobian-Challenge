import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Stalks and skyscraper modules

The stalk of a module sheaf is a module over the local ring. Morphisms to a
skyscraper module correspond to linear maps out of that stalk. This adjunction
is compatible with pushforward of skyscraper modules.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}} (point : scheme) (moduleType : Type u) [AddCommGroup moduleType] [Module (scheme.presheaf.stalk point) moduleType]

/-- Sections of the skyscraper module, supported at `point`. -/
def SkyscraperSections (targetOpen : scheme.Opens) : Type u :=
  PLift (point ∈ targetOpen) → moduleType

namespace SkyscraperSections

variable {point moduleType} {targetOpen : scheme.Opens}

instance : AddCommGroup (SkyscraperSections point moduleType targetOpen) :=
  inferInstanceAs (AddCommGroup (PLift (point ∈ targetOpen) → moduleType))

omit [AddCommGroup moduleType] [Module (scheme.presheaf.stalk point) moduleType] in
@[ext]
lemma ext {sectionValue otherSection : SkyscraperSections point moduleType targetOpen} (compatibility : ∀ membership : point ∈ targetOpen, sectionValue ⟨membership⟩ = otherSection ⟨membership⟩) : sectionValue = otherSection :=
  funext fun membership ↦ compatibility membership.down

omit [Module (scheme.presheaf.stalk point) moduleType] in
@[simp] lemma add_apply (sectionValue otherSection : SkyscraperSections point moduleType targetOpen) (membership : point ∈ targetOpen) :
    (sectionValue + otherSection) ⟨membership⟩ = sectionValue ⟨membership⟩ + otherSection ⟨membership⟩ := rfl

omit [Module (scheme.presheaf.stalk point) moduleType] in
@[simp] lemma zero_apply (membership : point ∈ targetOpen) : (0 : SkyscraperSections point moduleType targetOpen) ⟨membership⟩ = 0 := rfl

instance : SMul Γ(scheme, targetOpen) (SkyscraperSections point moduleType targetOpen) where
  smul leftScalar sectionValue membership := scheme.presheaf.germ targetOpen point membership.down leftScalar • sectionValue membership

@[simp] lemma smul_apply (leftScalar : Γ(scheme, targetOpen)) (sectionValue : SkyscraperSections point moduleType targetOpen) (membership : point ∈ targetOpen) :
    (leftScalar • sectionValue) ⟨membership⟩ = scheme.presheaf.germ targetOpen point membership leftScalar • sectionValue ⟨membership⟩ := rfl

instance : Module Γ(scheme, targetOpen) (SkyscraperSections point moduleType targetOpen) where
  one_smul sectionValue := by ext; simp
  mul_smul leftScalar rightScalar sectionValue := by ext; simp [mul_smul]
  smul_zero leftScalar := by ext; simp
  smul_add leftScalar sectionValue otherSection := by ext; simp
  add_smul leftScalar rightScalar sectionValue := by ext; simp [add_smul]
  zero_smul sectionValue := by ext; simp

end SkyscraperSections

/-- The abelian presheaf underlying the skyscraper module. -/
def skyscraperPresheafAb : scheme.Opensᵒᵖ ⥤ Ab.{u} where
  obj targetOpen := AddCommGrpCat.of (SkyscraperSections point moduleType targetOpen.unop)
  map inclusion := AddCommGrpCat.ofHom
    { toFun := fun sectionValue membership ↦ sectionValue ⟨inclusion.unop.le membership.down⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

instance (targetOpen : scheme.Opensᵒᵖ) :
    Module (scheme.ringCatSheaf.obj.obj targetOpen) ((skyscraperPresheafAb point moduleType).obj targetOpen) :=
  inferInstanceAs (Module Γ(scheme, targetOpen.unop) (SkyscraperSections point moduleType targetOpen.unop))

omit [Module (scheme.presheaf.stalk point) moduleType] in
lemma skyscraperPresheafAb_map_apply {targetOpen targetOpen' : scheme.Opensᵒᵖ} (inclusion : targetOpen ⟶ targetOpen')
    (sectionValue : SkyscraperSections point moduleType targetOpen.unop) (membership : point ∈ targetOpen'.unop) :
    (skyscraperPresheafAb point moduleType).map inclusion sectionValue ⟨membership⟩ = sectionValue ⟨inclusion.unop.le membership⟩ :=
  rfl

lemma skyscraperPresheafAb_map_smul {targetOpen targetOpen' : scheme.Opensᵒᵖ} (inclusion : targetOpen ⟶ targetOpen')
    (leftScalar : scheme.ringCatSheaf.obj.obj targetOpen) (sectionValue : (skyscraperPresheafAb point moduleType).obj targetOpen) :
    (skyscraperPresheafAb point moduleType).map inclusion (leftScalar • sectionValue) =
      scheme.ringCatSheaf.obj.map inclusion leftScalar • (skyscraperPresheafAb point moduleType).map inclusion sectionValue := by
  refine SkyscraperSections.ext fun membership ↦ ?_
  exact congrArg (· • (sectionValue ⟨inclusion.unop.le membership⟩ : moduleType))
    (TopCat.Presheaf.germ_res_apply scheme.presheaf inclusion.unop point membership leftScalar).symm

omit [Module (scheme.presheaf.stalk point) moduleType] in
lemma isSheaf_skyscraperPresheafAb :
    Presheaf.IsSheaf (Opens.grothendieckTopology scheme)
      (skyscraperPresheafAb point moduleType) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := scheme.carrier)
    (skyscraperPresheafAb point moduleType)).mpr
  intro indices cover sections compatible
  choose index index_mem using fun membership : PLift (point ∈ iSup cover) ↦
    Opens.mem_iSup.mp membership.down
  let glued : SkyscraperSections point moduleType (iSup cover) :=
    fun membership ↦ sections (index membership) ⟨index_mem membership⟩
  refine ⟨glued, ?_, ?_⟩
  · intro coverIndex
    funext membership
    exact congrFun (compatible
      (index ⟨(Opens.leSupr cover coverIndex).le membership.down⟩) coverIndex)
      ⟨⟨index_mem ⟨(Opens.leSupr cover coverIndex).le membership.down⟩, membership.down⟩⟩
  · intro other other_restrict
    funext membership
    exact congrFun (other_restrict (index membership)) ⟨index_mem membership⟩

/-- The skyscraper module, with scalars acting through the germ map. -/
def skyscraper : scheme.Modules where
  val := PresheafOfModules.ofPresheaf (skyscraperPresheafAb point moduleType)
    fun _ _ inclusion leftScalar sectionValue ↦ skyscraperPresheafAb_map_smul point moduleType inclusion leftScalar sectionValue
  isSheaf := isSheaf_skyscraperPresheafAb point moduleType

section Stalk

variable {scheme : Scheme.{u}}

instance (moduleSheaf : scheme.Modules) (point : scheme) : Module (scheme.presheaf.stalk point) (moduleSheaf.presheaf.stalk point) :=
  inferInstanceAs (Module (scheme.presheaf.stalk point) (TopCat.Presheaf.stalk (C := Ab.{u}) (X := scheme)
    (moduleSheaf.val : _root_.PresheafOfModules (scheme.presheaf ⋙ forget₂ _ _)).presheaf point))

lemma germ_smul (moduleSheaf : scheme.Modules) {sourceOpen : scheme.Opens} (point : scheme) (membership : point ∈ sourceOpen) (scalar : Γ(scheme, sourceOpen))
    (element : Γ(moduleSheaf, sourceOpen)) :
    moduleSheaf.presheaf.germ sourceOpen point membership (scalar • element) = scheme.presheaf.germ sourceOpen point membership scalar • moduleSheaf.presheaf.germ sourceOpen point membership element :=
  PresheafOfModules.germ_smul (R := scheme.presheaf) moduleSheaf.val point sourceOpen membership scalar element

def stalkLinearMapMk {moduleSheaf : scheme.Modules} {point : scheme} {targetType : Type*} [AddCommGroup targetType]
    [Module (scheme.presheaf.stalk point) targetType] (linearMap : moduleSheaf.presheaf.stalk point →+ targetType)
    (compatibility : ∀ (sourceOpen : scheme.Opens) (membership : point ∈ sourceOpen) (scalar : Γ(scheme, sourceOpen)) (element : Γ(moduleSheaf, sourceOpen)),
      linearMap (moduleSheaf.presheaf.germ sourceOpen point membership (scalar • element)) =
        scheme.presheaf.germ sourceOpen point membership scalar • linearMap (moduleSheaf.presheaf.germ sourceOpen point membership element)) :
    moduleSheaf.presheaf.stalk point →ₗ[scheme.presheaf.stalk point] targetType where
  __ := linearMap
  map_smul' scalar element := by
    obtain ⟨sourceOpen, sourceMembership, scalar, rfl⟩ := scheme.presheaf.exists_germ_eq scalar
    obtain ⟨targetOpen, targetMembership, element, rfl⟩ := moduleSheaf.presheaf.exists_germ_eq element
    have membership : point ∈ sourceOpen ⊓ targetOpen := ⟨sourceMembership, targetMembership⟩
    rw [← scheme.presheaf.germ_res_apply (homOfLE inf_le_left : sourceOpen ⊓ targetOpen ⟶ sourceOpen) point membership scalar,
      ← moduleSheaf.presheaf.germ_res_apply (homOfLE inf_le_right : sourceOpen ⊓ targetOpen ⟶ targetOpen) point membership element, ← germ_smul]
    exact compatibility _ membership _ _

@[simp]
lemma stalkLinearMapMk_apply {moduleSheaf : scheme.Modules} {point : scheme} {targetType : Type*} [AddCommGroup targetType]
    [Module (scheme.presheaf.stalk point) targetType] (linearMap : moduleSheaf.presheaf.stalk point →+ targetType) (compatibility) (element : moduleSheaf.presheaf.stalk point) :
    stalkLinearMapMk linearMap compatibility element = linearMap element :=
  rfl

/-- The linear map of stalks induced by a module-sheaf morphism. -/
def Hom.stalkLinearMap {moduleSheaf targetType : scheme.Modules} (morphism : moduleSheaf ⟶ targetType) (point : scheme) :
    moduleSheaf.presheaf.stalk point →ₗ[scheme.presheaf.stalk point] targetType.presheaf.stalk point :=
  stalkLinearMapMk
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} point).map morphism.mapPresheaf))
    fun sourceOpen membership scalar element ↦ by
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rw [mapPresheaf_app, Hom.app_smul, germ_smul]

lemma Hom.stalkLinearMap_apply {moduleSheaf targetType : scheme.Modules} (morphism : moduleSheaf ⟶ targetType) (point : scheme) (element : moduleSheaf.presheaf.stalk point) :
    morphism.stalkLinearMap point element = (TopCat.Presheaf.stalkFunctor Ab.{u} point).map morphism.mapPresheaf element :=
  rfl

@[simp]
lemma Hom.stalkLinearMap_germ {moduleSheaf targetType : scheme.Modules} (morphism : moduleSheaf ⟶ targetType) {sourceOpen : scheme.Opens} (point : scheme) (membership : point ∈ sourceOpen)
    (element : Γ(moduleSheaf, sourceOpen)) :
    morphism.stalkLinearMap point (moduleSheaf.presheaf.germ sourceOpen point membership element) = targetType.presheaf.germ sourceOpen point membership (morphism.app sourceOpen element) := by
  rw [Hom.stalkLinearMap_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply, mapPresheaf_app]

end Stalk

section SkyscraperHom

variable {scheme : Scheme.{u}} (point : scheme) (moduleType : Type u) [AddCommGroup moduleType] [Module (scheme.presheaf.stalk point) moduleType]

def skyscraperStalkEvalAddHom : (skyscraper point moduleType).presheaf.stalk point →+ moduleType :=
  ConcreteCategory.hom (Limits.colimit.desc _
    { pt := AddCommGrpCat.of moduleType
      ι :=
        { app sourceOpen := AddCommGrpCat.ofHom
            { toFun sectionValue := (show SkyscraperSections point moduleType sourceOpen.unop.1 from sectionValue) ⟨sourceOpen.unop.2⟩
              map_zero' := rfl
              map_add' _ _ := rfl }
          naturality _ _ _ := rfl } })

lemma skyscraperStalkEvalAddHom_germ {sourceOpen : scheme.Opens} (membership : point ∈ sourceOpen) (sectionValue : Γ(skyscraper point moduleType, sourceOpen)) :
    skyscraperStalkEvalAddHom point moduleType ((skyscraper point moduleType).presheaf.germ sourceOpen point membership sectionValue) =
      sectionValue ⟨membership⟩ := by
  rw [skyscraperStalkEvalAddHom, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

def skyscraperStalkEval : (skyscraper point moduleType).presheaf.stalk point →ₗ[scheme.presheaf.stalk point] moduleType :=
  stalkLinearMapMk (skyscraperStalkEvalAddHom point moduleType) fun sourceOpen membership scalar sectionValue ↦ by
    rw [skyscraperStalkEvalAddHom_germ, skyscraperStalkEvalAddHom_germ]
    rfl

@[simp]
lemma skyscraperStalkEval_germ {sourceOpen : scheme.Opens} (membership : point ∈ sourceOpen) (sectionValue : Γ(skyscraper point moduleType, sourceOpen)) :
    skyscraperStalkEval point moduleType ((skyscraper point moduleType).presheaf.germ sourceOpen point membership sectionValue) =
      sectionValue ⟨membership⟩ :=
  skyscraperStalkEvalAddHom_germ point moduleType membership sectionValue

variable {point moduleType}

def toSkyscraper {source : scheme.Modules} (linearMap : source.presheaf.stalk point →ₗ[scheme.presheaf.stalk point] moduleType) :
    source ⟶ skyscraper point moduleType :=
  ⟨PresheafOfModules.homMk
    { app targetOpen := AddCommGrpCat.ofHom
        { toFun sectionValue := show SkyscraperSections point moduleType targetOpen.unop from
            fun membership ↦ linearMap (source.presheaf.germ targetOpen.unop point membership.down sectionValue)
          map_zero' := SkyscraperSections.ext fun _ ↦ (congrArg linearMap (map_zero _)).trans (map_zero linearMap)
          map_add' _ _ := SkyscraperSections.ext fun _ ↦
            (congrArg linearMap (map_add _ _ _)).trans (map_add linearMap _ _) }
      naturality targetOpen targetOpen' inclusion := by
        ext sectionValue
        refine SkyscraperSections.ext fun membership ↦ ?_
        exact congrArg linearMap (source.presheaf.germ_res_apply inclusion.unop point membership sectionValue) }
    fun targetOpen scalar sectionValue ↦ by
      refine SkyscraperSections.ext fun membership ↦ ?_
      exact (congrArg linearMap (germ_smul source point membership scalar sectionValue)).trans (linearMap.map_smul _ _)⟩

lemma toSkyscraper_app_apply {source : scheme.Modules} (linearMap : source.presheaf.stalk point →ₗ[scheme.presheaf.stalk point] moduleType)
    {targetOpen : scheme.Opens} (sectionValue : Γ(source, targetOpen)) (membership : point ∈ targetOpen) :
    (toSkyscraper linearMap).app targetOpen sectionValue ⟨membership⟩ =
      linearMap (source.presheaf.germ targetOpen point membership sectionValue) :=
  rfl

lemma comp_toSkyscraper {source target : scheme.Modules} (morphism : source ⟶ target)
    (linearMap : target.presheaf.stalk point →ₗ[scheme.presheaf.stalk point] moduleType) :
    morphism ≫ toSkyscraper linearMap = toSkyscraper (linearMap ∘ₗ morphism.stalkLinearMap point) := by
  refine hom_ext _ _ fun targetOpen ↦ ?_
  ext sectionValue
  refine SkyscraperSections.ext fun membership ↦ ?_
  rw [Hom.comp_app, ConcreteCategory.comp_apply, toSkyscraper_app_apply, toSkyscraper_app_apply,
    LinearMap.comp_apply, Hom.stalkLinearMap_germ]

variable (point moduleType) in
/-- Linear maps out of a stalk correspond to morphisms to the skyscraper module. -/
def skyscraperHomEquiv (source : scheme.Modules) :
    (source.presheaf.stalk point →ₗ[scheme.presheaf.stalk point] moduleType) ≃ (source ⟶ skyscraper point moduleType) where
  toFun := toSkyscraper
  invFun morphism := skyscraperStalkEval point moduleType ∘ₗ morphism.stalkLinearMap point
  left_inv linearMap := by
    ext otherSection
    obtain ⟨sourceOpen, membership, sectionValue, rfl⟩ := source.presheaf.exists_germ_eq otherSection
    rw [LinearMap.comp_apply, Hom.stalkLinearMap_germ, skyscraperStalkEval_germ,
      toSkyscraper_app_apply]
  right_inv morphism := by
    refine hom_ext _ _ fun targetOpen ↦ ?_
    ext sectionValue
    refine SkyscraperSections.ext fun membership ↦ ?_
    rw [toSkyscraper_app_apply, LinearMap.comp_apply, Hom.stalkLinearMap_germ,
      skyscraperStalkEval_germ]

end SkyscraperHom

section Pushforward

variable {scheme sourceScheme : Scheme.{u}} (structureMap : sourceScheme ⟶ scheme) (sourcePoint : sourceScheme) (moduleType : Type u) [AddCommGroup moduleType]
  [Module (sourceScheme.presheaf.stalk sourcePoint) moduleType] [Module (scheme.presheaf.stalk (structureMap sourcePoint)) moduleType]
  [Algebra (scheme.presheaf.stalk (structureMap sourcePoint)) (sourceScheme.presheaf.stalk sourcePoint)]
  [IsScalarTower (scheme.presheaf.stalk (structureMap sourcePoint)) (sourceScheme.presheaf.stalk sourcePoint) moduleType]

include structureMap in
lemma germ_smul_eq_germ_app_smul
    (compatibility : algebraMap (scheme.presheaf.stalk (structureMap sourcePoint)) (sourceScheme.presheaf.stalk sourcePoint) = (structureMap.stalkMap sourcePoint).hom)
    {targetOpen : scheme.Opens} (sourceMembership : structureMap sourcePoint ∈ targetOpen) (scalar : Γ(scheme, targetOpen)) (inclusion : moduleType) :
    scheme.presheaf.germ targetOpen (structureMap sourcePoint) sourceMembership scalar • inclusion = sourceScheme.presheaf.germ (structureMap ⁻¹ᵁ targetOpen) sourcePoint sourceMembership (structureMap.app targetOpen scalar) • inclusion := by
  rw [← Scheme.Hom.germ_stalkMap_apply, ← algebraMap_smul (sourceScheme.presheaf.stalk sourcePoint), compatibility]

/-- Pushforward takes a skyscraper module to the skyscraper at the image point. -/
def pushforwardSkyscraperIso
    (compatibility : algebraMap (scheme.presheaf.stalk (structureMap sourcePoint)) (sourceScheme.presheaf.stalk sourcePoint) = (structureMap.stalkMap sourcePoint).hom) :
    (pushforward structureMap).obj (skyscraper sourcePoint moduleType) ≅ skyscraper (structureMap sourcePoint) moduleType where
  hom := ⟨PresheafOfModules.homMk
    { app targetOpen := AddCommGrpCat.ofHom
        { toFun sectionValue := show SkyscraperSections (structureMap sourcePoint) moduleType targetOpen.unop from
            fun membership ↦ sectionValue ⟨membership.down⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    fun _ scalar _ ↦ SkyscraperSections.ext fun membership ↦
      (germ_smul_eq_germ_app_smul structureMap sourcePoint moduleType compatibility membership scalar _).symm⟩
  inv := ⟨PresheafOfModules.homMk
    { app targetOpen := AddCommGrpCat.ofHom
        { toFun sectionValue := show SkyscraperSections sourcePoint moduleType (structureMap ⁻¹ᵁ targetOpen.unop) from
            fun membership ↦ sectionValue ⟨membership.down⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    fun _ scalar _ ↦ SkyscraperSections.ext fun membership ↦
      germ_smul_eq_germ_app_smul structureMap sourcePoint moduleType compatibility membership scalar _⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end Pushforward

end AlgebraicGeometry.Scheme.Modules
