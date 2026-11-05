import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Injective local isomorphisms of schemes

An injective local isomorphism is an open immersion: it is open on points and
induces isomorphisms on every stalk.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry

lemma IsOpenImmersion.of_isLocalIso_of_injective {sourceScheme targetScheme : Scheme.{schemeUniverse}} (map : sourceScheme ⟶ targetScheme)
    [IsLocalIso map] (hg : Function.Injective map.base) : IsOpenImmersion map := by
  have hle : @IsLocalIso ≤ @UniversallyOpen := IsLocalIso.le_of_isZariskiLocalAtSource _
  have : UniversallyOpen map := hle _ _ map ‹_›
  have hopen : IsOpenMap map.base := map.isOpenMap
  have : ∀ point, IsIso (map.stalkMap point) := by
    intro point
    obtain ⟨openSubset, hxU, hU⟩ := IsLocalIso.exists_isOpenImmersion (f := map) point
    have hx : point = openSubset.ι ⟨point, hxU⟩ := rfl
    have := Scheme.Hom.stalkMap_comp openSubset.ι map ⟨point, hxU⟩
    rw [hx]
    exact IsIso.of_isIso_fac_right this.symm
  exact IsOpenImmersion.of_isIso_stalkMap map
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap map.continuous hg hopen)

end AlgebraicGeometry
