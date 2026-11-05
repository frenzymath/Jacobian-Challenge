import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.RingHom.Flat

/-!
# Faithfully flat descent of flat ring maps

Flatness of a ring map can be checked after a faithfully flat scalar extension.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RingHom

/-- Flatness of ring maps codescends along faithfully flat ring maps. -/
lemma Flat.codescendsAlong_faithfullyFlat : CodescendsAlong Flat FaithfullyFlat := by
  refine .mk _ Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [flat_algebraMap_iff] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S

end RingHom
