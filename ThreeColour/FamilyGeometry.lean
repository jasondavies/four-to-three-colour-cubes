module

public import ThreeColour.CornerGeometry

@[expose] public section

namespace ThreeColour.Geometry
open scoped BigOperators

/-- The binary corner position obtained by rotating its three outward faces. -/
def rotatedSlot (r : Fin 24) (k : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (∑ f : Fin 3,
    let face := MacMahon.rotations r (MacMahon.exposedFaces k f)
    face.val % 2 * 2 ^ (2 - face.val / 2))

lemma rotatedSlot_bijective : ∀ r, Function.Bijective (rotatedSlot r) := by
  decide +kernel

noncomputable def slotEquiv (r : Fin 24) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (rotatedSlot r) (rotatedSlot_bijective r)

lemma rotatedSlot_frame : ∀ (r : Fin 24) (k : Fin 8), ∃ s : Fin 3, ∀ f,
    MacMahon.rotations r (frame k f) = frame (slotEquiv r k) (f + s) := by
  decide +kernel

end ThreeColour.Geometry
