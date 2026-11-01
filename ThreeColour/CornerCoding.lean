module

public import ThreeColour.CornerGeometry
public import ThreeColour.Data

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeColour
open ThreeColour.Geometry

/-- Base-four encoding of an ordered triple. -/
def linearCode (t : Fin 3 → Colour) : Fin 64 :=
  Fin.ofNat 64 (16 * (t 0).val + 4 * (t 1).val + (t 2).val)

/-- Canonical code of a cyclic corner type. -/
def cornerCode (t : Fin 3 → Colour) : Fin 64 :=
  min (linearCode t)
    (min (linearCode (fun j => t (j + 1))) (linearCode (fun j => t (j + 2))))

lemma cornerCode_eq_iff : ∀ a b : Fin 3 → Colour,
    cornerCode a = cornerCode b ↔ CyclicEq a b := by
  decide +kernel

end ThreeColour
