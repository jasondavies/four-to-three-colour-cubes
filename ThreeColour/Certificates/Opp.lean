module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma opposite_certificate : ∀ d : Colour,
    Certificate (fits (oppositeTarget d)) (oppGroups d) oppBounds := by
  intro d
  fin_cases d <;> decide +kernel

end ThreeColour
