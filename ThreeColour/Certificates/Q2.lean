module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma q_certificate_2 : ∀ b c : Colour, 2 ≠ b → 2 ≠ c → b ≠ c →
    Certificate (fits (qTarget 2 b c)) (qGroups 2 b c) qBounds := by decide +kernel

end ThreeColour
