module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma q_certificate_3 : ∀ b c : Colour, 3 ≠ b → 3 ≠ c → b ≠ c →
    Certificate (fits (qTarget 3 b c)) (qGroups 3 b c) qBounds := by
  intro b c
  fin_cases b <;> fin_cases c <;> decide +kernel

end ThreeColour
