module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma q_certificate_1 : ∀ b c : Colour, 1 ≠ b → 1 ≠ c → b ≠ c →
    Certificate (fits (qTarget 1 b c)) (qGroups 1 b c) qBounds := by
  intro b c
  fin_cases b <;> fin_cases c <;> decide +kernel

end ThreeColour
