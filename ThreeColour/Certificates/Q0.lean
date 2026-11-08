module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma q_certificate_0 : ∀ b c : Colour, 0 ≠ b → 0 ≠ c → b ≠ c →
    Certificate (fits (qTarget 0 b c)) (qGroups 0 b c) qBounds := by
  intro b c
  fin_cases b <;> fin_cases c <;> decide +kernel

end ThreeColour
