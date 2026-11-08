module

public import ThreeColour.RawChecks.Base

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma raw_check_60 : RawCheck 60 := by
  intro k
  fin_cases k <;> decide +kernel
end ThreeColour
