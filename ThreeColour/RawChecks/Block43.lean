module

public import ThreeColour.RawChecks.Base

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma raw_check_43 : RawCheck 43 := by
  intro k
  fin_cases k <;> decide +kernel
end ThreeColour
