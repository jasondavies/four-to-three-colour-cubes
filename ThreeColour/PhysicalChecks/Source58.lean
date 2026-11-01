module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_58 : ∀ t : Target, ∀ k : Slot,
    fits t k 58 = true ↔ ∃ r : Fin 24, FaceFits t 58 k r := by decide +kernel
end ThreeColour
