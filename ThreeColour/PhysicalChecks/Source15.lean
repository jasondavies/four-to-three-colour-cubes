module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_15 : ∀ t : Target, ∀ k : Slot,
    fits t k 15 = true ↔ ∃ r : Fin 24, FaceFits t 15 k r := by decide +kernel
end ThreeColour
