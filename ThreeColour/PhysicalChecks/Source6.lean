module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_6 : ∀ t : Target, ∀ k : Slot,
    fits t k 6 = true ↔ ∃ r : Fin 24, FaceFits t 6 k r := by decide +kernel
end ThreeColour
