module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_33 : ∀ t : Target, ∀ k : Slot,
    fits t k 33 = true ↔ ∃ r : Fin 24, FaceFits t 33 k r := by decide +kernel
end ThreeColour
