module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_63 : ∀ t : Target, ∀ k : Slot,
    fits t k 63 = true ↔ ∃ r : Fin 24, FaceFits t 63 k r := by decide +kernel
end ThreeColour
