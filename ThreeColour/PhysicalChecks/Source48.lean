module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_48 : ∀ t : Target, ∀ k : Slot,
    fits t k 48 = true ↔ ∃ r : Fin 24, FaceFits t 48 k r := by decide +kernel
end ThreeColour
