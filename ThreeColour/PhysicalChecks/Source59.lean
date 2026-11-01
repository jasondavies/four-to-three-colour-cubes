module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_59 : ∀ t : Target, ∀ k : Slot,
    fits t k 59 = true ↔ ∃ r : Fin 24, FaceFits t 59 k r := by decide +kernel
end ThreeColour
