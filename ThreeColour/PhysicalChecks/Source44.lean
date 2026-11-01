module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
theorem fits_physical_44 : ∀ t : Target, ∀ k : Slot,
    fits t k 44 = true ↔ ∃ r : Fin 24, FaceFits t 44 k r := by decide +kernel
end ThreeColour
