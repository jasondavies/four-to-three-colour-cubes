module

public import ThreeColour.PhysicalDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

/-- Distinct source indices represent distinct proper-rotation varieties.
The cases stay small enough for replay by the independent kernels. -/
theorem source_catalogue_unique (i j : Source) (r : Fin 24)
    (h : ∀ f, sourceFaces i (MacMahon.rotations r f) = sourceFaces j f) : i = j := by
  revert j r
  fin_cases i <;> decide +kernel
end ThreeColour
