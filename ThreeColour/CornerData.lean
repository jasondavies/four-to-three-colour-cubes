module

public import ThreeColour.CornerCoding

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeColour
open ColourCubes.Geometry

/-- Each stored source corner set is the set read from its six face colours. -/
lemma source_corners_correct (i : Source) :
    sourceCorners i = Finset.univ.image (fun k : Slot => cornerCode (corner (sourceFaces i) k)) := by
  fin_cases i <;> decide +kernel

/-- Each stored target corner has the code read from its three exposed faces. -/
lemma target_corner_correct (t : Target) (k : Slot) :
    targetCorner t k = cornerCode (corner (targetFaces t) k) := by
  revert k
  fin_cases t <;> decide +kernel

end ThreeColour
