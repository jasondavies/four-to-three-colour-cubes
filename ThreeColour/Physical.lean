module

public import ThreeColour.PhysicalDefs
public import ThreeColour.CornerData

@[expose] public section

namespace ThreeColour

/-- Catalogue compatibility is exactly physical matching by a proper rotation. -/
theorem fits_physical (t : Target) (k : Slot) (i : Source) :
    fits t k i = true ↔ ∃ r : Fin 24, FaceFits t i k r := by
  unfold fits
  rw [decide_eq_true_eq, source_corners_correct, target_corner_correct]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, cornerCode_eq_iff]
  exact (ColourCubes.Geometry.corner_rotation_iff (sourceFaces i) (targetFaces t) k).symm

theorem solvable_iff_physical (x : Inventory) : Solvable x ↔ PhysicalSolvable x := by
  constructor
  · rintro ⟨t,f,hf⟩
    exact ⟨t,f,fun k => (fits_physical t k (f k).1).mp (hf k)⟩
  · rintro ⟨t,f,hf⟩
    exact ⟨t,f,fun k => (fits_physical t k (f k).1).mpr (hf k)⟩
end ThreeColour
