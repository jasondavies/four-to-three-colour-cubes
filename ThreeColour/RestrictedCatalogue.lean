module

public import ThreeColour.RestrictedGeometry
public import ThreeColour.Catalogue
public import ThreeColour.Uniqueness

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

lemma restricted_target_rotations (t : Target) : ∀ r : Fin 24,
    RestrictedTarget (fun f => targetFaces t (ColourCubes.rotations r f)) ↔
      RestrictedTarget (targetFaces t) := by
  fin_cases t <;> decide +kernel

/-- Together with target uniqueness and the counts, this certifies that the
28 counted representatives exhaust the geometric target families. -/
theorem restricted_target_catalogue_complete (c : Fin 6 → Colour)
    (hc : RestrictedTarget c) :
    ∃ t : Target, RestrictedTarget (targetFaces t) ∧
      ∃ r : Fin 24, ∀ f, c f = targetFaces t (ColourCubes.rotations r f) := by
  have hu : Uses 3 c := by
    rcases hc with h | h | h <;> exact h.1
  obtain ⟨t, r, hr⟩ := target_catalogue_complete c hu
  refine ⟨t, ?_, r, hr⟩
  apply (restricted_target_rotations t r).mp
  have he := funext hr
  simpa only [← he] using hc

end ThreeColour
