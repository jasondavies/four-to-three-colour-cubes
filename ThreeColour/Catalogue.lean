module

public import ThreeColour.RawChecks
public import ThreeColour.Encoder

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma raw_at_decompose (n : Raw) : ∃ b k : Fin 64, rawAt b k = n := by
  refine ⟨⟨n.val / 64, by omega⟩, ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp [rawAt]
  omega
lemma raw_source_complete (n : Raw) (h : Uses 4 (rawFaces n)) :
    ∀ f : Fin 6, rawFaces n f = sourceFaces (sourceIndex n) (ColourCubes.rotations (rawRotation n) f) := by
  obtain ⟨b,k,rfl⟩ := raw_at_decompose n
  exact (raw_checks b k).1 h
lemma raw_target_complete (n : Raw) (h : Uses 3 (rawFaces n)) :
    ∀ f : Fin 6, rawFaces n f = targetFaces (targetIndex n) (ColourCubes.rotations (rawRotation n) f) := by
  obtain ⟨b,k,rfl⟩ := raw_at_decompose n
  exact (raw_checks b k).2 h
/-- Every four-colour face assignment is represented, up to a proper rotation. -/
theorem source_catalogue_complete (c : Fin 6 → Colour) (hc : Uses 4 c) :
    ∃ i : Source, ∃ r : Fin 24, ∀ f, c f = sourceFaces i (ColourCubes.rotations r f) := by
  refine ⟨sourceIndex (encode c), rawRotation (encode c), ?_⟩
  simpa only [encode_decode] using raw_source_complete (encode c) (by simpa only [encode_decode] using hc)
/-- Every exactly-three-colour target is represented, up to a proper rotation. -/
theorem target_catalogue_complete (c : Fin 6 → Colour) (hc : Uses 3 c) :
    ∃ t : Target, ∃ r : Fin 24, ∀ f, c f = targetFaces t (ColourCubes.rotations r f) := by
  refine ⟨targetIndex (encode c), rawRotation (encode c), ?_⟩
  simpa only [encode_decode] using raw_target_complete (encode c) (by simpa only [encode_decode] using hc)
end ThreeColour
