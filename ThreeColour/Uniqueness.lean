module

public import ThreeColour.PhysicalDefs
public import ThreeColour.Encoder

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
/-- The checked encoder recovers each target index after any proper rotation. -/
lemma target_index_rotations (i : Target) : ∀ r : Fin 24,
    targetIndex (encode (fun f => targetFaces i (MacMahon.rotations r f))) = i := by
  fin_cases i <;> decide +kernel

lemma target_index_faces : ∀ i : Target, targetIndex (encode (targetFaces i)) = i := by
  decide +kernel

/-- The target catalogue also has no duplicate rotation varieties. -/
theorem target_catalogue_unique (i j : Target) (r : Fin 24)
    (h : ∀ f, targetFaces i (MacMahon.rotations r f) = targetFaces j f) : i = j := by
  have he := funext h
  have hi := target_index_rotations i r
  rw [he, target_index_faces] at hi
  exact hi.symm

end ThreeColour
