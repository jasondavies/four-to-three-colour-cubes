module

public import ThreeColour.RawData

@[expose] public section

namespace ThreeColour
-- Each block proof splits the 64 raw colourings before kernel reduction. This
-- bounds the reduction cache without changing the catalogue coverage statement.
def rawAt (b k : Fin 64) : Raw := Fin.ofNat 4096 (64*b.val+k.val)
def RawCheck (b : Fin 64) : Prop := ∀ k : Fin 64,
  (Uses 4 (rawFaces (rawAt b k)) → ∀ f : Fin 6,
    rawFaces (rawAt b k) f = sourceFaces (sourceIndex (rawAt b k))
      (ColourCubes.rotations (rawRotation (rawAt b k)) f)) ∧
  (Uses 3 (rawFaces (rawAt b k)) → ∀ f : Fin 6,
    rawFaces (rawAt b k) f = targetFaces (targetIndex (rawAt b k))
      (ColourCubes.rotations (rawRotation (rawAt b k)) f))
instance (b : Fin 64) : Decidable (RawCheck b) := by unfold RawCheck; infer_instance
end ThreeColour
