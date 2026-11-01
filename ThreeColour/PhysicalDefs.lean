module

public import ThreeColour.Data
public import MacMahon.Rotations

@[expose] public section

namespace ThreeColour
def FaceFits (t : Target) (i : Source) (k : Slot) (r : Fin 24) : Prop :=
  ∀ f : Fin 3, sourceFaces i (MacMahon.rotations r (MacMahon.exposedFaces k f)) =
    targetFaces t (MacMahon.exposedFaces k f)
instance (t : Target) (i : Source) (k : Slot) (r : Fin 24) : Decidable (FaceFits t i k r) := by
  unfold FaceFits; infer_instance
def PhysicalSolvable (x : Inventory) : Prop :=
  ∃ t : Target, ∃ f : Slot ↪ Stock x, ∀ k, ∃ r : Fin 24, FaceFits t (f k).1 k r
end ThreeColour
