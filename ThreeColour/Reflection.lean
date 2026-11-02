module

public import ThreeColour.ReflectionData
public import ThreeColour.RData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma reflection_involutive : Function.Involutive reflection := by
  change ∀ i : Source, reflection (reflection i) = i
  decide +kernel
lemma reflection_geometry : ∀ i : Source, ∀ f : Fin 6,
    sourceFaces (reflection i) (ColourCubes.rotations (reflectionRotation i) f) =
    sourceFaces i (reflectFace f) := by decide +kernel
/-- Reflection exchanges the two extremal multisets. -/
theorem reflect_extremal : ∀ s : Fin 2, reflectInventory (extremal s) = extremal (flip s) := by decide +kernel
end ThreeColour
