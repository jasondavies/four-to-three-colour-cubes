module

public import ThreeColour.RawData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma encode_decode : ∀ c : Fin 6 → Colour, rawFaces (encode c) = c := by decide +kernel
lemma sources_use_four : ∀ i : Source, Uses 4 (sourceFaces i) := by decide +kernel
lemma targets_use_three : ∀ t : Target, Uses 3 (targetFaces t) := by decide +kernel
end ThreeColour
