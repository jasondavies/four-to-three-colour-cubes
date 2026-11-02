module

public import ThreeColour.RestrictedDefs
public import ThreeColour.RData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

lemma qTarget_isQ : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c →
    IsQ (targetFaces (qTarget a b c)) := by decide +kernel

lemma oppositeTarget_isD : ∀ d : Colour,
    IsD (targetFaces (oppositeTarget d)) := by decide +kernel

lemma rSingleTarget_isR : ∀ a : Colour, ∀ j : Fin 6,
    IsR (targetFaces (rSingleTarget a j)) := by decide +kernel

lemma rPairTarget_isR : ∀ a b : Colour, ∀ j : Fin 6, a ≠ b → Good a b j →
    IsR (targetFaces (rPairTarget a b j)) := by decide +kernel

lemma rMajorTarget_isR : ∀ a : Colour,
    IsR (targetFaces (rMajorTarget a)) := by decide +kernel

/-- Counts are of proper-rotation representatives, with the palette fixed. -/
theorem restricted_target_counts :
    (Finset.univ.filter (fun t : Target => IsQ (targetFaces t))).card = 12 ∧
    (Finset.univ.filter (fun t : Target => IsR (targetFaces t))).card = 12 ∧
    (Finset.univ.filter (fun t : Target => IsD (targetFaces t))).card = 4 ∧
    (Finset.univ.filter (fun t : Target => RestrictedTarget (targetFaces t))).card = 28 := by
  decide +kernel

end ThreeColour
