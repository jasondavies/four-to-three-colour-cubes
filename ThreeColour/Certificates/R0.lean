module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma r_single_certificate_0 : ∀ j : Fin 6, ∀ s : Fin 2,
    Certificate (fits (rSingleTarget 0 j))
      (packGroups (triple 0) ∅ (checker j) (ordinary s)) (packBounds 6 0) := by
  intro j
  fin_cases j <;> decide +kernel

lemma r_pair_certificate_0 : ∀ b : Colour, ∀ j : Fin 6, ∀ s : Fin 2,
    0 ≠ b → Good 0 b j → ∀ u : Fin 2,
    Certificate (fits (rPairTarget 0 b j))
      (packGroups (triple 0) (pairSupport 0 b) (checker j) (ordinary s))
      (packBounds (4+u.val) (2-u.val)) := by
  intro b j
  fin_cases b <;> fin_cases j <;> decide +kernel
lemma r_mixed_certificate_0 : ∀ b : Colour, ∀ s : Fin 2, 0 ≠ b →
    Certificate (fits (rMajorTarget 0))
      (packGroups (triple 0) ∅ (tripleClass b (flip s)) (ordinary s))
      (packBounds 6 0) := by
  intro b
  fin_cases b <;> decide +kernel
end ThreeColour
