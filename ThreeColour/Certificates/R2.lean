module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma r_single_certificate_2 : ∀ j : Fin 6, ∀ s : Fin 2,
    Certificate (fits (rSingleTarget 2 j))
      (packGroups (triple 2) ∅ (checker j) (ordinary s)) (packBounds 6 0) := by
  intro j
  fin_cases j <;> decide +kernel

lemma r_pair_certificate_2 : ∀ b : Colour, ∀ j : Fin 6, ∀ s : Fin 2,
    2 ≠ b → Good 2 b j → ∀ u : Fin 2,
    Certificate (fits (rPairTarget 2 b j))
      (packGroups (triple 2) (pairSupport 2 b) (checker j) (ordinary s))
      (packBounds (4+u.val) (2-u.val)) := by
  intro b j
  fin_cases b <;> fin_cases j <;> decide +kernel
lemma r_mixed_certificate_2 : ∀ b : Colour, ∀ s : Fin 2, 2 ≠ b →
    Certificate (fits (rMajorTarget 2))
      (packGroups (triple 2) ∅ (tripleClass b (flip s)) (ordinary s))
      (packBounds 6 0) := by
  intro b
  fin_cases b <;> decide +kernel
end ThreeColour
