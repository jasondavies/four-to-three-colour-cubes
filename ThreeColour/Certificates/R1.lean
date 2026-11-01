module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma r_single_certificate_1 : ∀ j : Fin 6, ∀ s : Fin 2,
    Certificate (fits (rSingleTarget 1 j))
      (packGroups (triple 1) ∅ (checker j) (ordinary s)) (packBounds 6 0) := by
  intro j
  fin_cases j <;> decide +kernel

lemma r_pair_certificate_1 : ∀ b : Colour, ∀ j : Fin 6, ∀ s : Fin 2,
    1 ≠ b → Good 1 b j → ∀ u : Fin 2,
    Certificate (fits (rPairTarget 1 b j))
      (packGroups (triple 1) (pairSupport 1 b) (checker j) (ordinary s))
      (packBounds (4+u.val) (2-u.val)) := by
  intro b j
  fin_cases b <;> fin_cases j <;> decide +kernel
lemma r_mixed_certificate_1 : ∀ b : Colour, ∀ s : Fin 2, 1 ≠ b →
    Certificate (fits (rMajorTarget 1))
      (packGroups (triple 1) ∅ (tripleClass b (flip s)) (ordinary s))
      (packBounds 6 0) := by
  intro b
  fin_cases b <;> decide +kernel
end ThreeColour
