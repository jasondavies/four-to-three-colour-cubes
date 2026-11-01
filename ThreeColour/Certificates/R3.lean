module

public import ThreeColour.ConstructionDefs

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma r_single_certificate_3 : ∀ j : Fin 6, ∀ s : Fin 2,
    Certificate (fits (rSingleTarget 3 j))
      (packGroups (triple 3) ∅ (checker j) (ordinary s)) (packBounds 6 0) := by
  intro j
  fin_cases j <;> decide +kernel

lemma r_pair_certificate_3 : ∀ b : Colour, ∀ j : Fin 6, ∀ s : Fin 2,
    3 ≠ b → Good 3 b j → ∀ u : Fin 2,
    Certificate (fits (rPairTarget 3 b j))
      (packGroups (triple 3) (pairSupport 3 b) (checker j) (ordinary s))
      (packBounds (4+u.val) (2-u.val)) := by
  intro b j
  fin_cases b <;> fin_cases j <;> decide +kernel
lemma r_mixed_certificate_3 : ∀ b : Colour, ∀ s : Fin 2, 3 ≠ b →
    Certificate (fits (rMajorTarget 3))
      (packGroups (triple 3) ∅ (tripleClass b (flip s)) (ordinary s))
      (packBounds 6 0) := by
  intro b
  fin_cases b <;> decide +kernel
end ThreeColour
