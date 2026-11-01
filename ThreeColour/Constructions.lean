module

public import ThreeColour.Certificates

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators


lemma solvable_q (x : Inventory) (a b c : Colour) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hb : 4 ≤ mass x (support a b))
    (hc : 4 ≤ mass x (support a c)) (hu : 8 ≤ mass x (bucket a)) : Solvable x := by
  refine ⟨qTarget a b c, builds_of_certificate x _ _ _ (q_certificate a b c hab hac hbc) ?_⟩
  intro j
  fin_cases j <;> simp_all [qBounds, qGroups, mass]


lemma ordinary_disjoint : Disjoint (ordinary 0) (ordinary 1) := by decide +kernel
lemma ordinary_eligible_disjoint : ∀ s : Fin 2, ∀ d : Colour,
    Disjoint (ordinary s) (eligible d) := by decide +kernel
lemma ordinary_union_eligible_disjoint : ∀ d : Colour,
    Disjoint (ordinary 0 ∪ ordinary 1) (eligible d) := by decide +kernel

lemma solvable_opposite (x : Inventory) (d : Colour)
    (h0 : 4 ≤ mass x (ordinary 0) + mass x (eligible d))
    (h1 : 4 ≤ mass x (ordinary 1) + mass x (eligible d))
    (hu : 8 ≤ mass x (ordinary 0) + mass x (ordinary 1) + mass x (eligible d)) : Solvable x := by
  refine ⟨oppositeTarget d, builds_of_certificate x _ _ _ (opposite_certificate d) ?_⟩
  intro j
  fin_cases j
  · simp [oppBounds, oppGroups, mass]
  · change 4 ≤ mass x (ordinary 0 ∪ eligible d)
    simpa [mass_union x _ _ (ordinary_eligible_disjoint 0 d)] using h0
  · change 4 ≤ mass x (ordinary 1 ∪ eligible d)
    simpa [mass_union x _ _ (ordinary_eligible_disjoint 1 d)] using h1
  · change 8 ≤ mass x ((ordinary 0 ∪ ordinary 1) ∪ eligible d)
    rw [mass_union x _ _ (ordinary_union_eligible_disjoint d),
      mass_union x _ _ ordinary_disjoint]
    exact hu
end ThreeColour
