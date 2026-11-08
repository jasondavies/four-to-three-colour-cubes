module

public import Mathlib

@[expose] public section

/-! Arithmetic interfaces for the sharp cuboid theorem. -/
namespace ThreeColour.Cuboid

/-- Every numerical hypothesis in the three-direction weighted lemma. -/
theorem weighted_bounds (a b c N : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (h29 : 29 ≤ N) (hL : 4*(a+b+c)-16 ≤ N) (hK : (24*c-1)/5 ≤ N) :
    5 ≤ N-4*c ∧ N ≤ 6*(N-4*c)+5 ∧
    7 ≤ N-4*b ∧ 2*b-1 ≤ N-4*b ∧
    4*b-1 ≤ N-4*a ∧ (4*b-1)/3 ≤ N-4*c := by
  omega

/-- The common single-edge Hall budget for Q and the shortest-axis H. -/
theorem residual_budget (a b c N : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (h29 : 29 ≤ N) (hL : 4*(a+b+c)-16 ≤ N) :
    4*a+2*b+2*c-5 ≤ N := by
  omega

/-- The intermediate aspect-ratio range in which frame cardinality suffices. -/
theorem exact_cardinality (a b c : ℕ) (ha : 2 ≤ a) (_hab : a ≤ b) (hbc : b ≤ c) :
    (16*a-3 ≤ 4*(a+b+c)-16 ∧ (24*c-1)/5 ≤ 4*(a+b+c)-16) ↔
      (3*a+4 ≤ b+c ∧ c ≤ 5*(a+b)-19) := by
  omega


/-- Frame threshold for ordered dimensions. -/
def threshold (a b c : ℕ) : ℕ := max (max (16*a-3) (4*(a+b+c)-16)) ((24*c-1)/5)

lemma threshold_le {a b c N : ℕ} : threshold a b c ≤ N ↔
    16*a-3 ≤ N ∧ 4*(a+b+c)-16 ≤ N ∧ (24*c-1)/5 ≤ N := by
  simp only [threshold, max_le_iff, and_assoc]

end ThreeColour.Cuboid
