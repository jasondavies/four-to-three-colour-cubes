import Mathlib

/-! Symbolic checks of the arithmetic interfaces in cuboid-theorem.txt.
This file does not formalise the geometric cuboid threshold theorem. -/
namespace CuboidReview

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

/-- No opposite-face corner solution bounds the minority supply. -/
theorem minority_bound (A B C N z0 z1 z2 z3 : ℕ)
    (hN : 29 ≤ N) (ht : A+B+C=N) (hz : z0+z1+z2+z3=2*C)
    (h0 : B+z0 ≤ 3) (h1 : B+z1 ≤ 3) (h2 : B+z2 ≤ 3) (h3 : B+z3 ≤ 3) :
    B+C ≤ 6 ∧ N-6 ≤ A ∧ 23 ≤ A := by
  omega

/-- Bucket counting gives the necessary size band and T supply. -/
theorem bucket_bounds (a N M A T P : ℕ) (ha : 2 ≤ a)
    (hN : 16*a-3 ≤ N) (hM : M ≤ 6) (ht : A+M=N)
    (hA : T+P=A) (hB : T+2*P ≤ 4*(4*a-1)) :
    N ≤ 16*a+2 ∧ 16*a-14 ≤ T ∧ 0 < M := by
  omega

/-- The critical wide-box partner and extra-source inequalities. -/
theorem wide_supply (a b c N A T : ℕ) (ha : 3 ≤ a) (hbc : b ≤ c)
    (hL : 4*(a+b+c)-16 ≤ N) (hN : N ≤ 16*a+2)
    (hA : 16*a-9 ≤ A) (hT : 16*a-14 ≤ T) :
    b+c ≤ 3*a+4 ∧ 2*b ≤ 3*a+4 ∧
    4*(2*a-1) < T ∧ 2*(b-1)+2*(4*a-1) < T ∧ 2*a+b+1 ≤ A := by
  omega

/-- If exactly two colours are high at a=2, the minority has at least five copies. -/
theorem two_high (b N M T : ℕ) (hb : b ≤ 4) (hN : 29 ≤ N)
    (hl : 2*(N-M)-28 ≤ T) (hu : T ≤ 2*b+12) (hM : M ≤ 6) :
    5 ≤ M := by
  omega

/-- The intermediate aspect-ratio range in which frame cardinality suffices. -/
theorem exact_cardinality (a b c : ℕ) (ha : 2 ≤ a) (_hab : a ≤ b) (hbc : b ≤ c) :
    (16*a-3 ≤ 4*(a+b+c)-16 ∧ (24*c-1)/5 ≤ 4*(a+b+c)-16) ↔
      (3*a+4 ≤ b+c ∧ c ≤ 5*(a+b)-19) := by
  omega

#print axioms weighted_bounds
#print axioms residual_budget
#print axioms minority_bound
#print axioms bucket_bounds
#print axioms wide_supply
#print axioms two_high
#print axioms exact_cardinality
end CuboidReview
