module

public import Mathlib

/-!
# Numerical bounds for thin cuboids

These lemmas verify the arithmetic used in the written rod/strip proof.
They do not assert a physical cuboid threshold: the geometry and allocation
bridges for non-cubic boxes are not yet formalised here.
-/
@[expose] public section

namespace ThreeColour.Thin

/-- Proposed sharp available-inventory threshold, proved in the manuscript. -/
def threshold (l : ℕ) : ℕ := max 29 ((24 * l - 1) / 5)

/-- The spare supply and the inequality driving propagation on weighted `K₄`. -/
theorem threshold_bounds {l N : ℕ} (hl : 2 ≤ l) (hN : threshold l ≤ N) :
    29 ≤ N ∧ 4 * l + 5 ≤ N ∧ N ≤ 6 * (N - 4 * l) + 5 := by
  unfold threshold at hN
  omega

/-- The balanced six-checkerboard witness has too few suppliers of every pair. -/
theorem balanced_shortage {l : ℕ} (hl : 2 ≤ l) :
    let K := (24 * l - 1) / 5
    1 ≤ K ∧ (K - 1) - (K - 1) / 6 < 4 * l := by
  dsimp
  omega

/-- Supplier and total-size bounds after the three strip reservations. -/
theorem strip_residual_bounds {l N : ℕ} (hl : 3 ≤ l) (hN : threshold l ≤ N) :
    4 * l + 4 ≤ N ∧
    2 * (l - 2) + 2 ≤ N - 13 ∧ 4 * (l - 2) + 2 ≤ N - 10 ∧
    2 * (l - 2) + 1 ≤ N - 12 ∧ 4 * (l - 2) + 3 ≤ N - 9 ∧
    2 * (l - 2) + 2 ≤ N - 11 ∧ 4 * (l - 2) + 4 ≤ N - 8 := by
  have := threshold_bounds (by omega : 2 ≤ l) hN
  omega

/-- The strip volume dominates the new checkerboard obstruction. -/
theorem strip_completion (l : ℕ) :
    max (6 * l) (threshold l) = max 29 (6 * l) := by
  unfold threshold
  omega

/-- No-D orientation counting: at most six sources lie outside the majority. -/
theorem minority_bound {A B C N : ℕ} (htotal : A + B + C = N)
    (hN : 29 ≤ N) (hdegree : 4 * B + 2 * C ≤ 12) :
    B + C ≤ 6 ∧ 23 ≤ A := by omega

/-- Counting bucket incidences forces eighteen majority T-sources. -/
theorem t_supply {T P : ℕ} (hA : 23 ≤ T + P) (hb : T + 2 * P ≤ 28) :
    18 ≤ T := by omega

/-- Either reserve six copies of one T-variety, or use the second H orientation. -/
theorem reservation_dichotomy (t : Fin 4 → ℕ)
    (hsum : 18 ≤ t 0 + t 1 + t 2 + t 3) :
    (∃ a, 6 ≤ t a) ∨ ((∀ a, 3 ≤ t a) ∧ ∃ a, 5 ≤ t a) := by
  by_cases h : ∃ a, 6 ≤ t a
  · exact Or.inl h
  right
  have hcap : ∀ a, t a ≤ 5 := by intro a; by_contra ha; exact h ⟨a, by omega⟩
  constructor
  · intro a
    have h0 := hcap 0; have h1 := hcap 1
    have h2 := hcap 2; have h3 := hcap 3
    clear hcap h
    fin_cases a <;> simp_all <;> omega
  · by_contra ha
    have hc : ∀ a, t a ≤ 4 := by intro a; by_contra hb; exact ha ⟨a, by omega⟩
    have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
    omega

/-- Among two distinct candidate partner colours, one has two T-copies. -/
theorem partner_supply (t : Fin 4 → ℕ) (hcap : ∀ a, t a ≤ 7)
    (hsum : 18 ≤ t 0 + t 1 + t 2 + t 3) (b c : Fin 4) (hbc : b ≠ c) :
    2 ≤ t b ∨ 2 ≤ t c := by
  have h0 := hcap 0; have h1 := hcap 1
  have h2 := hcap 2; have h3 := hcap 3
  clear hcap
  fin_cases b <;> fin_cases c <;> simp_all <;> omega

end ThreeColour.Thin
