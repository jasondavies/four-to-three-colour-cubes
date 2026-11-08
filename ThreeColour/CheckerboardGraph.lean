module

public import Mathlib

/-!
# Weighted K₄ selection for cuboids

Edges `0,…,5` are `01,02,03,12,13,23`. A good vertex represents a
corner-solvable D target on the other three colours. The physical interpretation
of goodness is a hypothesis, not a theorem of this module.
-/
@[expose] public section

namespace ThreeColour.Checkerboard

/-- Sum of the six checkerboard multiplicities. -/
def weight (x : Fin 6 → ℕ) : ℕ := x 0 + x 1 + x 2 + x 3 + x 4 + x 5

/-- Incident weight, counting checkerboards supporting the complementary triple. -/
def degree (x : Fin 6 → ℕ) : Fin 4 → ℕ
  | 0 => x 0 + x 1 + x 2
  | 1 => x 0 + x 3 + x 4
  | 2 => x 1 + x 3 + x 5
  | 3 => x 2 + x 4 + x 5

/-- Edges of the triangle complementary to a vertex. -/
def triangle : Fin 4 → Finset (Fin 6)
  | 0 => {3, 4, 5}
  | 1 => {1, 2, 5}
  | 2 => {0, 2, 4}
  | 3 => {0, 1, 3}

private theorem propagate (x : Fin 6 → ℕ) {s : ℕ} (hs : 3 ≤ s)
    (v w : Fin 4) (hvw : v ≠ w)
    (hh : ∀ e ∈ triangle v, s < x e) : 8 ≤ degree x w := by
  fin_cases v <;> fin_cases w <;>
    simp_all [triangle, degree] <;> omega

/-- A corner-solvable complementary triangle has a sufficiently supplied long pair. -/
theorem long_pair (x : Fin 6 → ℕ) (good : Fin 4 → Prop)
    {s : ℕ} (hs : 3 ≤ s) (hweight : weight x ≤ 6 * s + 5)
    (hgood : ∀ v, 8 ≤ degree x v → good v) (hex : ∃ v, good v) :
    ∃ v e, good v ∧ e ∈ triangle v ∧ x e ≤ s := by
  by_contra hn
  have hh : ∀ v, good v → ∀ e ∈ triangle v, s < x e := by
    intro v hv e he
    by_contra hb
    exact hn ⟨v, e, hv, he, by omega⟩
  obtain ⟨v, hv⟩ := hex
  have allgood : ∀ w, good w := by
    intro w
    by_cases h : v = w
    · simpa [← h] using hv
    · exact hgood w (propagate x hs v w h (hh v hv))
  have h0 := hh 0 (allgood 0)
  have h1 := hh 1 (allgood 1)
  have h2 := hh 2 (allgood 2)
  simp only [triangle, Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
  have e0 := h2 0 (by simp)
  have e1 := h1 1 (by simp)
  have e2 := h1 2 (by simp)
  have e3 := h0 3 (by simp)
  have e4 := h0 4 (by simp)
  have e5 := h0 5 (by simp)
  unfold weight at hweight
  omega


end ThreeColour.Checkerboard
