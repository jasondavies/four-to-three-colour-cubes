module

public import Mathlib

/-!
# Weighted K₄ selection for thin cuboids

Edges `0,…,5` are `01,02,03,12,13,23`. A good vertex represents a
corner-solvable D target on the other three colours. The physical interpretation
of goodness is a hypothesis, not a theorem of this module.
-/
@[expose] public section

namespace ThreeColour.Thin

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

private theorem other_edge (v : Fin 4) (e : Fin 6) (he : e ∈ triangle v) :
    ∃ f ∈ triangle v, f ≠ e := by
  fin_cases v <;> fin_cases e <;> norm_num [triangle] at *

private def triangleWeight (x : Fin 6 → ℕ) : Fin 4 → ℕ
  | 0 => x 3 + x 4 + x 5
  | 1 => x 1 + x 2 + x 5
  | 2 => x 0 + x 2 + x 4
  | 3 => x 0 + x 1 + x 3

private theorem small_triangle (x : Fin 6 → ℕ) (v : Fin 4)
    (h : triangleWeight x v ≤ 11) :
    (∀ f ∈ triangle v, x f ≤ 11) ∧ ∃ f ∈ triangle v, x f ≤ 3 := by
  constructor
  · intro f hf
    fin_cases v <;> simp only [triangle, triangleWeight] at * <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf <;>
      rcases hf with rfl | rfl | rfl <;> omega
  · by_contra hn
    have hh : ∀ f ∈ triangle v, 4 ≤ x f := by
      intro f hf
      by_contra hb
      exact hn ⟨f, hf, by omega⟩
    clear hn
    fin_cases v <;> simp only [triangle, triangleWeight] at *
    · have h3 := hh 3 (by simp); have h4 := hh 4 (by simp); have h5 := hh 5 (by simp)
      omega
    · have h1 := hh 1 (by simp); have h2 := hh 2 (by simp); have h5 := hh 5 (by simp)
      omega
    · have h0 := hh 0 (by simp); have h2 := hh 2 (by simp); have h4 := hh 4 (by simp)
      omega
    · have h0 := hh 0 (by simp); have h1 := hh 1 (by simp); have h3 := hh 3 (by simp)
      omega

/-- A heavy checkerboard type leaves a good triangle of total weight at most eleven. -/
private theorem heavy_triangle (x : Fin 6 → ℕ) (good : Fin 4 → Prop)
    {N : ℕ} (hN : 29 ≤ N) (hw : weight x ≤ N)
    (hg : ∀ v, 8 ≤ degree x v → good v)
    (e : Fin 6) (he : N - 12 < x e) :
    ∃ v, good v ∧ (∀ f ∈ triangle v, x f ≤ 11) ∧
      ∃ f ∈ triangle v, x f ≤ 3 := by
  have hv : ∃ v, 8 ≤ degree x v ∧ triangleWeight x v ≤ 11 := by
    unfold weight at hw
    fin_cases e
    · change N - 12 < x 0 at he
      exact ⟨0, by simp only [degree]; omega, by simp only [triangleWeight]; omega⟩
    · change N - 12 < x 1 at he
      exact ⟨0, by simp only [degree]; omega, by simp only [triangleWeight]; omega⟩
    · change N - 12 < x 2 at he
      exact ⟨0, by simp only [degree]; omega, by simp only [triangleWeight]; omega⟩
    · change N - 12 < x 3 at he
      exact ⟨1, by simp only [degree]; omega, by simp only [triangleWeight]; omega⟩
    · change N - 12 < x 4 at he
      exact ⟨1, by simp only [degree]; omega, by simp only [triangleWeight]; omega⟩
    · change N - 12 < x 5 at he
      exact ⟨2, by simp only [degree]; omega, by simp only [triangleWeight]; omega⟩
  obtain ⟨v, hv, ht⟩ := hv
  exact ⟨v, hg v hv, small_triangle x v ht⟩

/-- Simultaneous choice of long and short pairs, in the same good triangle. -/
theorem strip_pairs (x : Fin 6 → ℕ) (good : Fin 4 → Prop)
    {N s : ℕ} (hN : 29 ≤ N) (hs : 3 ≤ s)
    (hw : weight x ≤ N) (hNs : N ≤ 6 * s + 5)
    (hg : ∀ v, 8 ≤ degree x v → good v) (hex : ∃ v, good v) :
    ∃ v e f, good v ∧ e ∈ triangle v ∧ f ∈ triangle v ∧
      e ≠ f ∧ x e ≤ s ∧ x f ≤ N - 12 := by
  by_cases hall : ∀ e, x e ≤ N - 12
  · obtain ⟨v, e, hv, he, hx⟩ := long_pair x good hs (hw.trans hNs) hg hex
    obtain ⟨f, hf, hfe⟩ := other_edge v e he
    exact ⟨v, e, f, hv, he, hf, Ne.symm hfe, hx, hall f⟩
  · push Not at hall
    obtain ⟨e, he⟩ := hall
    obtain ⟨v, hv, hb, f, hf, hx⟩ := heavy_triangle x good hN hw hg e he
    obtain ⟨g, hgt, hgf⟩ := other_edge v f hf
    have hg11 := hb g hgt
    exact ⟨v, f, g, hv, hf, hgt, Ne.symm hgf, by omega, by omega⟩

end ThreeColour.Thin
