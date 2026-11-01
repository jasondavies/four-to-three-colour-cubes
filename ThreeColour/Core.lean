module

public import Mathlib

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators
abbrev Source := Fin 68
abbrev Slot := Fin 8
abbrev Inventory := Source → ℕ
/-- A finite pool of source varieties, not an algebraic group. -/
abbrev SourceSet := Finset Source
abbrev Stock (a : Inventory) := (i : Source) × Fin (a i)
def mass (a : Inventory) (g : SourceSet) : ℕ := ∑ i ∈ g, a i

def Hall (a : Inventory) (r : Slot → Source → Bool) : Prop :=
  ∀ s : Finset Slot, s.card ≤ mass a (Finset.univ.filter fun i => ∃ k ∈ s, r k i = true)

def Builds (a : Inventory) (r : Slot → Source → Bool) : Prop :=
  ∃ f : Slot ↪ Stock a, ∀ k, r k (f k).1 = true

lemma stock_card (a : Inventory) (g : SourceSet) :
    (Finset.univ.filter fun x : Stock a => x.1 ∈ g).card = mass a g := by
  classical
  have h := Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun i => Fin (a i)) (fun i => i ∈ g))
  simp only [Fintype.card_sigma, Fintype.card_fin] at h
  rw [Fintype.card_subtype] at h
  rw [h]
  exact Finset.sum_coe_sort g (fun i => a i)

lemma hall_iff_builds (a : Inventory) (r : Slot → Source → Bool) : Hall a r ↔ Builds a r := by
  classical
  have h := Fintype.all_card_le_filter_rel_iff_exists_injective (α := Slot) (β := Stock a)
    (fun k (c : Stock a) => r k c.1 = true)
  have hc : ∀ s : Finset Slot,
      (Finset.univ.filter fun c : Stock a => ∃ k ∈ s, r k c.1 = true).card =
      mass a (Finset.univ.filter fun i => ∃ k ∈ s, r k i = true) := by
    intro s
    simpa using stock_card a (Finset.univ.filter fun i => ∃ k ∈ s, r k i = true)
  constructor
  · intro ha
    have hh : ∀ s : Finset Slot,
        s.card ≤ (Finset.univ.filter fun c : Stock a => ∃ k ∈ s, r k c.1 = true).card := by
      intro s
      rw [hc s]
      exact ha s
    have hreal := h.mp (by
      intro s
      convert hh s using 1
      all_goals (congr 1; ext x; simp))
    obtain ⟨f, hi, hf⟩ := hreal
    exact ⟨⟨f, hi⟩, hf⟩
  · rintro ⟨f, hf⟩
    have hh := h.mpr ⟨f, f.injective, hf⟩
    intro s
    rw [← hc s]
    convert hh s using 1
    all_goals (congr 1; ext x; simp)

lemma mass_mono (a : Inventory) {g h : SourceSet} (hgh : g ⊆ h) : mass a g ≤ mass a h :=
  Finset.sum_le_sum_of_subset_of_nonneg hgh (by intros; omega)

lemma mass_union (a : Inventory) (g h : SourceSet) (hd : Disjoint g h) :
    mass a (g ∪ h) = mass a g + mass a h := Finset.sum_union hd

lemma mass_weight (a : Inventory) (g : SourceSet) :
    mass a g = ∑ i : Source, (if i ∈ g then 1 else 0) * a i := by
  simp [mass]

lemma mass_identity {m n : ℕ} (a : Inventory) (g : Fin m → SourceSet) (h : Fin n → SourceSet)
    (he : ∀ i : Source, (∑ j, if i ∈ g j then 1 else 0) = (∑ j, if i ∈ h j then 1 else 0)) :
    (∑ j, mass a (g j)) = ∑ j, mass a (h j) := by
  simp_rw [mass_weight]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j i => (if i ∈ h j then 1 else 0) * a i)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← Finset.sum_mul, he i]

/-- Count a family of source pools in which each member of `h` occurs `n` times. -/
lemma sum_mass_eq_multiple {m : ℕ} (x : Inventory) (g : Fin m → SourceSet)
    (h : SourceSet) (n : ℕ)
    (hc : ∀ i : Source, (∑ j, if i ∈ g j then 1 else 0) = if i ∈ h then n else 0) :
    (∑ j, mass x (g j)) = n * mass x h := by
  simp_rw [mass_weight]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul, hc i]
  split_ifs <;> simp_all

/-- A finite certificate selects one sufficient source pool for each Hall subset. -/
def Certificate {n : ℕ} (r : Slot → Source → Bool)
    (g : Fin n → SourceSet) (b : Fin n → ℕ) : Prop :=
  ∀ s : Finset Slot, ∃ j, s.card ≤ b j ∧
    ∀ i ∈ g j, ∃ k ∈ s, r k i = true

instance {n : ℕ} (r : Slot → Source → Bool) (g : Fin n → SourceSet) (b : Fin n → ℕ) :
    Decidable (Certificate r g b) := by unfold Certificate; infer_instance

lemma builds_of_certificate {n : ℕ} (a : Inventory) (r : Slot → Source → Bool)
    (g : Fin n → SourceSet) (b : Fin n → ℕ) (hc : Certificate r g b)
    (hb : ∀ j, b j ≤ mass a (g j)) : Builds a r := by
  apply (hall_iff_builds a r).mp
  intro s
  obtain ⟨j, hj, hg⟩ := hc s
  exact hj.trans ((hb j).trans (mass_mono a (by
    intro i hi
    simpa using hg i hi)))
end ThreeColour
