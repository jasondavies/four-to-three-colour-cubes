module

public import ThreeColour.Core

@[expose] public section

namespace ThreeColour
open scoped BigOperators

/-- Hall's condition after grouping positions that use the same source pool. -/
def PoolHall {m : ℕ} (x : Inventory) (g : Fin m → SourceSet)
    (d : Fin m → ℕ) : Prop :=
  ∀ s : Finset (Fin m), (∑ j ∈ s, d j) ≤ mass x (s.biUnion g)

/-- Grouping interchangeable positions does not lose the distinct-copy condition. -/
lemma pool_assignment {m : ℕ} {P : Type*} [Fintype P]
    (x : Inventory) (g : Fin m → SourceSet) (tag : P → Fin m)
    (d : Fin m → ℕ)
    (hd : ∀ j, Fintype.card {p // tag p = j} ≤ d j)
    (hh : PoolHall x g d) :
    ∃ f : P ↪ Stock x, ∀ p, (f p).1 ∈ g (tag p) := by
  classical
  have hall := Fintype.all_card_le_filter_rel_iff_exists_injective
    (α := P) (β := Stock x) (fun p c => c.1 ∈ g (tag p))
  obtain ⟨f, hf, hr⟩ := hall.mp (by
    intro s
    let js := s.image tag
    have hcard : s.card ≤ ∑ j ∈ js, d j := by
      rw [Finset.card_eq_sum_card_fiberwise (f := tag) (t := js) (by
        intro p hp
        exact Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
      apply Finset.sum_le_sum
      intro j hj
      apply le_trans _ (hd j)
      rw [Fintype.card_subtype]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    have hstock := stock_card x (js.biUnion g)
    have he : (Finset.univ.filter fun c : Stock x => c.1 ∈ js.biUnion g) =
        Finset.univ.filter (fun c => ∃ p ∈ s, c.1 ∈ g (tag p)) := by
      ext c
      simp [js]
    rw [he] at hstock
    have h := hcard.trans (hh js)
    rw [← hstock] at h
    exact h)
  exact ⟨⟨f, hf⟩, hr⟩

end ThreeColour
