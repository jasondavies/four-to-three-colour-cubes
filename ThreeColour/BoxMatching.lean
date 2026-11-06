module

public import ThreeColour.FrameMatching

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Pool Hall inequalities with an arbitrary finite index type. -/
def GroupHall {I : Type*} [DecidableEq I] (x : Inventory)
    (g : I → SourceSet) (d : I → ℕ) : Prop :=
  ∀ s : Finset I, (∑ j ∈ s, d j) ≤ mass x (s.biUnion g)

lemma grouped_assignment {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
    (x : Inventory) (g : I → SourceSet) (tag : P → I) (d : I → ℕ)
    (hd : ∀ j, Fintype.card {p // tag p = j} ≤ d j) (hh : GroupHall x g d) :
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

/-- Extend an initial matching with edge-type groups. A single edge group has
room for all initial reservations; any two edge pools cover the inventory. -/
lemma groupHall_extend {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (x : Inventory)
    (g : I → SourceSet) (d : I → ℕ) (e : J → SourceSet) (w : J → ℕ) (r : ℕ)
    (hg : GroupHall x g d) (hr : ∑ i, d i ≤ r)
    (he : ∀ j, r + w j ≤ mass x (e j))
    (hpair : ∀ j k, j ≠ k → e j ∪ e k = Finset.univ)
    (ht : r + ∑ j, w j ≤ mass x Finset.univ) :
    GroupHall x (Sum.elim g e) (Sum.elim d w) := by
  classical
  intro s
  let G := Sum.elim g e
  have hl : ∑ i ∈ s.toLeft, d i ≤ r :=
    (Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)).trans hr
  have hw : ∑ j ∈ s.toRight, w j ≤ ∑ j, w j :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hem (j : J) (hj : j ∈ s.toRight) : mass x (e j) ≤ mass x (s.biUnion G) :=
    mass_mono x (Finset.subset_biUnion_of_mem G (Finset.mem_toRight.mp hj))
  have hgm : mass x (s.toLeft.biUnion g) ≤ mass x (s.biUnion G) := by
    apply mass_mono
    intro i hi
    obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨.inl j, Finset.mem_toLeft.mp hj, hi⟩
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  change (∑ i ∈ s.toLeft, d i) + (∑ j ∈ s.toRight, w j) ≤ mass x (s.biUnion G)
  by_cases hne : s.toRight.Nonempty
  · obtain ⟨j, hj⟩ := hne
    by_cases hone : ∀ k ∈ s.toRight, k = j
    · have hset : s.toRight = {j} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hj, hone⟩
      rw [hset, Finset.sum_singleton]
      exact (Nat.add_le_add_right hl _).trans ((he j).trans (hem j hj))
    · push Not at hone
      obtain ⟨k, hk, hkj⟩ := hone
      have hu : mass x Finset.univ ≤ mass x (s.biUnion G) := by
        rw [← hpair j k hkj.symm]
        exact mass_mono x (Finset.union_subset
          (Finset.subset_biUnion_of_mem G (Finset.mem_toRight.mp hj))
          (Finset.subset_biUnion_of_mem G (Finset.mem_toRight.mp hk)))
      exact (Nat.add_le_add hl hw).trans (ht.trans hu)
  · have hz : s.toRight = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz, Finset.sum_empty, Nat.add_zero]
    exact (hg s.toLeft).trans hgm

end ThreeColour
