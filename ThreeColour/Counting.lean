module

public import ThreeColour.Constructions
public import ThreeColour.RConstructions

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators

/-- Choose the ordinary orientation class of greater or equal mass. -/
lemma exists_major_orientation (x : Inventory) :
    ∃ s : Fin 2, mass x (ordinary (flip s)) ≤ mass x (ordinary s) := by
  rcases le_total (mass x (ordinary 0)) (mass x (ordinary 1)) with h | h
  · exact ⟨1, by simpa [flip] using h⟩
  · exact ⟨0, by simpa [flip] using h⟩

lemma pair_support_exists (x : Inventory) (a : Colour) (n : ℕ)
    (hn : 1 ≤ n) (hn2 : n ≤ 2) (hp : n ≤ mass x (pair a)) :
    ∃ b : Colour, a ≠ b ∧ n ≤ mass x (pairSupport a b) := by
  have hsum := pair_support_totals x a
  have hz := pair_support_self x a
  by_contra h
  push Not at h
  fin_cases a <;>
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at h hsum hz hp ⊢ <;> omega

lemma bucket_bound (x : Inventory) (hn : ¬ RestrictedSolvable x) (a : Colour) : mass x (bucket a) ≤ 7 := by
  by_contra h
  have hu : 8 ≤ mass x (bucket a) := by omega
  have hp : ∀ b c : Colour, a ≠ b → a ≠ c → b ≠ c →
      mass x (support a b) ≤ 3 ∨ mass x (support a c) ≤ 3 := by
    intro b c hab hac hbc
    by_contra hbad
    push Not at hbad
    exact hn (restricted_solvable_q x a b c hab hac hbc (by omega) (by omega) hu)
  have hs := support_totals x a
  have hb := bucket_totals x a
  have hl := support_le x a
  have hz := support_self x a
  fin_cases a <;> norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hs hb hl hz hp hu h ⊢ <;> omega

lemma eligible_bound (x : Inventory) (hn : ¬ RestrictedSolvable x) (d : Colour) : mass x (eligible d) ≤ 7 := by
  by_contra h
  exact hn (restricted_solvable_opposite x d (by omega) (by omega) (by omega))

lemma ordered_totals (x : Inventory) (s : Fin 2) :
    mass x (ordinary s) + mass x (ordinary (flip s)) + mass x allCheckers = total x := by
  have h0 := ordinary_totals x
  have h1 := totals x
  fin_cases s <;> norm_num [flip] <;> omega

lemma minor_eligible_bound (x : Inventory) (hn : ¬ RestrictedSolvable x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) (ht : 28 ≤ total x)
    (d : Colour) : mass x (ordinary (flip s)) + mass x (eligible d) ≤ 3 := by
  have hc := eligible_totals x
  have hb := eligible_bound x hn
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hc hb
  have ho := ordered_totals x s
  have ha : 7 ≤ mass x (ordinary s) := by omega
  by_contra h
  have hlow : 4 ≤ mass x (ordinary (flip s)) + mass x (eligible d) := by omega
  apply hn
  fin_cases s <;> norm_num [flip] at ha hlow
  · exact restricted_solvable_opposite x d (by omega) hlow (by omega)
  · exact restricted_solvable_opposite x d hlow (by omega) (by omega)

lemma checker_and_major_bounds (x : Inventory) (hn : ¬ RestrictedSolvable x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) (ht : 28 ≤ total x) :
    mass x allCheckers + 2 * mass x (ordinary (flip s)) ≤ 6 ∧ 22 ≤ mass x (ordinary s) := by
  have hm := minor_eligible_bound x hn s hs ht
  have hz := eligible_totals x
  have ho := ordered_totals x s
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hm hz
  omega

lemma buckets_sum_bound (x : Inventory) (hn : ¬ RestrictedSolvable x) :
    mass x allTriples + 2 * mass x allPairs ≤ 28 := by
  have hb := bucket_bound x hn
  have hi := bucket_totals x
  have ht := triple_totals x
  have hp := pair_totals x
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hb hi ht hp
  omega

lemma triple_bound_with_checker (x : Inventory) (hn : ¬ RestrictedSolvable x) (s : Fin 2)
    (ho : 8 ≤ mass x (ordinary s)) (hc : 0 < mass x allCheckers) (a : Colour) :
    mass x (triple a) ≤ 5 := by
  have ht := checker_totals x
  have hj : ∃ j : Fin 6, 1 ≤ mass x (checker j) := by
    by_contra h
    push Not at h
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at ht h
    omega
  obtain ⟨j,hj⟩ := hj
  by_contra h
  exact hn (restricted_solvable_r_single x a j s (by omega) hj ho)

lemma not_good_omitted : ∀ a b : Colour, a ≠ b → ∀ j : Fin 6,
    ¬ Good a b j → a ∈ omitted j := by decide +kernel

lemma eligible_decomposition (x : Inventory) (a : Colour) :
    mass x (eligible a) = ∑ j : Fin 6, if a ∈ omitted j then mass x (checker j) else 0 := by
  have he : ∀ a : Colour, ∀ i : Source,
      (∑ j : Fin 1, if i ∈ (![eligible a] : Fin 1 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 6, if i ∈ (if a ∈ omitted j then checker j else ∅) then 1 else 0) := by decide +kernel
  have hh := mass_identity x (![eligible a] : Fin 1 → SourceSet)
    (fun j : Fin 6 => if a ∈ omitted j then checker j else ∅) (he a)
  simp only [Fin.sum_univ_one] at hh
  change mass x (eligible a) = ∑ j : Fin 6, mass x (if a ∈ omitted j then checker j else ∅) at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [mass]

lemma good_checker_exists (x : Inventory) (a b : Colour) (hab : a ≠ b)
    (hc : 4 ≤ mass x allCheckers) (hz : ∀ d, mass x (eligible d) ≤ 3) :
    ∃ j : Fin 6, Good a b j ∧ 1 ≤ mass x (checker j) := by
  by_contra h
  push Not at h
  have hm : ∀ j : Fin 6, mass x (checker j) ≤
      if a ∈ omitted j then mass x (checker j) else 0 := by
    intro j
    by_cases hj : a ∈ omitted j
    · simp [hj]
    · have hg : Good a b j := by
        by_contra hg
        exact hj (not_good_omitted a b hab j hg)
      have hh := h j hg
      simp [hj]
      omega
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hm j)
  rw [checker_totals x, ← eligible_decomposition x a] at hb
  have := hz a
  omega

lemma strengthened_bucket (x : Inventory) (hn : ¬ RestrictedSolvable x) (s : Fin 2)
    (ho : 8 ≤ mass x (ordinary s)) (hc : 4 ≤ mass x allCheckers)
    (hz : ∀ d, mass x (eligible d) ≤ 3) (a : Colour)
    (ht4 : 4 ≤ mass x (triple a)) (ht5 : mass x (triple a) ≤ 5) :
    mass x (bucket a) ≤ 5 := by
  by_contra h
  have htot := bucket_totals x a
  by_cases he : mass x (triple a) = 4
  · have hp : 2 ≤ mass x (pair a) := by omega
    obtain ⟨b,hab,hb⟩ := pair_support_exists x a 2 (by omega) (by omega) hp
    obtain ⟨j,hg,hj⟩ := good_checker_exists x a b hab hc hz
    exact hn (restricted_solvable_r_pair x a b j s 0 hab hg (by simpa using ht4) (by simpa using hb) hj ho)
  · have ht : mass x (triple a) = 5 := by omega
    have hp : 1 ≤ mass x (pair a) := by omega
    obtain ⟨b,hab,hb⟩ := pair_support_exists x a 1 (by omega) (by omega) hp
    obtain ⟨j,hg,hj⟩ := good_checker_exists x a b hab hc hz
    exact hn (restricted_solvable_r_pair x a b j s 1 hab hg (by simpa using ht.ge) (by simpa using hb) hj ho)

lemma no_checker (x : Inventory) (hn : ¬ RestrictedSolvable x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) (ht : 28 ≤ total x) :
    mass x allCheckers = 0 := by
  obtain ⟨hcb, ho⟩ := checker_and_major_bounds x hn s hs ht
  have hbucket := buckets_sum_bound x hn
  have htot := totals x
  by_contra hc
  have hcp : 0 < mass x allCheckers := by omega
  have htr := triple_bound_with_checker x hn s (by omega) hcp
  have hts := triple_totals x
  have hps := pair_totals x
  have hb := bucket_bound x hn
  have hbt := bucket_totals x
  have ht20 : mass x allTriples ≤ 20 := by
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at htr hts
    omega
  have hc4 : 4 ≤ mass x allCheckers := by omega
  have hz : ∀ d, mass x (eligible d) ≤ 3 := by
    intro d
    have := minor_eligible_bound x hn s hs ht d
    omega
  have hstrong := strengthened_bucket x hn s (by omega) hc4 hz
  have hlocal : ∀ a : Colour, mass x (bucket a) + mass x (triple a) ≤ 10 := by
    intro a
    have := htr a
    by_cases h4 : 4 ≤ mass x (triple a)
    · have := hstrong a h4 (htr a); omega
    · have := hb a; omega
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hlocal hts hps hbt
  omega

/-- The counting argument only needs targets of types Q, R, and D. -/
theorem restricted_solvable_of_29_le (x : Inventory) (ht : 29 ≤ total x) :
    RestrictedSolvable x := by
  by_contra hn
  obtain ⟨s, hs⟩ := exists_major_orientation x
  have hc := no_checker x hn s hs (by omega)
  have hb := buckets_sum_bound x hn
  have ht' := totals x
  omega

/-- Every multiset of at least 29 cubes builds an exactly-three-colour target. -/
theorem solvable_of_29_le (x : Inventory) (ht : 29 ≤ total x) : Solvable x :=
  (restricted_solvable_of_29_le x ht).solvable

theorem threshold29 (x : Inventory) (ht : total x = 29) : Solvable x :=
  solvable_of_29_le x (by omega)
end ThreeColour
