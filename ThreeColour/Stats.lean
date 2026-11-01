module

public import ThreeColour.Data

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators
lemma totals (x : Inventory) :
    mass x allTriples + mass x allPairs + mass x allCheckers = total x := by
  have he : ∀ i : Source,
      (∑ j : Fin 3, if i ∈ (![allTriples,allPairs,allCheckers] : Fin 3 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 1, if i ∈ (![Finset.univ] : Fin 1 → SourceSet) j then 1 else 0) := by decide +kernel
  have hh := mass_identity x (![allTriples,allPairs,allCheckers] : Fin 3 → SourceSet) (![Finset.univ] : Fin 1 → SourceSet) (he)
  norm_num [Fin.sum_univ_succ, total] at hh ⊢
  omega

lemma ordinary_totals (x : Inventory) :
    mass x (ordinary 0) + mass x (ordinary 1) = mass x allTriples + mass x allPairs := by
  have he : ∀ i : Source,
      (∑ j : Fin 2, if i ∈ (ordinary : Fin 2 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 2, if i ∈ (![allTriples,allPairs] : Fin 2 → SourceSet) j then 1 else 0) := by decide +kernel
  have hh := mass_identity x (ordinary : Fin 2 → SourceSet) (![allTriples,allPairs] : Fin 2 → SourceSet) (he)
  norm_num [Fin.sum_univ_succ, total] at hh ⊢
  omega

lemma triple_totals (x : Inventory) : (∑ a : Colour, mass x (triple a)) = mass x allTriples := by
  simpa using sum_mass_eq_multiple x (triple) (allTriples) 1 (by decide +kernel)

lemma pair_totals (x : Inventory) : (∑ a : Colour, mass x (pair a)) = 2 * mass x allPairs := by
  apply sum_mass_eq_multiple
  decide +kernel

lemma eligible_totals (x : Inventory) : (∑ d : Colour, mass x (eligible d)) = 2 * mass x allCheckers := by
  apply sum_mass_eq_multiple
  decide +kernel

lemma checker_totals (x : Inventory) : (∑ j : Fin 6, mass x (checker j)) = mass x allCheckers := by
  simpa using sum_mass_eq_multiple x (checker) (allCheckers) 1 (by decide +kernel)

lemma bucket_totals (x : Inventory) (a : Colour) :
    mass x (bucket a) = mass x (triple a) + mass x (pair a) := by
  have he : ∀ a : Colour, ∀ i : Source,
      (∑ j : Fin 1, if i ∈ (![bucket a] : Fin 1 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 2, if i ∈ (![triple a,pair a] : Fin 2 → SourceSet) j then 1 else 0) := by decide +kernel
  have hh := mass_identity x (![bucket a] : Fin 1 → SourceSet) (![triple a,pair a] : Fin 2 → SourceSet) (he a)
  norm_num [Fin.sum_univ_succ, total] at hh ⊢
  omega

lemma support_totals (x : Inventory) (a : Colour) :
    (∑ b : Colour, mass x (support a b)) = 3 * mass x (triple a) + 2 * mass x (pair a) := by
  have he : ∀ a : Colour, ∀ i : Source,
      (∑ j : Fin 4, if i ∈ ((support a) : Fin 4 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 5, if i ∈ (![triple a,triple a,triple a,pair a,pair a] : Fin 5 → SourceSet) j then 1 else 0) := by decide +kernel
  have hh := mass_identity x ((support a) : Fin 4 → SourceSet) (![triple a,triple a,triple a,pair a,pair a] : Fin 5 → SourceSet) (he a)
  norm_num [Fin.sum_univ_succ, total] at hh ⊢
  omega

lemma pair_support_totals (x : Inventory) (a : Colour) :
    (∑ b : Colour, mass x (pairSupport a b)) = 2 * mass x (pair a) := by
  apply sum_mass_eq_multiple
  revert a
  decide +kernel

lemma support_self (x : Inventory) (a : Colour) : mass x (support a a) = 0 := by
  fin_cases a <;> simp [mass, support]
lemma pair_support_self (x : Inventory) (a : Colour) : mass x (pairSupport a a) = 0 := by
  fin_cases a <;> simp [mass, pairSupport]
lemma support_subset : ∀ a b : Colour, support a b ⊆ bucket a := by decide +kernel
lemma support_le (x : Inventory) (a b : Colour) : mass x (support a b) ≤ mass x (bucket a) :=
  mass_mono x (support_subset a b)
lemma ordinary_checker_disjoint : ∀ s : Fin 2, ∀ j : Fin 6, Disjoint (ordinary s) (checker j) := by decide +kernel
lemma triple_checker_disjoint : ∀ a : Colour, ∀ j : Fin 6, Disjoint (triple a) (checker j) := by decide +kernel
lemma checker_in_eligible : ∀ j : Fin 6, ∀ d : Colour, d ∈ omitted j → checker j ⊆ eligible d := by decide +kernel
lemma omitted_nonempty : ∀ j : Fin 6, ∃ d : Colour, d ∈ omitted j := by decide +kernel
lemma triple_class_total (x : Inventory) (a : Colour) :
    mass x (tripleClass a 0) + mass x (tripleClass a 1) = mass x (triple a) := by
  have he : ∀ a : Colour, ∀ i : Source,
      (∑ j : Fin 2, if i ∈ ((tripleClass a) : Fin 2 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 1, if i ∈ (![triple a] : Fin 1 → SourceSet) j then 1 else 0) := by decide +kernel
  have hh := mass_identity x ((tripleClass a) : Fin 2 → SourceSet) (![triple a] : Fin 1 → SourceSet) (he a)
  norm_num [Fin.sum_univ_succ, total] at hh ⊢
  omega

end ThreeColour
