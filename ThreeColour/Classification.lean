module

public import ThreeColour.Counting
public import ThreeColour.Lower

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators
lemma member_le_mass (x : Inventory) {g : SourceSet} {i : Source} (hi : i ∈ g) : x i ≤ mass x g :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
lemma zero_of_mass_zero (x : Inventory) {g : SourceSet} {i : Source} (hi : i ∈ g)
    (hz : mass x g = 0) : x i = 0 := by
  have := member_le_mass x hi
  omega
lemma triple_class_subset : ∀ a : Colour, ∀ s : Fin 2, tripleClass a s ⊆ ordinary s := by decide +kernel
lemma ordinary_upper (x : Inventory) (s : Fin 2) :
    mass x (ordinary s) ≤ mass x allPairs + ∑ a : Colour, mass x (tripleClass a s) := by
  have he : ∀ s : Fin 2, ∀ i : Source,
      (∑ j : Fin 2, if i ∈ (![ordinary s, allPairs \ ordinary s] : Fin 2 → SourceSet) j then 1 else 0) =
      (∑ j : Fin 5, if i ∈ (![allPairs, tripleClass 0 s, tripleClass 1 s,
        tripleClass 2 s, tripleClass 3 s] : Fin 5 → SourceSet) j then 1 else 0) := by decide +kernel
  have h := mass_identity x (![ordinary s, allPairs \ ordinary s] : Fin 2 → SourceSet)
    (![allPairs, tripleClass 0 s, tripleClass 1 s, tripleClass 2 s, tripleClass 3 s] : Fin 5 → SourceSet) (he s)
  norm_num [Fin.sum_univ_succ] at h ⊢
  omega

/-- A source is excluded from the chosen orientation, or is its unique T variety
for one repeated colour. This is the finite geometry used by `inventory_determined`. -/
lemma classification_partition : ∀ s : Fin 2, ∀ i : Source,
    ((i ∈ allPairs ∨ i ∈ allCheckers ∨ i ∈ ordinary (flip s)) ∧ extremal s i = 0) ∨
    ∃ a : Colour, triple a = insert i (tripleClass a (flip s)) ∧
      i ∉ tripleClass a (flip s) ∧ extremal s i = 7 := by decide +kernel

lemma inventory_determined (x : Inventory) (s : Fin 2)
    (hp : mass x allPairs = 0) (hc : mass x allCheckers = 0)
    (ho : mass x (ordinary (flip s)) = 0) (ht : ∀ a, mass x (triple a) = 7) : x = extremal s := by
  funext i
  rcases classification_partition s i with ⟨hi,he⟩ | ⟨a,ha,hi,he⟩
  · rw [he]
    rcases hi with h | h | h
    · exact zero_of_mass_zero x h hp
    · exact zero_of_mass_zero x h hc
    · exact zero_of_mass_zero x h ho
  · have hz : mass x (tripleClass a (flip s)) = 0 := by
      have := mass_mono x (triple_class_subset a (flip s)); omega
    have ht' := ht a
    rw [ha] at ht'
    unfold mass at ht' hz
    rw [Finset.sum_insert hi, hz] at ht'
    omega

lemma classify_ordered (x : Inventory) (hn : ¬ Solvable x) (ht : total x = 28)
    (s : Fin 2) (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) : x = extremal s := by
  have hc := no_checker x hn s hs (by omega)
  have htot := totals x
  have hb := buckets_sum_bound x hn
  have hp : mass x allPairs = 0 := by omega
  have htt : ∀ a : Colour, mass x (triple a) = 7 := by
    have hts := triple_totals x
    have hbs := bucket_bound x hn
    have hbt := bucket_totals x
    intro a
    fin_cases a <;> norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ] at hts hbs hbt ⊢ <;> omega
  have ho : mass x (ordinary (flip s)) = 0 := by
    by_contra hh
    have hu := ordinary_upper x (flip s)
    have he : ∃ b : Colour, 1 ≤ mass x (tripleClass b (flip s)) := by
      by_contra he
      push Not at he
      norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ] at he hu
      omega
    obtain ⟨b,hb⟩ := he
    obtain ⟨a,hab⟩ := exists_ne b
    have hmajor := (checker_and_major_bounds x hn s hs (by omega)).2
    exact hn (solvable_r_mixed x a b s hab (by rw [htt]; omega) hb (by omega))
  exact inventory_determined x s hp hc ho htt

/-- Exactly the two printed multisets are extremal obstructions. -/
theorem classify28 (x : Inventory) (ht : total x = 28) :
    ¬ Solvable x ↔ ∃ s : Fin 2, x = extremal s := by
  constructor
  · intro hn
    obtain ⟨s, hs⟩ := exists_major_orientation x
    exact ⟨s, classify_ordered x hn ht s hs⟩
  · rintro ⟨s,rfl⟩
    exact extremal_not_solvable s
end ThreeColour
