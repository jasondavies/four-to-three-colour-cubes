module
public import ThreeColour.FrameCounting
public import ThreeColour.FrameLower
public import ThreeColour.Classification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators

lemma majorInventory_eq (x : Inventory) (s : Fin 2)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0) :
    majorInventory x s = x := by
  have partition : ∀ s : Fin 2, ∀ i : Source,
      i ∈ ordinary s ∨ i ∈ ordinary (flip s) ∨ i ∈ allCheckers := by decide +kernel
  funext i
  rcases partition s i with h | h | h
  · simp [majorInventory, h]
  · have hz := zero_of_mass_zero x h ho
    simp [majorInventory, hz]
  · have hz := zero_of_mass_zero x h hc
    simp [majorInventory, hz]

lemma frame_inventory_determined (k : ℕ) (x : Inventory) (s : Fin 2)
    (hp : mass x allPairs = 0) (hc : mass x allCheckers = 0)
    (ho : mass x (ordinary (flip s)) = 0)
    (ht : ∀ a, mass x (triple a) = 4*k+7) : x = frameExtremal k s := by
  funext i
  rcases classification_partition s i with ⟨hi,he⟩ | ⟨a,ha,hi,he⟩
  · simp [frameExtremal, extremalSupport, he]
    rcases hi with h | h | h
    · exact zero_of_mass_zero x h hp
    · exact zero_of_mass_zero x h hc
    · exact zero_of_mass_zero x h ho
  · simp [frameExtremal, extremalSupport, he]
    have hz : mass x (tripleClass a (flip s)) = 0 := by
      have := mass_mono x (triple_class_subset a (flip s)); omega
    have ht' := ht a
    rw [ha] at ht'
    unfold mass at ht' hz
    rw [Finset.sum_insert hi, hz] at ht'
    omega

/-- After eliminating the minority, majority bucket bounds apply to the whole
inventory. Both the classification and the upper bound use this step. -/
lemma frame_failure_bounds (k : ℕ) (hk : 1 ≤ k) (x : Inventory)
    (hn : ¬ FrameSolvable k x) (ht : 16*k+28 ≤ total x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    mass x (ordinary (flip s)) = 0 ∧ mass x allCheckers = 0 ∧
      ∀ a, mass x (bucket a) ≤ 4*k+7 := by
  have hpure := frame_purity k hk x hn ht s hs
  have ho : mass x (ordinary (flip s)) = 0 := by omega
  have hc : mass x allCheckers = 0 := by omega
  have hmajor := (frame_major_bounds k x hn ht s hs).2
  have hb := frame_bucket_bound k x hn s (by omega)
  rw [majorInventory_eq x s ho hc] at hb
  exact ⟨ho, hc, hb⟩

/-- Exactly two inventories fail at size `16n-4`, where `n=k+2`. -/
theorem frame_classification (k : ℕ) (x : Inventory) (ht : total x = 16*k+28) :
    ¬ FrameSolvable k x ↔ ∃ s : Fin 2, x = frameExtremal k s := by
  constructor
  · intro hn
    by_cases hk : k = 0
    · subst k
      rw [frame_zero_iff] at hn
      obtain ⟨s,hs⟩ := (classify28 x (by simpa using ht)).mp hn
      exact ⟨s, by simpa only [frameExtremal_zero] using hs⟩
    · obtain ⟨s,hs⟩ := exists_major_orientation x
      obtain ⟨ho, hc, hb⟩ := frame_failure_bounds k (by omega) x hn ht.ge s hs
      have hsum := frame_bucket_sum k x hb
      have htot := totals x
      have hp : mass x allPairs = 0 := by omega
      have hT := triple_totals x
      have hbt := bucket_totals x
      have htq : ∀ a, mass x (triple a) = 4*k+7 := by
        intro a
        fin_cases a <;>
          norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hT hbt hb ⊢ <;> omega
      exact ⟨s, frame_inventory_determined k x s hp hc ho htq⟩
  · rintro ⟨s,rfl⟩
    exact frameExtremal_not_solvable k s

/-- Every inventory of at least `16n-3` cubes has an `n`-frame. -/
theorem frame_solvable_of_le (k : ℕ) (x : Inventory) (ht : 16*k+29 ≤ total x) :
    FrameSolvable k x := by
  by_cases hk : k = 0
  · subst k
    rw [frame_zero_iff]
    exact solvable_of_29_le x (by simpa using ht)
  · by_contra hn
    obtain ⟨s,hs⟩ := exists_major_orientation x
    obtain ⟨ho, hc, hb⟩ := frame_failure_bounds k (by omega) x hn (by omega) s hs
    have hsum := frame_bucket_sum k x hb
    have htot := totals x
    omega

theorem frame_least_guaranteed_size (k : ℕ) :
    IsLeast {m : ℕ | ∀ x : Inventory, m ≤ total x → FrameSolvable k x} (16*k+29) := by
  constructor
  · exact frame_solvable_of_le k
  · intro m hm
    by_contra h
    exact frameExtremal_not_solvable k 0 (hm (frameExtremal k 0) (by
      rw [frameExtremal_total]; omega))

end ThreeColour
