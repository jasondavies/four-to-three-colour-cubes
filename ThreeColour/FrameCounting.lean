module
public import ThreeColour.FrameConstructions
public import ThreeColour.Counting
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ThreeColour
open scoped BigOperators

/-!
The frame argument uses `k = n - 2`. First, D-frames bound the minority
and force a large majority class. Q-frames bound each majority bucket.
For `k ≥ 1`, these bounds leave enough T cubes for a U-frame whenever any
minority cube remains. The corner argument handles `k = 0` separately.
-/

lemma mass_union_le (x : Inventory) (A B : SourceSet) :
    mass x (A ∪ B) ≤ mass x A + mass x B := by
  simp only [mass_weight, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [ha,hb]

lemma frame_opposite_impossible (k : ℕ) (x : Inventory) (hn : ¬ RestrictedFrameSolvable k x)
    (ht : 16*k+27 ≤ total x) (d : Colour)
    (h0 : 4 ≤ mass x (ordinary 0) + mass x (eligible d))
    (h1 : 4 ≤ mass x (ordinary 1) + mass x (eligible d))
    (hu : 8 ≤ mass x (ordinary 0) + mass x (ordinary 1) + mass x (eligible d)) : False := by
  have hchecker : ∀ j, mass x (checker j) < 12*k+8 := by
    intro j
    by_contra hj
    exact hn (frame_checker k x j (by omega))
  have he : ∀ j, 4*k+8 ≤ mass x (dEdgePool d j) := by
    intro j
    obtain ⟨l,hl⟩ := d_edge_complement d j
    have hsum : total x ≤ mass x (dEdgePool d j) + mass x (checker l) := by
      rw [total, ← hl]
      exact mass_union_le x _ _
    have := hchecker l
    omega
  apply hn
  apply frame_d k x d
  · simpa only [mass_union x _ _ (ordinary_eligible_disjoint 0 d)] using h0
  · simpa only [mass_union x _ _ (ordinary_eligible_disjoint 1 d)] using h1
  · have heq : (ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d) =
        (ordinary 0 ∪ ordinary 1) ∪ eligible d := (Finset.union_union_distrib_right _ _ _).symm
    rw [heq, mass_union x _ _ (ordinary_union_eligible_disjoint d),
      mass_union x _ _ ordinary_disjoint]
    exact hu
  · exact he
  · omega

lemma frame_eligible_bound (k : ℕ) (x : Inventory) (hn : ¬ RestrictedFrameSolvable k x)
    (ht : 16*k+27 ≤ total x) (d : Colour) : mass x (eligible d) ≤ 7 := by
  by_contra h
  exact frame_opposite_impossible k x hn ht d (by omega) (by omega) (by omega)

lemma frame_minor_eligible_bound (k : ℕ) (x : Inventory) (hn : ¬ RestrictedFrameSolvable k x)
    (ht : 16*k+27 ≤ total x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) (d : Colour) :
    mass x (ordinary (flip s)) + mass x (eligible d) ≤ 3 := by
  have hc := eligible_totals x
  have hb := frame_eligible_bound k x hn ht
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hc hb
  have ho := ordered_totals x s
  have ha : 7 ≤ mass x (ordinary s) := by omega
  by_contra h
  have hlow : 4 ≤ mass x (ordinary (flip s)) + mass x (eligible d) := by omega
  fin_cases s <;> norm_num [flip] at ha hlow
  · exact frame_opposite_impossible k x hn ht d (by omega) hlow (by omega)
  · exact frame_opposite_impossible k x hn ht d hlow (by omega) (by omega)

lemma frame_major_bounds (k : ℕ) (x : Inventory) (hn : ¬ RestrictedFrameSolvable k x)
    (ht : 16*k+27 ≤ total x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    mass x allCheckers + 2 * mass x (ordinary (flip s)) ≤ 6 ∧
      16*k+21 ≤ mass x (ordinary s) := by
  have hm := frame_minor_eligible_bound k x hn ht s hs
  have hz := eligible_totals x
  have ho := ordered_totals x s
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hm hz
  omega

/-- Restrict an inventory to one ordinary orientation class. -/
def majorInventory (x : Inventory) (s : Fin 2) : Inventory :=
  fun i => if i ∈ ordinary s then x i else 0

lemma major_mass (x : Inventory) (s : Fin 2) (g : SourceSet) :
    mass (majorInventory x s) g = mass x (g ∩ ordinary s) := by
  simp [mass, majorInventory]

lemma major_triple (x : Inventory) (s : Fin 2) (a : Colour) :
    mass (majorInventory x s) (triple a) = mass x (tripleClass a s) := by
  rw [major_mass]
  have h : ∀ a s, triple a ∩ ordinary s = tripleClass a s := by decide +kernel
  rw [h]

lemma major_totals (x : Inventory) (s : Fin 2) :
    mass (majorInventory x s) allTriples + mass (majorInventory x s) allPairs =
      mass x (ordinary s) := by
  have h := totals (majorInventory x s)
  have hz : ∀ s, allCheckers ∩ ordinary s = ∅ := by decide +kernel
  have hc : mass (majorInventory x s) allCheckers = 0 := by
    rw [major_mass, hz]; simp [mass]
  have ht : total (majorInventory x s) = mass x (ordinary s) := by
    change mass (majorInventory x s) Finset.univ = _
    rw [major_mass, Finset.univ_inter]
  rw [hc, ht, Nat.add_zero] at h
  exact h

lemma frame_bucket_bound (k : ℕ) (x : Inventory) (hn : ¬ RestrictedFrameSolvable k x)
    (s : Fin 2) (ho : 12*k+8 ≤ mass x (ordinary s)) (a : Colour) :
    mass (majorInventory x s) (bucket a) ≤ 4*k+7 := by
  by_contra h
  have hu : 4*k+8 ≤ mass (majorInventory x s) (bucket a) := by omega
  have hp : ∀ b c : Colour, a ≠ b → a ≠ c → b ≠ c →
      mass (majorInventory x s) (support a b) ≤ 3 ∨ mass (majorInventory x s) (support a c) ≤ 3 := by
    intro b c hab hac hbc
    by_contra hbad
    push Not at hbad
    apply hn
    apply frame_q k x a b c s hab hac hbc
    · rw [← major_mass]; omega
    · rw [← major_mass]; omega
    · rw [← major_mass]; exact hu
    · exact ho
  have hsum := support_totals (majorInventory x s) a
  have hb := bucket_totals (majorInventory x s) a
  have hl := support_le (majorInventory x s) a
  have hz := support_self (majorInventory x s) a
  fin_cases a <;> norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hsum hb hl hz hp hu ⊢ <;> omega

lemma minority_supported_triple (x : Inventory) (s : Fin 2) (a : Colour)
    (hm : 0 < mass x (ordinary (flip s)) + mass x allCheckers) :
    ∃ d : Colour, d ≠ a ∧ 1 ≤ mass x (minorityPool s d) := by
  have hsum := eligible_totals x
  have hsub : ∀ d : Colour, eligible d ⊆ allCheckers := by decide +kernel
  have hle := mass_mono x (hsub a)
  by_contra h
  push Not at h
  have hd (d : Colour) : mass x (minorityPool s d) =
      mass x (ordinary (flip s)) + mass x (eligible d) :=
    mass_union x _ _ (ordinary_eligible_disjoint (flip s) d)
  simp only [hd] at h
  fin_cases a <;> norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at h hsum hle <;> omega

lemma two_small_colours_impossible (k : ℕ) (hk : 1 ≤ k) (t : Colour → ℕ)
    (ht : 16*k+14 ≤ ∑ a, t a) (hb : ∀ a, t a ≤ 4*k+7) :
    ∀ a b, a ≠ b → k+2 ≤ t a ∨ k+2 ≤ t b := by
  intro a b hab
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at ht hb
  fin_cases a <;> fin_cases b <;> simp_all <;> omega

lemma palette_complement : ∀ a d : Colour, d ≠ a → ∃ b c : Colour,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ b ∧ d ≠ c := by decide +kernel

/-- Count each T cube once and each P cube twice across the four buckets. -/
lemma frame_bucket_sum (k : ℕ) (x : Inventory)
    (hb : ∀ a, mass x (bucket a) ≤ 4*k+7) :
    mass x allTriples + 2 * mass x allPairs ≤ 16*k+28 := by
  have ht := triple_totals x
  have hp := pair_totals x
  have hbt := bucket_totals x
  norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ] at ht hp hbt hb
  omega

/-- For side length at least three, a failing collection has no minority cubes. -/
lemma frame_purity (k : ℕ) (hk : 1 ≤ k) (x : Inventory)
    (hn : ¬ RestrictedFrameSolvable k x) (ht : 16*k+27 ≤ total x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    mass x (ordinary (flip s)) + mass x allCheckers = 0 := by
  obtain ⟨hm,ho⟩ := frame_major_bounds k x hn ht s hs
  have hb := frame_bucket_bound k x hn s (by omega)
  have hyt := major_totals x s
  have htrip := triple_totals (majorInventory x s)
  have hbuckets := bucket_totals (majorInventory x s)
  have htotal := ordered_totals x s
  have hweight := frame_bucket_sum k (majorInventory x s) hb
  have hT : 16*k+14 ≤ mass (majorInventory x s) allTriples := by omega
  have htb : ∀ a, mass (majorInventory x s) (triple a) ≤ 4*k+7 := by
    intro a
    have := hb a
    have := hbuckets a
    omega
  have hlarge : ∃ a, 3*k+4 ≤ mass (majorInventory x s) (triple a) := by
    by_contra h
    push Not at h
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at h htrip
    omega
  have hp := two_small_colours_impossible k hk (fun a => mass (majorInventory x s) (triple a))
    (by rw [triple_totals]; exact hT) htb
  by_contra hminor
  obtain ⟨a,ha⟩ := hlarge
  obtain ⟨d,hda,hd⟩ := minority_supported_triple x s a (by omega)
  obtain ⟨b,c,hab,hac,hbc,hdb,hdc⟩ := palette_complement a d hda
  rcases hp b c hbc with hb' | hc'
  · apply hn
    exact frame_u k x a b c d s hab hac hbc hda hdb hdc
      (by rwa [major_triple] at ha) (by rwa [major_triple] at hb') hd (by omega)
  · apply hn
    exact frame_u k x a c b d s hac hab hbc.symm hda hdc hdb
      (by rwa [major_triple] at ha) (by rwa [major_triple] at hc') hd (by omega)

end ThreeColour
