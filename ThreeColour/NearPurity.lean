module
public import ThreeColour.FrameTheorems
public import ThreeColour.RMajority0
public import ThreeColour.RMajority1
public import ThreeColour.RMajority2
public import ThreeColour.RMajority3
@[expose] public section
namespace ThreeColour
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

lemma r_majority_certificate (a b c d : Colour)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) (s : Fin 2) (u : Fin 3) :
    Certificate (fits (rTarget a b c))
      (packGroups (tripleClass a s) (pair a ∩ ordinary s)
        (minorityPool s d) (ordinary s)) (packBounds (4+u.val) (2-u.val)) := by
  fin_cases a
  · exact r_majority_certificate_0 b c d hab hac hbc hda hdb hdc s u
  · exact r_majority_certificate_1 b c d hab hac hbc hda hdb hdc s u
  · exact r_majority_certificate_2 b c d hab hac hbc hda hdb hdc s u
  · exact r_majority_certificate_3 b c d hab hac hbc hda hdb hdc s u

lemma r_majority_disjoint : ∀ a s d,
    Disjoint (tripleClass a s) (pair a ∩ ordinary s) ∧
    Disjoint (tripleClass a s) (minorityPool s d) ∧
    Disjoint (pair a ∩ ordinary s) (minorityPool s d) := by decide +kernel

/-- Four T cubes and six bucket cubes suffice for the repeated-colour part
of an R-target, provided a minority corner and a majority corner are available. -/
lemma solvable_r_majority (x : Inventory) (a : Colour) (s : Fin 2)
    (ht : 4 ≤ mass x (tripleClass a s))
    (hb : 6 ≤ mass (majorInventory x s) (bucket a))
    (hm : 0 < mass x (ordinary (flip s)) + mass x allCheckers)
    (ho : 8 ≤ mass x (ordinary s)) : Solvable x := by
  obtain ⟨d,hda,hd⟩ := minority_supported_triple x s a hm
  obtain ⟨b,c,hab,hac,hbc,hdb,hdc⟩ := palette_complement a d hda
  have hs := bucket_totals (majorInventory x s) a
  rw [major_triple, major_mass x s (pair a)] at hs
  obtain ⟨u,hu,hp⟩ : ∃ u : Fin 3, 4+u.val ≤ mass x (tripleClass a s) ∧
      2-u.val ≤ mass x (pair a ∩ ordinary s) := by
    by_cases h6 : 6 ≤ mass x (tripleClass a s)
    · exact ⟨2, by simpa using h6, by simp⟩
    by_cases h5 : 5 ≤ mass x (tripleClass a s)
    · exact ⟨1, by simpa using h5, by simp; omega⟩
    · exact ⟨0, by simpa using ht, by simp; omega⟩
  obtain ⟨hTP,hTM,hPM⟩ := r_majority_disjoint a s d
  exact ⟨rTarget a b c, pack_build x _ _ _ _ _ _ _
    (r_majority_certificate a b c d hab hac hbc hda hdb hdc s u)
    hTP hTM hPM hu hp hd ho⟩

/-- The ordinary-majority proof works already at twenty-seven cubes. -/
lemma corner_near_purity (x : Inventory) (hn : ¬ Solvable x)
    (ht : 27 ≤ total x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    mass x (ordinary (flip s)) + mass x allCheckers = 0 := by
  have hnf : ¬ RestrictedFrameSolvable 0 x := fun h => hn ((frame_zero_iff x).mp h.solvable)
  obtain ⟨_,ho⟩ := frame_major_bounds 0 x hnf (by simpa using ht) s hs
  have hb := frame_bucket_bound 0 x hnf s (by omega)
  have hbt := bucket_totals (majorInventory x s)
  have htr := triple_totals (majorInventory x s)
  have hpa := pair_totals (majorInventory x s)
  have htot := major_totals x s
  by_contra hm
  have hm' : 0 < mass x (ordinary (flip s)) + mass x allCheckers := by omega
  have hlocal : ∀ a, 2 * mass (majorInventory x s) (triple a) +
      mass (majorInventory x s) (pair a) ≤ 10 := by
    intro a
    have hbucket := hb a
    have hsum := hbt a
    by_cases h4 : 4 ≤ mass (majorInventory x s) (triple a)
    · have h5 : mass (majorInventory x s) (bucket a) ≤ 5 := by
        by_contra h
        exact hn (solvable_r_majority x a s (by rwa [major_triple] at h4)
          (by omega) hm' (by omega))
      omega
    · omega
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hlocal htr hpa
  omega

/-- Near-extremal failures are pure, with every colour bucket below demand. -/
theorem near_failure_bounds (k : ℕ) (x : Inventory) (hn : ¬ FrameSolvable k x)
    (ht : 16*k+27 ≤ total x) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    mass x (ordinary (flip s)) = 0 ∧ mass x allCheckers = 0 ∧
      ∀ a, mass x (bucket a) ≤ 4*k+7 := by
  by_cases hk : k = 0
  · subst k
    have hpure := corner_near_purity x (fun h => hn ((frame_zero_iff x).mpr h))
      (by simpa using ht) s hs
    have ho : mass x (ordinary (flip s)) = 0 := by omega
    have hc : mass x allCheckers = 0 := by omega
    have hmajor := (frame_major_bounds 0 x (fun h => hn h.solvable) ht s hs).2
    have hb := frame_bucket_bound 0 x (fun h => hn h.solvable) s (by omega)
    rw [majorInventory_eq x s ho hc] at hb
    exact ⟨ho,hc,hb⟩
  · exact frame_failure_bounds k (by omega) x hn ht s hs

/-- For `n ≥ 3`, the guaranteed frame can be found among forty targets. -/
theorem restricted_frame_solvable_of_le (k : ℕ) (hk : 1 ≤ k) (x : Inventory)
    (ht : 16*k+29 ≤ total x) : RestrictedFrameSolvable k x := by
  by_contra hn
  obtain ⟨s,hs⟩ := exists_major_orientation x
  have hpure := frame_purity k hk x hn (by omega) s hs
  have ho : mass x (ordinary (flip s)) = 0 := by omega
  have hc : mass x allCheckers = 0 := by omega
  have hmajor := (frame_major_bounds k x hn (by omega) s hs).2
  have hb := frame_bucket_bound k x hn s (by omega)
  rw [majorInventory_eq x s ho hc] at hb
  have := frame_bucket_sum k x hb
  have := totals x
  omega
end ThreeColour
