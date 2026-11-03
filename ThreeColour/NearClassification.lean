module
public import ThreeColour.NearPurity
public import ThreeColour.NearLower
@[expose] public section
namespace ThreeColour
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

lemma pure_support (x : Inventory) (s : Fin 2)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0)
    (i : Source) (hi : 0 < x i) : i ∈ ordinary s := by
  have partition : ∀ s i, i ∈ ordinary s ∨ i ∈ ordinary (flip s) ∨ i ∈ allCheckers := by decide +kernel
  rcases partition s i with h | h | h
  · exact h
  · have := zero_of_mass_zero x h ho; omega
  · have := zero_of_mass_zero x h hc; omega

lemma pure_inventory_ext (x y : Inventory) (s : Fin 2)
    (hxo : mass x (ordinary (flip s)) = 0) (hxc : mass x allCheckers = 0)
    (hyo : mass y (ordinary (flip s)) = 0) (hyc : mass y allCheckers = 0)
    (hp : ∀ i ∈ allPairs, x i = y i)
    (ht : ∀ a, mass x (triple a) = mass y (triple a)) : x = y := by
  funext i
  rcases classification_partition s i with ⟨hi,_⟩ | ⟨a,ha,hi,_⟩
  · rcases hi with h | h | h
    · exact hp i h
    · rw [zero_of_mass_zero x h hxc, zero_of_mass_zero y h hyc]
    · rw [zero_of_mass_zero x h hxo, zero_of_mass_zero y h hyo]
  · have hxz : mass x (tripleClass a (flip s)) = 0 := by
      have := mass_mono x (triple_class_subset a (flip s)); omega
    have hyz : mass y (tripleClass a (flip s)) = 0 := by
      have := mass_mono y (triple_class_subset a (flip s)); omega
    have h := ht a
    rw [ha] at h
    unfold mass at h hxz hyz
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hxz, hyz] at h
    simpa using h

lemma mass_one (x : Inventory) (g : SourceSet) (hg : mass x g = 1) :
    ∃ p ∈ g, ∀ i ∈ g, x i = if i = p then 1 else 0 := by
  obtain ⟨p,hp,hpos⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i ∈ g, x i from by change 0 < mass x g; omega)
  have hple := member_le_mass x hp
  have hp1 : x p = 1 := by omega
  refine ⟨p,hp,?_⟩
  intro i hi
  by_cases he : i = p
  · simpa [he] using hp1
  · have hs : ({i,p} : SourceSet) ⊆ g := by intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj; rcases hj with rfl | rfl <;> assumption
    have hle := mass_mono x hs
    simp [mass, he] at hle
    change (∑ j ∈ g, x j) = 1 at hg
    simp [he]
    omega

/-- Purity and bucket capacities leave precisely the two advertised forms. -/
lemma near_inventory_determined (k : ℕ) (x : Inventory) (s : Fin 2)
    (ht : total x = 16*k+27)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0)
    (hb : ∀ a, mass x (bucket a) ≤ 4*k+7) :
    ∃ p : NearParameter, x = nearInventory k p := by
  have hw := frame_bucket_sum k x hb
  have htot := totals x
  have htSum := triple_totals x
  have hpSum := pair_totals x
  have hbt := bucket_totals x
  have hp : mass x allPairs ≤ 1 := by omega
  by_cases hp0 : mass x allPairs = 0
  · have htBound : ∀ a, mass x (triple a) ≤ 4*k+7 := by intro a; have := hb a; have := hbt a; omega
    obtain ⟨a,ha⟩ : ∃ a, mass x (triple a) < 4*k+7 := by
      by_contra h
      push Not at h
      norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at h htSum
      omega
    have hv : ∀ b, mass x (triple b) = 4*k+7 - if b = a then 1 else 0 := by
      intro b
      fin_cases a <;> fin_cases b <;>
        norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at htSum htBound ha ⊢ <;> omega
    obtain ⟨p,hps,hpT,hpb⟩ := near_triple_parameter a s
    refine ⟨p, pure_inventory_ext x (nearInventory k p) s ho hc ?_ ?_ ?_ ?_⟩
    · simpa [hps] using (near_pure k p).1
    · exact (near_pure k p).2
    · intro i hi
      rw [zero_of_mass_zero x hi hp0, near_pairs k p i hi]
      have hnp : p.val ∉ allPairs := fun h => Finset.disjoint_left.mp triple_pair_disjoint hpT h
      simp [hnp]
    · intro b
      simp only [hv, near_triple, hpb]
  · have hp1 : mass x allPairs = 1 := by omega
    obtain ⟨i,hi,hxi⟩ := mass_one x allPairs hp1
    have hip : 0 < x i := by have h := hxi i hi; simp only [ite_true] at h; omega
    have his := pure_support x s ho hc i hip
    let p : NearParameter := ⟨i, ordinary_parameter s i his⟩
    have hps : nearOrientation p = s := near_orientation_eq p s his
    have hbEq : ∀ a, mass x (bucket a) = 4*k+7 := by
      intro a
      fin_cases a <;>
        norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at htSum hpSum hbt hb ⊢ <;> omega
    have hpair : ∀ a, mass x (pair a) = if i ∈ bucket a then 1 else 0 := by
      intro a
      have hsub : ∀ a, pair a ⊆ allPairs := by decide +kernel
      have hmem : ∀ i a, i ∈ allPairs → (i ∈ pair a ↔ i ∈ bucket a) := by decide +kernel
      calc
        mass x (pair a) = ∑ j ∈ pair a, if j = i then 1 else 0 := by
          apply Finset.sum_congr rfl; intro j hj; exact hxi j (hsub a hj)
        _ = if i ∈ bucket a then 1 else 0 := by simp [hmem i a hi]
    refine ⟨p, pure_inventory_ext x (nearInventory k p) s ho hc ?_ ?_ ?_ ?_⟩
    · simpa [hps] using (near_pure k p).1
    · exact (near_pure k p).2
    · intro j hj
      rw [hxi j hj, near_pairs k p j hj]
      simp only [show p.val = i from rfl, hi, true_and]
    · intro a
      have hs := hbt a
      rw [hbEq, hpair] at hs
      rw [near_triple]
      change mass x (triple a) = 4*k+7 - if i ∈ bucket a then 1 else 0
      split_ifs at * <;> omega

/-- Exactly thirty-two fixed-palette multisets fail at size `16n-5`. -/
theorem near_frame_classification (k : ℕ) (x : Inventory) :
    total x = 16*k+27 ∧ ¬ FrameSolvable k x ↔ x ∈ nearInventories k := by
  constructor
  · rintro ⟨ht,hn⟩
    obtain ⟨s,hs⟩ := exists_major_orientation x
    obtain ⟨ho,hc,hb⟩ := near_failure_bounds k x hn ht.ge s hs
    obtain ⟨p,rfl⟩ := near_inventory_determined k x s ht ho hc hb
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
  · intro h
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨near_total k p,near_not_solvable k p⟩

/-- Each of the twenty-four pair cases is inclusion-maximal: adding any
source cube produces a solution, although its size is below the maximum. -/
theorem near_pair_maximal (k : ℕ) (p : NearParameter) (hp : p.val ∈ allPairs)
    (i : Source) : FrameSolvable k (fun j => nearInventory k p j + if j = i then 1 else 0) := by
  let y : Inventory := fun j => nearInventory k p j + if j = i then 1 else 0
  have ht : total y = 16*k+28 := by
    change (∑ j : Source, (nearInventory k p j + if j = i then 1 else 0)) = _
    rw [Finset.sum_add_distrib]
    have := near_total k p
    simp only [total, mass] at this
    simp at *
    omega
  by_contra hn
  obtain ⟨s,hs⟩ := (frame_classification k y ht).mp hn
  have hz : frameExtremal k s p.val = 0 := by
    have hn : p.val ∉ extremalSupport s := fun h => Finset.disjoint_left.mp (near_support_disjoint s) h hp
    simp [frameExtremal, hn]
  have he := congrFun hs p.val
  rw [hz] at he
  have hp1 : nearInventory k p p.val = 1 := by simp [near_pairs k p p.val hp, hp]
  change nearInventory k p p.val + _ = 0 at he
  omega
end ThreeColour
