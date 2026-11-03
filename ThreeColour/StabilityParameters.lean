module
public import ThreeColour.Stability
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
@[expose] public section
namespace ThreeColour
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The twelve pair varieties in each ordinary class, in catalogue order. -/
def stabilityPair (s : Fin 2) : Fin 12 → Source :=
  if s = 0 then ![11,12,18,20,24,29,39,40,44,51,59,61]
  else ![14,15,17,21,26,30,37,38,46,52,62,63]

def stabilityTriple (s : Fin 2) : Colour → Source :=
  if s = 0 then ![10,23,45,66] else ![13,25,47,67]

/-- Twelve pair multiplicities and four bucket slacks. -/
abbrev StabilityCoordinate := Fin 12 ⊕ Colour
abbrev StabilityParameter (d : ℕ) := {v : StabilityCoordinate → ℕ // ∑ i, v i = d}

lemma stability_pair_injective : ∀ s, Function.Injective (stabilityPair s) := by decide +kernel
lemma stability_pair_mem : ∀ s j, stabilityPair s j ∈ allPairs ∩ ordinary s := by decide +kernel
lemma stability_pair_complete : ∀ s i, i ∈ allPairs ∩ ordinary s →
    ∃ j, stabilityPair s j = i := by decide +kernel
lemma stability_triple_bucket : ∀ s a b, stabilityTriple s a ∈ bucket b ↔ a = b := by decide +kernel
lemma stability_triple_mem : ∀ s a, stabilityTriple s a ∈ ordinary s := by decide +kernel
lemma stability_triple_not_pair : ∀ s a, stabilityTriple s a ∉ allPairs := by decide +kernel

/-- Place a prescribed multiplicity at one variety. -/
def pointInventory (i : Source) (v : ℕ) : Inventory := fun j => if i = j then v else 0

lemma mass_point (i : Source) (v : ℕ) (g : SourceSet) :
    mass (pointInventory i v) g = if i ∈ g then v else 0 := by
  simp [mass, pointInventory]

lemma mass_sum {α : Type*} [Fintype α] (x : α → Inventory) (g : SourceSet) :
    mass (fun i => ∑ a, x a i) g = ∑ a, mass (x a) g := by
  exact Finset.sum_comm

lemma mass_add (x y : Inventory) (g : SourceSet) :
    mass (fun i => x i + y i) g = mass x g + mass y g := Finset.sum_add_distrib

def stabilityPairs (s : Fin 2) (v : StabilityCoordinate → ℕ) : Inventory :=
  fun i => ∑ j, pointInventory (stabilityPair s j) (v (.inl j)) i

def stabilityCost (s : Fin 2) (v : StabilityCoordinate → ℕ) (a : Colour) : ℕ :=
  mass (stabilityPairs s v) (bucket a) + v (.inr a)

def stabilityInventory (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ) : Inventory :=
  fun i => stabilityPairs s v i +
    ∑ a, pointInventory (stabilityTriple s a) (4*k+7-stabilityCost s v a) i

lemma stability_pairs_mass (s : Fin 2) (v : StabilityCoordinate → ℕ) (g : SourceSet) :
    mass (stabilityPairs s v) g = ∑ j, if stabilityPair s j ∈ g then v (.inl j) else 0 := by
  unfold stabilityPairs
  rw [mass_sum]; simp only [mass_point]

lemma stability_pairs_total (s : Fin 2) (v : StabilityCoordinate → ℕ) :
    total (stabilityPairs s v) = ∑ j, v (.inl j) := by
  simp [total, stability_pairs_mass]

lemma stability_pairs_at (s : Fin 2) (v : StabilityCoordinate → ℕ) (j : Fin 12) :
    stabilityPairs s v (stabilityPair s j) = v (.inl j) := by
  simp [stabilityPairs, pointInventory, (stability_pair_injective s).eq_iff]

lemma stability_inventory_pair (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ) (j : Fin 12) :
    stabilityInventory k s v (stabilityPair s j) = v (.inl j) := by
  have hne (a : Colour) : stabilityTriple s a ≠ stabilityPair s j := by
    intro h
    have hm := stability_pair_mem s j
    have hn := stability_triple_not_pair s a
    exact hn (h ▸ Finset.mem_inter.mp hm |>.1)
  simp [stabilityInventory, stability_pairs_at, pointInventory, hne]

lemma stability_inventory_mass (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ) (g : SourceSet) :
    mass (stabilityInventory k s v) g = mass (stabilityPairs s v) g +
      ∑ a, if stabilityTriple s a ∈ g then 4*k+7-stabilityCost s v a else 0 := by
  unfold stabilityInventory
  rw [mass_add, mass_sum]; simp only [mass_point]

lemma stability_inventory_bucket (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ) (a : Colour) :
    mass (stabilityInventory k s v) (bucket a) =
      mass (stabilityPairs s v) (bucket a) + (4*k+7-stabilityCost s v a) := by
  rw [stability_inventory_mass]
  simp only [stability_triple_bucket]
  simp

lemma stability_cost_le {d : ℕ} (s : Fin 2) (v : StabilityParameter d) (a : Colour) :
    stabilityCost s v.val a ≤ d := by
  have hp : mass (stabilityPairs s v.val) (bucket a) ≤ total (stabilityPairs s v.val) :=
    mass_mono _ (Finset.subset_univ _)
  rw [stability_pairs_total] at hp
  have hs := Finset.single_le_sum (fun (b : Colour) _ => Nat.zero_le (v.val (.inr b)))
    (Finset.mem_univ a)
  have ht := v.property
  rw [Fintype.sum_sum_type] at ht
  unfold stabilityCost
  omega

lemma stability_inventory_pure (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ)
    (i : Source) (hi : i ∉ ordinary s) : stabilityInventory k s v i = 0 := by
  have hp (j : Fin 12) : stabilityPair s j ≠ i := by
    intro h
    exact hi (h ▸ (Finset.mem_inter.mp (stability_pair_mem s j)).2)
  have ht (a : Colour) : stabilityTriple s a ≠ i := by
    intro h
    exact hi (h ▸ stability_triple_mem s a)
  simp [stabilityInventory, stabilityPairs, pointInventory, hp, ht]

lemma stability_inventory_slack (k : ℕ) (s : Fin 2) {d : ℕ} (v : StabilityParameter d)
    (hd : d ≤ 4*k+7) (a : Colour) :
    mass (stabilityInventory k s v.val) (bucket a) + v.val (.inr a) = 4*k+7 := by
  rw [stability_inventory_bucket]
  have := (stability_cost_le s v a).trans hd
  unfold stabilityCost at *
  omega

lemma stability_inventory_zero_pools (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ) :
    mass (stabilityInventory k s v) (ordinary (flip s)) = 0 ∧
    mass (stabilityInventory k s v) allCheckers = 0 := by
  obtain ⟨ho,hc⟩ := near_ordinary_disjoint s
  constructor <;> apply Finset.sum_eq_zero <;> intro i hi
  · exact stability_inventory_pure k s v i (fun h => Finset.disjoint_left.mp ho h hi)
  · exact stability_inventory_pure k s v i (fun h => Finset.disjoint_left.mp hc h hi)

lemma stability_inventory_pairs (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ) :
    mass (stabilityInventory k s v) allPairs = ∑ j, v (.inl j) := by
  rw [stability_inventory_mass, stability_pairs_mass]
  simp only [show ∀ j, stabilityPair s j ∈ allPairs from
    fun j => (Finset.mem_inter.mp (stability_pair_mem s j)).1,
    stability_triple_not_pair, ite_true, ite_false, Finset.sum_const_zero, Nat.add_zero]

lemma stability_inventory_total (k : ℕ) (s : Fin 2) {d : ℕ} (v : StabilityParameter d)
    (hd : d ≤ 4*k+7) : total (stabilityInventory k s v.val) + d = 16*k+28 := by
  let x := stabilityInventory k s v.val
  change total x + d = 16*k+28
  have ht := totals x
  have hp := pair_totals x
  have htr := triple_totals x
  have hb := bucket_totals x
  have hz : mass x allCheckers = 0 := (stability_inventory_zero_pools k s v.val).2
  have hps : mass x allPairs = ∑ j, v.val (.inl j) := stability_inventory_pairs k s v.val
  have hsum := v.property
  rw [Fintype.sum_sum_type] at hsum
  have hs := stability_inventory_slack k s v hd
  change ∀ a, mass x (bucket a) + v.val (.inr a) = 4*k+7 at hs
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hp htr hb hs
  norm_num [Fin.sum_univ_succ] at hsum hps
  omega

lemma stability_inventory_fails (k : ℕ) (s : Fin 2) {d : ℕ} (v : StabilityParameter d)
    (hd : d ≤ 4*k+7) : ¬ FrameSolvable k (stabilityInventory k s v.val) := by
  apply pure_bucket_not_solvable k _ s
  · intro i hi
    by_contra h
    have := stability_inventory_pure k s v.val i h
    omega
  · intro a
    have := stability_inventory_slack k s v hd a
    omega

/-- Recover the twelve pair multiplicities and the four bucket slacks. -/
def stabilityEncode (k : ℕ) (s : Fin 2) (x : Inventory) : StabilityCoordinate → ℕ :=
  Sum.elim (fun j => x (stabilityPair s j)) (fun a => 4*k+7-mass x (bucket a))

lemma stability_encode_inventory (k : ℕ) (s : Fin 2) {d : ℕ} (v : StabilityParameter d)
    (hd : d ≤ 4*k+7) : stabilityEncode k s (stabilityInventory k s v.val) = v.val := by
  funext i
  cases i with
  | inl j => exact stability_inventory_pair k s v.val j
  | inr a =>
    change 4*k+7-mass (stabilityInventory k s v.val) (bucket a) = v.val (.inr a)
    have := stability_inventory_slack k s v hd a
    omega

lemma stability_encode_pairs (k : ℕ) (s : Fin 2) (x : Inventory)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0)
    (i : Source) (hi : i ∈ allPairs) :
    stabilityPairs s (stabilityEncode k s x) i = x i := by
  by_cases hs : i ∈ ordinary s
  · obtain ⟨j,rfl⟩ := stability_pair_complete s i (Finset.mem_inter.mpr ⟨hi,hs⟩)
    exact stability_pairs_at s (stabilityEncode k s x) j
  · have hz : x i = 0 := by
      by_contra h
      exact hs (pure_support x s ho hc i (by omega))
    have hne (j : Fin 12) : stabilityPair s j ≠ i := by
      intro h
      exact hs (h ▸ (Finset.mem_inter.mp (stability_pair_mem s j)).2)
    simp [stabilityPairs, pointInventory, hne, hz]

lemma stability_encode_pair_mass (k : ℕ) (s : Fin 2) (x : Inventory)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0) :
    (∑ j, x (stabilityPair s j)) = mass x allPairs := by
  have h : mass (stabilityPairs s (stabilityEncode k s x)) allPairs = mass x allPairs := by
    apply Finset.sum_congr rfl
    exact stability_encode_pairs k s x ho hc
  rw [stability_pairs_mass] at h
  simpa only [show ∀ j, stabilityPair s j ∈ allPairs from
    fun j => (Finset.mem_inter.mp (stability_pair_mem s j)).1,
    ite_true, stabilityEncode, Sum.elim_inl] using h

lemma stability_encode_sum (k : ℕ) (s : Fin 2) (x : Inventory) {d : ℕ}
    (ht : total x + d = 16*k+28)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0)
    (hb : ∀ a, mass x (bucket a) ≤ 4*k+7) : ∑ i, stabilityEncode k s x i = d := by
  rw [Fintype.sum_sum_type]
  simp only [stabilityEncode, Sum.elim_inl, Sum.elim_inr]
  rw [stability_encode_pair_mass k s x ho hc]
  have htot := totals x
  have htr := triple_totals x
  have hpa := pair_totals x
  have hbt := bucket_totals x
  norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at htr hpa hbt hb ⊢
  omega

lemma stability_inventory_encode (k : ℕ) (s : Fin 2) (x : Inventory)
    (ho : mass x (ordinary (flip s)) = 0) (hc : mass x allCheckers = 0)
    (hb : ∀ a, mass x (bucket a) ≤ 4*k+7) :
    stabilityInventory k s (stabilityEncode k s x) = x := by
  have hpair : ∀ a, mass (stabilityPairs s (stabilityEncode k s x)) (bucket a) = mass x (pair a) := by
    intro a
    rw [stability_pairs_mass]
    have hm : ∀ s j a, stabilityPair s j ∈ bucket a ↔ stabilityPair s j ∈ pair a := by decide +kernel
    simp only [hm]
    rw [← stability_pairs_mass]
    apply Finset.sum_congr rfl
    intro i hi
    have hsub : ∀ a, pair a ⊆ allPairs := by decide +kernel
    exact stability_encode_pairs k s x ho hc i (hsub a hi)
  obtain ⟨hyo,hyc⟩ := stability_inventory_zero_pools k s (stabilityEncode k s x)
  apply pure_inventory_ext _ x s hyo hyc ho hc
  · intro i hi
    have hn : ∀ a, stabilityTriple s a ≠ i := by
      intro a h
      exact stability_triple_not_pair s a (h ▸ hi)
    simp only [stabilityInventory, pointInventory, hn, ite_false, Finset.sum_const_zero, Nat.add_zero]
    exact stability_encode_pairs k s x ho hc i hi
  · intro a
    have hbt := bucket_totals x a
    have hcap := hb a
    have hsum := bucket_totals (stabilityInventory k s (stabilityEncode k s x)) a
    have hp : mass (stabilityInventory k s (stabilityEncode k s x)) (pair a) = mass x (pair a) := by
      rw [stability_inventory_mass]
      have hn : ∀ b, stabilityTriple s b ∉ pair a := by
        intro b h
        have hsub : ∀ a, pair a ⊆ allPairs := by decide +kernel
        exact stability_triple_not_pair s b (hsub a h)
      simp only [hn, ite_false, Finset.sum_const_zero, Nat.add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      have hsub : ∀ a, pair a ⊆ allPairs := by decide +kernel
      exact stability_encode_pairs k s x ho hc i (hsub a hi)
    rw [stability_inventory_bucket] at hsum
    rw [hp] at hsum
    unfold stabilityCost at hsum
    rw [hpair] at hsum
    simp only [stabilityEncode, Sum.elim_inr] at hsum
    simp only [stabilityEncode] at *
    omega

end ThreeColour
