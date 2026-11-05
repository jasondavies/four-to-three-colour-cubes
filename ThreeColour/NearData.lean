module
public import ThreeColour.FrameTheorems
@[expose] public section
namespace ThreeColour
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The eight T and twenty-four P varieties. -/
def nearSupport : SourceSet :=
  letI : NeZero 2 := frameFinTwo
  ordinary 0 ∪ ordinary 1

/-- One parameter for each of the eight T and twenty-four P varieties. -/
abbrev NearParameter := {i : Source // i ∈ nearSupport}

def nearOrientation (p : NearParameter) : Fin 2 :=
  letI : NeZero 2 := frameFinTwo
  if p.val ∈ ordinary 0 then 0 else 1

/-- A T parameter deletes that T; a P parameter lowers its two T buckets
and inserts the parameter itself. This is the twenty-seven-cube case. -/
def nearBase (p : NearParameter) : Inventory := fun i =>
  if i ∈ extremalSupport (nearOrientation p) then
    7 - if ∃ a : Colour, i ∈ triple a ∧ p.val ∈ bucket a then 1 else 0
  else if p.val ∈ allPairs ∧ i = p.val then 1 else 0

/-- Increase each of the four T multiplicities by `4k`, where `n=k+2`. -/
def nearInventory (k : ℕ) (p : NearParameter) : Inventory := fun i =>
  nearBase p i + if i ∈ extremalSupport (nearOrientation p) then 4*k else 0

lemma near_parameter_card : Fintype.card NearParameter = 32 := by decide +kernel
lemma near_orientation_mem : ∀ p : NearParameter, p.val ∈ ordinary (nearOrientation p) := by decide +kernel
lemma near_orientation_eq : ∀ p : NearParameter, ∀ s, p.val ∈ ordinary s → nearOrientation p = s := by decide +kernel
lemma near_base_injective : Function.Injective nearBase := by decide +kernel
lemma near_base_total : ∀ p, total (nearBase p) = 27 := by decide +kernel
lemma near_base_triple : ∀ p a, mass (nearBase p) (triple a) =
    7 - if p.val ∈ bucket a then 1 else 0 := by decide +kernel
lemma near_base_pair : ∀ p a, mass (nearBase p) (pair a) =
    if p.val ∈ allPairs ∧ p.val ∈ bucket a then 1 else 0 := by decide +kernel
lemma near_base_pairs : ∀ p i, i ∈ allPairs → nearBase p i =
    if p.val ∈ allPairs ∧ i = p.val then 1 else 0 := by decide +kernel
lemma near_base_outside : ∀ p i, i ∉ ordinary (nearOrientation p) → nearBase p i = 0 := by decide +kernel
lemma near_support_triples : ∀ s i, i ∈ extremalSupport s → i ∈ allTriples := by decide +kernel
lemma near_base_zero_triple : ∀ p i, i ∈ allTriples → i ∉ extremalSupport (nearOrientation p) → nearBase p i = 0 := by decide +kernel
lemma near_support_disjoint : ∀ s, Disjoint (extremalSupport s) allPairs := by decide +kernel
lemma near_ordinary_disjoint : ∀ s, Disjoint (ordinary s) (ordinary (flip s)) ∧ Disjoint (ordinary s) allCheckers := by decide +kernel
lemma ordinary_parameter : ∀ s i, i ∈ ordinary s → i ∈ ordinary 0 ∪ ordinary 1 := by decide +kernel
lemma near_triple_parameter : ∀ a s, ∃ p : NearParameter,
    nearOrientation p = s ∧ p.val ∈ allTriples ∧
    (∀ b, p.val ∈ bucket b ↔ b = a) := by decide +kernel
lemma triple_pair_disjoint : Disjoint allTriples allPairs := by decide +kernel

lemma near_mass (k : ℕ) (p : NearParameter) (g : SourceSet) :
    mass (nearInventory k p) g = mass (nearBase p) g +
      (g ∩ extremalSupport (nearOrientation p)).card * (4*k) := by
  simp only [mass, nearInventory, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter]

lemma near_total (k : ℕ) (p : NearParameter) : total (nearInventory k p) = 16*k+27 := by
  rw [total, near_mass, Finset.univ_inter, extremalSupport_card]
  change total (nearBase p) + 4*(4*k) = _
  rw [near_base_total]; omega

lemma near_triple (k : ℕ) (p : NearParameter) (a : Colour) :
    mass (nearInventory k p) (triple a) = 4*k+7 - if p.val ∈ bucket a then 1 else 0 := by
  rw [near_mass, near_base_triple, Finset.inter_comm, extremalSupport_triple_card]
  split_ifs <;> simp_all <;> omega

lemma near_pair (k : ℕ) (p : NearParameter) (a : Colour) :
    mass (nearInventory k p) (pair a) = if p.val ∈ allPairs ∧ p.val ∈ bucket a then 1 else 0 := by
  have hz : ∀ a s, pair a ∩ extremalSupport s = ∅ := by decide +kernel
  rw [near_mass, hz]; simpa using near_base_pair p a

lemma near_pairs (k : ℕ) (p : NearParameter) (i : Source) (hi : i ∈ allPairs) :
    nearInventory k p i = if p.val ∈ allPairs ∧ i = p.val then 1 else 0 := by
  have hn : i ∉ extremalSupport (nearOrientation p) := fun h =>
    Finset.disjoint_left.mp (near_support_disjoint _) h hi
  simp only [nearInventory, ite_eq_right hn, Nat.add_zero, near_base_pairs p i hi]

lemma near_outside (k : ℕ) (p : NearParameter) (i : Source)
    (hi : i ∉ ordinary (nearOrientation p)) : nearInventory k p i = 0 := by
  have hs : ∀ s, extremalSupport s ⊆ ordinary s := by decide +kernel
  have hn : i ∉ extremalSupport (nearOrientation p) := fun h => hi (hs _ h)
  simp [nearInventory, hn, near_base_outside p i hi]

lemma near_pure (k : ℕ) (p : NearParameter) :
    mass (nearInventory k p) (ordinary (flip (nearOrientation p))) = 0 ∧
    mass (nearInventory k p) allCheckers = 0 := by
  obtain ⟨ho,hc⟩ := near_ordinary_disjoint (nearOrientation p)
  constructor <;> apply Finset.sum_eq_zero <;> intro i hi
  · exact near_outside k p i (fun h => Finset.disjoint_left.mp ho h hi)
  · exact near_outside k p i (fun h => Finset.disjoint_left.mp hc h hi)

lemma near_bucket (k : ℕ) (p : NearParameter) (a : Colour) :
    mass (nearInventory k p) (bucket a) ≤ 4*k+7 := by
  rw [bucket_totals, near_triple, near_pair]
  split_ifs <;> simp_all

lemma near_inventory_injective (k : ℕ) : Function.Injective (nearInventory k) := by
  have recover (p : NearParameter) (i : Source) :
      nearInventory k p i - (if i ∈ allTriples then 4*k else 0) = nearBase p i := by
    by_cases hs : i ∈ extremalSupport (nearOrientation p)
    · simp [nearInventory, hs, near_support_triples _ _ hs]
    · by_cases ht : i ∈ allTriples
      · simp [nearInventory, hs, ht, near_base_zero_triple p i ht hs]
      · simp [nearInventory, hs, ht]
  intro p q h
  apply near_base_injective
  funext i
  rw [← recover p i, ← recover q i, h]

/-- The explicitly listed set of near-extremal inventories. -/
def nearInventories (k : ℕ) : Finset Inventory := Finset.univ.image (nearInventory k)

theorem near_inventories_card (k : ℕ) : (nearInventories k).card = 32 := by
  rw [nearInventories, Finset.card_image_of_injective _ (near_inventory_injective k)]
  exact near_parameter_card

end ThreeColour
