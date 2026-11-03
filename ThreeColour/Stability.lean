module
public import ThreeColour.NearClassification
public import ThreeColour.FrameFamily
@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- The structural obstruction: one ordinary orientation and four bounded buckets. -/
def PureBuckets (k : ℕ) (x : Inventory) : Prop :=
  ∃ s : Fin 2, (∀ i, 0 < x i → i ∈ ordinary s) ∧
    ∀ a, mass x (bucket a) ≤ 4*k+7

/-- Stability throughout the band `N ≥ 14n`, where `n=k+2 ≥ 3`. -/
theorem frame_stability (k : ℕ) (hk : 1 ≤ k) (x : Inventory)
    (ht : 14*k+28 ≤ total x) : ¬ FrameSolvable k x ↔ PureBuckets k x := by
  constructor
  · intro hn
    obtain ⟨s,hs⟩ := exists_major_orientation x
    obtain ⟨ho,hc,hb⟩ := frame_failure_bounds k hk x hn ht s hs
    exact ⟨s, pure_support x s ho hc, hb⟩
  · rintro ⟨s,hs,hb⟩
    exact pure_bucket_not_solvable k x s hs hb

/-- The same criterion for arbitrary physical source families; rotation classes
are used only to state the structural classification. -/
theorem family_frame_stability {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hm : 14*n ≤ m) :
    ¬ FamilyFrameSolvable (n-2) cubes ↔ PureBuckets (n-2) (familyInventory cubes) := by
  rw [familyFrame_iff (n-2) cubes hc]
  apply frame_stability (n-2) (by omega)
  rw [familyInventory_total]
  omega

end ThreeColour
