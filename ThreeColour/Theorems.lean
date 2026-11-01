module

public import ThreeColour.Classification
public import ThreeColour.Physical
public import ThreeColour.Catalogue
public import ThreeColour.Reflection
public import ThreeColour.Uniqueness

@[expose] public section

namespace ThreeColour
/-- The 29-cube theorem, with explicit proper rotations at all eight positions. -/
theorem physical_threshold29 (x : Inventory) (ht : total x = 29) : PhysicalSolvable x :=
  (solvable_iff_physical x).mp (threshold29 x ht)

/-- The complete extremal classification, in the physical matching model. -/
theorem physical_classify28 (x : Inventory) (ht : total x = 28) :
    ¬ PhysicalSolvable x ↔ x = extremal 0 ∨ x = extremal 1 := by
  rw [← solvable_iff_physical, classify28 x ht]
  simp [Fin.exists_fin_succ]

/-- A sufficient collection size and an explicit obstruction immediately below it. -/
theorem sharp_threshold29 :
    (∀ x : Inventory, total x = 29 → PhysicalSolvable x) ∧
    ∃ x : Inventory, total x = 28 ∧ ¬ PhysicalSolvable x := by
  refine ⟨physical_threshold29, extremal 0, extremal_total 0, ?_⟩
  rw [← solvable_iff_physical]
  exact extremal_not_solvable 0
/-- Twenty-nine is the least size guaranteeing a solution for every larger multiset. -/
theorem least_guaranteed_size :
    IsLeast {n : ℕ | ∀ x : Inventory, n ≤ total x → PhysicalSolvable x} 29 := by
  constructor
  · intro x hx
    exact (solvable_iff_physical x).mp (solvable_of_29_le x hx)
  · intro n hn
    by_contra h
    have hc := hn (extremal 0) (by rw [extremal_total]; omega)
    exact extremal_not_solvable 0 ((solvable_iff_physical _).mpr hc)
end ThreeColour

