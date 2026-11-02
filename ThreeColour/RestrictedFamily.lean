module

public import ThreeColour.Family

@[expose] public section

namespace ThreeColour

/-- A physical solution with a target of type Q, R, or D. No catalogue appears
in this definition: the sources, target, and rotations are face maps. -/
def FamilyRestrictedSolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Prop :=
  ∃ target : Fin 6 → Colour, RestrictedTarget target ∧ Uses 3 target ∧
    ∃ placement : Fin 8 ↪ Fin n, ∀ k,
      ∃ r : Fin 6 → Fin 6, MacMahon.ProperRotation r ∧
        ∀ axis : Fin 3, cubes (placement k) (r (MacMahon.exposedFaces k axis)) =
          target (MacMahon.exposedFaces k axis)

lemma familyRestrictedSolvable_of_inventory {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j))
    (h : RestrictedSolvable (familyInventory cubes)) : FamilyRestrictedSolvable cubes := by
  obtain ⟨t, ht, p, hp⟩ := h
  exact ⟨targetFaces t, ht, targets_use_three t,
    familyBuilds_of_physical cubes hc t p (fun k => (fits_physical t k _).mp (hp k))⟩

/-- At least 29 cubes guarantee a target in the three named families. -/
theorem family_restricted_of_29_le {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hn : 29 ≤ n) : FamilyRestrictedSolvable cubes := by
  apply familyRestrictedSolvable_of_inventory cubes hc
  exact restricted_solvable_of_29_le _ (by simpa only [familyInventory_total] using hn)

theorem family_restricted_threshold29 (cubes : Fin 29 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilyRestrictedSolvable cubes :=
  family_restricted_of_29_le cubes hc le_rfl

/-- At size 28, solvability is already witnessed by one of Q, R, or D. -/
theorem family_restricted_of_solvable28 (cubes : Fin 28 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (h : FamilySolvable cubes) :
    FamilyRestrictedSolvable cubes := by
  apply familyRestrictedSolvable_of_inventory cubes hc
  exact restricted_of_solvable28 _ (familyInventory_total cubes)
    ((solvable_iff_physical _).mpr ((family_solvable_iff cubes hc).mp h))

end ThreeColour
