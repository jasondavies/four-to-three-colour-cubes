module
public import ThreeColour.FrameFamily
public import ThreeColour.FullCube
public import ThreeColour.InventoryFamily
@[expose] public section
namespace ThreeColour

lemma inventoryFamily_frame_obstruction (k : ℕ) (s : Fin 2) :
    ¬ FamilyFrameSolvable k (inventoryFamily (frameExtremal k s)) := by
  rw [familyFrame_iff k _ (inventoryFamily_uses_four _),inventoryFamily_inventory]
  exact frameExtremal_not_solvable k s

/-- Sharp frame threshold for arbitrary oriented cubes, with no source or target catalogue. -/
theorem family_frame_least_guaranteed_size (k : ℕ) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyFrameSolvable k cubes} (16*k+29) := by
  constructor
  · intro m cubes hc hm
    exact family_frame_threshold k cubes hc hm
  · intro v hv
    by_contra h
    apply inventoryFamily_frame_obstruction k 0
    exact hv _ _ (inventoryFamily_uses_four _) (by rw [frameExtremal_total]; omega)

/-- A frame can always be completed once enough pieces are present. -/
theorem family_full_threshold {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hm : max ((k+2)^3) (16*k+29) ≤ m) :
    FamilyFullSolvable k cubes := by
  have h := max_le_iff.mp hm
  exact full_of_frame k cubes hc h.1 (family_frame_threshold k cubes hc h.2)

/-- The exact complete-cube threshold is `max(n³,16n-3)`, where `n=k+2`. -/
theorem family_full_least_guaranteed_size (k : ℕ) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyFullSolvable k cubes}
      (max ((k+2)^3) (16*k+29)) := by
  constructor
  · intro m cubes hc hm
    exact family_full_threshold k cubes hc hm
  · intro v hv
    apply max_le
    · by_contra h
      let cubes : Fin ((k+2)^3-1) → Fin 6 → Colour := fun _ => sourceFaces 0
      have hc : ∀ j, Uses 4 (cubes j) := fun _ => sources_use_four 0
      have hs := hv _ cubes hc (by omega)
      have := full_requires_pieces k cubes hs
      have hpos : 0 < (k+2)^3 := pow_pos (by omega) 3
      omega
    · by_contra h
      apply inventoryFamily_frame_obstruction k 0
      exact frame_of_full k _ (hv _ _ (inventoryFamily_uses_four _) (by
        rw [frameExtremal_total]; omega))

lemma full_size_dominates (k : ℕ) (hk : 2 ≤ k) : 16*k+29 ≤ (k+2)^3 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  nlinarith [Nat.zero_le (l*l),Nat.zero_le (l*l*l)]

/-- For side length at least four, the number of pieces alone is sufficient. -/
theorem family_full_of_side_ge_four (k : ℕ) (hk : 2 ≤ k)
    (cubes : Fin ((k+2)^3) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyFullSolvable k cubes :=
  family_full_threshold k cubes hc (max_le le_rfl (full_size_dominates k hk))

end ThreeColour
