module
public import ThreeColour.CuboidResults
@[expose] public section
namespace ThreeColour

/-- Sharp frame threshold for rods. -/
theorem rod_frame_threshold (l : ℕ) (hl : 2 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFrameSolvable ![0,0,l-2] cubes}
      (max 29 ((24*l-1)/5)) := by
  have h := cuboid_frame_threshold 2 2 l (by omega) le_rfl hl
  have hb : max (max (16*2-3) (4*(2+2+l)-16)) ((24*l-1)/5) = max 29 ((24*l-1)/5) := by omega
  simpa only [hb, Nat.reduceSub] using h

/-- Sharp frame threshold for strips. -/
theorem strip_frame_threshold (l : ℕ) (hl : 3 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFrameSolvable ![0,1,l-2] cubes}
      (max 29 ((24*l-1)/5)) := by
  have h := cuboid_frame_threshold 2 3 l (by omega) (by omega) hl
  have hb : max (max (16*2-3) (4*(2+3+l)-16)) ((24*l-1)/5) = max 29 ((24*l-1)/5) := by omega
  simpa only [hb, Nat.reduceSub] using h

/-- A complete rod has the same threshold as its frame. -/
theorem rod_full_threshold (l : ℕ) (hl : 2 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFullSolvable ![0,0,l-2] cubes}
      (max 29 ((24*l-1)/5)) := by
  have h := cuboid_full_threshold 2 2 l (by omega) le_rfl hl
  have hb : max (2*2*l) (max (16*2-3) ((24*l-1)/5)) = max 29 ((24*l-1)/5) := by omega
  simpa only [hb, Nat.reduceSub] using h

/-- A complete strip requires the corner threshold and its volume. -/
theorem strip_full_threshold (l : ℕ) (hl : 3 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFullSolvable ![0,1,l-2] cubes}
      (max 29 (6*l)) := by
  have h := cuboid_full_threshold 2 3 l (by omega) (by omega) hl
  have hb : max (2*3*l) (max (16*2-3) ((24*l-1)/5)) = max 29 (6*l) := by omega
  simpa only [hb, Nat.reduceSub] using h

/-- Strips of length at least five assemble from exactly their volume. -/
theorem strip_full_of_five_le (l : ℕ) (hl : 5 ≤ l)
    (cubes : Fin (6*l) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable ![0,1,l-2] cubes :=
  (strip_full_threshold l (by omega)).1 _ cubes hc (by omega)

end ThreeColour
