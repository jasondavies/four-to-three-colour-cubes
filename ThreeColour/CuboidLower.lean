module

public import ThreeColour.CheckerboardLower
public import ThreeColour.FrameFamily
public import ThreeColour.InventoryFamily
public import ThreeColour.CuboidBounds

@[expose] public section
namespace ThreeColour

lemma boxFrame_requires_pieces {n : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin n → Fin 6 → Colour) (h : FamilyBoxFrameSolvable l cubes) :
    8+4*(l 0+l 1+l 2) ≤ n := by
  obtain ⟨_,_,p,_⟩ := h
  simpa only [boxFrameSlot_card,Fintype.card_fin] using Fintype.card_le_of_embedding p

/-- All three lower bounds, with arbitrary physical inventories as the universal quantifier. -/
theorem cuboid_frame_lower (a b c v : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hv : ∀ n, ∀ cubes : Fin n → Fin 6 → Colour, (∀ j, Uses 4 (cubes j)) →
      v ≤ n → FamilyBoxFrameSolvable ![a-2,b-2,c-2] cubes) : Cuboid.threshold a b c ≤ v := by
  apply Cuboid.threshold_le.mpr
  refine ⟨?_,?_,?_⟩
  · by_contra h
    have hs := hv _ (inventoryFamily (frameExtremal (a-2) 0))
      (inventoryFamily_uses_four _) (by rw [frameExtremal_total]; omega)
    have hf : FamilyFrameSolvable (a-2) (inventoryFamily (frameExtremal (a-2) 0)) :=
      boxFrame_mono (by intro i; fin_cases i <;> simp <;> omega) _ hs
    have hi := (familyFrame_iff _ _ (inventoryFamily_uses_four _)).mp hf
    rw [inventoryFamily_inventory] at hi
    exact frameExtremal_not_solvable (a-2) 0 hi
  · let cubes : Fin v → Fin 6 → Colour := fun _ => sourceFaces 0
    have h := boxFrame_requires_pieces _ cubes (hv v cubes (fun _ => sources_use_four 0) le_rfl)
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h
    omega
  · by_contra h
    apply checker_rod_obstruction c (by omega)
    apply boxFrame_mono _ _ (hv _ _ (checkerFamily_uses _) (by omega))
    intro i; fin_cases i <;> simp

lemma cuboid_frame_le_volume (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    4*(a+b+c)-16 ≤ a*b*c := by
  obtain ⟨x,rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y,rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le hc
  have he : 4*(2+x+(2+y)+(2+z))-16 = 8+4*(x+y+z) := by omega
  rw [he]
  nlinarith [Nat.zero_le (x*y*z),Nat.zero_le (x*y),Nat.zero_le (x*z),Nat.zero_le (y*z)]

end ThreeColour
