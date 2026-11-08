module
public import ThreeColour.BoxModel
@[expose] public section
namespace ThreeColour

abbrev FullSlot (k : ℕ) := BoxFullSlot (fun _ => k)
abbrev FamilyFullSolvable {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour) :=
  FamilyBoxFullSolvable (fun _ => k) cubes

lemma fullSlot_card (k : ℕ) : Fintype.card (FullSlot k) = (k+2)^3 := by
  simpa only [FullSlot, pow_succ, pow_zero, Nat.one_mul] using boxFullSlot_card (fun _ => k)

theorem full_iff_frame_and_size {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilyFullSolvable k cubes ↔
      FamilyFrameSolvable k cubes ∧ (k+2)^3 ≤ m := by
  simpa only [pow_succ, pow_zero, Nat.one_mul] using boxFull_iff_frame_and_size (fun _ => k) cubes hc

end ThreeColour
