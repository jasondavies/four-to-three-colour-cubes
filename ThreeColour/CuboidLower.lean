module

public import ThreeColour.ThinResults
public import ThreeColour.FrameResults
public import ThreeColour.CuboidBounds

@[expose] public section
namespace ThreeColour

/-- The equal-sided box model restricts to the existing physical cube-frame model. -/
lemma cubeFrame_of_box {n : ℕ} (k : ℕ) (cubes : Fin n → Fin 6 → Colour)
    (h : FamilyBoxFrameSolvable (fun _ => k) cubes) : FamilyFrameSolvable k cubes := by
  obtain ⟨t,ht,p,hp⟩ := h
  let e : FrameSlot k ↪ BoxFrameSlot (fun _ => k) :=
    Function.Embedding.sumMap (Function.Embedding.refl _)
      (Equiv.sigmaEquivProd (Fin 12) (Fin k)).symm.toEmbedding
  refine ⟨t,ht,e.trans p,?_⟩
  intro q
  cases q <;> exact hp _

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
  · apply (frame_threshold_n a ha).2
    intro n cubes hc hn
    apply cubeFrame_of_box (a-2) cubes
    apply boxFrame_mono _ cubes (hv n cubes hc hn)
    intro i; fin_cases i <;> simp <;> omega
  · let cubes : Fin v → Fin 6 → Colour := fun _ => sourceFaces 0
    have h := boxFrame_requires_pieces _ cubes (hv v cubes (fun _ => sources_use_four 0) le_rfl)
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h
    omega
  · by_contra h
    apply checker_rod_obstruction c (by omega)
    apply boxFrame_mono _ _ (hv _ _ (thinCheckerFamily_uses _) (by omega))
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
