module

public import ThreeColour.CuboidUpper
public import ThreeColour.CuboidLower

@[expose] public section
namespace ThreeColour

/-- Sharp frame threshold for every cuboid with ordered side lengths at least two.
The statement quantifies over arbitrary physical cubes and preserves distinct copies,
proper rotations and exactly three exterior colours. -/
theorem cuboid_frame_threshold (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    IsLeast {v : ℕ | ∀ n, ∀ cubes : Fin n → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ n → FamilyBoxFrameSolvable ![a-2,b-2,c-2] cubes}
      (max (max (16*a-3) (4*(a+b+c)-16)) ((24*c-1)/5)) := by
  constructor
  · intro n cubes hc hn
    exact family_cuboid_upper a b c ha hab hbc cubes hc hn
  · intro v hv
    exact cuboid_frame_lower a b c v ha hab hbc hv

/-- Complete boxes require the volume and the two geometric obstruction bounds. -/
theorem cuboid_full_threshold (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    IsLeast {v : ℕ | ∀ n, ∀ cubes : Fin n → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ n → FamilyBoxFullSolvable ![a-2,b-2,c-2] cubes}
      (max (a*b*c) (max (16*a-3) ((24*c-1)/5))) := by
  have hb : 2 ≤ b := by omega
  have hc : 2 ≤ c := by omega
  have hvolume := cuboid_frame_le_volume a b c ha hb hc
  constructor
  · intro n cubes hcol hn
    have hframe : Cuboid.threshold a b c ≤ n := by
      rw [Cuboid.threshold_le]
      omega
    apply boxFull_of_frame _ cubes hcol _ (family_cuboid_upper a b c ha hab hbc cubes hcol hframe)
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Nat.sub_add_cancel ha,Nat.sub_add_cancel hb,Nat.sub_add_cancel hc] using (show a*b*c ≤ n by omega)
  · intro v hv
    have hl := cuboid_frame_lower a b c v ha hab hbc (fun n cubes hcol hn =>
      boxFrame_of_full _ cubes (hv n cubes hcol hn))
    have hbds := Cuboid.threshold_le.mp hl
    let cubes : Fin v → Fin 6 → Colour := fun _ => sourceFaces 0
    have hsize := boxFull_requires_pieces _ cubes (hv v cubes (fun _ => sources_use_four 0) le_rfl)
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Nat.sub_add_cancel ha,Nat.sub_add_cancel hb,Nat.sub_add_cancel hc] at hsize
    omega

/-- Precisely the aspect ratios at which every frame can use all its supplied pieces. -/
theorem cuboid_frame_exact_cardinality (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    Cuboid.threshold a b c = 4*(a+b+c)-16 ↔ 3*a+4 ≤ b+c ∧ c ≤ 5*(a+b)-19 := by
  have hh := Cuboid.exact_cardinality a b c ha hab hbc
  unfold Cuboid.threshold
  omega

/-- Exact-volume assembly whenever the two geometric lower bounds fit inside the volume. -/
theorem family_cuboid_full_of_volume (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hshort : 16*a-3 ≤ a*b*c) (hlong : (24*c-1)/5 ≤ a*b*c)
    (cubes : Fin (a*b*c) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable ![a-2,b-2,c-2] cubes :=
  (cuboid_full_threshold a b c ha hab hbc).1 _ cubes hc (by omega)

/-- The complete-box exceptions are exactly rods and the four small non-rod shapes.
For ordered sides, this is equivalent to requiring b ≥ 3 and either b ≥ 4 or c ≥ 5. -/
theorem cuboid_full_exact_volume (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    max (a*b*c) (max (16*a-3) ((24*c-1)/5)) = a*b*c ↔
      3 ≤ b ∧ (4 ≤ b ∨ 5 ≤ c) := by
  have hb : 2 ≤ b := by omega
  constructor
  · intro h
    have hshort : 16*a-3 ≤ a*b*c := by omega
    have hlong : (24*c-1)/5 ≤ a*b*c := by omega
    have hb3 : 3 ≤ b := by
      by_contra hn
      have hb2 : b=2 := by omega
      have ha2 : a=2 := by omega
      subst a; subst b
      norm_num at hlong
      omega
    refine ⟨hb3,?_⟩
    by_contra hn
    push Not at hn
    have hb3' : b=3 := by omega
    subst b
    have hc4 : c ≤ 4 := by omega
    interval_cases a <;> interval_cases c <;> norm_num at hshort
  · rintro ⟨hb3,hcase⟩
    have hab6 : 6 ≤ a*b := by nlinarith
    have hvol : 6*c ≤ a*b*c := Nat.mul_le_mul_right c hab6
    have hlong : (24*c-1)/5 ≤ a*b*c := by omega
    have hshort : 16*a-3 ≤ a*b*c := by
      rcases hcase with hb4 | hc5
      · have hprod : 16 ≤ b*c := by nlinarith
        have hmul := Nat.mul_le_mul_left a hprod
        rw [← Nat.mul_assoc] at hmul
        omega
      · by_cases hb4 : 4 ≤ b
        · have hprod : 16 ≤ b*c := by nlinarith
          have hmul := Nat.mul_le_mul_left a hprod
          rw [← Nat.mul_assoc] at hmul
          omega
        · have hb3' : b=3 := by omega
          subst b
          interval_cases a <;> norm_num <;> omega
    omega

end ThreeColour
