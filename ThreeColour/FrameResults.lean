module
public import ThreeColour.FrameThresholds
public import ThreeColour.Reflection
@[expose] public section
namespace ThreeColour

lemma edge_faces_geometry :
    (∀ e : Fin 12, (edgeFaces e 0).val / 2 ≠ (edgeFaces e 1).val / 2) ∧
    Function.Injective (fun e : Fin 12 => ({edgeFaces e 0,edgeFaces e 1} : Finset (Fin 6))) ∧
    (∀ f g : Fin 6, f.val / 2 ≠ g.val / 2 →
      ∃ e : Fin 12, ({f,g} : Finset (Fin 6)) = {edgeFaces e 0,edgeFaces e 1}) := by
  decide +kernel

lemma frame_extremal_distinct (k : ℕ) : frameExtremal k 0 ≠ frameExtremal k 1 := by
  intro h
  have h0 : (10 : Source) ∈ extremalSupport 0 := by decide +kernel
  have h1 : (10 : Source) ∉ extremalSupport 1 := by decide +kernel
  have hi := congrFun h 10
  simp only [frameExtremal,ite_eq_left h0,ite_eq_right h1] at hi
  omega

lemma reflect_frame_extremal (k : ℕ) (s : Fin 2) :
    reflectInventory (frameExtremal k s) = frameExtremal k (flip s) := by
  have h : ∀ s i, reflection i ∈ extremalSupport s ↔ i ∈ extremalSupport (flip s) := by
    decide +kernel
  funext i
  simp only [reflectInventory,frameExtremal,h]

/-- The sharp frame threshold in terms of the actual side length. -/
theorem frame_threshold_n (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyFrameSolvable (n-2) cubes} (16*n-3) := by
  have h : 16*(n-2)+29 = 16*n-3 := by omega
  simpa only [h] using family_frame_least_guaranteed_size (n-2)

/-- The sharp complete-cube threshold in terms of the actual side length. -/
theorem full_threshold_n (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyFullSolvable (n-2) cubes}
      (max (n^3) (16*n-3)) := by
  have h : 16*(n-2)+29 = 16*n-3 := by omega
  have hn' : n-2+2 = n := by omega
  simpa only [h,hn'] using family_full_least_guaranteed_size (n-2)

theorem full_cube_of_four_le (n : ℕ) (hn : 4 ≤ n)
    (cubes : Fin (n^3) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyFullSolvable (n-2) cubes := by
  have hn' : n-2+2 = n := by omega
  have h := family_full_of_side_ge_four (n-2) (by omega)
  rw [hn'] at h
  exact h cubes hc

end ThreeColour
