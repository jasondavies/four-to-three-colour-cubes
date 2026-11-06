module

public import ThreeColour.ThinUpper
public import ThreeColour.ThinLower

@[expose] public section
namespace ThreeColour

lemma boxFrame_zero_of_corners {m : ℕ} (cubes : Fin m → Fin 6 → Colour)
    (h : FamilySolvable cubes) : FamilyBoxFrameSolvable ![0,0,0] cubes := by
  obtain ⟨t,ht,p,hp⟩ := h
  have hz : (![0,0,0] : Fin 3 → ℕ) = fun _ => 0 := by decide
  rw [hz]
  let f : BoxFrameSlot (fun _ => 0) ↪ Fin m :=
    ⟨Sum.elim p (fun q => Fin.elim0 q.2), by
      intro a b hab
      cases a with
      | inl a => cases b with
        | inl b => exact congrArg Sum.inl (p.injective hab)
        | inr b => exact Fin.elim0 b.2
      | inr a => exact Fin.elim0 a.2⟩
  refine ⟨t,ht,f,?_⟩
  intro q
  cases q with
  | inl q =>
    obtain ⟨r,hr,hh⟩ := hp q
    refine ⟨r,hr,?_⟩
    intro f hf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hf
    exact hh a
  | inr q => exact Fin.elim0 q.2

/-- Rods inherit the strip construction; length two is the established corner theorem. -/
theorem family_rod_upper {m : ℕ} (l : ℕ) (hl : 2 ≤ l)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hm : Thin.threshold l ≤ m) : FamilyBoxFrameSolvable ![0,0,l-2] cubes := by
  by_cases h3 : 3 ≤ l
  · exact boxFrame_mono (by intro i; fin_cases i <;> simp) cubes
      (family_strip_upper l h3 cubes hc hm)
  · have hl2 : l = 2 := by omega
    subst l
    apply boxFrame_zero_of_corners
    exact family_solvable_of_29_le cubes hc (by simpa [Thin.threshold] using hm)

/-- Sharp rod frame threshold, quantified over arbitrary physical source families. -/
theorem rod_frame_threshold (l : ℕ) (hl : 2 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFrameSolvable ![0,0,l-2] cubes}
      (Thin.threshold l) := by
  constructor
  · intro m cubes hc hm
    exact family_rod_upper l hl cubes hc hm
  · intro v hv
    unfold Thin.threshold
    apply max_le
    · by_contra h
      exact lowerFamily_not_solvable (boxFrame_corners _ _
        (hv 28 lowerFamily lowerFamily_uses_four (by omega)))
    · by_contra h
      exact checker_rod_obstruction l hl (hv _ _ (thinCheckerFamily_uses _) (by omega))

/-- Sharp strip frame threshold, with exactly three exterior colours. -/
theorem strip_frame_threshold (l : ℕ) (hl : 3 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFrameSolvable ![0,1,l-2] cubes}
      (Thin.threshold l) := by
  constructor
  · intro m cubes hc hm
    exact family_strip_upper l hl cubes hc hm
  · intro v hv
    apply (rod_frame_threshold l (by omega)).2
    intro m cubes hc hm
    exact boxFrame_mono (by intro i; fin_cases i <;> simp) cubes (hv m cubes hc hm)

/-- A rod's complete assembly has the same sharp threshold as its frame. -/
theorem rod_full_threshold (l : ℕ) (hl : 2 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFullSolvable ![0,0,l-2] cubes}
      (Thin.threshold l) := by
  constructor
  · intro m cubes hc hm
    apply boxFull_of_frame _ cubes hc _ (family_rod_upper l hl cubes hc hm)
    have hsp := (Thin.threshold_bounds hl hm).2.1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Nat.zero_add, Nat.sub_add_cancel hl]
    omega
  · intro v hv
    apply (rod_frame_threshold l hl).2
    intro m cubes hc hm
    exact boxFrame_of_full _ cubes (hv m cubes hc hm)

/-- Complete strips require only the corner threshold and their volume. -/
theorem strip_full_threshold (l : ℕ) (hl : 3 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFullSolvable ![0,1,l-2] cubes}
      (max 29 (6*l)) := by
  have hl2 : 2 ≤ l := by omega
  constructor
  · intro m cubes hc hm
    have hframe : Thin.threshold l ≤ m := by
      rw [← Thin.strip_completion] at hm
      exact (max_le_iff.mp hm).2
    apply boxFull_of_frame _ cubes hc _ (family_strip_upper l hl cubes hc hframe)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Nat.zero_add, Nat.sub_add_cancel hl2]
    omega
  · intro v hv
    apply max_le
    · by_contra h
      exact lowerFamily_not_solvable (boxFrame_corners _ _ (boxFrame_of_full _ _
        (hv 28 lowerFamily lowerFamily_uses_four (by omega))))
    · by_contra h
      let cubes : Fin (6*l-1) → Fin 6 → Colour := fun _ => sourceFaces 0
      have hc : ∀ j, Uses 4 (cubes j) := fun _ => sources_use_four 0
      have hs := boxFull_requires_pieces _ cubes (hv _ cubes hc (by omega))
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Nat.zero_add, Nat.sub_add_cancel hl2] at hs
      omega

theorem strip_full_of_five_le (l : ℕ) (hl : 5 ≤ l)
    (cubes : Fin (6*l) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable ![0,1,l-2] cubes :=
  (strip_full_threshold l (by omega)).1 _ cubes hc (by omega)

end ThreeColour
