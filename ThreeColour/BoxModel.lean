module

public import ThreeColour.FullCube

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Coordinate direction parallel to each geometric edge. -/
def boxEdgeAxis : Fin 12 → Fin 3 := ![2,2,1,1,2,2,1,1,0,0,0,0]

/-- `l i` counts the positions strictly between corners along axis `i`. -/
abbrev BoxFrameSlot (l : Fin 3 → ℕ) := Slot ⊕ (Σ e : Fin 12, Fin (l (boxEdgeAxis e)))

def boxFrameExposed (l : Fin 3 → ℕ) : BoxFrameSlot l → Finset (Fin 6)
  | .inl p => Finset.univ.image (ColourCubes.exposedFaces p)
  | .inr p => {edgeFaces p.1 0, edgeFaces p.1 1}

/-- A physical frame in a fixed coordinate system. The target is arbitrary, so
all assignments of colours and opposite face pairs to the axes are permitted. -/
def FamilyBoxFrameSolvable {m : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin m → Fin 6 → Colour) : Prop :=
  ∃ t : Fin 6 → Colour, Uses 3 t ∧ ∃ p : BoxFrameSlot l ↪ Fin m,
    ∀ q, FacesFit (cubes (p q)) t (boxFrameExposed l q)

lemma boxFrameSlot_card (l : Fin 3 → ℕ) :
    Fintype.card (BoxFrameSlot l) = 8 + 4 * (l 0 + l 1 + l 2) := by
  unfold BoxFrameSlot
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp [boxEdgeAxis, Fin.sum_univ_succ]
  omega

/-- Restricting the length of any edge preserves an existing frame assembly. -/
lemma boxFrame_mono {m : ℕ} {l k : Fin 3 → ℕ}
    (hkl : ∀ i, k i ≤ l i) (cubes : Fin m → Fin 6 → Colour)
    (h : FamilyBoxFrameSolvable l cubes) : FamilyBoxFrameSolvable k cubes := by
  obtain ⟨t, ht, p, hp⟩ := h
  let e : BoxFrameSlot k ↪ BoxFrameSlot l :=
    Function.Embedding.sumMap (Function.Embedding.refl _) (Function.Embedding.sigmaMap
      (Function.Embedding.refl _) (fun i => Fin.castLEEmb (hkl (boxEdgeAxis i))))
  refine ⟨t, ht, e.trans p, ?_⟩
  intro q
  cases q <;> exact hp _

lemma boxFrame_corners {m : ℕ} (l : Fin 3 → ℕ) (cubes : Fin m → Fin 6 → Colour)
    (h : FamilyBoxFrameSolvable l cubes) : FamilySolvable cubes := by
  obtain ⟨t, ht, p, hp⟩ := h
  refine ⟨t, ht, Function.Embedding.inl.trans p, ?_⟩
  intro q
  obtain ⟨r, hr, hf⟩ := hp (.inl q)
  exact ⟨r, hr, fun a => hf _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)⟩

/-- The free axes of a face interior. -/
def boxFaceAxis₁ : Fin 6 → Fin 3 := ![1,1,0,0,0,0]
def boxFaceAxis₂ : Fin 6 → Fin 3 := ![2,2,2,2,1,1]
abbrev BoxFillerSlot (l : Fin 3 → ℕ) :=
  (Σ f : Fin 6, Fin (l (boxFaceAxis₁ f)) × Fin (l (boxFaceAxis₂ f))) ⊕
    (Fin (l 0) × Fin (l 1) × Fin (l 2))
abbrev BoxFullSlot (l : Fin 3 → ℕ) := BoxFrameSlot l ⊕ BoxFillerSlot l

def boxFullExposed (l : Fin 3 → ℕ) : BoxFullSlot l → Finset (Fin 6)
  | .inl p => boxFrameExposed l p
  | .inr (.inl p) => {p.1}
  | .inr (.inr _) => ∅

def FamilyBoxFullSolvable {m : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin m → Fin 6 → Colour) : Prop :=
  ∃ t : Fin 6 → Colour, Uses 3 t ∧ ∃ p : BoxFullSlot l ↪ Fin m,
    ∀ q, FacesFit (cubes (p q)) t (boxFullExposed l q)

lemma boxFullSlot_card (l : Fin 3 → ℕ) :
    Fintype.card (BoxFullSlot l) = (l 0 + 2) * (l 1 + 2) * (l 2 + 2) := by
  unfold BoxFullSlot
  rw [Fintype.card_sum, boxFrameSlot_card]
  unfold BoxFillerSlot
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  simp [boxFaceAxis₁, boxFaceAxis₂, Fin.sum_univ_succ]
  ring

lemma boxFull_requires_pieces {m : ℕ} (l : Fin 3 → ℕ) (cubes : Fin m → Fin 6 → Colour)
    (h : FamilyBoxFullSolvable l cubes) : (l 0 + 2) * (l 1 + 2) * (l 2 + 2) ≤ m := by
  obtain ⟨_, _, p, _⟩ := h
  simpa only [boxFullSlot_card, Fintype.card_fin] using Fintype.card_le_of_embedding p

lemma boxFrame_of_full {m : ℕ} (l : Fin 3 → ℕ) (cubes : Fin m → Fin 6 → Colour)
    (h : FamilyBoxFullSolvable l cubes) : FamilyBoxFrameSolvable l cubes := by
  obtain ⟨t, ht, p, hp⟩ := h
  exact ⟨t, ht, Function.Embedding.inl.trans p, fun q => hp (.inl q)⟩

lemma boxFull_of_frame {m : ℕ} (l : Fin 3 → ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hm : (l 0 + 2) * (l 1 + 2) * (l 2 + 2) ≤ m)
    (h : FamilyBoxFrameSolvable l cubes) : FamilyBoxFullSolvable l cubes := by
  classical
  obtain ⟨t, ht, p, hp⟩ := h
  obtain ⟨q, hq⟩ := embedding_extend_sum (B := BoxFillerSlot l) p (by
    have he : Fintype.card (BoxFrameSlot l) + Fintype.card (BoxFillerSlot l) =
        (l 0 + 2) * (l 1 + 2) * (l 2 + 2) :=
      (Fintype.card_sum (α := BoxFrameSlot l) (β := BoxFillerSlot l)).symm.trans (boxFullSlot_card l)
    simpa only [Fintype.card_fin, he] using hm)
  refine ⟨t, ht, q, ?_⟩
  intro pos
  cases pos with
  | inl pos => simpa only [hq, boxFullExposed] using hp pos
  | inr pos => cases pos with
    | inl pos => exact fits_one_face _ t (hc _) pos.1
    | inr pos =>
      refine ⟨ColourCubes.rotations 0, (ColourCubes.proper_rotation_iff _).mpr ⟨0,rfl⟩, ?_⟩
      intro f hf
      exact False.elim (Finset.notMem_empty f hf)

/-- Completion has no geometric requirement beyond the frame and the volume. -/
theorem boxFull_iff_frame_and_size {m : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable l cubes ↔ FamilyBoxFrameSolvable l cubes ∧
      (l 0 + 2) * (l 1 + 2) * (l 2 + 2) ≤ m :=
  ⟨fun h => ⟨boxFrame_of_full l cubes h, boxFull_requires_pieces l cubes h⟩,
    fun h => boxFull_of_frame l cubes hc h.2 h.1⟩

end ThreeColour
