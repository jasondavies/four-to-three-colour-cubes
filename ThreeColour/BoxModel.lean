module

public import ThreeColour.FramePhysical

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Extend a placement by assigning the new positions to unused copies. -/
lemma embedding_extend_sum {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : A ↪ C) (h : Fintype.card A + Fintype.card B ≤ Fintype.card C) :
    ∃ q : A ⊕ B ↪ C, ∀ a, q (.inl a) = p a := by
  classical
  let R := {c : C // c ∉ Set.range p}
  have hR : Fintype.card B ≤ Fintype.card R := by
    rw [Fintype.card_subtype_compl, Fintype.card_range]
    omega
  obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le hR
  refine ⟨⟨Sum.elim p (fun b => (r b).val), ?_⟩, fun _ => rfl⟩
  exact p.injective.sumElim (Subtype.val_injective.comp r.injective)
    (fun a b heq => (r b).property ⟨a, heq⟩)

lemma uses_four_surjective (c : Fin 6 → Colour) (hc : Uses 4 c) : Function.Surjective c := by
  have hi : Finset.univ.image c = Finset.univ := (Finset.card_eq_iff_eq_univ _).mp hc
  intro a
  have ha : a ∈ Finset.univ.image c := by rw [hi]; exact Finset.mem_univ _
  obtain ⟨f,_,hf⟩ := Finset.mem_image.mp ha
  exact ⟨f,hf⟩

lemma rotations_face_transitive : ∀ f g : Fin 6,
    ∃ r : Fin 24, ColourCubes.rotations r f = g := by decide +kernel

lemma fits_one_face (c t : Fin 6 → Colour) (hc : Uses 4 c) (f : Fin 6) :
    FacesFit c t {f} := by
  obtain ⟨g,hg⟩ := uses_four_surjective c hc (t f)
  obtain ⟨r,hr⟩ := rotations_face_transitive f g
  refine ⟨ColourCubes.rotations r,(ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩,?_⟩
  intro h hh
  rcases Finset.mem_singleton.mp hh with rfl
  simpa only [hr] using hg

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
