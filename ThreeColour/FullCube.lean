module
public import ThreeColour.FramePhysical
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ThreeColour

/-- The remaining positions: six face interiors and the interior of the cube. -/
abbrev FillerSlot (k : ℕ) := (Fin 6 × Fin k × Fin k) ⊕ (Fin k × Fin k × Fin k)
/-- Positions classified by how many of their coordinates lie on the boundary. -/
abbrev FullSlot (k : ℕ) := FrameSlot k ⊕ FillerSlot k

def fullExposed (k : ℕ) : FullSlot k → Finset (Fin 6)
  | .inl q => frameExposed k q
  | .inr (.inl q) => {q.1}
  | .inr (.inr _) => ∅

def FamilyFullSolvable {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour) : Prop :=
  ∃ target : Fin 6 → Colour, Uses 3 target ∧
    ∃ p : FullSlot k ↪ Fin m, ∀ q, FacesFit (cubes (p q)) target (fullExposed k q)

lemma fullSlot_card (k : ℕ) : Fintype.card (FullSlot k) = (k+2)^3 := by
  simp only [FullSlot, FillerSlot, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  ring

lemma full_requires_pieces {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (h : FamilyFullSolvable k cubes) : (k+2)^3 ≤ m := by
  obtain ⟨_,_,p,_⟩ := h
  simpa only [fullSlot_card,Fintype.card_fin] using Fintype.card_le_of_embedding p

lemma frame_of_full {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (h : FamilyFullSolvable k cubes) : FamilyFrameSolvable k cubes := by
  obtain ⟨t,ht,p,hp⟩ := h
  exact ⟨t,ht,Function.Embedding.inl.trans p,fun q => hp (.inl q)⟩

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
  intro a b heq
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (p.injective heq)
    | inr b => exact False.elim ((r b).property ⟨a,heq⟩)
  | inr a => cases b with
    | inl b => exact False.elim ((r a).property ⟨b,heq.symm⟩)
    | inr b => exact congrArg Sum.inr (r.injective (Subtype.ext heq))

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
  have he : h = f := Finset.mem_singleton.mp hh
  subst h
  simpa only [hr] using hg

lemma full_of_frame {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hm : (k+2)^3 ≤ m)
    (h : FamilyFrameSolvable k cubes) : FamilyFullSolvable k cubes := by
  classical
  obtain ⟨t,ht,p,hp⟩ := h
  obtain ⟨q,hq⟩ := embedding_extend_sum (B := FillerSlot k) p (by
    have hcard : Fintype.card (FrameSlot k) + Fintype.card (FillerSlot k) = (k+2)^3 :=
      (Fintype.card_sum (α := FrameSlot k) (β := FillerSlot k)).symm.trans (fullSlot_card k)
    simpa only [Fintype.card_fin] using hcard.le.trans hm)

  refine ⟨t,ht,q,?_⟩
  intro pos
  cases pos with
  | inl pos => simpa only [hq, fullExposed] using hp pos
  | inr pos => cases pos with
    | inl pos => exact fits_one_face _ t (hc _) pos.1
    | inr pos =>
      refine ⟨ColourCubes.rotations 0,(ColourCubes.proper_rotation_iff _).mpr ⟨0,rfl⟩,?_⟩
      intro f hf
      exact False.elim (Finset.notMem_empty f hf)

/-- Completing a frame adds only the requirement that enough physical pieces remain. -/
theorem full_iff_frame_and_size {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilyFullSolvable k cubes ↔
      FamilyFrameSolvable k cubes ∧ (k+2)^3 ≤ m :=
  ⟨fun h => ⟨frame_of_full k cubes h,full_requires_pieces k cubes h⟩,
    fun h => full_of_frame k cubes hc h.2 h.1⟩

end ThreeColour
