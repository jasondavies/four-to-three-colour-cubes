module

public import ThreeColour.BoxDefs

@[expose] public section

namespace ThreeColour

/-- `k` counts the non-corner positions on each edge; the side length is `k+2`. -/
abbrev FrameSlot (k : ℕ) := BoxFrameSlot (fun _ => k)

def frameFits (k : ℕ) (t : Target) : FrameSlot k → Source → Prop
  | .inl p, i => fits t p i = true
  | .inr p, i => HasEdge (sourceFaces i)
      (targetFaces t (edgeFaces p.1 0)) (targetFaces t (edgeFaces p.1 1))

/-- A frame matches every corner and edge occurrence to a distinct physical copy. -/
def FrameSolvable (k : ℕ) (x : Inventory) : Prop :=
  ∃ t : Target, ∃ p : FrameSlot k ↪ Stock x, ∀ q, frameFits k t q (p q).1

lemma frameSlot_card (k : ℕ) : Fintype.card (FrameSlot k) = 12 * k + 8 := by
  simp [FrameSlot, BoxFrameSlot, Slot]
  omega

lemma frame_zero_iff (x : Inventory) : FrameSolvable 0 x ↔ Solvable x := by
  constructor
  · rintro ⟨t, p, hp⟩
    exact ⟨t, Function.Embedding.inl.trans p, fun q => hp (.inl q)⟩
  · rintro ⟨t, p, hp⟩
    refine ⟨t, ⟨Sum.elim p (fun q => Fin.elim0 q.2), ?_⟩, ?_⟩
    · intro a b hab
      cases a with
      | inl a => cases b with
        | inl b => exact congrArg Sum.inl (p.injective hab)
        | inr b => exact Fin.elim0 b.2
      | inr a => exact Fin.elim0 a.2
    · intro q
      cases q with
      | inl q => exact hp q
      | inr q => exact Fin.elim0 q.2

end ThreeColour
