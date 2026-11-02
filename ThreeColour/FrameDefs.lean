module

public import ThreeColour.Data
public import ColourCubes.Geometry

@[expose] public section

namespace ThreeColour

/-- The twelve edges, listed by their two outward face normals. -/
theorem frameFinSix : NeZero 6 := by infer_instance
theorem frameFinTwo : NeZero 2 := by infer_instance

def edgeFaces : Fin 12 → Fin 2 → Fin 6 :=
  letI : NeZero 6 := frameFinSix
  ![![0,2], ![0,3], ![0,4], ![0,5], ![1,2], ![1,3],
    ![1,4], ![1,5], ![2,4], ![2,5], ![3,4], ![3,5]]

/-- Availability of an unordered pair on adjacent faces. -/
def HasEdge (cube : Fin 6 → Colour) (a b : Colour) : Prop :=
  ∃ f g : Fin 6, f.val / 2 ≠ g.val / 2 ∧ cube f = a ∧ cube g = b

instance (cube : Fin 6 → Colour) (a b : Colour) : Decidable (HasEdge cube a b) := by
  unfold HasEdge
  infer_instance

/-- `k` counts the non-corner positions on each edge; the side length is `k+2`. -/
abbrev FrameSlot (k : ℕ) := Slot ⊕ (Fin 12 × Fin k)

def frameFits (k : ℕ) (t : Target) : FrameSlot k → Source → Prop
  | .inl p, i => fits t p i = true
  | .inr p, i => HasEdge (sourceFaces i)
      (targetFaces t (edgeFaces p.1 0)) (targetFaces t (edgeFaces p.1 1))

/-- A frame matches every corner and edge occurrence to a distinct physical copy. -/
def FrameSolvable (k : ℕ) (x : Inventory) : Prop :=
  ∃ t : Target, ∃ p : FrameSlot k ↪ Stock x, ∀ q, frameFits k t q (p q).1

lemma frameSlot_card (k : ℕ) : Fintype.card (FrameSlot k) = 12 * k + 8 := by
  simp [FrameSlot, Slot]
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
