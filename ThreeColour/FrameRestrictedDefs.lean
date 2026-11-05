module
public import ThreeColour.FrameData
public import ThreeColour.RestrictedGeometry
@[expose] public section
namespace ThreeColour

/-- Three faces at a corner have one colour; their opposite faces use two others. -/
def IsU (t : Fin 6 → Colour) : Prop :=
  Uses 3 t ∧ ∃ a : Colour,
    (Finset.univ.filter (fun f => t f = a)).card = 3 ∧
    ∀ f, t f = a → t (ColourCubes.opposite f) ≠ a

instance (t : Fin 6 → Colour) : Decidable (IsU t) := by unfold IsU; infer_instance

/-- The Q, D and U targets used by the larger-frame constructions. -/
def FrameTarget (t : Target) : Prop :=
  IsQ (targetFaces t) ∨ IsD (targetFaces t) ∨ IsU (targetFaces t)

instance (t : Target) : Decidable (FrameTarget t) := by
  unfold FrameTarget; infer_instance

set_option maxRecDepth 100000 in
/-- `uTarget a b c` has face tuple `(a,b,a,b,a,c)`. -/
lemma uTarget_isU : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c →
    IsU (targetFaces (uTarget a b c)) := by decide +kernel

/-- Retain the target family as well as the frame matching. -/
def RestrictedFrameSolvable (k : ℕ) (x : Inventory) : Prop :=
  ∃ t : Target, FrameTarget t ∧ ∃ p : FrameSlot k ↪ Stock x,
    ∀ q, frameFits k t q (p q).1

lemma RestrictedFrameSolvable.solvable {k : ℕ} {x : Inventory}
    (h : RestrictedFrameSolvable k x) : FrameSolvable k x := by
  obtain ⟨t, _, p, hp⟩ := h
  exact ⟨t, p, hp⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Counts use a fixed labelled palette and proper rotations. -/
theorem frame_target_count :
    (Finset.univ.filter FrameTarget).card = 40 := by decide +kernel

end ThreeColour
