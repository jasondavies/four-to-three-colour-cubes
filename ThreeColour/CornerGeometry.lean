module

public import MacMahon.Rotations

@[expose] public section

namespace ThreeColour.Geometry

/-- Reorder each corner's coordinate faces with consistent orientation. -/
def cornerOrder : Fin 8 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![0,2,1], ![0,1,2],
    ![0,2,1], ![0,1,2], ![0,1,2], ![0,2,1]]

def frame (k : Fin 8) (f : Fin 3) : Fin 6 :=
  MacMahon.exposedFaces k (cornerOrder k f)

lemma cornerOrder_involutive : ∀ k f, cornerOrder k (cornerOrder k f) = f := by
  decide +kernel

/-- A rotation takes an oriented corner frame to a cyclic shift of another. -/
lemma rotated_frame : ∀ (k : Fin 8) (r : Fin 24),
    ∃ (l : Fin 8) (s : Fin 3), ∀ f,
      MacMahon.rotations r (frame k f) = frame l (f + s) := by
  decide +kernel

/-- Every cyclic alignment of two oriented corner frames is realised by a rotation. -/
lemma align_frame : ∀ (k l : Fin 8) (s : Fin 3),
    ∃ r : Fin 24, ∀ f,
      MacMahon.rotations r (frame k f) = frame l (f + s) := by
  decide +kernel

/-- The ordered colours of a corner, for an arbitrary palette. -/
def corner {α : Type*} (c : Fin 6 → α) (k : Fin 8) : Fin 3 → α :=
  fun f => c (frame k f)

/-- Equality of oriented triples up to cyclic shift. -/
def CyclicEq {α : Type*} (a b : Fin 3 → α) : Prop :=
  ∃ s : Fin 3, ∀ f, a (f + s) = b f

instance {α : Type*} [DecidableEq α] (a b : Fin 3 → α) : Decidable (CyclicEq a b) := by
  unfold CyclicEq
  infer_instance

/-- A cube fits a target corner precisely when it has the same cyclic corner type.
This statement is independent of the palette and allows repeated colours. -/
theorem corner_rotation_iff {α : Type*} (c t : Fin 6 → α) (k : Fin 8) :
    (∃ r : Fin 24, ∀ f : Fin 3,
      c (MacMahon.rotations r (MacMahon.exposedFaces k f)) =
        t (MacMahon.exposedFaces k f)) ↔
    ∃ l : Fin 8, CyclicEq (corner c l) (corner t k) := by
  constructor
  · rintro ⟨r, h⟩
    obtain ⟨l, s, hs⟩ := rotated_frame k r
    refine ⟨l, s, fun f => ?_⟩
    change c (frame l (f + s)) = t (frame k f)
    rw [← hs f]
    exact h (cornerOrder k f)
  · rintro ⟨l, s, h⟩
    obtain ⟨r, hr⟩ := align_frame k l s
    refine ⟨r, fun f => ?_⟩
    have hf := h (cornerOrder k f)
    change c (frame l (cornerOrder k f + s)) = t (frame k (cornerOrder k f)) at hf
    rw [← hr (cornerOrder k f)] at hf
    simpa only [frame, cornerOrder_involutive] using hf

/-- The same correspondence expressed using geometric proper rotations rather
than indices in the verified rotation table. -/
theorem corner_proper_rotation_iff {α : Type*} (c t : Fin 6 → α) (k : Fin 8) :
    (∃ r : Fin 6 → Fin 6, MacMahon.ProperRotation r ∧ ∀ f : Fin 3,
      c (r (MacMahon.exposedFaces k f)) = t (MacMahon.exposedFaces k f)) ↔
    ∃ l : Fin 8, CyclicEq (corner c l) (corner t k) := by
  rw [← corner_rotation_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨n, rfl⟩ := (MacMahon.proper_rotation_iff r).mp hr
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨MacMahon.rotations n,
      (MacMahon.proper_rotation_iff _).mpr ⟨n, rfl⟩, h⟩

end ThreeColour.Geometry
