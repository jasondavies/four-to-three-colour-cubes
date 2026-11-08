module

public import ThreeColour.RawData
public import ColourCubes.Geometry

@[expose] public section
namespace ThreeColour

/-- Named nonzero witnesses for the finite vector notation below. -/
theorem frameFinSix : NeZero 6 := by infer_instance
theorem frameFinTwo : NeZero 2 := by infer_instance

/-- The twelve edges, listed by their two outward face normals. -/
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

def FacesFit (c t : Fin 6 → Colour) (faces : Finset (Fin 6)) : Prop :=
  ∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧ ∀ f ∈ faces, c (r f) = t f

/-- Coordinate direction parallel to each geometric edge. -/
def boxEdgeAxis : Fin 12 → Fin 3 := ![2,2,1,1,2,2,1,1,0,0,0,0]

/-- `l i` counts the positions strictly between corners along axis `i`. -/
abbrev BoxFrameSlot (l : Fin 3 → ℕ) := Slot ⊕ (Σ e : Fin 12, Fin (l (boxEdgeAxis e)))

def boxFrameExposed (l : Fin 3 → ℕ) : BoxFrameSlot l → Finset (Fin 6)
  | .inl p => Finset.univ.image (ColourCubes.exposedFaces p)
  | .inr p =>
    letI : NeZero 2 := frameFinTwo
    {edgeFaces p.1 0, edgeFaces p.1 1}

/-- A physical frame in a fixed coordinate system. The target is arbitrary, so
all assignments of colours and opposite face pairs to the axes are permitted. -/
def FamilyBoxFrameSolvable {m : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin m → Fin 6 → Colour) : Prop :=
  ∃ t : Fin 6 → Colour, Uses 3 t ∧ ∃ p : BoxFrameSlot l ↪ Fin m,
    ∀ q, FacesFit (cubes (p q)) t (boxFrameExposed l q)

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

end ThreeColour
