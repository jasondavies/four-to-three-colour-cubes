module

public import ThreeColour.RawData

@[expose] public section

namespace ThreeColour

/-- Four faces have one colour; the two other faces are opposite. -/
def IsQ (t : Fin 6 → Colour) : Prop :=
  Uses 3 t ∧ ∃ a : Colour,
    (Finset.univ.filter (fun f => t f = a)).card = 4 ∧
    ∀ f, t f ≠ a → t (ColourCubes.opposite f) ≠ a

/-- Four faces have one colour; the two other faces are adjacent. -/
def IsR (t : Fin 6 → Colour) : Prop :=
  Uses 3 t ∧ ∃ a : Colour,
    (Finset.univ.filter (fun f => t f = a)).card = 4 ∧
    ∃ f, t f ≠ a ∧ t (ColourCubes.opposite f) = a

/-- Three monochromatic opposite pairs, in three different colours. -/
def IsD (t : Fin 6 → Colour) : Prop :=
  Uses 3 t ∧ ∀ f, t (ColourCubes.opposite f) = t f

def RestrictedTarget (t : Fin 6 → Colour) : Prop := IsQ t ∨ IsR t ∨ IsD t

instance (t : Fin 6 → Colour) : Decidable (IsQ t) := by unfold IsQ; infer_instance
instance (t : Fin 6 → Colour) : Decidable (IsR t) := by unfold IsR; infer_instance
instance (t : Fin 6 → Colour) : Decidable (IsD t) := by unfold IsD; infer_instance
instance (t : Fin 6 → Colour) : Decidable (RestrictedTarget t) := by
  unfold RestrictedTarget; infer_instance

def RestrictedSolvable (x : Inventory) : Prop :=
  ∃ t : Target, RestrictedTarget (targetFaces t) ∧ Builds x (fits t)

lemma RestrictedSolvable.solvable {x : Inventory} (h : RestrictedSolvable x) : Solvable x :=
  let ⟨t, _, ht⟩ := h
  ⟨t, ht⟩

end ThreeColour
