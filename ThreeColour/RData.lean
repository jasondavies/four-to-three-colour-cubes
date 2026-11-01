module

public import ThreeColour.Data

@[expose] public section

namespace ThreeColour
def rSingleTarget : Colour → Fin 6 → Target := ![![4, 9, 9, 9, 4, 3], ![47, 47, 46, 91, 91, 91], ![70, 71, 71, 108, 108, 108], ![84, 89, 89, 119, 119, 119]]
def rPairTarget : Colour → Colour → Fin 6 → Target := ![![![0, 0, 0, 0, 0, 0], ![4, 4, 3, 0, 4, 3], ![3, 9, 9, 9, 0, 3], ![4, 9, 9, 9, 4, 0]], ![![47, 47, 46, 0, 47, 46], ![0, 0, 0, 0, 0, 0], ![46, 0, 46, 91, 91, 91], ![47, 47, 0, 91, 91, 91]], ![![70, 71, 71, 71, 0, 70], ![70, 0, 70, 108, 108, 108], ![0, 0, 0, 0, 0, 0], ![0, 71, 71, 108, 108, 108]], ![![84, 89, 89, 89, 84, 0], ![84, 84, 0, 119, 119, 119], ![0, 89, 89, 119, 119, 119], ![0, 0, 0, 0, 0, 0]]]
def rMajorTarget : Colour → Target := ![3, 46, 70, 84]
def flip : Fin 2 → Fin 2 := ![1,0]
def Good (a b : Colour) (j : Fin 6) : Prop := ∃ d ∈ omitted j, d ≠ a ∧ d ≠ b
instance (a b : Colour) (j : Fin 6) : Decidable (Good a b j) := by unfold Good; infer_instance
end ThreeColour
