module

public import ThreeColour.RData

@[expose] public section

namespace ThreeColour
def qGroups (a b c : Colour) : Fin 4 → SourceSet :=
  ![∅, support a b, support a c, bucket a]
def qBounds : Fin 4 → ℕ := ![0,4,4,8]
def oppGroups (d : Colour) : Fin 4 → SourceSet :=
  ![∅, ordinary 0 ∪ eligible d, ordinary 1 ∪ eligible d,
    (ordinary 0 ∪ ordinary 1) ∪ eligible d]
def oppBounds : Fin 4 → ℕ := ![0,4,4,8]
def packGroups (g h k big : SourceSet) : Fin 9 → SourceSet :=
  ![∅,g,h,g ∪ h,k,g ∪ k,h ∪ k,(g ∪ h) ∪ k,big]
def packBounds (t p : ℕ) : Fin 9 → ℕ := ![0,t,p,t+p,1,t+1,p+1,t+p+1,8]
end ThreeColour
