module

public import ThreeColour.BoxAssignment
public import ThreeColour.FrameCertificates
public import ThreeColour.CheckerboardGraph

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Colour-pair indices agree with the edge order of `CheckerboardGraph`. -/
def colourPairIndex : Colour → Colour → Fin 6 :=
  ![![0,0,1,2], ![0,0,3,4], ![1,3,0,5], ![2,4,5,0]]
def checkerPair (e : Fin 6) : SourceSet := checker (![3,4,5,1,2,0] e)
def cuboidPairPool (a b : Colour) : SourceSet :=
  Finset.univ.filter fun i => HasEdge (sourceFaces i) a b

def tripleSource : Colour → Fin 2 → Source :=
  ![![10,13], ![23,25], ![45,47], ![66,67]]

/-- D, Q and H targets with their axes fixed for the reservation construction. -/
def cuboidTarget : Fin 3 → Colour → Colour → Colour → Fin 6 → Colour
  | 0, a, b, c => ![a,a,b,b,c,c]
  | 1, a, b, c => ![b,c,a,a,a,a]
  | 2, a, b, c => ![b,c,a,a,a,b]

def cuboidBasePools (kind : Fin 3) (a b c d : Colour) (s : Fin 2) : Fin 4 → SourceSet :=
  if kind = 0 then ![ordinary 0 ∪ eligible d, ordinary 1 ∪ eligible d,
    (ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d), Finset.univ]
  else if kind = 1 then qFramePools a b c s
  else uFramePools a b d s

def cuboidEdgePools (a b c : Colour) : Fin 3 → SourceSet :=
  ![cuboidPairPool a b, cuboidPairPool a c, cuboidPairPool b c]

def cuboidCornerTag (kind : Fin 3) (a b c : Colour) (s : Fin 2) (p : Slot) : Fin 4 ⊕ Fin 3 :=
  let code := cornerCode (ColourCubes.Geometry.corner (cuboidTarget kind a b c) p)
  .inl (if kind = 0 then (if code ∈ sourceCorners 10 then 0 else 1)
    else if kind = 1 then (if code = cornerCode ![a,a,b] then 0 else 1)
    else if code = cornerCode ![a,a,b] ∨ code = cornerCode ![a,a,c] then 0
    else if code = cornerCode ![a,b,b] then 1
    else if code ∈ sourceCorners (tripleSource a s) then 3 else 2)

def cuboidEdgeTag (kind : Fin 3) (a b c : Colour) (e : Fin 12) : Fin 4 ⊕ Fin 3 :=
  let u := cuboidTarget kind a b c (edgeFaces e 0)
  let v := cuboidTarget kind a b c (edgeFaces e 1)
  if u = v then .inl (if kind = 1 then 2 else if u = a then 0 else 1)
  else .inr (if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then 0
    else if (u = a ∧ v = c) ∨ (u = c ∧ v = a) then 1 else 2)

def DistinctColours (a b c d : Colour) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c
instance (a b c d : Colour) : Decidable (DistinctColours a b c d) := by
  unfold DistinctColours; infer_instance

end ThreeColour
