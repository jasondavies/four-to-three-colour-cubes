module
public import ThreeColour.FrameDefs
@[expose] public section
namespace ThreeColour

/-! Geometric descriptions of the `ordinary` and `bucket` pools. -/

/-- Named nonzero witness for colour literals below. -/
theorem colourFinBound : NeZero 4 := by infer_instance

/-- BES's universal corners `012, 031, 023, 132`, closed under cyclic rotation. -/
def universalCorners : Finset (Colour × Colour × Colour) :=
  letI : NeZero 4 := colourFinBound
  {(0,1,2), (1,2,0), (2,0,1), (0,3,1), (3,1,0), (1,0,3),
   (0,2,3), (2,3,0), (3,0,2), (1,3,2), (3,2,1), (2,1,3)}

/-- Corner colours in a fixed cyclic orientation: the order of `exposedFaces k`
when its face indices have even sum, and the reverse cyclic order otherwise. -/
def cornerRead (c : Fin 6 → Colour) (k : Slot) : Colour × Colour × Colour :=
  if ((ColourCubes.exposedFaces k 0).val + (ColourCubes.exposedFaces k 1).val +
      (ColourCubes.exposedFaces k 2).val) % 2 = 0 then
    (c (ColourCubes.exposedFaces k 0), c (ColourCubes.exposedFaces k 1),
      c (ColourCubes.exposedFaces k 2))
  else
    (c (ColourCubes.exposedFaces k 0), c (ColourCubes.exposedFaces k 2),
      c (ColourCubes.exposedFaces k 1))

def Trichromatic (t : Colour × Colour × Colour) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- Class `0` reads corners as given; class `1` reverses them. -/
def classRead (s : Fin 2) (t : Colour × Colour × Colour) : Colour × Colour × Colour :=
  letI : NeZero 2 := frameFinTwo
  if s = 0 then t else (t.1, t.2.2, t.2.1)

/-- Orientation class `s`: every trichromatic corner is a universal corner after
`classRead s`, and every set of three colours occurs at some corner. -/
def OrdinaryClass (s : Fin 2) (c : Fin 6 → Colour) : Prop :=
  (∀ k, Trichromatic (cornerRead c k) → classRead s (cornerRead c k) ∈ universalCorners) ∧
  ∀ d : Colour, ∃ k, Trichromatic (cornerRead c k) ∧
    (cornerRead c k).1 ≠ d ∧ (cornerRead c k).2.1 ≠ d ∧ (cornerRead c k).2.2 ≠ d

/-- Bucket `a`: at least two of the three corner types `aab`, with `b ≠ a`. -/
def InBucket (a : Colour) (c : Fin 6 → Colour) : Prop :=
  2 ≤ (Finset.univ.filter fun b : Colour => b ≠ a ∧ ∃ k : Slot,
    ({c (ColourCubes.exposedFaces k 0), c (ColourCubes.exposedFaces k 1),
      c (ColourCubes.exposedFaces k 2)} : Multiset Colour) = {a, a, b}).card

instance (t : Colour × Colour × Colour) : Decidable (Trichromatic t) := by
  unfold Trichromatic; infer_instance
instance (s : Fin 2) (c : Fin 6 → Colour) : Decidable (OrdinaryClass s c) := by
  unfold OrdinaryClass; infer_instance
instance (a : Colour) (c : Fin 6 → Colour) : Decidable (InBucket a c) := by
  unfold InBucket; infer_instance

set_option maxRecDepth 100000 in
/-- The two ordinary pools are exactly the two geometric orientation classes. -/
theorem ordinary_geometry : ∀ s : Fin 2, ∀ i : Source,
    i ∈ ordinary s ↔ OrdinaryClass s (sourceFaces i) := by decide +kernel

set_option maxRecDepth 100000 in
/-- On ordinary varieties, the bucket pools are given by corner types. -/
theorem bucket_geometry : ∀ a : Colour, ∀ i ∈ ordinary 0 ∪ ordinary 1,
    i ∈ bucket a ↔ InBucket a (sourceFaces i) := by decide +kernel

end ThreeColour
