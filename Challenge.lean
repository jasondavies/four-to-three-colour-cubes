module

public import Mathlib

@[expose] public section

/-! Independent physical statements. No proof-library imports. The intentional
statement holes are comparator targets, not part of the proof library.
The comparator compares exported declarations, including helper-proof names.
When adding `Fin` literals, preserve the library's named bounds and run the
comparator: ordinary elaboration can accept definitions that it rejects. -/
namespace ColourCubes

def exposedFaces : Fin 8 → Fin 3 → Fin 6 := ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]

def rotations : Fin 24 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 5, 4], ![0, 1, 4, 5, 3, 2], ![0, 1, 5, 4, 2, 3], ![1, 0, 2, 3, 5, 4], ![1, 0, 3, 2, 4, 5], ![1, 0, 4, 5, 2, 3], ![1, 0, 5, 4, 3, 2], ![2, 3, 0, 1, 5, 4], ![2, 3, 1, 0, 4, 5], ![2, 3, 4, 5, 0, 1], ![2, 3, 5, 4, 1, 0], ![3, 2, 0, 1, 4, 5], ![3, 2, 1, 0, 5, 4], ![3, 2, 4, 5, 1, 0], ![3, 2, 5, 4, 0, 1], ![4, 5, 0, 1, 2, 3], ![4, 5, 1, 0, 3, 2], ![4, 5, 2, 3, 1, 0], ![4, 5, 3, 2, 0, 1], ![5, 4, 0, 1, 3, 2], ![5, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]]

def opposite (f : Fin 6) : Fin 6 :=
  if f.val % 2 = 0 then f + 1 else f - 1
def fromAxes (a b c : Fin 6) : Fin 6 → Fin 6 :=
  ![a, opposite a, b, opposite b, c, opposite c]

/-- Distinct coordinate axes and determinant +1. -/
def ValidAxes (a b c : Fin 6) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ c.val / 2 ∧
  (a.val % 2 + b.val % 2 + c.val % 2) % 2 =
    ((if a.val / 2 > b.val / 2 then 1 else 0) +
     (if a.val / 2 > c.val / 2 then 1 else 0) +
     (if b.val / 2 > c.val / 2 then 1 else 0)) % 2
instance (a b c : Fin 6) : Decidable (ValidAxes a b c) := by
  unfold ValidAxes; infer_instance

def ProperRotation (r : Fin 6 → Fin 6) : Prop :=
  ∃ a b c, ValidAxes a b c ∧ r = fromAxes a b c

/-- Face colours from an arbitrary palette; colours may repeat. -/
abbrev Cube (α : Type*) := Fin 6 → α

/-- Exactly `n` distinct colours occur on the six faces. -/
def Uses {α : Type*} [DecidableEq α] (n : ℕ) (c : Cube α) : Prop :=
  (Finset.univ.image c).card = n

instance {α : Type*} [DecidableEq α] (n : ℕ) (c : Cube α) : Decidable (Uses n c) := by
  unfold Uses
  infer_instance

/-- Every colour in the palette occurs. -/
def UsesAllColours {α : Type*} (c : Cube α) : Prop := ∀ a, ∃ f, c f = a

instance {α : Type*} [Fintype α] [DecidableEq α] (c : Cube α) :
    Decidable (UsesAllColours c) := by
  unfold UsesAllColours
  infer_instance

/-- Matching by an index in the verified rotation table. -/
def TableFits {α : Type*} (c t : Cube α) (k : Fin 8) : Prop :=
  ∃ r : Fin 24, ∀ f : Fin 3,
    c (rotations r (exposedFaces k f)) = t (exposedFaces k f)

/-- Matching the three exterior faces by a geometric proper rotation. -/
def Fits {α : Type*} (c t : Cube α) (k : Fin 8) : Prop :=
  ∃ r : Fin 6 → Fin 6, ProperRotation r ∧ ∀ f : Fin 3,
    c (r (exposedFaces k f)) = t (exposedFaces k f)

/-- Build a specified target using eight distinct indexed copies. -/
def Builds {α ι : Type*} (cubes : ι → Cube α) (target : Cube α) : Prop :=
  ∃ placement : Fin 8 ↪ ι, ∀ k, Fits (cubes (placement k)) target k

/-- Each application chooses its own admissible target predicate. -/
def HasSolution {α ι : Type*} (allowed : Cube α → Prop) (cubes : ι → Cube α) : Prop :=
  ∃ target, allowed target ∧ Builds cubes target

theorem proper_rotation_iff (r : Fin 6 → Fin 6) :
    ProperRotation r ↔ ∃ n : Fin 24, r = rotations n := by sorry

theorem exposed_face_rule : ∀ k : Fin 8, ∀ d : Fin 3,
    (exposedFaces k d).val = 2*d.val + (k.val / 2^(2-d.val)) % 2 := by sorry

end ColourCubes
namespace ThreeColour
open scoped BigOperators
abbrev Source := Fin 68
abbrev Slot := Fin 8
abbrev Inventory := Source → ℕ
abbrev SourceSet := Finset Source
abbrev Stock (a : Inventory) := (i : Source) × Fin (a i)
def mass (a : Inventory) (g : SourceSet) : ℕ := ∑ i ∈ g, a i
abbrev Colour := Fin 4
abbrev Target := Fin 120
def sourceFaces : Source → Fin 6 → Colour := fun i => (#[![0, 0, 0, 1, 2, 3], ![0, 0, 0, 2, 1, 3], ![0, 0, 0, 3, 1, 2], ![0, 0, 1, 1, 2, 3], ![0, 0, 1, 2, 1, 3], ![0, 0, 1, 2, 2, 3], ![0, 0, 1, 2, 3, 3], ![0, 0, 1, 3, 2, 2], ![0, 0, 1, 3, 2, 3], ![0, 1, 0, 1, 2, 3], ![0, 1, 0, 2, 0, 3], ![0, 1, 0, 2, 1, 3], ![0, 1, 0, 2, 2, 3], ![0, 1, 0, 2, 3, 0], ![0, 1, 0, 2, 3, 1], ![0, 1, 0, 2, 3, 2], ![0, 1, 0, 2, 3, 3], ![0, 1, 0, 3, 1, 2], ![0, 1, 0, 3, 2, 1], ![0, 1, 0, 3, 2, 2], ![0, 1, 0, 3, 2, 3], ![0, 1, 0, 3, 3, 2], ![0, 1, 1, 1, 2, 3], ![0, 1, 1, 2, 1, 3], ![0, 1, 1, 2, 2, 3], ![0, 1, 1, 2, 3, 1], ![0, 1, 1, 2, 3, 2], ![0, 1, 1, 2, 3, 3], ![0, 1, 1, 3, 2, 2], ![0, 1, 1, 3, 2, 3], ![0, 1, 1, 3, 3, 2], ![0, 1, 2, 2, 2, 3], ![0, 1, 2, 2, 3, 3], ![0, 1, 2, 3, 2, 3], ![0, 1, 2, 3, 3, 3], ![0, 2, 0, 2, 1, 3], ![0, 2, 0, 3, 1, 1], ![0, 2, 0, 3, 1, 2], ![0, 2, 0, 3, 1, 3], ![0, 2, 0, 3, 2, 1], ![0, 2, 0, 3, 3, 1], ![0, 2, 1, 1, 1, 3], ![0, 2, 1, 1, 2, 3], ![0, 2, 1, 1, 3, 3], ![0, 2, 1, 2, 1, 3], ![0, 2, 1, 2, 2, 3], ![0, 2, 1, 2, 3, 1], ![0, 2, 1, 2, 3, 2], ![0, 2, 1, 2, 3, 3], ![0, 2, 1, 3, 1, 3], ![0, 2, 1, 3, 2, 2], ![0, 2, 1, 3, 2, 3], ![0, 2, 1, 3, 3, 2], ![0, 2, 1, 3, 3, 3], ![0, 3, 0, 3, 1, 2], ![0, 3, 1, 1, 1, 2], ![0, 3, 1, 1, 2, 2], ![0, 3, 1, 1, 2, 3], ![0, 3, 1, 2, 1, 2], ![0, 3, 1, 2, 1, 3], ![0, 3, 1, 2, 2, 2], ![0, 3, 1, 2, 2, 3], ![0, 3, 1, 2, 3, 1], ![0, 3, 1, 2, 3, 2], ![0, 3, 1, 2, 3, 3], ![0, 3, 1, 3, 2, 2], ![0, 3, 1, 3, 2, 3], ![0, 3, 1, 3, 3, 2]] : Array (Fin 6 → Colour))[i.val]!
def targetFaces : Target → Fin 6 → Colour := fun i => (#[![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 1, 3], ![0, 0, 0, 0, 2, 3], ![0, 0, 0, 1, 0, 2], ![0, 0, 0, 1, 0, 3], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 1, 1, 3], ![0, 0, 0, 1, 2, 2], ![0, 0, 0, 1, 3, 3], ![0, 0, 0, 2, 0, 3], ![0, 0, 0, 2, 1, 1], ![0, 0, 0, 2, 1, 2], ![0, 0, 0, 2, 2, 3], ![0, 0, 0, 2, 3, 3], ![0, 0, 0, 3, 1, 1], ![0, 0, 0, 3, 1, 3], ![0, 0, 0, 3, 2, 2], ![0, 0, 0, 3, 2, 3], ![0, 0, 1, 1, 1, 2], ![0, 0, 1, 1, 1, 3], ![0, 0, 1, 1, 2, 2], ![0, 0, 1, 1, 3, 3], ![0, 0, 1, 2, 1, 2], ![0, 0, 1, 2, 2, 2], ![0, 0, 1, 3, 1, 3], ![0, 0, 1, 3, 3, 3], ![0, 0, 2, 2, 2, 3], ![0, 0, 2, 2, 3, 3], ![0, 0, 2, 3, 2, 3], ![0, 0, 2, 3, 3, 3], ![0, 1, 0, 1, 0, 2], ![0, 1, 0, 1, 0, 3], ![0, 1, 0, 1, 1, 2], ![0, 1, 0, 1, 1, 3], ![0, 1, 0, 1, 2, 2], ![0, 1, 0, 1, 3, 3], ![0, 1, 0, 2, 0, 2], ![0, 1, 0, 2, 1, 1], ![0, 1, 0, 2, 1, 2], ![0, 1, 0, 2, 2, 1], ![0, 1, 0, 2, 2, 2], ![0, 1, 0, 3, 0, 3], ![0, 1, 0, 3, 1, 1], ![0, 1, 0, 3, 1, 3], ![0, 1, 0, 3, 3, 1], ![0, 1, 0, 3, 3, 3], ![0, 1, 1, 1, 1, 2], ![0, 1, 1, 1, 1, 3], ![0, 1, 1, 1, 2, 2], ![0, 1, 1, 1, 3, 3], ![0, 1, 1, 2, 1, 2], ![0, 1, 1, 2, 2, 2], ![0, 1, 1, 3, 1, 3], ![0, 1, 1, 3, 3, 3], ![0, 1, 2, 2, 2, 2], ![0, 1, 3, 3, 3, 3], ![0, 2, 0, 2, 0, 3], ![0, 2, 0, 2, 1, 1], ![0, 2, 0, 2, 1, 2], ![0, 2, 0, 2, 2, 3], ![0, 2, 0, 2, 3, 3], ![0, 2, 0, 3, 0, 3], ![0, 2, 0, 3, 2, 2], ![0, 2, 0, 3, 2, 3], ![0, 2, 0, 3, 3, 2], ![0, 2, 0, 3, 3, 3], ![0, 2, 1, 1, 1, 1], ![0, 2, 1, 1, 1, 2], ![0, 2, 1, 1, 2, 2], ![0, 2, 1, 2, 1, 2], ![0, 2, 1, 2, 2, 2], ![0, 2, 2, 2, 2, 3], ![0, 2, 2, 2, 3, 3], ![0, 2, 2, 3, 2, 3], ![0, 2, 2, 3, 3, 3], ![0, 2, 3, 3, 3, 3], ![0, 3, 0, 3, 1, 1], ![0, 3, 0, 3, 1, 3], ![0, 3, 0, 3, 2, 2], ![0, 3, 0, 3, 2, 3], ![0, 3, 1, 1, 1, 1], ![0, 3, 1, 1, 1, 3], ![0, 3, 1, 1, 3, 3], ![0, 3, 1, 3, 1, 3], ![0, 3, 1, 3, 3, 3], ![0, 3, 2, 2, 2, 2], ![0, 3, 2, 2, 2, 3], ![0, 3, 2, 2, 3, 3], ![0, 3, 2, 3, 2, 3], ![0, 3, 2, 3, 3, 3], ![1, 1, 1, 1, 2, 3], ![1, 1, 1, 2, 1, 3], ![1, 1, 1, 2, 2, 3], ![1, 1, 1, 2, 3, 3], ![1, 1, 1, 3, 2, 2], ![1, 1, 1, 3, 2, 3], ![1, 1, 2, 2, 2, 3], ![1, 1, 2, 2, 3, 3], ![1, 1, 2, 3, 2, 3], ![1, 1, 2, 3, 3, 3], ![1, 2, 1, 2, 1, 3], ![1, 2, 1, 2, 2, 3], ![1, 2, 1, 2, 3, 3], ![1, 2, 1, 3, 1, 3], ![1, 2, 1, 3, 2, 2], ![1, 2, 1, 3, 2, 3], ![1, 2, 1, 3, 3, 2], ![1, 2, 1, 3, 3, 3], ![1, 2, 2, 2, 2, 3], ![1, 2, 2, 2, 3, 3], ![1, 2, 2, 3, 2, 3], ![1, 2, 2, 3, 3, 3], ![1, 2, 3, 3, 3, 3], ![1, 3, 1, 3, 2, 2], ![1, 3, 1, 3, 2, 3], ![1, 3, 2, 2, 2, 2], ![1, 3, 2, 2, 2, 3], ![1, 3, 2, 2, 3, 3], ![1, 3, 2, 3, 2, 3], ![1, 3, 2, 3, 3, 3]] : Array (Fin 6 → Colour))[i.val]!
def total (a : Inventory) : ℕ := mass a Finset.univ
def extremal : Fin 2 → Inventory := ![fun i => (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0] : Array (ℕ))[i.val]!, fun i => (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] : Array (ℕ))[i.val]!]
def reflection : Source → Source := fun i => (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 10, 11, 12, 16, 18, 17, 19, 21, 20, 22, 25, 26, 23, 24, 27, 28, 30, 29, 31, 32, 33, 34, 35, 36, 39, 40, 37, 38, 41, 42, 43, 46, 47, 44, 45, 48, 49, 50, 52, 51, 53, 54, 55, 56, 57, 58, 62, 60, 63, 59, 61, 64, 65, 67, 66] : Array (Source))[i.val]!
def reflectionRotation : Source → Fin 24 := fun i => (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 6, 4, 12, 4, 4, 4, 4, 4, 5, 5, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 12, 5, 4, 5, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4] : Array (Fin 24))[i.val]!
def reflectFace (f : Fin 6) : Fin 6 := if f.val < 2 then ColourCubes.opposite f else f
def reflectInventory (x : Inventory) : Inventory := fun i => x (reflection i)
def flip : Fin 2 → Fin 2 := ![1,0]
def Uses (n : ℕ) (c : Fin 6 → Colour) : Prop := ColourCubes.Uses n c
instance (n : ℕ) (c : Fin 6 → Colour) : Decidable (Uses n c) := by unfold Uses; infer_instance
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

def FaceFits (t : Target) (i : Source) (k : Slot) (r : Fin 24) : Prop :=
  ∀ f : Fin 3, sourceFaces i (ColourCubes.rotations r (ColourCubes.exposedFaces k f)) =
    targetFaces t (ColourCubes.exposedFaces k f)
def PhysicalSolvable (x : Inventory) : Prop :=
  ∃ t : Target, ∃ f : Slot ↪ Stock x, ∀ k, ∃ r : Fin 24, FaceFits t (f k).1 k r

theorem physical_threshold29 (x : Inventory) (ht : total x = 29) : PhysicalSolvable x := by sorry

theorem physical_classify28 (x : Inventory) (ht : total x = 28) :
    ¬ PhysicalSolvable x ↔ x = extremal 0 ∨ x = extremal 1 := by sorry

theorem sharp_threshold29 :
    (∀ x : Inventory, total x = 29 → PhysicalSolvable x) ∧
    ∃ x : Inventory, total x = 28 ∧ ¬ PhysicalSolvable x := by sorry

theorem least_guaranteed_size :
    IsLeast {n : ℕ | ∀ x : Inventory, n ≤ total x → PhysicalSolvable x} 29 := by sorry

theorem source_catalogue_complete (c : Fin 6 → Colour) (hc : Uses 4 c) :
    ∃ i : Source, ∃ r : Fin 24, ∀ f, c f = sourceFaces i (ColourCubes.rotations r f) := by sorry

theorem target_catalogue_complete (c : Fin 6 → Colour) (hc : Uses 3 c) :
    ∃ t : Target, ∃ r : Fin 24, ∀ f, c f = targetFaces t (ColourCubes.rotations r f) := by sorry

theorem source_catalogue_unique (i j : Source) (r : Fin 24)
    (h : ∀ f, sourceFaces i (ColourCubes.rotations r f) = sourceFaces j f) : i = j := by sorry

theorem reflect_extremal : ∀ s : Fin 2, reflectInventory (extremal s) = extremal (flip s) := by sorry

theorem extremal_distinct : extremal 0 ≠ extremal 1 := by sorry

/-- Actual face colourings and geometric rotations. The outward positions
are pinned by `ColourCubes.exposed_face_rule`; no source or target catalogue is used. -/
def FamilySolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Prop :=
  ColourCubes.HasSolution (Uses 3) cubes

lemma sources_use_four : ∀ i : Source, Uses 4 (sourceFaces i) := by sorry
lemma targets_use_three : ∀ t : Target, Uses 3 (targetFaces t) := by sorry
lemma reflection_geometry : ∀ i : Source, ∀ f : Fin 6,
    sourceFaces (reflection i) (ColourCubes.rotations (reflectionRotation i) f) =
    sourceFaces i (reflectFace f) := by sorry

theorem family_solvable_of_29_le {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hn : 29 ≤ n) : FamilySolvable cubes := by sorry

theorem family_threshold29 (cubes : Fin 29 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilySolvable cubes := by sorry

theorem family_sharp_threshold29 :
    (∀ cubes : Fin 29 → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → FamilySolvable cubes) ∧
    ∃ cubes : Fin 28 → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) ∧ ¬ FamilySolvable cubes := by sorry

theorem family_least_guaranteed_size :
    IsLeast {m : ℕ | ∀ n, ∀ cubes : Fin n → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → m ≤ n → FamilySolvable cubes} 29 := by sorry

theorem family_classify28_geometric (cubes : Fin 28 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilySolvable cubes ↔ ∃ s : Fin 2, ∀ i : Source,
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = extremal s i := by sorry

/-- A physical solution with a target of type Q, R, or D. No catalogue appears
in this definition: the sources, target, and rotations are face maps. -/
def FamilyRestrictedSolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Prop :=
  ∃ target : Fin 6 → Colour, RestrictedTarget target ∧ Uses 3 target ∧
    ColourCubes.Builds cubes target

theorem family_restricted_of_29_le {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hn : 29 ≤ n) : FamilyRestrictedSolvable cubes := by sorry

theorem family_restricted_threshold29 (cubes : Fin 29 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilyRestrictedSolvable cubes := by sorry

theorem family_restricted_of_solvable28 (cubes : Fin 28 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (h : FamilySolvable cubes) :
    FamilyRestrictedSolvable cubes := by sorry

theorem restricted_target_counts :
    (Finset.univ.filter (fun t : Target => IsQ (targetFaces t))).card = 12 ∧
    (Finset.univ.filter (fun t : Target => IsR (targetFaces t))).card = 12 ∧
    (Finset.univ.filter (fun t : Target => IsD (targetFaces t))).card = 4 ∧
    (Finset.univ.filter (fun t : Target => RestrictedTarget (targetFaces t))).card = 28 := by sorry

theorem restricted_target_catalogue_complete (c : Fin 6 → Colour)
    (hc : RestrictedTarget c) :
    ∃ t : Target, RestrictedTarget (targetFaces t) ∧
      ∃ r : Fin 24, ∀ f, c f = targetFaces t (ColourCubes.rotations r f) := by sorry

theorem target_catalogue_unique (i j : Target) (r : Fin 24)
    (h : ∀ f, targetFaces i (ColourCubes.rotations r f) = targetFaces j f) : i = j := by sorry

theorem frameFinSix : NeZero 6 := by infer_instance
theorem frameFinTwo : NeZero 2 := by infer_instance

def edgeFaces : Fin 12 → Fin 2 → Fin 6 :=
  letI : NeZero 6 := frameFinSix
  ![![0,2], ![0,3], ![0,4], ![0,5], ![1,2], ![1,3],
    ![1,4], ![1,5], ![2,4], ![2,5], ![3,4], ![3,5]]

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


abbrev FrameSlot (k : ℕ) := BoxFrameSlot (fun _ => k)
abbrev frameExposed (k : ℕ) := boxFrameExposed (fun _ => k)
abbrev FamilyFrameSolvable {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour) :=
  FamilyBoxFrameSolvable (fun _ => k) cubes
abbrev FullSlot (k : ℕ) := BoxFullSlot (fun _ => k)
abbrev FamilyFullSolvable {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour) :=
  FamilyBoxFullSolvable (fun _ => k) cubes

def extremalSupport (s : Fin 2) : SourceSet := Finset.univ.filter (fun i => extremal s i = 7)

def frameExtremal (k : ℕ) (s : Fin 2) : Inventory :=
  fun i => if i ∈ extremalSupport s then 4*k+7 else 0

theorem frame_threshold_n (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyFrameSolvable (n-2) cubes} (16*n-3) := by sorry

theorem full_threshold_n (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyFullSolvable (n-2) cubes}
      (max (n^3) (16*n-3)) := by sorry

theorem full_cube_of_four_le (n : ℕ) (hn : 4 ≤ n)
    (cubes : Fin (n^3) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyFullSolvable (n-2) cubes := by sorry

theorem edge_faces_geometry :
    (∀ e : Fin 12, (edgeFaces e 0).val / 2 ≠ (edgeFaces e 1).val / 2) ∧
    Function.Injective (fun e : Fin 12 => ({edgeFaces e 0,edgeFaces e 1} : Finset (Fin 6))) ∧
    (∀ f g : Fin 6, f.val / 2 ≠ g.val / 2 →
      ∃ e : Fin 12, ({f,g} : Finset (Fin 6)) = {edgeFaces e 0,edgeFaces e 1}) := by sorry

theorem frame_extremal_distinct (k : ℕ) : frameExtremal k 0 ≠ frameExtremal k 1 := by sorry

theorem reflect_frame_extremal (k : ℕ) (s : Fin 2) :
    reflectInventory (frameExtremal k s) = frameExtremal k (flip s) := by sorry

theorem family_frame_classification (k : ℕ) (cubes : Fin (16*k+28) → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilyFrameSolvable k cubes ↔ ∃ s : Fin 2, ∀ i : Source,
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = frameExtremal k s i := by sorry

theorem full_iff_frame_and_size {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilyFullSolvable k cubes ↔
      FamilyFrameSolvable k cubes ∧ (k+2)^3 ≤ m := by sorry

theorem fullSlot_card (k : ℕ) : Fintype.card (FullSlot k) = (k+2)^3 := by sorry

theorem frameSlot_card (k : ℕ) : Fintype.card (FrameSlot k) = 12 * k + 8 := by sorry

/-! ### Stability, near-extremal failures and forty targets

`ordinary s` lists the sixteen T and P varieties of orientation class `s`, and
`bucket a` the T and P varieties in colour bucket `a`; `ordinary_geometry` and
`bucket_geometry` characterise both tables by corner types. `triple a` lists the
two T varieties with repeated colour `a`, and `allPairs` the 24 P varieties. -/

theorem sourceFinBound : NeZero 68 := by infer_instance
theorem colourFinBound : NeZero 4 := by infer_instance
theorem cornerFinBound : NeZero 3 := by infer_instance

def triple : Fin 4 → SourceSet :=
  letI : NeZero 68 := sourceFinBound
  ![{10, 13}, {23, 25}, {45, 47}, {66, 67}]
def bucket : Fin 4 → SourceSet :=
  letI : NeZero 68 := sourceFinBound
  ![{10, 11, 12, 13, 14, 15, 17, 18, 20, 21, 37, 38, 39, 40}, {11, 14, 17, 18, 23, 24, 25, 26, 29, 30, 44, 46, 59, 62}, {12, 15, 24, 26, 37, 39, 44, 45, 46, 47, 51, 52, 61, 63}, {20, 21, 29, 30, 38, 40, 51, 52, 59, 61, 62, 63, 66, 67}]
def ordinary : Fin 2 → SourceSet :=
  letI : NeZero 68 := sourceFinBound
  ![{10, 11, 12, 18, 20, 23, 24, 29, 39, 40, 44, 45, 51, 59, 61, 66}, {13, 14, 15, 17, 21, 25, 26, 30, 37, 38, 46, 47, 52, 62, 63, 67}]
def allPairs : SourceSet :=
  letI : NeZero 68 := sourceFinBound
  {11, 12, 14, 15, 17, 18, 20, 21, 24, 26, 29, 30, 37, 38, 39, 40, 44, 46, 51, 52, 59, 61, 62, 63}

/-- BES's universal corners `012, 031, 023, 132`, closed under cyclic rotation. -/
def universalCorners : Finset (Colour × Colour × Colour) :=
  letI : NeZero 4 := colourFinBound
  {(0,1,2), (1,2,0), (2,0,1), (0,3,1), (3,1,0), (1,0,3),
   (0,2,3), (2,3,0), (3,0,2), (1,3,2), (3,2,1), (2,1,3)}

/-- Corner colours in a fixed cyclic orientation: the order of `exposedFaces k`
when its face indices have even sum, and the reverse cyclic order otherwise. -/
def cornerRead (c : Fin 6 → Colour) (k : Slot) : Colour × Colour × Colour :=
  letI : NeZero 3 := cornerFinBound
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
  letI : NeZero 3 := cornerFinBound
  2 ≤ (Finset.univ.filter fun b : Colour => b ≠ a ∧ ∃ k : Slot,
    ({c (ColourCubes.exposedFaces k 0), c (ColourCubes.exposedFaces k 1),
      c (ColourCubes.exposedFaces k 2)} : Multiset Colour) = {a, a, b}).card

theorem ordinary_geometry : ∀ s : Fin 2, ∀ i : Source,
    i ∈ ordinary s ↔ OrdinaryClass s (sourceFaces i) := by sorry

theorem bucket_geometry : ∀ a : Colour, ∀ i ∈ ordinary 0 ∪ ordinary 1,
    i ∈ bucket a ↔ InBucket a (sourceFaces i) := by sorry

/-- Copies of source variety `i`, up to proper rotation, in an indexed family. -/
def classCount {m : ℕ} (cubes : Fin m → Fin 6 → Colour) (i : Source) : ℕ :=
  Fintype.card {j // ∃ r : Fin 24, ∀ f, cubes j f = sourceFaces i (ColourCubes.rotations r f)}

/-- Some family of four-colour cubes with these rotation-class counts has no frame. -/
def FrameFails (k : ℕ) (x : Inventory) : Prop :=
  ∃ m, ∃ cubes : Fin m → Fin 6 → Colour,
    (∀ j, Uses 4 (cubes j)) ∧ classCount cubes = x ∧ ¬ FamilyFrameSolvable k cubes

/-- A failure to which no further cube can be added without creating a frame. -/
def MaximalFrameFails (k : ℕ) (x : Inventory) : Prop :=
  FrameFails k x ∧ ∀ y : Inventory, x ≤ y → FrameFails k y → y = x

/-- The structural obstruction: one ordinary orientation and four bounded buckets. -/
def PureBuckets (k : ℕ) (x : Inventory) : Prop :=
  ∃ s : Fin 2, (∀ i, 0 < x i → i ∈ ordinary s) ∧
    ∀ a, mass x (bucket a) ≤ 4*k+7

theorem family_frame_stability {m : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hm : 14*n ≤ m) :
    ¬ FamilyFrameSolvable (n-2) cubes ↔ PureBuckets (n-2) (classCount cubes) := by sorry

/-- Sizes `16n-4-d` with `n=k+2`, `0 ≤ d ≤ 2n-4`. -/
theorem family_stability_failure_count (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Nat.card {x : Inventory // total x + d = 16*k+28 ∧ FrameFails k x} =
      2 * (d+15).choose 15 := by sorry

theorem family_stability_maximal_count (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Nat.card {x : Inventory // total x + d = 16*k+28 ∧ MaximalFrameFails k x} =
      2 * (d+11).choose 11 := by sorry

/-- The eight T and twenty-four P varieties. -/
def nearSupport : SourceSet :=
  letI : NeZero 2 := frameFinTwo
  ordinary 0 ∪ ordinary 1

/-- One parameter for each of the eight T and twenty-four P varieties. -/
abbrev NearParameter := {i : Source // i ∈ nearSupport}

def nearOrientation (p : NearParameter) : Fin 2 :=
  letI : NeZero 2 := frameFinTwo
  if p.val ∈ ordinary 0 then 0 else 1

/-- A T parameter deletes that T; a P parameter lowers its two T buckets
and inserts the parameter itself. This is the twenty-seven-cube case. -/
def nearBase (p : NearParameter) : Inventory := fun i =>
  if i ∈ extremalSupport (nearOrientation p) then
    7 - if ∃ a : Colour, i ∈ triple a ∧ p.val ∈ bucket a then 1 else 0
  else if p.val ∈ allPairs ∧ i = p.val then 1 else 0

/-- Increase each of the four T multiplicities by `4k`, where `n=k+2`. -/
def nearInventory (k : ℕ) (p : NearParameter) : Inventory := fun i =>
  nearBase p i + if i ∈ extremalSupport (nearOrientation p) then 4*k else 0

theorem family_near_frame_classification (k : ℕ)
    (cubes : Fin (16*k+27) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilyFrameSolvable k cubes ↔ ∃ p : NearParameter, ∀ i : Source,
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = nearInventory k p i := by sorry

theorem family_near_failure_count (k : ℕ) :
    Nat.card {x : Inventory // total x = 16*k+27 ∧ FrameFails k x} = 32 := by sorry

theorem family_near_pair_maximal (k : ℕ) (p : NearParameter) (hp : p.val ∈ allPairs) :
    MaximalFrameFails k (nearInventory k p) := by sorry

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

theorem frame_target_count :
    (Finset.univ.filter FrameTarget).card = 40 := by sorry

theorem family_restricted_frame_of_le {m : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hm : 16*k+29 ≤ m) :
    ∃ t : Target, FrameTarget t ∧ Uses 3 (targetFaces t) ∧
      ∃ p : FrameSlot k ↪ Fin m,
        ∀ q, FacesFit (cubes (p q)) (targetFaces t) (frameExposed k q) := by sorry


namespace Cuboid
def threshold (a b c : ℕ) : ℕ := max (max (16*a-3) (4*(a+b+c)-16)) ((24*c-1)/5)
end Cuboid

theorem cuboid_frame_threshold (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    IsLeast {v : ℕ | ∀ n, ∀ cubes : Fin n → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ n → FamilyBoxFrameSolvable ![a-2,b-2,c-2] cubes}
      (max (max (16*a-3) (4*(a+b+c)-16)) ((24*c-1)/5)) := by sorry

theorem cuboid_full_threshold (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    IsLeast {v : ℕ | ∀ n, ∀ cubes : Fin n → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ n → FamilyBoxFullSolvable ![a-2,b-2,c-2] cubes}
      (max (a*b*c) (max (16*a-3) ((24*c-1)/5))) := by sorry

theorem cuboid_frame_exact_cardinality (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    Cuboid.threshold a b c = 4*(a+b+c)-16 ↔ 3*a+4 ≤ b+c ∧ c ≤ 5*(a+b)-19 := by sorry

theorem family_cuboid_full_of_volume (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hshort : 16*a-3 ≤ a*b*c) (hlong : (24*c-1)/5 ≤ a*b*c)
    (cubes : Fin (a*b*c) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable ![a-2,b-2,c-2] cubes := by sorry

theorem cuboid_full_exact_volume (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    max (a*b*c) (max (16*a-3) ((24*c-1)/5)) = a*b*c ↔
      3 ≤ b ∧ (4 ≤ b ∨ 5 ≤ c) := by sorry

lemma boxFrameSlot_card (l : Fin 3 → ℕ) :
    Fintype.card (BoxFrameSlot l) = 8 + 4 * (l 0 + l 1 + l 2) := by sorry

lemma boxFullSlot_card (l : Fin 3 → ℕ) :
    Fintype.card (BoxFullSlot l) = (l 0 + 2) * (l 1 + 2) * (l 2 + 2) := by sorry

theorem boxFull_iff_frame_and_size {m : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable l cubes ↔ FamilyBoxFrameSolvable l cubes ∧
      (l 0 + 2) * (l 1 + 2) * (l 2 + 2) ≤ m := by sorry

theorem rod_frame_threshold (l : ℕ) (hl : 2 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFrameSolvable ![0,0,l-2] cubes}
      (max 29 ((24*l-1)/5)) := by sorry

theorem strip_frame_threshold (l : ℕ) (hl : 3 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFrameSolvable ![0,1,l-2] cubes}
      (max 29 ((24*l-1)/5)) := by sorry

theorem rod_full_threshold (l : ℕ) (hl : 2 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFullSolvable ![0,0,l-2] cubes}
      (max 29 ((24*l-1)/5)) := by sorry

theorem strip_full_threshold (l : ℕ) (hl : 3 ≤ l) :
    IsLeast {v : ℕ | ∀ m, ∀ cubes : Fin m → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → v ≤ m → FamilyBoxFullSolvable ![0,1,l-2] cubes}
      (max 29 (6*l)) := by sorry

theorem strip_full_of_five_le (l : ℕ) (hl : 5 ≤ l)
    (cubes : Fin (6*l) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyBoxFullSolvable ![0,1,l-2] cubes := by sorry

end ThreeColour
