module

public import Mathlib

@[expose] public section

/-! Independent physical statements. No proof-library imports. The intentional
statement holes are comparator targets, not part of the proof library.
The comparator compares exported declarations, including helper-proof names.
When adding `Fin` literals, preserve the library's named bounds and run the
comparator: ordinary elaboration can accept definitions that it rejects. -/
namespace MacMahon
abbrev Slot := Fin 8
def exposedFaces : Slot → Fin 3 → Fin 6 := ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]
def rotations : Fin 24 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 5, 4], ![0, 1, 4, 5, 3, 2], ![0, 1, 5, 4, 2, 3], ![1, 0, 2, 3, 5, 4], ![1, 0, 3, 2, 4, 5], ![1, 0, 4, 5, 2, 3], ![1, 0, 5, 4, 3, 2], ![2, 3, 0, 1, 5, 4], ![2, 3, 1, 0, 4, 5], ![2, 3, 4, 5, 0, 1], ![2, 3, 5, 4, 1, 0], ![3, 2, 0, 1, 4, 5], ![3, 2, 1, 0, 5, 4], ![3, 2, 4, 5, 1, 0], ![3, 2, 5, 4, 0, 1], ![4, 5, 0, 1, 2, 3], ![4, 5, 1, 0, 3, 2], ![4, 5, 2, 3, 1, 0], ![4, 5, 3, 2, 0, 1], ![5, 4, 0, 1, 3, 2], ![5, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]]
theorem faceOne_bound : 1 < 6 := by decide

def opposite (f : Fin 6) : Fin 6 :=
  if f.val % 2 = 0 then f + ⟨1, faceOne_bound⟩ else f - ⟨1, faceOne_bound⟩
def fromAxes (a b c : Fin 6) : Fin 6 → Fin 6 :=
  ![a, opposite a, b, opposite b, c, opposite c]
def ValidAxes (a b c : Fin 6) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ c.val / 2 ∧
  (a.val % 2 + b.val % 2 + c.val % 2) % 2 =
    ((if a.val / 2 > b.val / 2 then 1 else 0) +
     (if a.val / 2 > c.val / 2 then 1 else 0) +
     (if b.val / 2 > c.val / 2 then 1 else 0)) % 2
def ProperRotation (r : Fin 6 → Fin 6) : Prop :=
  ∃ a b c, ValidAxes a b c ∧ r = fromAxes a b c

theorem proper_rotation_iff (r : Fin 6 → Fin 6) :
    ProperRotation r ↔ ∃ n : Fin 24, r = rotations n := by sorry

theorem exposed_face_rule : ∀ k : Slot, ∀ d : Fin 3,
    (exposedFaces k d).val = 2*d.val + (k.val / 2^(2-d.val)) % 2 := by sorry
end MacMahon
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
def reflectFace (f : Fin 6) : Fin 6 := if f.val < 2 then MacMahon.opposite f else f
def reflectInventory (x : Inventory) : Inventory := fun i => x (reflection i)
def flip : Fin 2 → Fin 2 := ![1,0]
def Uses (n : ℕ) (c : Fin 6 → Colour) : Prop := (Finset.univ.image c).card = n
def FaceFits (t : Target) (i : Source) (k : Slot) (r : Fin 24) : Prop :=
  ∀ f : Fin 3, sourceFaces i (MacMahon.rotations r (MacMahon.exposedFaces k f)) =
    targetFaces t (MacMahon.exposedFaces k f)
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
    ∃ i : Source, ∃ r : Fin 24, ∀ f, c f = sourceFaces i (MacMahon.rotations r f) := by sorry

theorem target_catalogue_complete (c : Fin 6 → Colour) (hc : Uses 3 c) :
    ∃ t : Target, ∃ r : Fin 24, ∀ f, c f = targetFaces t (MacMahon.rotations r f) := by sorry

theorem source_catalogue_unique (i j : Source) (r : Fin 24)
    (h : ∀ f, sourceFaces i (MacMahon.rotations r f) = sourceFaces j f) : i = j := by sorry

theorem reflect_extremal : ∀ s : Fin 2, reflectInventory (extremal s) = extremal (flip s) := by sorry

theorem extremal_distinct : extremal 0 ≠ extremal 1 := by sorry

/-- Actual face colourings and geometric rotations. The outward positions
are pinned by `MacMahon.exposed_face_rule`; no source or target catalogue is used. -/
def FamilySolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Prop :=
  ∃ target : Fin 6 → Colour, Uses 3 target ∧
    ∃ placement : Fin 8 ↪ Fin n, ∀ k,
      ∃ r : Fin 6 → Fin 6, MacMahon.ProperRotation r ∧
        ∀ axis : Fin 3, cubes (placement k) (r (MacMahon.exposedFaces k axis)) =
          target (MacMahon.exposedFaces k axis)

lemma sources_use_four : ∀ i : Source, Uses 4 (sourceFaces i) := by sorry
lemma targets_use_three : ∀ t : Target, Uses 3 (targetFaces t) := by sorry
lemma reflection_geometry : ∀ i : Source, ∀ f : Fin 6,
    sourceFaces (reflection i) (MacMahon.rotations (reflectionRotation i) f) =
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
        cubes j f = sourceFaces i (MacMahon.rotations r f)} = extremal s i := by sorry

end ThreeColour
