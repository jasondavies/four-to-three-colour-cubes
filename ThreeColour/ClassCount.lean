module
public import ThreeColour.FrameFamily
public import ThreeColour.InventoryFamily
@[expose] public section
namespace ThreeColour

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

lemma classCount_eq {m : ℕ} (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    classCount cubes = familyInventory cubes := by
  funext i
  simp only [classCount, ← familySource_eq_iff cubes hc, familyInventory]

/-- Physical failure depends only on rotation-class counts. -/
lemma frameFails_iff (k : ℕ) (x : Inventory) : FrameFails k x ↔ ¬ FrameSolvable k x := by
  constructor
  · rintro ⟨m, cubes, hc, hx, hn⟩
    rwa [familyFrame_iff k cubes hc, ← classCount_eq cubes hc, hx] at hn
  · intro hn
    have hc := inventoryFamily_uses_four x
    refine ⟨total x, inventoryFamily x, hc, ?_, ?_⟩
    · rw [classCount_eq _ hc, inventoryFamily_inventory]
    · rwa [familyFrame_iff k _ hc, inventoryFamily_inventory]

lemma frameSolvable_mono (k : ℕ) {x y : Inventory} (hxy : x ≤ y) (h : FrameSolvable k x) :
    FrameSolvable k y := by
  obtain ⟨t, p, hp⟩ := h
  let e : Stock x ↪ Stock y :=
    Function.Embedding.sigmaMap (Function.Embedding.refl Source)
      (fun i => Fin.castLEEmb (hxy i))
  exact ⟨t, p.trans e, fun q => hp q⟩

end ThreeColour
