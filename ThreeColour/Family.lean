module

public import ThreeColour.Theorems
public import ColourCubes.RotationAction

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeColour
open scoped BigOperators

/-- A solution for an arbitrary indexed family of face colourings. The target
uses exactly three colours, and rotations are specified geometrically. -/
def FamilySolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Prop :=
  ColourCubes.HasSolution (Uses 3) cubes

/-- The catalogue index of each individual cube. -/
def familySource {n : ℕ} (cubes : Fin n → Fin 6 → Colour) (j : Fin n) : Source :=
  sourceIndex (encode (cubes j))

def familyInventory {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Inventory :=
  fun i => Fintype.card {j : Fin n // familySource cubes j = i}

/-- Copies in the inventory correspond bijectively to the original indexed cubes. -/
noncomputable def familyStockEquiv {n : ℕ} (cubes : Fin n → Fin 6 → Colour) :
    Stock (familyInventory cubes) ≃ Fin n :=
  (Equiv.sigmaCongrRight fun i =>
    (Fintype.equivFin {j : Fin n // familySource cubes j = i}).symm).trans
      (Equiv.sigmaFiberEquiv (familySource cubes))

lemma familyStock_source {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (q : Stock (familyInventory cubes)) :
    familySource cubes (familyStockEquiv cubes q) = q.1 :=
  ((Fintype.equivFin {j : Fin n // familySource cubes j = q.1}).symm q.2).property

lemma familyInventory_total {n : ℕ} (cubes : Fin n → Fin 6 → Colour) :
    total (familyInventory cubes) = n := by
  have h := Fintype.card_congr (familyStockEquiv cubes)
  simpa [total, mass, Fintype.card_sigma] using h

lemma familySource_faces {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (j : Fin n) :
    ∀ f, cubes j f = sourceFaces (familySource cubes j)
      (ColourCubes.rotations (rawRotation (encode (cubes j))) f) := by
  simpa only [familySource, encode_decode] using
    raw_source_complete (encode (cubes j)) (by simpa only [encode_decode] using hc j)

/-- Transport a fixed target without losing its geometric properties. -/
lemma familyBuilds_of_physical {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (t : Target)
    (p : Slot ↪ Stock (familyInventory cubes))
    (hp : ∀ k, ∃ r : Fin 24, FaceFits t (p k).1 k r) :
    ∃ placement : Fin 8 ↪ Fin n, ∀ k,
      ∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧
        ∀ axis : Fin 3, cubes (placement k) (r (ColourCubes.exposedFaces k axis)) =
          targetFaces t (ColourCubes.exposedFaces k axis) := by
  classical
  refine ⟨p.trans (familyStockEquiv cubes).toEmbedding, ?_⟩
  intro k
  obtain ⟨r, hr⟩ := hp k
  let j := familyStockEquiv cubes (p k)
  let q := rawRotation (encode (cubes j))
  obtain ⟨s, hs⟩ := ColourCubes.rotation_inverse q
  obtain ⟨u, hu⟩ := ColourCubes.rotation_composition s r
  refine ⟨ColourCubes.rotations u, (ColourCubes.proper_rotation_iff _).mpr ⟨u, rfl⟩, ?_⟩
  intro axis
  change cubes j (ColourCubes.rotations u (ColourCubes.exposedFaces k axis)) = _
  rw [familySource_faces cubes hc j, hu, hs, familyStock_source]
  exact hr axis

lemma familySolvable_of_physical {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j))
    (h : PhysicalSolvable (familyInventory cubes)) : FamilySolvable cubes := by
  obtain ⟨t, p, hp⟩ := h
  exact ⟨targetFaces t, targets_use_three t, familyBuilds_of_physical cubes hc t p hp⟩

/-- Every family of at least 29 four-colour cubes has a physical three-colour
solution; no source, target, or rotation catalogue appears in this statement. -/
theorem family_solvable_of_29_le {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (hn : 29 ≤ n) : FamilySolvable cubes := by
  apply familySolvable_of_physical cubes hc
  apply (solvable_iff_physical _).mp
  exact solvable_of_29_le _ (by simpa only [familyInventory_total] using hn)

theorem family_threshold29 (cubes : Fin 29 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) : FamilySolvable cubes :=
  family_solvable_of_29_le cubes hc le_rfl

lemma physical_of_familySolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j))
    (h : FamilySolvable cubes) : PhysicalSolvable (familyInventory cubes) := by
  classical
  obtain ⟨target, ht, p, hp⟩ := h
  obtain ⟨t, rt, htarget⟩ := target_catalogue_complete target ht
  obtain ⟨ri, hi⟩ := ColourCubes.rotation_inverse rt
  let e := ColourCubes.Geometry.slotEquiv ri
  let placement := (e.toEmbedding.trans p).trans (familyStockEquiv cubes).symm.toEmbedding
  refine ⟨t, placement, ?_⟩
  intro k
  obtain ⟨r, hr, hfit⟩ := hp (e k)
  obtain ⟨rf, rfl⟩ := (ColourCubes.proper_rotation_iff r).mp hr
  let j := p (e k)
  let q := rawRotation (encode (cubes j))
  obtain ⟨u, hu⟩ := ColourCubes.rotation_composition rf ri
  obtain ⟨v, hv⟩ := ColourCubes.rotation_composition q u
  refine ⟨v, ?_⟩
  have hsource : (placement k).1 = familySource cubes j := by
    have hh := familyStock_source cubes ((familyStockEquiv cubes).symm j)
    simpa [placement, j] using hh.symm
  have hframes : ∀ f : Fin 3,
      sourceFaces (placement k).1 (ColourCubes.rotations v (ColourCubes.Geometry.frame k f)) =
        targetFaces t (ColourCubes.Geometry.frame k f) := by
    intro f
    obtain ⟨s, hs⟩ := ColourCubes.Geometry.rotatedSlot_frame ri k
    rw [hsource, hv, hu, ← familySource_faces cubes hc j]
    rw [hs f]
    have hh := hfit (ColourCubes.Geometry.cornerOrder (e k) (f + s))
    change cubes j (ColourCubes.rotations rf (ColourCubes.Geometry.frame (e k) (f + s))) =
      target (ColourCubes.Geometry.frame (e k) (f + s)) at hh
    rw [hh, htarget, ← hs f, hi]
  intro axis
  simpa only [ColourCubes.Geometry.frame, ColourCubes.Geometry.cornerOrder_involutive] using
    hframes (ColourCubes.Geometry.cornerOrder k axis)

theorem family_solvable_iff {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    FamilySolvable cubes ↔ PhysicalSolvable (familyInventory cubes) :=
  ⟨physical_of_familySolvable cubes hc, familySolvable_of_physical cubes hc⟩

/-- The complete classification applies to arbitrarily oriented input cubes
after counting their rotation varieties. -/
theorem family_classify28 (cubes : Fin 28 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilySolvable cubes ↔ familyInventory cubes = extremal 0 ∨
      familyInventory cubes = extremal 1 := by
  rw [family_solvable_iff cubes hc]
  exact physical_classify28 _ (familyInventory_total cubes)

/-- Membership in a source rotation class, without the internal encoder. -/
lemma familySource_eq_iff {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (j : Fin n) (i : Source) :
    familySource cubes j = i ↔
      ∃ r : Fin 24, ∀ f, cubes j f = sourceFaces i (ColourCubes.rotations r f) := by
  constructor
  · intro h
    exact ⟨rawRotation (encode (cubes j)), by
      simpa only [h] using familySource_faces cubes hc j⟩
  · rintro ⟨r, hr⟩
    let q := rawRotation (encode (cubes j))
    obtain ⟨s, hs⟩ := ColourCubes.rotation_inverse r
    obtain ⟨u, hu⟩ := ColourCubes.rotation_composition q s
    apply source_catalogue_unique (familySource cubes j) i u
    intro f
    rw [hu, ← familySource_faces cubes hc j, hr, hs]

/-- Classification by geometric rotation-class counts, with no encoder in
its statement. This is the arbitrary-family comparator interface. -/
theorem family_classify28_geometric (cubes : Fin 28 → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilySolvable cubes ↔ ∃ s : Fin 2, ∀ i : Source,
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = extremal s i := by
  have hcount (i : Source) :
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = familyInventory cubes i := by
    simp only [← familySource_eq_iff cubes hc, familyInventory]
  simp only [hcount]
  rw [family_classify28 cubes hc]
  constructor
  · rintro (h | h)
    · exact ⟨0, fun i => congrFun h i⟩
    · exact ⟨1, fun i => congrFun h i⟩
  · rintro ⟨s, hs⟩
    fin_cases s
    · exact Or.inl (funext hs)
    · exact Or.inr (funext hs)

/-- Seven copies of each of the four face tuples printed in the paper. -/
def lowerFamily (j : Fin 28) : Fin 6 → Colour :=
  (![![0,1,0,2,0,3], ![0,1,1,2,1,3], ![0,2,1,2,2,3], ![0,3,1,3,2,3]] :
    Fin 4 → Fin 6 → Colour) (Fin.ofNat 4 (j.val / 7))

lemma lowerFamily_uses_four : ∀ j, Uses 4 (lowerFamily j) := by decide +kernel

lemma lowerFamily_source : ∀ j, familySource lowerFamily j =
    (![10, 23, 45, 66] : Fin 4 → Source) (Fin.ofNat 4 (j.val / 7)) := by
  decide +kernel

lemma lowerFamily_inventory : familyInventory lowerFamily = extremal 0 := by
  funext i
  simp only [familyInventory, lowerFamily_source]
  fin_cases i <;> decide +kernel

lemma lowerFamily_not_solvable : ¬ FamilySolvable lowerFamily := by
  rw [family_solvable_iff lowerFamily lowerFamily_uses_four, lowerFamily_inventory,
    ← solvable_iff_physical]
  exact extremal_not_solvable 0

/-- The sharp threshold expressed solely using actual face colourings. -/
theorem family_sharp_threshold29 :
    (∀ cubes : Fin 29 → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → FamilySolvable cubes) ∧
    ∃ cubes : Fin 28 → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) ∧ ¬ FamilySolvable cubes :=
  ⟨family_threshold29, lowerFamily, lowerFamily_uses_four, lowerFamily_not_solvable⟩

theorem family_least_guaranteed_size :
    IsLeast {m : ℕ | ∀ n, ∀ cubes : Fin n → Fin 6 → Colour,
      (∀ j, Uses 4 (cubes j)) → m ≤ n → FamilySolvable cubes} 29 := by
  constructor
  · intro n cubes hc hn
    exact family_solvable_of_29_le cubes hc hn
  · intro m hm
    by_contra h
    exact lowerFamily_not_solvable (hm 28 lowerFamily lowerFamily_uses_four (by omega))

end ThreeColour
