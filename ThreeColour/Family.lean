module

public import ThreeColour.Theorems
public import ThreeColour.FamilyGeometry

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeColour
open scoped BigOperators

/-- The outward coordinate face at a binary cube position, without a lookup table. -/
def outwardFace (k : Fin 8) (axis : Fin 3) : Fin 6 :=
  Fin.ofNat 6 (2 * axis.val + (k.val / 2 ^ (2 - axis.val)) % 2)

lemma outwardFace_eq : outwardFace = MacMahon.exposedFaces := by decide +kernel

/-- A solution for an arbitrary indexed family of face colourings. The target
uses exactly three colours, and rotations are specified geometrically. -/
def FamilySolvable {n : ℕ} (cubes : Fin n → Fin 6 → Colour) : Prop :=
  ∃ target : Fin 6 → Colour, Uses 3 target ∧
    ∃ placement : Fin 8 ↪ Fin n, ∀ k,
      ∃ r : Fin 6 → Fin 6, MacMahon.ProperRotation r ∧
        ∀ axis : Fin 3, cubes (placement k) (r (outwardFace k axis)) =
          target (outwardFace k axis)

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
      (MacMahon.rotations (rawRotation (encode (cubes j))) f) := by
  simpa only [familySource, encode_decode] using
    raw_source_complete (encode (cubes j)) (by simpa only [encode_decode] using hc j)

lemma familySolvable_of_physical {n : ℕ} (cubes : Fin n → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j))
    (h : PhysicalSolvable (familyInventory cubes)) : FamilySolvable cubes := by
  classical
  obtain ⟨t, p, hp⟩ := h
  refine ⟨targetFaces t, targets_use_three t,
    p.trans (familyStockEquiv cubes).toEmbedding, ?_⟩
  intro k
  obtain ⟨r, hr⟩ := hp k
  let j := familyStockEquiv cubes (p k)
  let q := rawRotation (encode (cubes j))
  obtain ⟨s, hs⟩ := MacMahon.rotation_inverse q
  obtain ⟨u, hu⟩ := MacMahon.rotation_composition s r
  refine ⟨MacMahon.rotations u, (MacMahon.proper_rotation_iff _).mpr ⟨u, rfl⟩, ?_⟩
  intro axis
  change cubes j (MacMahon.rotations u (outwardFace k axis)) = _
  rw [familySource_faces cubes hc j, hu, hs, familyStock_source, outwardFace_eq]
  exact hr axis

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
  obtain ⟨ri, hi⟩ := MacMahon.rotation_inverse rt
  let e := Geometry.slotEquiv ri
  let placement := (e.toEmbedding.trans p).trans (familyStockEquiv cubes).symm.toEmbedding
  refine ⟨t, placement, ?_⟩
  intro k
  obtain ⟨r, hr, hfit⟩ := hp (e k)
  obtain ⟨rf, rfl⟩ := (MacMahon.proper_rotation_iff r).mp hr
  let j := p (e k)
  let q := rawRotation (encode (cubes j))
  obtain ⟨u, hu⟩ := MacMahon.rotation_composition rf ri
  obtain ⟨v, hv⟩ := MacMahon.rotation_composition q u
  refine ⟨v, ?_⟩
  have hsource : (placement k).1 = familySource cubes j := by
    have hh := familyStock_source cubes ((familyStockEquiv cubes).symm j)
    simpa [placement, j] using hh.symm
  have hframes : ∀ f : Fin 3,
      sourceFaces (placement k).1 (MacMahon.rotations v (Geometry.frame k f)) =
        targetFaces t (Geometry.frame k f) := by
    intro f
    obtain ⟨s, hs⟩ := Geometry.rotatedSlot_frame ri k
    rw [hsource, hv, hu, ← familySource_faces cubes hc j]
    rw [hs f]
    have hh := hfit (Geometry.cornerOrder (e k) (f + s))
    rw [outwardFace_eq] at hh
    change cubes j (MacMahon.rotations rf (Geometry.frame (e k) (f + s))) =
      target (Geometry.frame (e k) (f + s)) at hh
    rw [hh, htarget, ← hs f, hi]
  intro axis
  simpa only [Geometry.frame, Geometry.cornerOrder_involutive] using
    hframes (Geometry.cornerOrder k axis)

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
