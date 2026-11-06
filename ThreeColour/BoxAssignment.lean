module

public import ThreeColour.BoxModel
public import ThreeColour.BoxMatching

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Cyclic compatibility for an arbitrary oriented target, without canonicalising its axes. -/
def boxCornerFits (t : Fin 6 → Colour) (p : Slot) (i : Source) : Prop :=
  cornerCode (ColourCubes.Geometry.corner t p) ∈ sourceCorners i

instance (t : Fin 6 → Colour) (p : Slot) (i : Source) : Decidable (boxCornerFits t p i) := by
  unfold boxCornerFits
  infer_instance

lemma boxCornerFits_physical (t : Fin 6 → Colour) (p : Slot) (i : Source) :
    boxCornerFits t p i ↔
      FacesFit (sourceFaces i) t (Finset.univ.image (ColourCubes.exposedFaces p)) := by
  unfold boxCornerFits
  rw [source_corners_correct]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, cornerCode_eq_iff]
  rw [← ColourCubes.Geometry.corner_rotation_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨ColourCubes.rotations r, (ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩, ?_⟩
    intro f hf
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hf
    exact hr a
  · rintro ⟨r, hr, hf⟩
    obtain ⟨r, rfl⟩ := (ColourCubes.proper_rotation_iff _).mp hr
    exact ⟨r, fun a => hf _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)⟩

/-- Transport any catalogue placement of prescribed exposed faces to original copies. -/
lemma family_faces_of_inventory {m : ℕ} {P : Type*}
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (t : Fin 6 → Colour) (faces : P → Finset (Fin 6))
    (p : P ↪ Stock (familyInventory cubes))
    (hp : ∀ q, FacesFit (sourceFaces (p q).1) t (faces q)) :
    ∃ f : P ↪ Fin m, ∀ q, FacesFit (cubes (f q)) t (faces q) := by
  refine ⟨p.trans (familyStockEquiv cubes).toEmbedding, ?_⟩
  intro q
  obtain ⟨r, hr, hfit⟩ := hp q
  obtain ⟨r, rfl⟩ := (ColourCubes.proper_rotation_iff _).mp hr
  let j := familyStockEquiv cubes (p q)
  let v := rawRotation (encode (cubes j))
  obtain ⟨s, hs⟩ := ColourCubes.rotation_inverse v
  obtain ⟨u, hu⟩ := ColourCubes.rotation_composition s r
  refine ⟨ColourCubes.rotations u, (ColourCubes.proper_rotation_iff _).mpr ⟨u,rfl⟩, ?_⟩
  intro f hf
  change cubes j (ColourCubes.rotations u f) = _
  rw [familySource_faces cubes hc j, hu, hs, familyStock_source]
  exact hfit f hf

/-- A catalogue matching, with every occurrence kept as a separate position. -/
def BoxInventorySolvable (l : Fin 3 → ℕ) (x : Inventory) : Prop :=
  ∃ t : Fin 6 → Colour, Uses 3 t ∧ ∃ p : BoxFrameSlot l ↪ Stock x,
    ∀ q, FacesFit (sourceFaces (p q).1) t (boxFrameExposed l q)

lemma familyBox_of_inventory {m : ℕ} (l : Fin 3 → ℕ)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (h : BoxInventorySolvable l (familyInventory cubes)) : FamilyBoxFrameSolvable l cubes := by
  obtain ⟨t, ht, p, hp⟩ := h
  exact ⟨t, ht, family_faces_of_inventory cubes hc t _ p hp⟩

def boxTag {I : Type*} (l : Fin 3 → ℕ) (c : Slot → I) (e : Fin 12 → I) :
    BoxFrameSlot l → I := Sum.elim c (fun p => e p.1)

def boxCount {I : Type*} [DecidableEq I] {n : ℕ} (tag : Fin n → I) (j : I) : ℕ :=
  ∑ p, if tag p = j then 1 else 0

lemma boxTag_count {I : Type*} [DecidableEq I] (l : Fin 3 → ℕ)
    (c : Slot → I) (e : Fin 12 → I) (j : I) :
    Fintype.card {p // boxTag l c e p = j} = boxCount c j +
      ∑ p, l (boxEdgeAxis p) * (if e p = j then 1 else 0) := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, boxTag, Sum.elim_inl, Sum.elim_inr, boxCount]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

lemma stripTag_count {I : Type*} [DecidableEq I] (q : ℕ)
    (c : Slot → I) (e : Fin 12 → I) (j : I) :
    Fintype.card {p // boxTag ![0,1,q] c e p = j} = boxCount c j +
      boxCount (fun k : Fin 4 => e (![2,3,6,7] k)) j +
      q * boxCount (fun k : Fin 4 => e (![0,1,4,5] k)) j := by
  rw [boxTag_count, Nat.add_assoc]
  congr 1
  let w : Fin 12 → ℕ := fun k => if e k = j then 1 else 0
  simp only [boxCount, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change q*w 0 + (q*w 1 + (1*w 2 + (1*w 3 + (q*w 4 + (q*w 5 +
    (1*w 6 + (1*w 7 + (0*w 8 + (0*w 9 + (0*w 10 + (0*w 11 + 0))))))))))) =
    (w 2 + (w 3 + (w 6 + (w 7 + 0)))) + q * (w 0 + (w 1 + (w 4 + (w 5 + 0))))
  ring

lemma box_at_of_pools {I : Type*} [Fintype I] [DecidableEq I]
    (l : Fin 3 → ℕ) (x : Inventory) (t : Fin 6 → Colour)
    (g : I → SourceSet) (c : Slot → I) (e : Fin 12 → I) (d : I → ℕ)
    (hc : ∀ p i, i ∈ g (c p) → boxCornerFits t p i)
    (he : ∀ p i, i ∈ g (e p) → HasEdge (sourceFaces i) (t (edgeFaces p 0)) (t (edgeFaces p 1)))
    (hd : ∀ j, Fintype.card {p // boxTag l c e p = j} ≤ d j)
    (hh : GroupHall x g d) :
    ∃ f : BoxFrameSlot l ↪ Stock x, ∀ p,
      FacesFit (sourceFaces (f p).1) t (boxFrameExposed l p) := by
  obtain ⟨f, hf⟩ := grouped_assignment x g (boxTag l c e) d hd hh
  refine ⟨f, ?_⟩
  intro p
  cases p with
  | inl p => exact (boxCornerFits_physical t p _).mp (hc p _ (hf (.inl p)))
  | inr p => exact (edge_fits_iff _ _ p.1).mp (he p.1 _ (hf (.inr p)))

end ThreeColour
