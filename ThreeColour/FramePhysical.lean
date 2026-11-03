module
public import ThreeColour.FrameDefs
public import ThreeColour.Family
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

/-- Exterior faces prescribed at a frame position. -/
def frameExposed (k : ℕ) (q : FrameSlot k) : Finset (Fin 6) :=
  letI : NeZero 2 := frameFinTwo
  match q with
  | .inl p => Finset.univ.image (ColourCubes.exposedFaces p)
  | .inr p => {edgeFaces p.1 0, edgeFaces p.1 1}

def FacesFit (c t : Fin 6 → Colour) (faces : Finset (Fin 6)) : Prop :=
  ∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧ ∀ f ∈ faces, c (r f) = t f

/-- An arbitrary indexed family builds a frame using real proper rotations. -/
def FamilyFrameSolvable {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour) : Prop :=
  ∃ target : Fin 6 → Colour, Uses 3 target ∧
    ∃ p : FrameSlot k ↪ Fin m, ∀ q, FacesFit (cubes (p q)) target (frameExposed k q)

lemma edge_rotation_complete : ∀ e : Fin 12, ∀ f g : Fin 6,
    f.val / 2 ≠ g.val / 2 → ∃ r : Fin 24,
      ColourCubes.rotations r (edgeFaces e 0) = f ∧
      ColourCubes.rotations r (edgeFaces e 1) = g := by decide +kernel

lemma edge_rotation_adjacent : ∀ r : Fin 24, ∀ e : Fin 12,
    (ColourCubes.rotations r (edgeFaces e 0)).val / 2 ≠
      (ColourCubes.rotations r (edgeFaces e 1)).val / 2 := by decide +kernel

lemma edge_fits_iff (c t : Fin 6 → Colour) (e : Fin 12) :
    HasEdge c (t (edgeFaces e 0)) (t (edgeFaces e 1)) ↔
      FacesFit c t {edgeFaces e 0,edgeFaces e 1} := by
  constructor
  · rintro ⟨f,g,hfg,hf,hg⟩
    obtain ⟨r,hr0,hr1⟩ := edge_rotation_complete e f g hfg
    refine ⟨ColourCubes.rotations r, (ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩, ?_⟩
    intro h hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · simpa only [hr0] using hf
    · simpa only [hr1] using hg
  · rintro ⟨r,hr,h⟩
    obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff r).mp hr
    exact ⟨_,_,edge_rotation_adjacent r e,h _ (by simp),h _ (by simp)⟩

lemma frame_fits_iff (k : ℕ) (t : Target) (q : FrameSlot k) (i : Source) :
    frameFits k t q i ↔ FacesFit (sourceFaces i) (targetFaces t) (frameExposed k q) := by
  cases q with
  | inl q =>
    rw [frameFits, fits_physical]
    constructor
    · rintro ⟨r,hr⟩
      refine ⟨ColourCubes.rotations r, (ColourCubes.proper_rotation_iff _).mpr ⟨r,rfl⟩, ?_⟩
      intro f hf
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hf
      exact hr a
    · rintro ⟨r,hr,h⟩
      obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff r).mp hr
      exact ⟨r,fun a => h _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)⟩
  | inr q => exact edge_fits_iff _ _ q.1

lemma familyFrame_at_of_inventory {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (t : Target)
    (p : FrameSlot k ↪ Stock (familyInventory cubes))
    (hp : ∀ q, frameFits k t q (p q).1) :
    ∃ f : FrameSlot k ↪ Fin m,
      ∀ q, FacesFit (cubes (f q)) (targetFaces t) (frameExposed k q) := by
  refine ⟨p.trans (familyStockEquiv cubes).toEmbedding, ?_⟩
  intro q
  obtain ⟨r,hr,hfit⟩ := (frame_fits_iff k t q (p q).1).mp (hp q)
  obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff r).mp hr
  let j := familyStockEquiv cubes (p q)
  let v := rawRotation (encode (cubes j))
  obtain ⟨s,hs⟩ := ColourCubes.rotation_inverse v
  obtain ⟨u,hu⟩ := ColourCubes.rotation_composition s r
  refine ⟨ColourCubes.rotations u, (ColourCubes.proper_rotation_iff _).mpr ⟨u,rfl⟩, ?_⟩
  intro f hf
  change cubes j (ColourCubes.rotations u f) = _
  rw [familySource_faces cubes hc j,hu,hs,familyStock_source]
  exact hfit f hf

lemma familyFrame_of_inventory {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (h : FrameSolvable k (familyInventory cubes)) :
    FamilyFrameSolvable k cubes := by
  obtain ⟨t,p,hp⟩ := h
  exact ⟨targetFaces t, targets_use_three t, familyFrame_at_of_inventory k cubes hc t p hp⟩

end ThreeColour
