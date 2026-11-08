module
public import ThreeColour.FramePhysical
public import ThreeColour.FrameTheorems
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

lemma edgeRotation_bijective : ∀ r, Function.Bijective (edgeRotation r) := by decide +kernel

noncomputable def edgeEquiv (r : Fin 24) : Equiv.Perm (Fin 12) :=
  Equiv.ofBijective (edgeRotation r) (edgeRotation_bijective r)

noncomputable def frameSlotEquiv (k : ℕ) (r : Fin 24) : Equiv.Perm (FrameSlot k) :=
  Equiv.sumCongr (ColourCubes.Geometry.slotEquiv r) (Equiv.sigmaCongr (edgeEquiv r) (fun _ => Equiv.refl (Fin k)))

lemma corner_exposed_rotate : ∀ r p,
    Finset.univ.image (ColourCubes.exposedFaces (ColourCubes.Geometry.slotEquiv r p)) =
      (Finset.univ.image (ColourCubes.exposedFaces p)).image (ColourCubes.rotations r) := by
  decide +kernel

lemma edge_exposed_rotate : ∀ r e,
    ({edgeFaces (edgeEquiv r e) 0,edgeFaces (edgeEquiv r e) 1} : Finset (Fin 6)) =
      ({edgeFaces e 0,edgeFaces e 1} : Finset (Fin 6)).image (ColourCubes.rotations r) := by
  decide +kernel

lemma frameExposed_rotate (k : ℕ) (r : Fin 24) (q : FrameSlot k) :
    frameExposed k (frameSlotEquiv k r q) =
      (frameExposed k q).image (ColourCubes.rotations r) := by
  cases q with
  | inl q => exact corner_exposed_rotate r q
  | inr q => exact edge_exposed_rotate r q.1

lemma inventoryFrame_of_family {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) (h : FamilyFrameSolvable k cubes) :
    FrameSolvable k (familyInventory cubes) := by
  classical
  obtain ⟨target,ht,p,hp⟩ := h
  obtain ⟨t,rt,htarget⟩ := target_catalogue_complete target ht
  obtain ⟨ri,hi⟩ := ColourCubes.rotation_inverse rt
  let e := frameSlotEquiv k ri
  let placement := (e.toEmbedding.trans p).trans (familyStockEquiv cubes).symm.toEmbedding
  refine ⟨t,placement,?_⟩
  intro q
  apply (frame_fits_iff k t q (placement q).1).mpr
  obtain ⟨r,hr,hfit⟩ := hp (e q)
  obtain ⟨rf,rfl⟩ := (ColourCubes.proper_rotation_iff r).mp hr
  let j := p (e q)
  let rs := rawRotation (encode (cubes j))
  obtain ⟨u,hu⟩ := ColourCubes.rotation_composition rf ri
  obtain ⟨v,hv⟩ := ColourCubes.rotation_composition rs u
  refine ⟨ColourCubes.rotations v,(ColourCubes.proper_rotation_iff _).mpr ⟨v,rfl⟩,?_⟩
  have hsource : (placement q).1 = familySource cubes j := by
    have hh := familyStock_source cubes ((familyStockEquiv cubes).symm j)
    simpa [placement,j] using hh.symm
  intro f hf
  rw [hsource,hv,hu,← familySource_faces cubes hc j]
  have hmem : ColourCubes.rotations ri f ∈ frameExposed k (e q) := by
    rw [frameExposed_rotate]
    exact Finset.mem_image.mpr ⟨f,hf,rfl⟩
  rw [hfit _ hmem,htarget,hi]

lemma familyFrame_iff {m : ℕ} (k : ℕ) (cubes : Fin m → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    FamilyFrameSolvable k cubes ↔ FrameSolvable k (familyInventory cubes) :=
  ⟨inventoryFrame_of_family k cubes hc,familyFrame_of_inventory k cubes hc⟩

/-- Classification by rotation classes for arbitrary oriented source families. -/
theorem family_frame_classification (k : ℕ) (cubes : Fin (16*k+28) → Fin 6 → Colour)
    (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilyFrameSolvable k cubes ↔ ∃ s : Fin 2, ∀ i : Source,
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = frameExtremal k s i := by
  simp only [← familySource_eq_iff cubes hc]
  rw [familyFrame_iff k cubes hc, frame_classification k _ (familyInventory_total cubes)]
  simp only [funext_iff, familyInventory]

end ThreeColour
