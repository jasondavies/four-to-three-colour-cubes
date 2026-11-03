module
public import ThreeColour.NearClassification
public import ThreeColour.FrameFamily
@[expose] public section
namespace ThreeColour
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Eight deletion parameters and twenty-four pair parameters, without
identifying colour permutations or reflection. -/
theorem near_parameter_counts :
    (Finset.univ.filter fun p : NearParameter => p.val ∈ allTriples).card = 8 ∧
    (Finset.univ.filter fun p : NearParameter => p.val ∈ allPairs).card = 24 := by
  decide +kernel

/-- The near-extremal classification for arbitrary oriented physical cubes. -/
theorem family_near_frame_classification (k : ℕ)
    (cubes : Fin (16*k+27) → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j)) :
    ¬ FamilyFrameSolvable k cubes ↔ ∃ p : NearParameter, ∀ i : Source,
      Fintype.card {j // ∃ r : Fin 24, ∀ f,
        cubes j f = sourceFaces i (ColourCubes.rotations r f)} = nearInventory k p i := by
  simp only [← familySource_eq_iff cubes hc]
  rw [familyFrame_iff k cubes hc]
  have h := near_frame_classification k (familyInventory cubes)
  simp only [familyInventory_total, true_and] at h
  rw [h]
  simp only [nearInventories, Finset.mem_image, Finset.mem_univ, true_and,
    funext_iff, familyInventory]
  constructor <;> rintro ⟨p,hp⟩ <;> exact ⟨p, fun i => (hp i).symm⟩

/-- A guaranteed frame on one of the forty targets, with distinct source
copies and proper rotations at every exposed face. Here `n=k+2 ≥ 3`. -/
theorem family_restricted_frame_of_le {m : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hm : 16*k+29 ≤ m) :
    ∃ t : Target, FrameTarget t ∧ Uses 3 (targetFaces t) ∧
      ∃ p : FrameSlot k ↪ Fin m,
        ∀ q, FacesFit (cubes (p q)) (targetFaces t) (frameExposed k q) := by
  obtain ⟨t,ht,p,hp⟩ := restricted_frame_solvable_of_le k hk (familyInventory cubes)
    (by simpa only [familyInventory_total] using hm)
  exact ⟨t,ht,targets_use_three t,familyFrame_at_of_inventory k cubes hc t p hp⟩
end ThreeColour
