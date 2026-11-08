module

public import ThreeColour.CuboidTemplates

@[expose] public section
namespace ThreeColour

/-- Six actual checkerboards, indexed by their missing pair in K4 edge order. -/
def checkerSource : Fin 6 → Source := ![32,43,56,6,7,3]

set_option maxRecDepth 100000 in
lemma checker_corner_tricoloured : ∀ (j : Fin 6) (c : Fin 3 → Colour),
    cornerCode c ∈ sourceCorners (checkerSource j) → Function.Injective c := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma checker_edge_iff : ∀ j a b, a ≠ b →
    (HasEdge (sourceFaces (checkerSource j)) a b ↔ j ≠ colourPairIndex a b) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A three-colour target with only tricoloured corners has opposite equal faces. -/
lemma tricoloured_target_opposite : ∀ t : Fin 6 → Colour, Uses 3 t →
    (∀ p : Slot, Function.Injective (ColourCubes.Geometry.corner t p)) →
    t 0 = t 1 ∧ t 2 = t 3 ∧ t 4 = t 5 ∧ t 0 ≠ t 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma corner_two_axes : ∀ p : Slot, ∃ f g : Fin 6,
    f ∈ Finset.univ.image (ColourCubes.exposedFaces p) ∧
    g ∈ Finset.univ.image (ColourCubes.exposedFaces p) ∧ f.val / 2 = 0 ∧ g.val / 2 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma long_edge_two_axes : ∀ e : Fin 12, boxEdgeAxis e = 2 →
    (edgeFaces e 0).val / 2 = 0 ∧ (edgeFaces e 1).val / 2 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
lemma rotation_adjacent_faces : ∀ r : Fin 24, ∀ f g : Fin 6,
    f.val / 2 ≠ g.val / 2 →
    (ColourCubes.rotations r f).val / 2 ≠ (ColourCubes.rotations r g).val / 2 := by
  decide +kernel

lemma rod_position_two_axes (q : ℕ) (p : BoxFrameSlot ![0,0,q]) :
    ∃ f g : Fin 6, f ∈ boxFrameExposed ![0,0,q] p ∧
      g ∈ boxFrameExposed ![0,0,q] p ∧ f.val / 2 = 0 ∧ g.val / 2 = 1 := by
  cases p with
  | inl p => exact corner_two_axes p
  | inr p =>
    have he : boxEdgeAxis p.1 = 2 := by
      by_contra hne
      have hz : ∀ e : Fin 12, boxEdgeAxis e ≠ 2 →
          (![0,0,q] : Fin 3 → ℕ) (boxEdgeAxis e) = 0 := by
        intro e
        fin_cases e <;> simp [boxEdgeAxis]
      have hp := p.2.isLt
      have hh := hz p.1 hne
      omega
    obtain ⟨h0,h1⟩ := long_edge_two_axes p.1 he
    exact ⟨edgeFaces p.1 0,edgeFaces p.1 1,by simp [boxFrameExposed],
      by simp [boxFrameExposed],h0,h1⟩

/-- All rod positions, including the corners, require its transverse colour pair. -/
lemma rod_position_requires_pair (q : ℕ) (p : BoxFrameSlot ![0,0,q])
    (c t : Fin 6 → Colour) (h0 : t 0 = t 1) (h1 : t 2 = t 3)
    (h : FacesFit c t (boxFrameExposed ![0,0,q] p)) : HasEdge c (t 0) (t 2) := by
  obtain ⟨f,g,hf,hg,hfa,hga⟩ := rod_position_two_axes q p
  obtain ⟨r,hr,hh⟩ := h
  obtain ⟨r,rfl⟩ := (ColourCubes.proper_rotation_iff _).mp hr
  have ha : t f = t 0 := by fin_cases f <;> norm_num at hfa <;> simp_all
  have hb : t g = t 2 := by fin_cases g <;> norm_num at hga <;> simp_all
  exact ⟨ColourCubes.rotations r f,ColourCubes.rotations r g,
    rotation_adjacent_faces r f g (by omega), (hh f hf).trans ha, (hh g hg).trans hb⟩

end ThreeColour
