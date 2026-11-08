module

public import ThreeColour.CuboidTemplates

@[expose] public section
namespace ThreeColour

set_option maxRecDepth 100000 in
lemma cuboid_target_uses : ∀ kind a b c, a ≠ b → a ≠ c → b ≠ c →
    Uses 3 (cuboidTarget kind a b c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma cuboid_pair_complement : ∀ a b, a ≠ b →
    cuboidPairPool a b ∪ checkerPair (colourPairIndex a b) = Finset.univ := by decide +kernel

set_option maxRecDepth 100000 in
lemma cuboid_edge_cover : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ∀ j k : Fin 3,
    j ≠ k → cuboidEdgePools a b c j ∪ cuboidEdgePools a b c k = Finset.univ := by decide +kernel

set_option maxRecDepth 100000 in
lemma cuboid_checker_eligible : ∀ j, ∃ d, checkerPair j ⊆ eligible d := by decide +kernel

-- Splitting the colour cases bounds kernel-reduction memory; assembling those
-- cases requires a larger, still bounded, elaboration budget.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma cuboid_corners (kind : Fin 3) : ∀ a b c d, DistinctColours a b c d → ∀ s p i,
    i ∈ Sum.elim (cuboidBasePools kind a b c d s) (cuboidEdgePools a b c)
      (cuboidCornerTag kind a b c s p) → boxCornerFits (cuboidTarget kind a b c) p i := by
  intro a
  fin_cases kind <;> fin_cases a <;> decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma cuboid_edges (kind : Fin 3) : ∀ a b c d, DistinctColours a b c d → ∀ s p i,
    i ∈ Sum.elim (cuboidBasePools kind a b c d s) (cuboidEdgePools a b c)
      (cuboidEdgeTag kind a b c p) →
    HasEdge (sourceFaces i) (cuboidTarget kind a b c (edgeFaces p 0))
      (cuboidTarget kind a b c (edgeFaces p 1)) := by
  intro a
  fin_cases kind <;> fin_cases a <;> decide +kernel

end ThreeColour
