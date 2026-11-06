module

public import ThreeColour.ThinGeometryDefs

@[expose] public section
namespace ThreeColour

set_option maxRecDepth 100000 in
lemma thin_target_uses : ∀ kind a b c, a ≠ b → a ≠ c → b ≠ c →
    Uses 3 (thinTarget kind a b c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma thin_pair_complement : ∀ a b, a ≠ b →
    thinPairPool a b ∪ thinChecker (thinPairIndex a b) = Finset.univ := by decide +kernel

set_option maxRecDepth 100000 in
lemma thin_edge_cover : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ∀ j k : Fin 3,
    j ≠ k → thinEdgePools a b c j ∪ thinEdgePools a b c k = Finset.univ := by decide +kernel

set_option maxRecDepth 100000 in
lemma thin_selection_colours : ∀ v e f, e ∈ Thin.triangle v → f ∈ Thin.triangle v → e ≠ f →
    ∃ a b c, ThinDistinct a b c v ∧ thinPairIndex a b = e ∧ thinPairIndex a c = f := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma thin_eligible_edge : ∀ a b c d, ThinDistinct a b c d →
    (ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d) ⊆ thinPairPool b c := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma thin_checker_eligible : ∀ j, ∃ d, thinChecker j ⊆ eligible d := by decide +kernel

set_option maxRecDepth 100000 in
lemma thin_corners (kind : Fin 4) : ∀ a b c d, ThinDistinct a b c d → ∀ s p i,
    i ∈ Sum.elim (thinBasePools kind a b c d s) (thinEdgePools a b c)
      (thinCornerTag kind a b c s p) → boxCornerFits (thinTarget kind a b c) p i := by
  fin_cases kind <;> decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
lemma thin_edges (kind : Fin 4) : ∀ a b c d, ThinDistinct a b c d → ∀ s p i,
    i ∈ Sum.elim (thinBasePools kind a b c d s) (thinEdgePools a b c)
      (thinEdgeTag kind a b c p) →
    HasEdge (sourceFaces i) (thinTarget kind a b c (edgeFaces p 0))
      (thinTarget kind a b c (edgeFaces p 1)) := by
  fin_cases kind <;> decide +kernel

set_option maxRecDepth 100000 in
lemma thin_counts (kind : Fin 4) : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ∀ s j,
    (boxCount (thinCornerTag kind a b c s) j +
      boxCount (fun k : Fin 4 => thinEdgeTag kind a b c (![2,3,6,7] k)) j =
      Sum.elim (thinBaseDemand kind) (thinEdgeConstant kind) j) ∧
    (boxCount (fun k : Fin 4 => thinEdgeTag kind a b c (![0,1,4,5] k)) j =
      Sum.elim (fun _ => 0) (thinEdgeSlope kind) j) := by
  fin_cases kind <;> decide +kernel

end ThreeColour
