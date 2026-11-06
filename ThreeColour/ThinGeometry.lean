module

public import ThreeColour.ThinGeometryChecks
public import ThreeColour.FrameCounting

@[expose] public section
namespace ThreeColour
open scoped BigOperators

lemma thin_degree (x : Inventory) (v : Colour) :
    Thin.degree (fun j => mass x (thinChecker j)) v = mass x (eligible v) := by
  rw [eligible_decomposition]
  fin_cases v <;> simp [Thin.degree, thinChecker, omitted, Fin.sum_univ_succ] <;> omega

lemma thin_weight (x : Inventory) :
    Thin.weight (fun j => mass x (thinChecker j)) = mass x allCheckers := by
  rw [← checker_totals]
  simp [Thin.weight, thinChecker, Fin.sum_univ_succ]
  omega

lemma thin_pair_supply (x : Inventory) (a b : Colour) (hab : a ≠ b) :
    total x ≤ mass x (thinPairPool a b) + mass x (thinChecker (thinPairIndex a b)) := by
  rw [total, ← thin_pair_complement a b hab]
  exact mass_union_le x _ _

lemma strip_at_of_hall (q : ℕ) (x : Inventory) (kind : Fin 4)
    (a b c d : Colour) (h : ThinDistinct a b c d) (s : Fin 2)
    (hh : GroupHall x (Sum.elim (thinBasePools kind a b c d s) (thinEdgePools a b c))
      (Sum.elim (thinBaseDemand kind) (thinEdgeDemand kind q))) :
    BoxInventorySolvable ![0,1,q] x := by
  refine ⟨thinTarget kind a b c, thin_target_uses _ _ _ _ h.1 h.2.1 h.2.2.1, ?_⟩
  apply box_at_of_pools _ x _ _ (thinCornerTag kind a b c s) (thinEdgeTag kind a b c) _
    (thin_corners kind a b c d h s) (thin_edges kind a b c d h s) _ hh
  intro j
  rw [stripTag_count]
  obtain ⟨hc, he⟩ := thin_counts kind a b c h.1 h.2.1 h.2.2.1 s j
  rw [hc, he]
  cases j <;> simp [thinEdgeDemand]

end ThreeColour
