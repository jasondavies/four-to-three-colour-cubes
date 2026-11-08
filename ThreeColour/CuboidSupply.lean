module

public import ThreeColour.CuboidTemplateChecks
public import ThreeColour.FrameCounting

@[expose] public section
namespace ThreeColour
open scoped BigOperators

lemma cuboid_degree (x : Inventory) (v : Colour) :
    Checkerboard.degree (fun j => mass x (checkerPair j)) v = mass x (eligible v) := by
  rw [eligible_decomposition]
  fin_cases v <;> simp [Checkerboard.degree, checkerPair, omitted, Fin.sum_univ_succ] <;> omega

lemma cuboid_weight (x : Inventory) :
    Checkerboard.weight (fun j => mass x (checkerPair j)) = mass x allCheckers := by
  rw [← checker_totals]
  simp [Checkerboard.weight, checkerPair, Fin.sum_univ_succ]
  omega

lemma cuboid_pair_supply (x : Inventory) (a b : Colour) (hab : a ≠ b) :
    total x ≤ mass x (cuboidPairPool a b) + mass x (checkerPair (colourPairIndex a b)) := by
  rw [total, ← cuboid_pair_complement a b hab]
  exact mass_union_le x _ _

end ThreeColour
