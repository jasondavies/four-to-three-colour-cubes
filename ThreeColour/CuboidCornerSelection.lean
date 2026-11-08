module

public import ThreeColour.CuboidSupply

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Numerical criterion for a D corner solution in the reduced inventory. -/
def OppositeCornerSupply (x : Inventory) (d : Colour) : Prop :=
  4 ≤ mass x (ordinary 0) + mass x (eligible d) ∧
  4 ≤ mass x (ordinary 1) + mass x (eligible d) ∧
  8 ≤ mass x (ordinary 0) + mass x (ordinary 1) + mass x (eligible d)

lemma cuboid_good_large (x : Inventory) (d : Colour) (h : 8 ≤ mass x (eligible d)) : OppositeCornerSupply x d := by
  unfold OppositeCornerSupply
  omega

lemma cuboid_good_union (x : Inventory) (d : Colour) (h : OppositeCornerSupply x d) :
    8 ≤ mass x ((ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d)) := by
  have heq : (ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d) =
      (ordinary 0 ∪ ordinary 1) ∪ eligible d := (Finset.union_union_distrib_right _ _ _).symm
  rw [heq, mass_union x _ _ (ordinary_union_eligible_disjoint d),
    mass_union x _ _ ordinary_disjoint]
  exact h.2.2

lemma cuboid_nogood_bounds (x : Inventory) (hN : 29 ≤ total x)
    (hn : ¬ ∃ d, OppositeCornerSupply x d) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    (∀ d, mass x (ordinary (flip s)) + mass x (eligible d) ≤ 3) ∧
    23 ≤ mass x (ordinary s) ∧
    (∀ j, mass x (checkerPair j) ≤ 3) := by
  have hb (d : Colour) : mass x (eligible d) ≤ 7 := by
    by_contra h
    exact hn ⟨d, cuboid_good_large x d (by omega)⟩
  have hz := eligible_totals x
  have ho := ordered_totals x s
  have hm (d : Colour) : mass x (ordinary (flip s)) + mass x (eligible d) ≤ 3 := by
    have hc := hb
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hc hz
    have hA : 8 ≤ mass x (ordinary s) := by omega
    by_contra h
    apply hn
    refine ⟨d, ?_⟩
    unfold OppositeCornerSupply
    fin_cases s <;> norm_num [flip] at * <;> omega
  refine ⟨hm, ?_, ?_⟩
  · have hh := hm
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hh hz
    omega
  · intro j
    obtain ⟨d, hd⟩ := cuboid_checker_eligible j
    have := mass_mono x hd
    have := hm d
    omega

lemma cuboid_fourth : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c →
    ∃ d, DistinctColours a b c d := by decide +kernel

end ThreeColour
