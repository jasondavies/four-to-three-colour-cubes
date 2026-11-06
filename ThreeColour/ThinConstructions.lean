module

public import ThreeColour.ThinGeometry
public import ThreeColour.ThinBounds

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- Numerical criterion for a D corner solution in the reduced inventory. -/
def ThinGood (x : Inventory) (d : Colour) : Prop :=
  4 ≤ mass x (ordinary 0) + mass x (eligible d) ∧
  4 ≤ mass x (ordinary 1) + mass x (eligible d) ∧
  8 ≤ mass x (ordinary 0) + mass x (ordinary 1) + mass x (eligible d)

lemma thin_good_large (x : Inventory) (d : Colour) (h : 8 ≤ mass x (eligible d)) : ThinGood x d := by
  unfold ThinGood
  omega

lemma thin_good_union (x : Inventory) (d : Colour) (h : ThinGood x d) :
    8 ≤ mass x ((ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d)) := by
  have heq : (ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d) =
      (ordinary 0 ∪ ordinary 1) ∪ eligible d := (Finset.union_union_distrib_right _ _ _).symm
  rw [heq, mass_union x _ _ (ordinary_union_eligible_disjoint d),
    mass_union x _ _ ordinary_disjoint]
  exact h.2.2

lemma strip_d (q : ℕ) (hq : 1 ≤ q) (x : Inventory)
    (hN : Thin.threshold (q+2) ≤ total x) (hex : ∃ d, ThinGood x d) :
    BoxInventorySolvable ![0,1,q] x := by
  obtain ⟨h29, hsp, hNs⟩ := Thin.threshold_bounds (by omega : 2 ≤ q+2) hN
  have hw : Thin.weight (fun j => mass x (thinChecker j)) ≤ total x := by
    rw [thin_weight]
    exact mass_mono x (Finset.subset_univ _)
  obtain ⟨d,e,f,hd,he,hf,hef,hxe,hxf⟩ := Thin.strip_pairs
    (fun j => mass x (thinChecker j)) (ThinGood x) h29 (by omega) hw hNs
    (fun v hv => thin_good_large x v (by rwa [thin_degree] at hv)) hex
  obtain ⟨a,b,c,h,habe,hacf⟩ := thin_selection_colours d e f he hf hef
  apply strip_at_of_hall q x 0 a b c d h 0
  apply groupHall_extend x _ _ _ _ 8
  · change PoolHall x _ _
    apply q_pool_hall x _ _ _ _ 0 rfl
    · simpa only [mass_union x _ _ (ordinary_eligible_disjoint 0 d)] using hd.1
    · simpa only [mass_union x _ _ (ordinary_eligible_disjoint 1 d)] using hd.2.1
    · simpa using thin_good_union x d hd
    · exact le_trans (by omega) h29
  · norm_num [thinBaseDemand, Fin.sum_univ_succ]
  · intro j
    have hp0 := thin_pair_supply x a b h.1
    have hp1 := thin_pair_supply x a c h.2.1
    rw [habe] at hp0
    rw [hacf] at hp1
    have hp2 := (thin_good_union x d hd).trans
      (mass_mono x (thin_eligible_edge a b c d h))
    fin_cases j <;> simp [thinEdgePools, thinEdgeDemand, thinEdgeConstant, thinEdgeSlope] <;> omega
  · exact thin_edge_cover a b c h.1 h.2.1 h.2.2.1
  · simp [thinEdgeDemand, thinEdgeConstant, thinEdgeSlope, Fin.sum_univ_succ]
    change 8 + (q * 4 + 4) ≤ total x
    omega

lemma thin_nogood_bounds (x : Inventory) (hN : 29 ≤ total x)
    (hn : ¬ ∃ d, ThinGood x d) (s : Fin 2)
    (hs : mass x (ordinary (flip s)) ≤ mass x (ordinary s)) :
    (∀ d, mass x (ordinary (flip s)) + mass x (eligible d) ≤ 3) ∧
    23 ≤ mass x (ordinary s) ∧
    (∀ j, mass x (thinChecker j) ≤ 3) := by
  have hb (d : Colour) : mass x (eligible d) ≤ 7 := by
    by_contra h
    exact hn ⟨d, thin_good_large x d (by omega)⟩
  have hz := eligible_totals x
  have ho := ordered_totals x s
  have hm (d : Colour) : mass x (ordinary (flip s)) + mass x (eligible d) ≤ 3 := by
    have hc := hb
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hc hz
    have hA : 8 ≤ mass x (ordinary s) := by omega
    by_contra h
    apply hn
    refine ⟨d, ?_⟩
    unfold ThinGood
    fin_cases s <;> norm_num [flip] at * <;> omega
  refine ⟨hm, ?_, ?_⟩
  · have hh := hm
    norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hh hz
    omega
  · intro j
    obtain ⟨d, hd⟩ := thin_checker_eligible j
    have := mass_mono x hd
    have := hm d
    omega

lemma strip_noD_hall (q : ℕ) (hq : 1 ≤ q) (x : Inventory)
    (hN : Thin.threshold (q+2) ≤ total x) (hx : ∀ j, mass x (thinChecker j) ≤ 3)
    (kind : Fin 4) (hk : kind ≠ 0) (a b c d : Colour) (h : ThinDistinct a b c d) (s : Fin 2)
    (hbase : GroupHall x (thinBasePools kind a b c d s) (thinBaseDemand kind)) :
    BoxInventorySolvable ![0,1,q] x := by
  obtain ⟨h29,hsp,_⟩ := Thin.threshold_bounds (by omega : 2 ≤ q+2) hN
  apply strip_at_of_hall q x kind a b c d h s
  apply groupHall_extend x _ _ _ _ (∑ i, thinBaseDemand kind i) hbase le_rfl
  · intro j
    have hab := thin_pair_supply x a b h.1
    have hac := thin_pair_supply x a c h.2.1
    have hbc := thin_pair_supply x b c h.2.2.1
    have xa := hx (thinPairIndex a b)
    have xb := hx (thinPairIndex a c)
    have xc := hx (thinPairIndex b c)
    fin_cases kind <;> fin_cases j <;>
      norm_num [thinBaseDemand, thinEdgeDemand, thinEdgeConstant, thinEdgeSlope,
        thinEdgePools, Fin.sum_univ_succ] at * <;> omega
  · exact thin_edge_cover a b c h.1 h.2.1 h.2.2.1
  · change (∑ i, thinBaseDemand kind i) + (∑ j, thinEdgeDemand kind q j) ≤ total x
    fin_cases kind <;>
      simp_all [thinBaseDemand, thinEdgeDemand, thinEdgeConstant, thinEdgeSlope,
        Fin.sum_univ_succ] <;> omega

lemma strip_q (q : ℕ) (hq : 1 ≤ q) (x : Inventory)
    (hN : Thin.threshold (q+2) ≤ total x) (hx : ∀ j, mass x (thinChecker j) ≤ 3)
    (a b c d : Colour) (h : ThinDistinct a b c d) (s : Fin 2)
    (hb : 4 ≤ mass x (support a b ∩ ordinary s))
    (hc : 4 ≤ mass x (support a c ∩ ordinary s))
    (hbucket : 8 ≤ mass x (bucket a ∩ ordinary s))
    (ho : 23 ≤ mass x (ordinary s)) : BoxInventorySolvable ![0,1,q] x := by
  apply strip_noD_hall q hq x hN hx 1 (by decide) a b c d h s
  exact q_pool_hall x _ _ _ _ 0 (q_frame_union a b c h.1 h.2.1 h.2.2.1 s)
    hb hc hbucket (by omega)

lemma strip_h (q : ℕ) (hq : 1 ≤ q) (x : Inventory)
    (hN : Thin.threshold (q+2) ≤ total x) (hx : ∀ j, mass x (thinChecker j) ≤ 3)
    (kind : Fin 4) (hk : kind = 2 ∨ kind = 3)
    (a b c d : Colour) (h : ThinDistinct a b c d) (s : Fin 2)
    (ha : thinBaseDemand kind 0 ≤ mass x (tripleClass a s))
    (hb : thinBaseDemand kind 1 ≤ mass x (tripleClass b s))
    (hm : 1 ≤ mass x (minorityPool s d)) (ho : 23 ≤ mass x (ordinary s)) :
    BoxInventorySolvable ![0,1,q] x := by
  apply strip_noD_hall q hq x hN hx kind (by rcases hk with rfl | rfl <;> decide) a b c d h s
  obtain ⟨hAB,hAC,hBC,hCD⟩ := u_pool_geometry a b d h.1 s
  rcases hk with rfl | rfl
  · exact u_pool_hall x _ _ _ _ 6 2 1 1 hAB hAC hBC hCD ha hb hm (by omega)
  · exact u_pool_hall x _ _ _ _ 4 3 1 1 hAB hAC hBC hCD ha hb hm (by omega)

end ThreeColour
