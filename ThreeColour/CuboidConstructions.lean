module

public import ThreeColour.CuboidGeometry
public import ThreeColour.CuboidSelection

@[expose] public section
namespace ThreeColour
open scoped BigOperators

lemma cuboid_d (m t q : ℕ) (hmt : m ≤ t) (htq : t ≤ q) (x : Inventory)
    (hN : Cuboid.threshold (m+2) (t+2) (q+2) ≤ total x) (hex : ∃ d, OppositeCornerSupply x d) :
    BoxInventorySolvable ![m,t,q] x := by
  obtain ⟨hshort,hL,hK⟩ := Cuboid.threshold_le.mp hN
  have h29 : 29 ≤ total x := by omega
  have hw : Checkerboard.weight (fun j => mass x (checkerPair j)) ≤ total x := by
    rw [cuboid_weight]; exact mass_mono x (Finset.subset_univ _)
  obtain ⟨d,e,f,g,hd,he,hf,hg,hef,heg,hfg,hxe,hxf,hxg⟩ :=
    Cuboid.triangle_selection (fun j => mass x (checkerPair j)) (OppositeCornerSupply x)
      (m+2) (t+2) (q+2) (total x) (by omega) (by omega) (by omega) h29 hL hK hw
      (fun v hv => cuboid_good_large x v (by rwa [cuboid_degree] at hv)) hex
  obtain ⟨a,b,c,h,habe,hacf,hbcg⟩ := cuboid_selection_colours d e f g he hf hg hef heg hfg
  apply cuboid_at_of_hall _ x 0 a b c d h 0
  apply groupHall_extend x _ _ _ _ 8
  · have hbase := q_pool_hall x (ordinary 0 ∪ eligible d) (ordinary 1 ∪ eligible d)
      ((ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d)) Finset.univ 0 rfl
      (by simpa only [mass_union x _ _ (ordinary_eligible_disjoint 0 d)] using hd.1)
      (by simpa only [mass_union x _ _ (ordinary_eligible_disjoint 1 d)] using hd.2.1)
      (by simpa using cuboid_good_union x d hd) (by omega : 8 ≤ total x)
    have he : cuboidBaseDemand 0 ![m,t,q] = ![4,4,0,0] := by
      funext i; fin_cases i <;> simp [cuboidBaseDemand,cuboidBaseConst,cuboidBaseAxis,Fin.sum_univ_succ]
    rw [he]
    exact hbase
  · norm_num [cuboidBaseDemand,cuboidBaseConst,cuboidBaseAxis,Fin.sum_univ_succ]
  · intro j
    have hp0 := cuboid_pair_supply x a b h.1
    have hp1 := cuboid_pair_supply x a c h.2.1
    have hp2 := cuboid_pair_supply x b c h.2.2.1
    rw [habe] at hp0; rw [hacf] at hp1; rw [hbcg] at hp2
    fin_cases j <;> simp [cuboidEdgePools,cuboidEdgeDemand,cuboidEdgeAxis,Fin.sum_univ_succ] <;> omega
  · exact cuboid_edge_cover a b c h.1 h.2.1 h.2.2.1
  · simp [cuboidEdgeDemand,cuboidEdgeAxis,Fin.sum_univ_succ]
    change 8 + (q*4 + (t*4 + m*4)) ≤ total x
    omega

lemma cuboid_noD_hall (m t q : ℕ) (hmt : m ≤ t) (htq : t ≤ q) (x : Inventory)
    (hN : Cuboid.threshold (m+2) (t+2) (q+2) ≤ total x)
    (hx : ∀ j, mass x (checkerPair j) ≤ 3)
    (k : Fin 3) (hk : k ≠ 0) (a b c d : Colour) (h : DistinctColours a b c d) (s : Fin 2)
    (hbase : GroupHall x (cuboidBasePools k a b c d s) (cuboidBaseDemand k ![m,t,q])) :
    BoxInventorySolvable ![m,t,q] x := by
  obtain ⟨hshort,hL,hK⟩ := Cuboid.threshold_le.mp hN
  have hbudget := Cuboid.residual_budget (m+2) (t+2) (q+2) (total x)
    (by omega) (by omega) (by omega) (by omega) hL
  apply cuboid_at_of_hall _ x k a b c d h s
  apply groupHall_extend x _ _ _ _ (∑ i, cuboidBaseDemand k ![m,t,q] i) hbase le_rfl
  · intro j
    have hab := cuboid_pair_supply x a b h.1
    have hac := cuboid_pair_supply x a c h.2.1
    have hbc := cuboid_pair_supply x b c h.2.2.1
    have xa := hx (colourPairIndex a b)
    have xb := hx (colourPairIndex a c)
    have xc := hx (colourPairIndex b c)
    fin_cases k <;> fin_cases j <;>
      norm_num [cuboidBaseDemand,cuboidBaseConst,cuboidBaseAxis,cuboidEdgeDemand,cuboidEdgeAxis,
        cuboidEdgePools,Fin.sum_univ_succ] at * <;> omega
  · exact cuboid_edge_cover a b c h.1 h.2.1 h.2.2.1
  · change (∑ i, cuboidBaseDemand k ![m,t,q] i) + (∑ j, cuboidEdgeDemand k ![m,t,q] j) ≤ total x
    fin_cases k <;> simp_all [cuboidBaseDemand,cuboidBaseConst,cuboidBaseAxis,
      cuboidEdgeDemand,cuboidEdgeAxis,Fin.sum_univ_succ] <;> omega

lemma cuboid_q (m t q : ℕ) (hmt : m ≤ t) (htq : t ≤ q) (x : Inventory)
    (hN : Cuboid.threshold (m+2) (t+2) (q+2) ≤ total x) (hx : ∀ j, mass x (checkerPair j) ≤ 3)
    (a b c d : Colour) (h : DistinctColours a b c d) (s : Fin 2)
    (hb : 4 ≤ mass x (support a b ∩ ordinary s))
    (hc : 4 ≤ mass x (support a c ∩ ordinary s))
    (hbucket : 4*m+8 ≤ mass x (bucket a ∩ ordinary s))
    (ho : 12*m+8 ≤ mass x (ordinary s)) : BoxInventorySolvable ![m,t,q] x := by
  apply cuboid_noD_hall m t q hmt htq x hN hx 1 (by decide) a b c d h s
  have hh := q_pool_hall x _ _ _ _ m (q_frame_union a b c h.1 h.2.1 h.2.2.1 s) hb hc hbucket ho
  intro js
  apply le_trans _ (hh js)
  apply Finset.sum_le_sum
  intro i hi
  fin_cases i <;> simp [cuboidBaseDemand,cuboidBaseConst,cuboidBaseAxis,Fin.sum_univ_succ]
  omega

lemma cuboid_h (m t q : ℕ) (hmt : m ≤ t) (htq : t ≤ q) (x : Inventory)
    (hN : Cuboid.threshold (m+2) (t+2) (q+2) ≤ total x) (hx : ∀ j, mass x (checkerPair j) ≤ 3)
    (a b c d : Colour) (h : DistinctColours a b c d) (s : Fin 2)
    (ha : 2*m+4 ≤ mass x (tripleClass a s))
    (hb : t+2 ≤ mass x (tripleClass b s))
    (hm : 1 ≤ mass x (minorityPool s d))
    (ho : 2*m+t+7 ≤ mass x (ordinary s)) : BoxInventorySolvable ![m,t,q] x := by
  apply cuboid_noD_hall m t q hmt htq x hN hx 2 (by decide) a b c d h s
  obtain ⟨hAB,hAC,hBC,hCD⟩ := u_pool_geometry a b d h.1 s
  have he : cuboidBaseDemand 2 ![m,t,q] = ![2*m+4,t+2,1,1] := by
    funext i; fin_cases i <;> simp [cuboidBaseDemand,cuboidBaseConst,cuboidBaseAxis,Fin.sum_univ_succ] <;> omega
  rw [he]
  exact u_pool_hall x _ _ _ _ (2*m+4) (t+2) 1 1 hAB hAC hBC hCD ha hb hm (by omega)

end ThreeColour
