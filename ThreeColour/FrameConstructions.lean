module
public import ThreeColour.FrameDGeometry
public import ThreeColour.FramePoolBounds
public import ThreeColour.Constructions
public import ThreeColour.FrameRestrictedDefs
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators

lemma q_frame_union : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c → ∀ s,
    (support a b ∩ ordinary s) ∪ (support a c ∩ ordinary s) = bucket a ∩ ordinary s := by
  decide +kernel

lemma frame_q (k : ℕ) (x : Inventory) (a b c : Colour) (s : Fin 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : 4 ≤ mass x (support a b ∩ ordinary s))
    (hc : 4 ≤ mass x (support a c ∩ ordinary s))
    (hbucket : 4*k+8 ≤ mass x (bucket a ∩ ordinary s))
    (hmajor : 12*k+8 ≤ mass x (ordinary s)) : RestrictedFrameSolvable k x := by
  refine ⟨qTarget a b c, Or.inl (qTarget_isQ a b c hab hac hbc), ?_⟩
  apply frame_at_of_pools k x (qTarget a b c) (qFramePools a b c s)
    (qCornerTag a b c) (qEdgeTag a b c)
    (q_frame_corners a b c hab hac hbc s) (q_frame_edges a b c hab hac hbc s)
  rw [(q_frame_counts a b c hab hac hbc).1, (q_frame_counts a b c hab hac hbc).2]
  have hd : (fun j : Fin 4 => (![4,4,0,0] : Fin 4 → ℕ) j +
      k * (![0,0,4,8] : Fin 4 → ℕ) j) = ![4,4,4*k,8*k] := by
    funext j; fin_cases j <;> simp <;> omega
  rw [hd]
  exact q_pool_hall x _ _ _ _ k (q_frame_union a b c hab hac hbc s)
    hb hc hbucket hmajor

lemma u_pool_geometry : ∀ a b d : Colour, a ≠ b → ∀ s,
    Disjoint (tripleClass a s) (tripleClass b s) ∧
    Disjoint (tripleClass a s) (minorityPool s d) ∧
    Disjoint (tripleClass b s) (minorityPool s d) ∧
    Disjoint (minorityPool s d) (ordinary s) := by decide +kernel

lemma frame_u (k : ℕ) (x : Inventory) (a b c d : Colour) (s : Fin 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (ha : 3*k+4 ≤ mass x (tripleClass a s))
    (hb : k+2 ≤ mass x (tripleClass b s))
    (hm : 1 ≤ mass x (minorityPool s d))
    (ho : 12*k+7 ≤ mass x (ordinary s)) : RestrictedFrameSolvable k x := by
  refine ⟨uTarget a b c, Or.inr (Or.inr (uTarget_isU a b c hab hac hbc)), ?_⟩
  apply frame_at_of_pools k x (uTarget a b c) (uFramePools a b d s)
    (uCornerTag a b c s) (uEdgeTag a b c)
    (u_frame_corners a b c d hab hac hbc hda hdb hdc s)
    (u_frame_edges a b c d hab hac hbc hda hdb hdc s)
  rw [(u_frame_counts a b c hab hac hbc s).1, (u_frame_counts a b c hab hac hbc s).2]
  have hd : (fun j : Fin 4 => (![4,2,1,1] : Fin 4 → ℕ) j +
      k * (![3,1,0,8] : Fin 4 → ℕ) j) = ![3*k+4,k+2,1,8*k+1] := by
    funext j; fin_cases j <;> simp <;> omega
  rw [hd]
  obtain ⟨hAB,hAC,hBC,hCD⟩ := u_pool_geometry a b d hab s
  exact u_pool_hall x _ _ _ _ _ _ _ _ hAB hAC hBC hCD ha hb hm (by omega)

lemma frame_d (k : ℕ) (x : Inventory) (d : Colour)
    (h0 : 4 ≤ mass x (ordinary 0 ∪ eligible d))
    (h1 : 4 ≤ mass x (ordinary 1 ∪ eligible d))
    (h01 : 8 ≤ mass x ((ordinary 0 ∪ eligible d) ∪ (ordinary 1 ∪ eligible d)))
    (he : ∀ j, 4*k+8 ≤ mass x (dEdgePool d j))
    (hn : 12*k+8 ≤ total x) : RestrictedFrameSolvable k x := by
  refine ⟨oppositeTarget d, Or.inr (Or.inl (oppositeTarget_isD d)), ?_⟩
  apply frame_at_of_pools k x (oppositeTarget d) (dFramePools d)
    (dCornerTag d) (dEdgeTag d) (d_frame_corners d) (d_frame_edges d)
  rw [(d_frame_counts d).1, (d_frame_counts d).2]
  have hd : (fun j : Fin 5 => (![4,4,0,0,0] : Fin 5 → ℕ) j +
      k * (![0,0,4,4,4] : Fin 5 → ℕ) j) = ![4,4,4*k,4*k,4*k] := by
    funext j; fin_cases j <;> simp <;> omega
  rw [hd]
  exact d_pool_hall x _ _ _ _ _ k h01 h0 h1 (he 0) (he 1) (he 2)
    (d_edge_pairs_cover d 0 1 (by decide)) (d_edge_pairs_cover d 0 2 (by decide))
    (d_edge_pairs_cover d 1 2 (by decide)) hn

/-- A concentrated checkerboard supplies the corners and each individual edge
requirement; all remaining cubes supply unions of two edge requirements. -/
lemma frame_checker_many (k : ℕ) (x : Inventory) (j : Fin 6)
    (hj : 4*k+8 ≤ mass x (checker j)) (ht : 12*k+8 ≤ total x) :
    RestrictedFrameSolvable k x := by
  have hc : ∀ j : Fin 6, checker j ⊆ eligible (checkerFrameOmitted j) := by
    decide +kernel
  have he : ∀ (j : Fin 6) (l : Fin 3),
      checker j ⊆ dEdgePool (checkerFrameOmitted j) l := by decide +kernel
  have h0 : mass x (checker j) ≤ mass x (ordinary 0 ∪ eligible (checkerFrameOmitted j)) :=
    mass_mono x ((hc j).trans Finset.subset_union_right)
  have h1 : mass x (checker j) ≤ mass x (ordinary 1 ∪ eligible (checkerFrameOmitted j)) :=
    mass_mono x ((hc j).trans Finset.subset_union_right)
  apply frame_d k x (checkerFrameOmitted j) (by omega) (by omega)
  · have hu : mass x (ordinary 0 ∪ eligible (checkerFrameOmitted j)) ≤
        mass x ((ordinary 0 ∪ eligible (checkerFrameOmitted j)) ∪
          (ordinary 1 ∪ eligible (checkerFrameOmitted j))) :=
      mass_mono x Finset.subset_union_left
    omega
  · intro l
    exact hj.trans (mass_mono x (he j l))
  · exact ht

end ThreeColour
