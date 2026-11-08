module

public import ThreeColour.CuboidCornerSelection

@[expose] public section
namespace ThreeColour
open scoped BigOperators

def cuboidBaseConst : Fin 3 → Fin 4 → ℕ := ![![4,4,0,0],![4,4,0,0],![4,2,1,1]]
def cuboidBaseAxis : Fin 3 → Fin 3 → Fin 4 → ℕ :=
  ![![![0,0,0,0],![0,0,0,0],![0,0,0,0]],
    ![![0,0,4,0],![0,0,0,0],![0,0,0,0]],
    ![![2,0,0,0],![0,1,0,0],![0,0,0,0]]]
def cuboidEdgeAxis : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![0,0,4],![0,4,0],![4,0,0]],
    ![![0,0,0],![2,2,0],![2,2,0]],
    ![![2,0,0],![1,1,1],![2,2,0]]]
def cuboidBaseDemand (k : Fin 3) (l : Fin 3 → ℕ) (i : Fin 4) : ℕ :=
  cuboidBaseConst k i + ∑ a, l a * cuboidBaseAxis k a i
def cuboidEdgeDemand (k : Fin 3) (l : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  ∑ a, l a * cuboidEdgeAxis k a i

def cuboidAxisEdges : Fin 3 → Fin 4 → Fin 12 := ![![8,9,10,11],![2,3,6,7],![0,1,4,5]]

set_option maxRecDepth 100000 in
lemma cuboid_counts (k : Fin 3) : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ∀ s j,
    boxCount (cuboidCornerTag k a b c s) j =
      Sum.elim (cuboidBaseConst k) (fun _ => 0) j ∧
    ∀ axis, boxCount (fun e => cuboidEdgeTag k a b c (cuboidAxisEdges axis e)) j =
      Sum.elim (cuboidBaseAxis k axis) (cuboidEdgeAxis k axis) j := by
  fin_cases k <;> decide +kernel

lemma cuboidTag_count {I : Type*} [DecidableEq I] (l : Fin 3 → ℕ)
    (c : Slot → I) (e : Fin 12 → I) (j : I) :
    Fintype.card {p // boxTag l c e p = j} = boxCount c j +
      ∑ a, l a * boxCount (fun k => e (cuboidAxisEdges a k)) j := by
  rw [boxTag_count]
  congr 1
  simp only [boxCount, Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [cuboidAxisEdges, boxEdgeAxis]
  ring_nf
  rfl

lemma cuboid_at_of_hall (l : Fin 3 → ℕ) (x : Inventory) (k : Fin 3)
    (a b c d : Colour) (h : DistinctColours a b c d) (s : Fin 2)
    (hh : GroupHall x (Sum.elim (cuboidBasePools k a b c d s) (cuboidEdgePools a b c))
      (Sum.elim (cuboidBaseDemand k l) (cuboidEdgeDemand k l))) :
    BoxInventorySolvable l x := by
  refine ⟨cuboidTarget k a b c, cuboid_target_uses _ _ _ _ h.1 h.2.1 h.2.2.1, ?_⟩
  apply box_at_of_pools l x _ _ (cuboidCornerTag k a b c s)
    (cuboidEdgeTag k a b c) _
    (cuboid_corners _ a b c d h s) (cuboid_edges _ a b c d h s) _ hh
  intro j
  rw [cuboidTag_count]
  obtain ⟨hc,he⟩ := cuboid_counts k a b c h.1 h.2.1 h.2.2.1 s j
  rw [hc]
  simp_rw [he]
  cases j <;> simp [cuboidBaseDemand,cuboidEdgeDemand]

set_option maxRecDepth 100000 in
lemma cuboid_selection_colours : ∀ v e f g, e ∈ Checkerboard.triangle v → f ∈ Checkerboard.triangle v →
    g ∈ Checkerboard.triangle v → e ≠ f → e ≠ g → f ≠ g →
    ∃ a b c, DistinctColours a b c v ∧ colourPairIndex a b = e ∧
      colourPairIndex a c = f ∧ colourPairIndex b c = g := by decide +kernel

end ThreeColour
