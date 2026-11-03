module

public import ThreeColour.FrameData
public import ThreeColour.FrameMatching
public import ThreeColour.Stats
public import ThreeColour.RData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators

/-- Assign corners and all `k` positions along each edge to source pools. -/
def frameTag {m : ℕ} (k : ℕ) (c : Slot → Fin m) (e : Fin 12 → Fin m) :
    FrameSlot k → Fin m := Sum.elim c (fun p => e p.1)

/-- Number of corners or edges assigned to one pool, before scaling by `k`. -/
def tagCount {n m : ℕ} (tag : Fin n → Fin m) (j : Fin m) : ℕ :=
  ∑ p, if tag p = j then 1 else 0

lemma frameTag_count {m : ℕ} (k : ℕ) (c : Slot → Fin m) (e : Fin 12 → Fin m)
    (j : Fin m) : Fintype.card {p // frameTag k c e p = j} =
      tagCount c j + k * tagCount e j := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, frameTag,
    Sum.elim_inl, Sum.elim_inr, tagCount, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp_all

lemma frame_at_of_pools {m : ℕ} (k : ℕ) (x : Inventory) (t : Target)
    (g : Fin m → SourceSet) (c : Slot → Fin m) (e : Fin 12 → Fin m)
    (hc : ∀ p i, i ∈ g (c p) → fits t p i = true)
    (he : ∀ p i, i ∈ g (e p) → HasEdge (sourceFaces i)
      (targetFaces t (edgeFaces p 0)) (targetFaces t (edgeFaces p 1)))
    (hh : PoolHall x g (fun j => tagCount c j + k * tagCount e j)) :
    ∃ p : FrameSlot k ↪ Stock x, ∀ q, frameFits k t q (p q).1 := by
  obtain ⟨p, hp⟩ := pool_assignment x g (frameTag k c e) _
    (fun j => (frameTag_count k c e j).le) hh
  refine ⟨p, ?_⟩
  intro q
  cases q with
  | inl q => exact hc q _ (hp (.inl q))
  | inr q => exact he q.1 _ (hp (.inr q))

/-- Pools for the two corner types, the monochromatic edges, and the
bichromatic edges of Q, all in the same ordinary orientation class. -/
def qFramePools (a b c : Colour) (s : Fin 2) : Fin 4 → SourceSet :=
  ![support a b ∩ ordinary s, support a c ∩ ordinary s,
    bucket a ∩ ordinary s, ordinary s]

/-- Cubes providing the opposite orientation on the triple omitting `d`. -/
def minorityPool (s : Fin 2) (d : Colour) : SourceSet := ordinary (flip s) ∪ eligible d

/-- U uses T_a and T_b for repeated-colour demands, one minority corner,
and ordinary cubes for the other trichromatic corner and bichromatic edges. -/
def uFramePools (a b d : Colour) (s : Fin 2) : Fin 4 → SourceSet :=
  ![tripleClass a s, tripleClass b s, minorityPool s d, ordinary s]

def edgePool (t : Target) (e : Fin 12) : SourceSet := Finset.univ.filter fun i =>
  HasEdge (sourceFaces i) (targetFaces t (edgeFaces e 0)) (targetFaces t (edgeFaces e 1))

lemma q_frame_counts : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c →
    tagCount (qCornerTag a b c) = ![4,4,0,0] ∧
    tagCount (qEdgeTag a b c) = ![0,0,4,8] := by decide +kernel

lemma q_frame_corners : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c → ∀ s p i,
    i ∈ qFramePools a b c s (qCornerTag a b c p) → fits (qTarget a b c) p i = true := by
  decide +kernel

lemma q_frame_edges : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c → ∀ s p i,
    i ∈ qFramePools a b c s (qEdgeTag a b c p) →
      HasEdge (sourceFaces i) (targetFaces (qTarget a b c) (edgeFaces p 0))
        (targetFaces (qTarget a b c) (edgeFaces p 1)) := by decide +kernel

lemma u_frame_counts : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c → ∀ s,
    tagCount (uCornerTag a b c s) = ![4,2,1,1] ∧
    tagCount (uEdgeTag a b c) = ![3,1,0,8] := by decide +kernel

lemma u_frame_corners : ∀ a b c d : Colour,
    a ≠ b → a ≠ c → b ≠ c → d ≠ a → d ≠ b → d ≠ c → ∀ s p i,
    i ∈ uFramePools a b d s (uCornerTag a b c s p) → fits (uTarget a b c) p i = true := by
  decide +kernel

lemma u_frame_edges : ∀ a b c d : Colour,
    a ≠ b → a ≠ c → b ≠ c → d ≠ a → d ≠ b → d ≠ c → ∀ s p i,
    i ∈ uFramePools a b d s (uEdgeTag a b c p) →
      HasEdge (sourceFaces i) (targetFaces (uTarget a b c) (edgeFaces p 0))
        (targetFaces (uTarget a b c) (edgeFaces p 1)) := by decide +kernel

end ThreeColour
