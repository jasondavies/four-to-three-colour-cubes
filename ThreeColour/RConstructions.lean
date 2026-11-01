module

public import ThreeColour.Certificates
public import ThreeColour.Stats

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

lemma pack_build (x : Inventory) (r : Slot → Source → Bool) (g h k big : SourceSet) (t p : ℕ)
    (hc : Certificate r (packGroups g h k big) (packBounds t p))
    (gh : Disjoint g h) (gk : Disjoint g k) (hk : Disjoint h k)
    (ht : t ≤ mass x g) (hp : p ≤ mass x h) (h1 : 1 ≤ mass x k)
    (hb : 8 ≤ mass x big) : Builds x r := by
  have ghk : Disjoint (g ∪ h) k := Finset.disjoint_union_left.mpr ⟨gk,hk⟩
  apply builds_of_certificate x _ _ _ hc
  intro j
  fin_cases j
  · simp [packGroups, packBounds, mass]
  · exact ht
  · exact hp
  · change t+p ≤ mass x (g ∪ h)
    rw [mass_union x g h gh]; omega
  · exact h1
  · change t+1 ≤ mass x (g ∪ k)
    rw [mass_union x g k gk]; omega
  · change p+1 ≤ mass x (h ∪ k)
    rw [mass_union x h k hk]; omega
  · change t+p+1 ≤ mass x ((g ∪ h) ∪ k)
    rw [mass_union x _ _ ghk, mass_union x _ _ gh]; omega
  · exact hb



lemma solvable_r_single (x : Inventory) (a : Colour) (j : Fin 6) (s : Fin 2)
    (ht : 6 ≤ mass x (triple a)) (hc : 1 ≤ mass x (checker j))
    (ho : 8 ≤ mass x (ordinary s)) : Solvable x := by
  refine ⟨rSingleTarget a j, pack_build x _ _ _ _ _ _ _ (r_single_certificate a j s)
    (by simp) (triple_checker_disjoint a j) (by simp) ht (by simp [mass]) hc ho⟩

lemma triple_pair_support_disjoint : ∀ a b : Colour,
    Disjoint (triple a) (pairSupport a b) := by decide +kernel
lemma pair_support_checker_disjoint : ∀ a b : Colour, ∀ j : Fin 6,
    Disjoint (pairSupport a b) (checker j) := by decide +kernel

lemma solvable_r_pair (x : Inventory) (a b : Colour) (j : Fin 6) (s u : Fin 2)
    (hab : a ≠ b) (hg : Good a b j)
    (ht : 4+u.val ≤ mass x (triple a)) (hp : 2-u.val ≤ mass x (pairSupport a b))
    (hc : 1 ≤ mass x (checker j)) (ho : 8 ≤ mass x (ordinary s)) : Solvable x := by
  exact ⟨rPairTarget a b j, pack_build x _ _ _ _ _ _ _ (r_pair_certificate a b j s hab hg u)
    (triple_pair_support_disjoint a b) (triple_checker_disjoint a j)
    (pair_support_checker_disjoint a b j) ht hp hc ho⟩

lemma triple_class_disjoint : ∀ a b : Colour, ∀ s : Fin 2, a ≠ b →
    Disjoint (triple a) (tripleClass b s) := by decide +kernel

lemma solvable_r_mixed (x : Inventory) (a b : Colour) (s : Fin 2) (hab : a ≠ b)
    (ht : 6 ≤ mass x (triple a)) (hb : 1 ≤ mass x (tripleClass b (flip s)))
    (ho : 8 ≤ mass x (ordinary s)) : Solvable x := by
  exact ⟨rMajorTarget a, pack_build x _ _ _ _ _ _ _ (r_mixed_certificate a b s hab)
    (by simp) (triple_class_disjoint a b (flip s) hab) (by simp) ht (by simp [mass]) hb ho⟩
end ThreeColour
