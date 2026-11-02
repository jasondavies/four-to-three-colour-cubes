module
public import ThreeColour.FrameMatching
@[expose] public section
namespace ThreeColour
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma mass_pools_mem {m : ℕ} (x : Inventory) (g : Fin m → SourceSet)
    (js : Finset (Fin m)) (j : Fin m) (hj : j ∈ js) :
    mass x (g j) ≤ mass x (js.biUnion g) :=
  mass_mono x (Finset.subset_biUnion_of_mem g hj)

lemma mass_pools_pair {m : ℕ} (x : Inventory) (g : Fin m → SourceSet)
    (js : Finset (Fin m)) (j l : Fin m) (hj : j ∈ js) (hl : l ∈ js) :
    mass x (g j ∪ g l) ≤ mass x (js.biUnion g) :=
  mass_mono x (Finset.union_subset (Finset.subset_biUnion_of_mem g hj)
    (Finset.subset_biUnion_of_mem g hl))

lemma q_pool_hall (x : Inventory) (A B C D : SourceSet) (k : ℕ)
    (hAB : A ∪ B = C) (_hCD : C ⊆ D)
    (ha : 4 ≤ mass x A) (hb : 4 ≤ mass x B)
    (hc : 4*k+8 ≤ mass x C) (hd : 12*k+8 ≤ mass x D) :
    PoolHall x (![A,B,C,D]) (![4,4,4*k,8*k]) := by
  intro js
  let g : Fin 4 → SourceSet := ![A,B,C,D]
  let z := mass x (js.biUnion g)
  have h0 (h : 0 ∈ js) : 4 ≤ z := ha.trans (mass_pools_mem x g js 0 h)
  have h1 (h : 1 ∈ js) : 4 ≤ z := hb.trans (mass_pools_mem x g js 1 h)
  have h2 (h : 2 ∈ js) : 4*k+8 ≤ z := hc.trans (mass_pools_mem x g js 2 h)
  have h3 (h : 3 ∈ js) : 12*k+8 ≤ z := hd.trans (mass_pools_mem x g js 3 h)
  have h01 (h : 0 ∈ js) (h' : 1 ∈ js) : 4*k+8 ≤ z := by
    have hh := mass_pools_pair x g js 0 1 h h'
    change mass x (A ∪ B) ≤ z at hh
    rw [hAB] at hh
    omega
  change (∑ j ∈ js, (![4,4,4*k,8*k] : Fin 4 → ℕ) j) ≤ z
  generalize hz : z = w at *
  clear hz z g ha hb hc hd hAB _hCD A B C D x
  fin_cases js <;> norm_num at * <;> omega

lemma u_pool_hall (x : Inventory) (A B C D : SourceSet) (a b c d : ℕ)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hCD : Disjoint C D) (_hAD : A ⊆ D) (_hBD : B ⊆ D)
    (ha : a ≤ mass x A) (hb : b ≤ mass x B) (hc : c ≤ mass x C)
    (hd : a+b+d ≤ mass x D) :
    PoolHall x (![A,B,C,D]) (![a,b,c,d]) := by
  intro js
  let g : Fin 4 → SourceSet := ![A,B,C,D]
  let z := mass x (js.biUnion g)
  have h0 (h : 0 ∈ js) : a ≤ z := ha.trans (mass_pools_mem x g js 0 h)
  have h1 (h : 1 ∈ js) : b ≤ z := hb.trans (mass_pools_mem x g js 1 h)
  have h2 (h : 2 ∈ js) : c ≤ z := hc.trans (mass_pools_mem x g js 2 h)
  have h3 (h : 3 ∈ js) : a+b+d ≤ z := hd.trans (mass_pools_mem x g js 3 h)
  have h01 (h : 0 ∈ js) (h' : 1 ∈ js) : a+b ≤ z := by
    have hh := mass_pools_pair x g js 0 1 h h'
    change mass x (A ∪ B) ≤ z at hh
    rw [mass_union x _ _ hAB] at hh
    omega
  have h02 (h : 0 ∈ js) (h' : 2 ∈ js) : a+c ≤ z := by
    have hh := mass_pools_pair x g js 0 2 h h'
    change mass x (A ∪ C) ≤ z at hh
    rw [mass_union x _ _ hAC] at hh
    omega
  have h12 (h : 1 ∈ js) (h' : 2 ∈ js) : b+c ≤ z := by
    have hh := mass_pools_pair x g js 1 2 h h'
    change mass x (B ∪ C) ≤ z at hh
    rw [mass_union x _ _ hBC] at hh
    omega
  have h23 (h : 2 ∈ js) (h' : 3 ∈ js) : a+b+c+d ≤ z := by
    have hh := mass_pools_pair x g js 2 3 h h'
    change mass x (C ∪ D) ≤ z at hh
    rw [mass_union x _ _ hCD] at hh
    omega
  have h012 (h0 : 0 ∈ js) (h1 : 1 ∈ js) (h2 : 2 ∈ js) : a+b+c ≤ z := by
    have hh : mass x (A ∪ B ∪ C) ≤ z := mass_mono x
      (Finset.union_subset (Finset.union_subset (Finset.subset_biUnion_of_mem g h0)
        (Finset.subset_biUnion_of_mem g h1)) (Finset.subset_biUnion_of_mem g h2))
    rw [mass_union x _ _ (Finset.disjoint_union_left.mpr ⟨hAC,hBC⟩),
      mass_union x _ _ hAB] at hh
    omega
  change (∑ j ∈ js, (![a,b,c,d] : Fin 4 → ℕ) j) ≤ z
  generalize hz : z = w at *
  clear hz z g ha hb hc hd hAB hAC hBC hCD _hAD _hBD A B C D x
  fin_cases js <;> norm_num at * <;> omega

lemma d_pool_hall (x : Inventory) (A B E F G : SourceSet) (k : ℕ)
    (hab : 8 ≤ mass x (A ∪ B)) (ha : 4 ≤ mass x A) (hb : 4 ≤ mass x B)
    (he : 4*k+8 ≤ mass x E) (hf : 4*k+8 ≤ mass x F) (hg : 4*k+8 ≤ mass x G)
    (hef : E ∪ F = Finset.univ) (heg : E ∪ G = Finset.univ)
    (hfg : F ∪ G = Finset.univ) (hn : 12*k+8 ≤ mass x Finset.univ) :
    PoolHall x (![A,B,E,F,G]) (![4,4,4*k,4*k,4*k]) := by
  intro js
  let g : Fin 5 → SourceSet := ![A,B,E,F,G]
  let z := mass x (js.biUnion g)
  have h0 (h : 0 ∈ js) : 4 ≤ z := ha.trans (mass_pools_mem x g js 0 h)
  have h1 (h : 1 ∈ js) : 4 ≤ z := hb.trans (mass_pools_mem x g js 1 h)
  have h01 (h : 0 ∈ js) (h' : 1 ∈ js) : 8 ≤ z :=
    hab.trans (mass_pools_pair x g js 0 1 h h')
  have h2 (h : 2 ∈ js) : 4*k+8 ≤ z := he.trans (mass_pools_mem x g js 2 h)
  have h3 (h : 3 ∈ js) : 4*k+8 ≤ z := hf.trans (mass_pools_mem x g js 3 h)
  have h4 (h : 4 ∈ js) : 4*k+8 ≤ z := hg.trans (mass_pools_mem x g js 4 h)
  have h23 (h : 2 ∈ js) (h' : 3 ∈ js) : 12*k+8 ≤ z := by
    have hh := mass_pools_pair x g js 2 3 h h'
    change mass x (E ∪ F) ≤ z at hh
    rw [hef] at hh
    omega
  have h24 (h : 2 ∈ js) (h' : 4 ∈ js) : 12*k+8 ≤ z := by
    have hh := mass_pools_pair x g js 2 4 h h'
    change mass x (E ∪ G) ≤ z at hh
    rw [heg] at hh
    omega
  have h34 (h : 3 ∈ js) (h' : 4 ∈ js) : 12*k+8 ≤ z := by
    have hh := mass_pools_pair x g js 3 4 h h'
    change mass x (F ∪ G) ≤ z at hh
    rw [hfg] at hh
    omega
  change (∑ j ∈ js, (![4,4,4*k,4*k,4*k] : Fin 5 → ℕ) j) ≤ z
  generalize hz : z = w at *
  clear hz z g ha hb hab he hf hg hef heg hfg hn A B E F G x
  fin_cases js <;> norm_num at * <;> omega

end ThreeColour
