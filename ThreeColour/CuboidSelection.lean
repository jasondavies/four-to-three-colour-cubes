module

public import ThreeColour.CheckerboardGraph
public import ThreeColour.CuboidBounds

@[expose] public section
namespace ThreeColour.Cuboid
open Checkerboard

private def edges : Fin 4 → Fin 3 → Fin 6 :=
  ![![3,4,5], ![1,2,5], ![0,2,4], ![0,1,3]]
private lemma edges_mem : ∀ v j, edges v j ∈ triangle v := by decide
private lemma edges_inj : ∀ v, Function.Injective (edges v) := by decide

private lemma three_fit (u v w sc sb sa : ℕ)
    (h3 : u+v+w ≤ 3*sc+2) (h2 : u+v+w ≤ 2*sb+1) (h1 : u+v+w ≤ sa) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (![u,v,w] : Fin 3 → ℕ) i ≤ sc ∧ (![u,v,w] : Fin 3 → ℕ) j ≤ sb ∧
      (![u,v,w] : Fin 3 → ℕ) k ≤ sa := by
  have hh : (u ≤ sc ∧ v ≤ sb ∧ w ≤ sa) ∨ (u ≤ sc ∧ w ≤ sb ∧ v ≤ sa) ∨
      (v ≤ sc ∧ u ≤ sb ∧ w ≤ sa) ∨ (v ≤ sc ∧ w ≤ sb ∧ u ≤ sa) ∨
      (w ≤ sc ∧ u ≤ sb ∧ v ≤ sa) ∨ (w ≤ sc ∧ v ≤ sb ∧ u ≤ sa) := by omega
  rcases hh with h | h | h | h | h | h
  · exact ⟨0,1,2,by decide,by decide,by decide,h⟩
  · exact ⟨0,2,1,by decide,by decide,by decide,h⟩
  · exact ⟨1,0,2,by decide,by decide,by decide,h⟩
  · exact ⟨1,2,0,by decide,by decide,by decide,h⟩
  · exact ⟨2,0,1,by decide,by decide,by decide,h⟩
  · exact ⟨2,1,0,by decide,by decide,by decide,h⟩

/-- All three directional demands can be met by one corner-solvable triple. -/
theorem triangle_selection (x : Fin 6 → ℕ) (good : Fin 4 → Prop)
    (a b c N : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (h29 : 29 ≤ N) (hL : 4*(a+b+c)-16 ≤ N) (hK : (24*c-1)/5 ≤ N)
    (hw : weight x ≤ N) (hg : ∀ v, 8 ≤ degree x v → good v) (hex : ∃ v, good v) :
    ∃ v e f g, good v ∧ e ∈ triangle v ∧ f ∈ triangle v ∧ g ∈ triangle v ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g ∧ x e ≤ N-4*c ∧ x f ≤ N-4*b ∧ x g ≤ N-4*a := by
  obtain ⟨hsc,hns,hsb,hb2,ha4,hc3⟩ := weighted_bounds a b c N ha hab hbc h29 hL hK
  by_cases hall : ∀ e, x e ≤ N-4*b
  · obtain ⟨v,e,hv,he,hxe⟩ := Checkerboard.long_pair x good (by omega) (hw.trans hns) hg hex
    have ht : ∀ v e, e ∈ triangle v → ∃ f g, f ∈ triangle v ∧ g ∈ triangle v ∧
        e ≠ f ∧ e ≠ g ∧ f ≠ g := by decide
    obtain ⟨f,g,hf,hg',hef,heg,hfg⟩ := ht v e he
    exact ⟨v,e,f,g,hv,he,hf,hg',hef,heg,hfg,hxe,hall f,by have := hall g; omega⟩
  · push Not at hall
    obtain ⟨e,he⟩ := hall
    have hv : ∃ v, 8 ≤ degree x v ∧ x (edges v 0)+x (edges v 1)+x (edges v 2) ≤ 4*b-1 := by
      unfold weight at hw
      fin_cases e
      · change N-4*b < x 0 at he
        exact ⟨0,by simp [degree]; omega,by simp [edges]; omega⟩
      · change N-4*b < x 1 at he
        exact ⟨0,by simp [degree]; omega,by simp [edges]; omega⟩
      · change N-4*b < x 2 at he
        exact ⟨0,by simp [degree]; omega,by simp [edges]; omega⟩
      · change N-4*b < x 3 at he
        exact ⟨1,by simp [degree]; omega,by simp [edges]; omega⟩
      · change N-4*b < x 4 at he
        exact ⟨1,by simp [degree]; omega,by simp [edges]; omega⟩
      · change N-4*b < x 5 at he
        exact ⟨2,by simp [degree]; omega,by simp [edges]; omega⟩
    obtain ⟨v,hv,ht⟩ := hv
    obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := three_fit
      (x (edges v 0)) (x (edges v 1)) (x (edges v 2)) (N-4*c) (N-4*b) (N-4*a)
      (by omega) (by omega) (by omega)
    have hf : (![x (edges v 0),x (edges v 1),x (edges v 2)] : Fin 3 → ℕ) = fun j => x (edges v j) := by
      funext j; fin_cases j <;> rfl
    rw [hf] at hi hj hk
    exact ⟨v,edges v i,edges v j,edges v k,hg v hv,edges_mem v i,edges_mem v j,edges_mem v k,
      fun h => hij (edges_inj v h),fun h => hik (edges_inj v h),fun h => hjk (edges_inj v h),hi,hj,hk⟩

end ThreeColour.Cuboid
