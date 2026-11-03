module
public import ThreeColour.NearData
@[expose] public section
namespace ThreeColour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- A target either demands an absent orientation, or four monochromatic edges
and all eight corners require one repeated colour. -/
lemma ordinary_lower_geometry : ∀ s : Fin 2, ∀ t : Target,
    (∃ p : Slot, ∀ i ∈ ordinary s, fits t p i ≠ true) ∨
    ∃ a : Colour,
      (∀ p i, i ∈ ordinary s → fits t p i = true → i ∈ bucket a) ∧
      (Finset.univ.filter fun e : Fin 12 =>
        targetFaces t (edgeFaces e 0) = a ∧ targetFaces t (edgeFaces e 1) = a).card = 4 ∧
      (∀ i, i ∈ ordinary s → HasEdge (sourceFaces i) a a → i ∈ bucket a) := by
  decide +kernel

lemma pure_bucket_not_solvable (k : ℕ) (x : Inventory) (s : Fin 2)
    (hx : ∀ i, 0 < x i → i ∈ ordinary s)
    (hb : ∀ a, mass x (bucket a) ≤ 4*k+7) : ¬ FrameSolvable k x := by
  have hm (p : Stock x) : p.1 ∈ ordinary s := hx p.1 (by have := p.2.isLt; omega)
  rintro ⟨t,p,hp⟩
  rcases ordinary_lower_geometry s t with h | ⟨a,hcorners,hcount,hedges⟩
  · obtain ⟨q,hq⟩ := h
    exact hq _ (hm (p (.inl q))) (hp (.inl q))
  · let E := {e : Fin 12 //
        targetFaces t (edgeFaces e 0) = a ∧ targetFaces t (edgeFaces e 1) = a}
    let pos : (Slot ⊕ (E × Fin k)) ↪ FrameSlot k :=
      Function.Embedding.sumMap (Function.Embedding.refl _)
        (Function.Embedding.prodMap (Function.Embedding.subtype _) (Function.Embedding.refl _))
    have hh := embedding_pool_bound x (bucket a) (pos.trans p) (by
      intro q
      cases q with
      | inl q => exact hcorners q _ (hm (p (.inl q))) (hp (.inl q))
      | inr q =>
        apply hedges _ (hm (p (pos (.inr q))))
        have h := hp (pos (.inr q))
        change HasEdge _ (targetFaces t (edgeFaces q.1.val 0))
          (targetFaces t (edgeFaces q.1.val 1)) at h
        simpa only [q.1.property.1,q.1.property.2] using h)
    have hE : Fintype.card E = 4 := by rw [Fintype.card_subtype]; exact hcount
    have hb := hb a
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hE] at hh
    change 8 + 4*k ≤ mass x (bucket a) at hh
    omega

lemma near_not_solvable (k : ℕ) (p : NearParameter) :
    ¬ FrameSolvable k (nearInventory k p) := by
  apply pure_bucket_not_solvable k _ (nearOrientation p) _ (near_bucket k p)
  intro i hi
  by_contra h
  have := near_outside k p i h
  omega
end ThreeColour
