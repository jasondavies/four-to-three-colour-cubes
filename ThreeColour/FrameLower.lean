module
public import ThreeColour.FrameDefs
public import ThreeColour.Lower
public import ThreeColour.Stats
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
open scoped BigOperators

def extremalSupport (s : Fin 2) : SourceSet := Finset.univ.filter (fun i => extremal s i = 7)

def frameExtremal (k : ℕ) (s : Fin 2) : Inventory :=
  fun i => if i ∈ extremalSupport s then 4*k+7 else 0

lemma extremalSupport_card : ∀ s, (extremalSupport s).card = 4 := by decide +kernel
lemma extremalSupport_triple_card : ∀ s a, (extremalSupport s ∩ triple a).card = 1 := by
  decide +kernel
lemma frameExtremal_zero : ∀ s, frameExtremal 0 s = extremal s := by decide +kernel

lemma frameExtremal_total (k : ℕ) (s : Fin 2) : total (frameExtremal k s) = 16*k+28 := by
  simp [total, mass, frameExtremal, extremalSupport_card]
  omega

lemma frameExtremal_triple (k : ℕ) (s : Fin 2) (a : Colour) :
    mass (frameExtremal k s) (triple a) = 4*k+7 := by
  have he : (triple a).filter (fun i => i ∈ extremalSupport s) =
      extremalSupport s ∩ triple a := by ext i; simp; tauto
  simp only [mass, frameExtremal, ← Finset.sum_filter, he, Finset.sum_const,
    extremalSupport_triple_card, one_smul]

lemma frameExtremal_member (k : ℕ) (s : Fin 2) (p : Stock (frameExtremal k s)) :
    p.1 ∈ extremalSupport s := by
  have hp := p.2.isLt
  by_contra h
  simp [frameExtremal, h] at hp

/-- A target either demands an absent orientation, or four monochromatic edges
and all eight corners require one repeated colour. -/
lemma frame_lower_geometry : ∀ s : Fin 2, ∀ t : Target,
    (∃ p : Slot, ∀ i ∈ extremalSupport s, fits t p i ≠ true) ∨
    ∃ a : Colour,
      (∀ p i, i ∈ extremalSupport s → fits t p i = true → i ∈ triple a) ∧
      (Finset.univ.filter fun e : Fin 12 =>
        targetFaces t (edgeFaces e 0) = a ∧ targetFaces t (edgeFaces e 1) = a).card = 4 ∧
      (∀ i, i ∈ extremalSupport s → HasEdge (sourceFaces i) a a → i ∈ triple a) := by
  decide +kernel

lemma embedding_pool_bound {P : Type*} [Fintype P] (x : Inventory)
    (g : SourceSet) (p : P ↪ Stock x) (hp : ∀ j, (p j).1 ∈ g) :
    Fintype.card P ≤ mass x g := by
  classical
  let f : P ↪ {q : Stock x // q.1 ∈ g} :=
    ⟨fun j => ⟨p j, hp j⟩, fun _ _ h => p.injective (congrArg Subtype.val h)⟩
  have h := Fintype.card_le_of_embedding f
  rw [Fintype.card_subtype, stock_card] at h
  exact h

lemma frameExtremal_not_solvable (k : ℕ) (s : Fin 2) :
    ¬ FrameSolvable k (frameExtremal k s) := by
  rintro ⟨t,p,hp⟩
  rcases frame_lower_geometry s t with h | ⟨a,hcorners,hcount,hedges⟩
  · obtain ⟨q,hq⟩ := h
    exact hq _ (frameExtremal_member k s (p (.inl q))) (hp (.inl q))
  · let E := {e : Fin 12 //
        targetFaces t (edgeFaces e 0) = a ∧ targetFaces t (edgeFaces e 1) = a}
    let pos : (Slot ⊕ (Σ _ : E, Fin k)) ↪ FrameSlot k :=
      Function.Embedding.sumMap (Function.Embedding.refl _)
        (Function.Embedding.sigmaMap (Function.Embedding.subtype _) (fun _ => Function.Embedding.refl _))
    have hh := embedding_pool_bound (frameExtremal k s) (triple a) (pos.trans p) (by
      intro q
      cases q with
      | inl q => exact hcorners q _ (frameExtremal_member k s (p (.inl q))) (hp (.inl q))
      | inr q =>
        apply hedges _ (frameExtremal_member k s (p (pos (.inr q))))
        have h := hp (pos (.inr q))
        change HasEdge _ (targetFaces t (edgeFaces q.1.val 0))
          (targetFaces t (edgeFaces q.1.val 1)) at h
        simpa only [q.1.property.1,q.1.property.2] using h)
    have hE : Fintype.card E = 4 := by rw [Fintype.card_subtype]; exact hcount
    rw [frameExtremal_triple] at hh
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, hE] at hh
    change 8 + 4*k ≤ 4*k+7 at hh
    omega

end ThreeColour
