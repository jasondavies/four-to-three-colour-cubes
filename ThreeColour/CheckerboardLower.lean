module

public import ThreeColour.CheckerboardGeometry

@[expose] public section
namespace ThreeColour

/-- A balanced family; each checkerboard occurs floor(N/6) or ceil(N/6) times. -/
def checkerFamily (N : ℕ) (i : Fin N) : Fin 6 → Colour :=
  sourceFaces (checkerSource ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩)

lemma checkerFamily_uses (N : ℕ) : ∀ i, Uses 4 (checkerFamily N i) :=
  fun _ => sources_use_four _

/-- At least floor(N/6) physical copies miss every prescribed bichromatic pair. -/
lemma checker_nonsuppliers (N : ℕ) (a b : Colour) (hab : a ≠ b) :
    N / 6 ≤ Fintype.card {i : Fin N // ¬ HasEdge (checkerFamily N i) a b} := by
  classical
  let j := colourPairIndex a b
  let f : Fin (N/6) → Fin N := fun k => ⟨6*k.val+j.val, by
    have hk := k.isLt
    have hj := j.isLt
    omega⟩
  have hf : Function.Injective f := by
    intro u v h
    have hh := congrArg Fin.val h
    dsimp [f] at hh
    apply Fin.ext
    omega
  have hn (k : Fin (N/6)) : ¬ HasEdge (checkerFamily N (f k)) a b := by
    change ¬ HasEdge (sourceFaces (checkerSource _)) a b
    rw [checker_edge_iff _ a b hab]
    simp only [not_not]
    apply Fin.ext
    dsimp [f]
    have hj := j.isLt
    omega
  let e : Fin (N/6) ↪ {i : Fin N // ¬ HasEdge (checkerFamily N i) a b} :=
    ⟨fun k => ⟨f k,hn k⟩, fun u v h => hf (congrArg Subtype.val h)⟩
  simpa using Fintype.card_le_of_embedding e

lemma checker_rod_shortage (q N : ℕ) (hN : N - N/6 < 4*q+8) :
    ¬ FamilyBoxFrameSolvable ![0,0,q] (checkerFamily N) := by
  classical
  rintro ⟨t,ht,p,hp⟩
  have hcorners : ∀ k : Slot, Function.Injective (ColourCubes.Geometry.corner t k) := by
    intro k
    have hfit := (boxCornerFits_physical t k _).mpr (hp (.inl k))
    exact checker_corner_tricoloured _ _ hfit
  obtain ⟨ht0,ht1,_,hab⟩ := tricoloured_target_opposite t ht hcorners
  have hs (k : BoxFrameSlot ![0,0,q]) : HasEdge (checkerFamily N (p k)) (t 0) (t 2) :=
    rod_position_requires_pair q k _ t ht0 ht1 (hp k)
  let e : BoxFrameSlot ![0,0,q] ↪ {i : Fin N // HasEdge (checkerFamily N i) (t 0) (t 2)} :=
    ⟨fun k => ⟨p k,hs k⟩, fun u v h => p.injective (congrArg Subtype.val h)⟩
  have hcard := Fintype.card_le_of_embedding e
  have hbad := checker_nonsuppliers N (t 0) (t 2) hab
  have hsum := Fintype.card_subtype_compl (p := fun i : Fin N => HasEdge (checkerFamily N i) (t 0) (t 2))
  simp only [boxFrameSlot_card, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Nat.zero_add] at hcard
  have hle := Fintype.card_subtype_le (fun i : Fin N => HasEdge (checkerFamily N i) (t 0) (t 2))
  simp only [Fintype.card_fin] at hsum hle
  omega

/-- The lower witness immediately below the checkerboard bound, at every length. -/
theorem checker_rod_obstruction (l : ℕ) (hl : 2 ≤ l) :
    ¬ FamilyBoxFrameSolvable ![0,0,l-2]
      (checkerFamily ((24*l-1)/5-1)) := by
  apply checker_rod_shortage
  have h : ((24*l-1)/5-1) - ((24*l-1)/5-1)/6 < 4*l := by omega
  omega

end ThreeColour
