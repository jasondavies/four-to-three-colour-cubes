module

public import ThreeColour.ThinConstructions

@[expose] public section
namespace ThreeColour
open scoped BigOperators

lemma thin_fourth : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c →
    ∃ d, ThinDistinct a b c d := by decide +kernel

lemma strip_bucket_bound (q : ℕ) (hq : 1 ≤ q) (x : Inventory)
    (hn : ¬ BoxInventorySolvable ![0,1,q] x)
    (hN : Thin.threshold (q+2) ≤ total x) (hx : ∀ j, mass x (thinChecker j) ≤ 3)
    (s : Fin 2) (ho : 23 ≤ mass x (ordinary s)) (a : Colour) :
    mass (majorInventory x s) (bucket a) ≤ 7 := by
  by_contra h
  have hu : 8 ≤ mass (majorInventory x s) (bucket a) := by omega
  have hp : ∀ b c : Colour, a ≠ b → a ≠ c → b ≠ c →
      mass (majorInventory x s) (support a b) ≤ 3 ∨ mass (majorInventory x s) (support a c) ≤ 3 := by
    intro b c hab hac hbc
    by_contra hbad
    push Not at hbad
    obtain ⟨d, hd⟩ := thin_fourth a b c hab hac hbc
    apply hn
    exact strip_q q hq x hN hx a b c d hd s
      (by rw [← major_mass]; omega) (by rw [← major_mass]; omega)
      (by rwa [← major_mass]) ho
  have hsum := support_totals (majorInventory x s) a
  have hb := bucket_totals (majorInventory x s) a
  have hl := support_le (majorInventory x s) a
  have hz := support_self (majorInventory x s) a
  fin_cases a <;> norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hsum hb hl hz hp hu ⊢ <;> omega

/-- The symbolic strip upper bound for every inventory of original source varieties. -/
theorem strip_inventory_upper (q : ℕ) (hq : 1 ≤ q) (x : Inventory)
    (hN : Thin.threshold (q+2) ≤ total x) : BoxInventorySolvable ![0,1,q] x := by
  by_contra hn
  have h29 := (Thin.threshold_bounds (by omega : 2 ≤ q+2) hN).1
  have hno : ¬ ∃ d, ThinGood x d := fun h => hn (strip_d q hq x hN h)
  obtain ⟨s, hs⟩ := exists_major_orientation x
  obtain ⟨hm, ho, hx⟩ := thin_nogood_bounds x h29 hno s hs
  have hb := strip_bucket_bound q hq x hn hN hx s ho
  have hweight := frame_bucket_sum 0 (majorInventory x s) hb
  have hyt := major_totals x s
  have hT : 18 ≤ mass (majorInventory x s) allTriples := by omega
  let t : Colour → ℕ := fun a => mass (majorInventory x s) (triple a)
  have hsum : 18 ≤ t 0 + t 1 + t 2 + t 3 := by
    have ht := triple_totals (majorInventory x s)
    norm_num [Fin.sum_univ_succ] at ht
    dsimp [t]
    omega
  have hcap : ∀ a, t a ≤ 7 := by
    intro a
    have hi := bucket_totals (majorInventory x s) a
    have := hb a
    dsimp [t]
    omega
  have hminor : 0 < mass x (ordinary (flip s)) + mass x allCheckers := by
    have ht := ordered_totals x s
    omega
  rcases Thin.reservation_dichotomy t hsum with ⟨a, ha⟩ | ⟨ht3, a, ha⟩
  · obtain ⟨d,hda,hd⟩ := minority_supported_triple x s a hminor
    obtain ⟨b,c,hab,hac,hbc,hdb,hdc⟩ := palette_complement a d hda
    rcases Thin.partner_supply t hcap hsum b c hbc with hb' | hc'
    · apply hn
      exact strip_h q hq x hN hx 2 (Or.inl rfl) a b c d
        ⟨hab,hac,hbc,hda,hdb,hdc⟩ s
        (by simpa [t, major_triple, thinBaseDemand] using ha)
        (by simpa [t, major_triple, thinBaseDemand] using hb') hd ho
    · apply hn
      exact strip_h q hq x hN hx 2 (Or.inl rfl) a c b d
        ⟨hac,hab,hbc.symm,hda,hdc,hdb⟩ s
        (by simpa [t, major_triple, thinBaseDemand] using ha)
        (by simpa [t, major_triple, thinBaseDemand] using hc') hd ho
  · obtain ⟨d,hda,hd⟩ := minority_supported_triple x s a hminor
    obtain ⟨b,c,hab,hac,hbc,hdb,hdc⟩ := palette_complement a d hda
    apply hn
    apply strip_h q hq x hN hx 3 (Or.inr rfl) a b c d
      ⟨hab,hac,hbc,hda,hdb,hdc⟩ s _ _ hd ho
    · have haa : 4 ≤ t a := by omega
      simpa [t, major_triple, thinBaseDemand] using haa
    · simpa [t, major_triple, thinBaseDemand] using ht3 b

/-- A strip frame using distinct physical cubes and proper rotations. -/
theorem family_strip_upper {m : ℕ} (l : ℕ) (hl : 3 ≤ l)
    (cubes : Fin m → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hm : Thin.threshold l ≤ m) : FamilyBoxFrameSolvable ![0,1,l-2] cubes := by
  apply familyBox_of_inventory _ cubes hc
  apply strip_inventory_upper (l-2) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ l), familyInventory_total] using hm

end ThreeColour
