module

public import ThreeColour.CuboidCounting

@[expose] public section
namespace ThreeColour
open scoped BigOperators

/-- The all-cuboid upper bound for inventories of original source varieties. -/
theorem cuboid_inventory_upper (m t q : ℕ) (hmt : m ≤ t) (htq : t ≤ q) (x : Inventory)
    (hN : Cuboid.threshold (m+2) (t+2) (q+2) ≤ total x) : BoxInventorySolvable ![m,t,q] x := by
  by_contra hn
  obtain ⟨hshort,hL,hK⟩ := Cuboid.threshold_le.mp hN
  have h29 : 29 ≤ total x := by omega
  have hno : ¬ ∃ d, ThinGood x d := fun h => hn (cuboid_d m t q hmt htq x hN h)
  obtain ⟨s,hs⟩ := exists_major_orientation x
  obtain ⟨hm,_,hx⟩ := thin_nogood_bounds x h29 hno s hs
  have htotal := ordered_totals x s
  have hel := eligible_totals x
  have hM : mass x (ordinary (flip s)) + mass x allCheckers ≤ 6 := by
    have hh := hm
    norm_num [Fin.sum_univ_succ,Fin.forall_fin_succ] at hh hel
    omega
  have ho : 16*m+23 ≤ mass x (ordinary s) := by omega
  have hb := cuboid_bucket_bound m t q hmt htq x hn hN hx s (by omega)
  have hw := frame_bucket_sum m (majorInventory x s) hb
  have hyt := major_totals x s
  have htrip := triple_totals (majorInventory x s)
  have hcap : ∀ a, mass (majorInventory x s) (triple a) ≤ 4*m+7 := by
    intro a
    have := hb a
    have := bucket_totals (majorInventory x s) a
    omega
  have hminor : 0 < mass x (ordinary (flip s)) + mass x allCheckers := by omega
  have hextra : 2*m+t+7 ≤ mass x (ordinary s) := by omega
  have hp := cuboid_partner_alternative m t q (total x)
    (mass x (ordinary (flip s)) + mass x allCheckers) (mass x (ordinary s))
    (mass (majorInventory x s) allTriples) (mass (majorInventory x s) allPairs)
    hmt htq (by omega) (by omega) hM (by omega) hyt hw
    (fun a => mass (majorInventory x s) (triple a)) htrip hcap
  rcases hp with ⟨a,ha,hpartner⟩ | ⟨hm0,ht,hm5,a,b,hab,ha,hb⟩
  · obtain ⟨d,hda,hd⟩ := minority_supported_triple x s a hminor
    obtain ⟨b,c,hab,hac,hbc,hdb,hdc⟩ := palette_complement a d hda
    rcases hpartner b c hbc with hb | hc
    · exact hn (cuboid_h m t q hmt htq x hN hx a b c d
        ⟨hab,hac,hbc,hda,hdb,hdc⟩ s (by rwa [major_triple] at ha)
        (by rwa [major_triple] at hb) hd hextra)
    · exact hn (cuboid_h m t q hmt htq x hN hx a c b d
        ⟨hac,hab,hbc.symm,hda,hdc,hdb⟩ s (by rwa [major_triple] at ha)
        (by rwa [major_triple] at hc) hd hextra)
  · obtain ⟨d,hda,hdb,hd⟩ := cuboid_minority_pair x s a b hab hm5 hx
    have hc : ∃ c, ThinDistinct a b c d := by
      have hf : ∀ a b d : Colour, a ≠ b → d ≠ a → d ≠ b → ∃ c, ThinDistinct a b c d := by decide
      exact hf a b d hab hda hdb
    obtain ⟨c,hc⟩ := hc
    exact hn (cuboid_h m t q hmt htq x hN hx a b c d hc s
      (by rw [major_triple] at ha; omega) (by rw [major_triple] at hb; omega) hd hextra)

/-- The universal cuboid-frame guarantee with arbitrary indexed physical source cubes. -/
theorem family_cuboid_upper {n : ℕ} (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (cubes : Fin n → Fin 6 → Colour) (hc : ∀ j, Uses 4 (cubes j))
    (hn : Cuboid.threshold a b c ≤ n) : FamilyBoxFrameSolvable ![a-2,b-2,c-2] cubes := by
  apply familyBox_of_inventory _ cubes hc
  apply cuboid_inventory_upper (a-2) (b-2) (c-2) (by omega) (by omega)
  simpa only [Nat.sub_add_cancel ha, Nat.sub_add_cancel (by omega : 2 ≤ b),
    Nat.sub_add_cancel (by omega : 2 ≤ c),familyInventory_total] using hn

end ThreeColour
