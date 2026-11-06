module

public import ThreeColour.CuboidConstructions
public import ThreeColour.ThinUpper

@[expose] public section
namespace ThreeColour
open scoped BigOperators

lemma cuboid_bucket_bound (m t q : ℕ) (hmt : m ≤ t) (htq : t ≤ q) (x : Inventory)
    (hn : ¬ BoxInventorySolvable ![m,t,q] x)
    (hN : Cuboid.threshold (m+2) (t+2) (q+2) ≤ total x) (hx : ∀ j, mass x (thinChecker j) ≤ 3)
    (s : Fin 2) (ho : 12*m+8 ≤ mass x (ordinary s)) (a : Colour) :
    mass (majorInventory x s) (bucket a) ≤ 4*m+7 := by
  by_contra h
  have hu : 4*m+8 ≤ mass (majorInventory x s) (bucket a) := by omega
  have hp : ∀ b c : Colour, a ≠ b → a ≠ c → b ≠ c →
      mass (majorInventory x s) (support a b) ≤ 3 ∨ mass (majorInventory x s) (support a c) ≤ 3 := by
    intro b c hab hac hbc
    by_contra hbad
    push Not at hbad
    obtain ⟨d,hd⟩ := thin_fourth a b c hab hac hbc
    exact hn (cuboid_q m t q hmt htq x hN hx a b c d hd s
      (by rw [← major_mass]; omega) (by rw [← major_mass]; omega)
      (by rwa [← major_mass]) ho)
  have hsum := support_totals (majorInventory x s) a
  have hb := bucket_totals (majorInventory x s) a
  have hl := support_le (majorInventory x s) a
  have hz := support_self (majorInventory x s) a
  fin_cases a <;> norm_num [Fin.sum_univ_succ, Fin.forall_fin_succ] at hsum hb hl hz hp hu ⊢ <;> omega

/-- Either any minority triple through a large colour works, or the two-high-colour case applies. -/
lemma cuboid_partner_alternative (m t q N M A T P : ℕ) (hmt : m ≤ t) (htq : t ≤ q)
    (hN : 16*m+29 ≤ N) (hL : 4*(m+t+q)+8 ≤ N) (hM : M ≤ 6) (hA : A+M=N)
    (ht : T+P=A) (hw : T+2*P ≤ 16*m+28)
    (f : Colour → ℕ) (hf : ∑ a, f a = T) (hcap : ∀ a, f a ≤ 4*m+7) :
    (∃ a, 2*m+4 ≤ f a ∧ ∀ b c, b ≠ c → t+2 ≤ f b ∨ t+2 ≤ f c) ∨
    (m=0 ∧ t≤2 ∧ 5≤M ∧ ∃ a b, a ≠ b ∧ 4≤f a ∧ 4≤f b) := by
  have hT : 16*m+18 ≤ T := by omega
  have hmax : ∃ a, 2*m+4 ≤ f a := by
    by_contra h
    push Not at h
    norm_num [Fin.forall_fin_succ,Fin.sum_univ_succ] at h hf
    omega
  by_cases hp : ∀ b c : Colour, b ≠ c → t+2 ≤ f b ∨ t+2 ≤ f c
  · obtain ⟨a,ha⟩ := hmax
    exact Or.inl ⟨a,ha,hp⟩
  · push Not at hp
    obtain ⟨b,c,hbc,hb,hc⟩ := hp
    have hu : T ≤ 8*m+2*t+16 := by
      norm_num [Fin.sum_univ_succ,Fin.forall_fin_succ] at hf hcap
      fin_cases b <;> fin_cases c <;> simp_all <;> omega
    have hsmall : m=0 ∧ t≤2 ∧ 5≤M := by omega
    refine Or.inr ⟨hsmall.1,hsmall.2.1,hsmall.2.2,?_⟩
    have hh : ∃ a b : Colour, a ≠ b ∧ 4≤f a ∧ 4≤f b := by
      by_contra h
      norm_num [Fin.exists_fin_succ,Fin.sum_univ_succ,Fin.forall_fin_succ] at h hf hcap
      omega
    exact hh

lemma cuboid_minority_pair (x : Inventory) (s : Fin 2) (a b : Colour) (hab : a ≠ b)
    (hm : 5 ≤ mass x (ordinary (flip s)) + mass x allCheckers)
    (hx : ∀ j, mass x (thinChecker j) ≤ 3) :
    ∃ d, d ≠ a ∧ d ≠ b ∧ 1 ≤ mass x (minorityPool s d) := by
  obtain ⟨c,d,hac,had,hcd,hbc,hbd⟩ := palette_complement a b hab.symm
  have hdist : ThinDistinct a b c d := ⟨hab,hac,hbc,had.symm,hbd.symm,hcd.symm⟩
  have cover : ∀ a b c d, ThinDistinct a b c d →
      allCheckers ⊆ thinChecker (thinPairIndex a b) ∪ eligible c ∪ eligible d := by decide +kernel
  have hs := (mass_mono x (cover a b c d hdist)).trans
    ((mass_union_le x _ _).trans (Nat.add_le_add_right (mass_union_le x _ _) _))
  have hc' : mass x (ordinary (flip s)) + mass x (eligible c) = mass x (minorityPool s c) :=
    (mass_union x _ _ (ordinary_eligible_disjoint (flip s) c)).symm
  have hd' : mass x (ordinary (flip s)) + mass x (eligible d) = mass x (minorityPool s d) :=
    (mass_union x _ _ (ordinary_eligible_disjoint (flip s) d)).symm
  have hp := hx (thinPairIndex a b)
  by_cases hh : 1 ≤ mass x (minorityPool s c)
  · exact ⟨c,hac.symm,hbc.symm,hh⟩
  · exact ⟨d,had.symm,hbd.symm,by omega⟩

end ThreeColour
