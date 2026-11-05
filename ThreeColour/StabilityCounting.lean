module
public import ThreeColour.StabilityParameters
@[expose] public section
namespace ThreeColour
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev StabilityFailure (k d : ℕ) :=
  {x : Inventory // total x + d = 16*k+28 ∧ ¬ FrameSolvable k x}

lemma ordinary_orientation_unique (x : Inventory) (ht : 0 < total x) (s t : Fin 2)
    (hs : ∀ i, 0 < x i → i ∈ ordinary s)
    (ht' : ∀ i, 0 < x i → i ∈ ordinary t) : s = t := by
  change 0 < ∑ i : Source, x i at ht
  obtain ⟨i,_,hi⟩ := Finset.sum_pos_iff.mp ht
  have h : ∀ s t i, i ∈ ordinary s → i ∈ ordinary t → s = t := by decide +kernel
  exact h s t i (hs i hi) (ht' i hi)

lemma stability_inventory_positive (k : ℕ) (s : Fin 2) {d : ℕ} (v : StabilityParameter d)
    (hd : d ≤ 4*k+7) : 0 < total (stabilityInventory k s v.val) := by
  have := stability_inventory_total k s v hd
  omega

lemma stability_inventory_support (k : ℕ) (s : Fin 2) (v : StabilityCoordinate → ℕ)
    (i : Source) (hi : 0 < stabilityInventory k s v i) : i ∈ ordinary s := by
  by_contra hn
  have := stability_inventory_pure k s v i hn
  omega

noncomputable def stabilityFailureMap (k d : ℕ) (hd : d ≤ 2*k)
    (p : Fin 2 × StabilityParameter d) : StabilityFailure k d :=
  ⟨stabilityInventory k p.1 p.2.val,
    stability_inventory_total k p.1 p.2 (by omega),
    stability_inventory_fails k p.1 p.2 (by omega)⟩

lemma stabilityFailureMap_injective (k d : ℕ) (hd : d ≤ 2*k) :
    Function.Injective (stabilityFailureMap k d hd) := by
  rintro ⟨s,v⟩ ⟨t,w⟩ h
  have he : stabilityInventory k s v.val = stabilityInventory k t w.val := congrArg Subtype.val h
  have hs : s = t := ordinary_orientation_unique _
    (stability_inventory_positive k s v (by omega)) s t
    (stability_inventory_support k s v.val)
    (by rw [he]; exact stability_inventory_support k t w.val)
  subst t
  have hv : v = w := by
    apply Subtype.ext
    rw [← stability_encode_inventory k s v (by omega),
      ← stability_encode_inventory k s w (by omega), he]
  subst w
  rfl

lemma stabilityFailureMap_surjective (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Function.Surjective (stabilityFailureMap k d hd) := by
  rintro ⟨x,ht,hn⟩
  obtain ⟨s,hs⟩ := exists_major_orientation x
  obtain ⟨ho,hc,hb⟩ := frame_failure_bounds k hk x hn (by omega) s hs
  let v : StabilityParameter d := ⟨stabilityEncode k s x,
    stability_encode_sum k s x ht ho hc hb⟩
  refine ⟨(s,v), ?_⟩
  apply Subtype.ext
  exact stability_inventory_encode k s x ho hc hb

/-- A bijection, not just an upper bound: twelve pair counts and four slacks
freely parametrise all failures in the stability band. -/
noncomputable def stabilityEquiv (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    (Fin 2 × StabilityParameter d) ≃ StabilityFailure k d :=
  Equiv.ofBijective (stabilityFailureMap k d hd)
    ⟨stabilityFailureMap_injective k d hd, stabilityFailureMap_surjective k d hk hd⟩

lemma stability_parameter_count (d : ℕ) : Nat.card (StabilityParameter d) = (d+15).choose 15 := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype StabilityCoordinate d),
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  simp only [StabilityCoordinate, Fintype.card_sum, Fintype.card_fin]
  have h : 12+4+d-1 = d+15 := by omega
  rw [h, Nat.choose_symm_add]

/-- Fixed-palette multisets are counted without quotienting by colour permutations. -/
theorem stability_failure_count (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Nat.card (StabilityFailure k d) = 2 * (d+15).choose 15 := by
  rw [← Nat.card_congr (stabilityEquiv k d hk hd), Nat.card_prod,
    stability_parameter_count]
  simp

/-- Inclusion maximality uses the pointwise order on multiplicities. -/
def FrameMaximalFailure (k : ℕ) (x : Inventory) : Prop :=
  ¬ FrameSolvable k x ∧ ∀ y : Inventory, x ≤ y → ¬ FrameSolvable k y → y = x

lemma mass_mono_inventory {x y : Inventory} (h : x ≤ y) (g : SourceSet) :
    mass x g ≤ mass y g := Finset.sum_le_sum (fun i _ => h i)

lemma saturated_pure_maximal (k : ℕ) (hk : 1 ≤ k) (x : Inventory)
    (ht : 14*k+28 ≤ total x) (s : Fin 2)
    (hs : ∀ i, 0 < x i → i ∈ ordinary s)
    (hb : ∀ a, mass x (bucket a) = 4*k+7) : FrameMaximalFailure k x := by
  refine ⟨pure_bucket_not_solvable k x s hs (fun a => (hb a).le), ?_⟩
  intro y hxy hny
  have hy : 14*k+28 ≤ total y := ht.trans (mass_mono_inventory hxy _)
  obtain ⟨t,hty,hby⟩ := (frame_stability k hk y hy).mp hny
  have he : s = t := ordinary_orientation_unique x (by omega) s t hs
    (fun i hi => hty i (lt_of_lt_of_le hi (hxy i)))
  subst t
  funext i
  by_cases hi : i ∈ ordinary s
  · have hcover : ∀ s i, i ∈ ordinary s → ∃ a, i ∈ bucket a := by decide +kernel
    obtain ⟨a,ha⟩ := hcover s i hi
    have hm := mass_mono_inventory hxy (bucket a)
    have hcap := hby a
    have hsat := hb a
    have heq : mass x (bucket a) = mass y (bucket a) := by omega
    exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hxy j)).mp heq i ha).symm
  · have hx0 : x i = 0 := by by_contra h; exact hi (hs i (by omega))
    have hy0 : y i = 0 := by by_contra h; exact hi (hty i (by omega))
    omega

lemma stability_inventory_maximal_iff (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k)
    (s : Fin 2) (v : StabilityParameter d) :
    FrameMaximalFailure k (stabilityInventory k s v.val) ↔ ∀ a, v.val (.inr a) = 0 := by
  let x := stabilityInventory k s v.val
  have htotal : total x + d = 16*k+28 := stability_inventory_total k s v (by omega)
  have hslack := stability_inventory_slack k s v (by omega)
  constructor
  · rintro ⟨_,hmax⟩ a
    by_contra hpos
    let y : Inventory := fun i => x i + pointInventory (stabilityTriple s a) 1 i
    have hxy : x ≤ y := fun i => Nat.le_add_right _ _
    have hny : ¬ FrameSolvable k y := by
      apply pure_bucket_not_solvable k y s
      · intro i hi
        by_cases he : stabilityTriple s a = i
        · exact he ▸ stability_triple_mem s a
        · have hx : 0 < x i := by simpa [y,pointInventory,he] using hi
          exact stability_inventory_support k s v.val i hx
      · intro b
        have hb := hslack b
        change mass x (bucket b) + v.val (.inr b) = 4*k+7 at hb
        change mass (fun i => x i + pointInventory (stabilityTriple s a) 1 i) (bucket b) ≤ _
        rw [mass_add, mass_point]
        simp only [stability_triple_bucket]
        split_ifs with he
        · subst b; omega
        · omega
    have he := congrFun (hmax y hxy hny) (stabilityTriple s a)
    simp only [y, pointInventory, ite_true] at he
    change x (stabilityTriple s a) + 1 = x (stabilityTriple s a) at he
    omega
  · intro hz
    apply saturated_pure_maximal k hk x (by omega) s (stability_inventory_support k s v.val)
    intro a
    have := hslack a
    rw [hz a, Nat.add_zero] at this
    exact this

abbrev SaturatedParameter (d : ℕ) := {v : Fin 12 → ℕ // ∑ j, v j = d}
abbrev MaximalStabilityFailure (k d : ℕ) :=
  {x : Inventory // total x + d = 16*k+28 ∧ FrameMaximalFailure k x}

/-- Zero-slack parameters are precisely twelve-part weak compositions. -/
noncomputable def saturatedParameterEquiv (d : ℕ) :
    SaturatedParameter d ≃ {v : StabilityParameter d // ∀ a, v.val (.inr a) = 0} where
  toFun v := ⟨⟨Sum.elim v.val (fun _ => 0), by
    simpa [Fintype.sum_sum_type] using v.property⟩, fun _ => rfl⟩
  invFun v := ⟨fun j => v.val.val (.inl j), by
    have h := v.val.property
    simpa [Fintype.sum_sum_type, v.property] using h⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i with
    | inl j => rfl
    | inr a => exact (v.property a).symm

noncomputable def maximalStabilityEquiv (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    (Fin 2 × SaturatedParameter d) ≃ MaximalStabilityFailure k d := by
  let e := stabilityEquiv k d hk hd
  let h (p : Fin 2 × StabilityParameter d) :
      (∀ a, p.2.val (.inr a) = 0) ↔ FrameMaximalFailure k (e p).val :=
    (stability_inventory_maximal_iff k d hk hd p.1 p.2).symm
  let e' : {p : Fin 2 × StabilityParameter d // ∀ a, p.2.val (.inr a) = 0} ≃
      {x : StabilityFailure k d // FrameMaximalFailure k x.val} := e.subtypeEquiv h
  let left : (Fin 2 × SaturatedParameter d) ≃
      {p : Fin 2 × StabilityParameter d // ∀ a, p.2.val (.inr a) = 0} := {
    toFun := fun p => ⟨(p.1, (saturatedParameterEquiv d p.2).val),
      (saturatedParameterEquiv d p.2).property⟩
    invFun := fun p => (p.val.1, (saturatedParameterEquiv d).symm ⟨p.val.2,p.property⟩)
    left_inv := by intro p; simp
    right_inv := by intro p; apply Subtype.ext; simp }
  let right : {x : StabilityFailure k d // FrameMaximalFailure k x.val} ≃
      MaximalStabilityFailure k d := {
    toFun := fun x => ⟨x.val.val, x.val.property.1, x.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.1,x.property.2.1⟩,x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact left.trans (e'.trans right)

lemma saturated_parameter_count (d : ℕ) : Nat.card (SaturatedParameter d) = (d+11).choose 11 := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin 12) d),
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  have h : 12+d-1 = d+11 := by omega
  rw [h, Nat.choose_symm_add]

/-- Exactly the zero-slack failures are inclusion maximal. -/
theorem stability_maximal_count (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Nat.card (MaximalStabilityFailure k d) = 2 * (d+11).choose 11 := by
  rw [← Nat.card_congr (maximalStabilityEquiv k d hk hd), Nat.card_prod,
    saturated_parameter_count]
  simp

lemma maximalFrameFails_iff (k : ℕ) (x : Inventory) :
    MaximalFrameFails k x ↔ FrameMaximalFailure k x := by
  simp only [MaximalFrameFails, FrameMaximalFailure, frameFails_iff]

/-- Failing rotation-class count vectors of size `16n-4-d`, where `n=k+2`. -/
theorem family_stability_failure_count (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Nat.card {x : Inventory // total x + d = 16*k+28 ∧ FrameFails k x} =
      2 * (d+15).choose 15 := by
  rw [← stability_failure_count k d hk hd]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [frameFails_iff])

/-- Inclusion-maximal failing rotation-class count vectors of size `16n-4-d`. -/
theorem family_stability_maximal_count (k d : ℕ) (hk : 1 ≤ k) (hd : d ≤ 2*k) :
    Nat.card {x : Inventory // total x + d = 16*k+28 ∧ MaximalFrameFails k x} =
      2 * (d+11).choose 11 := by
  rw [← stability_maximal_count k d hk hd]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [maximalFrameFails_iff])

end ThreeColour
