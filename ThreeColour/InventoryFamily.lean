module
public import ThreeColour.Family
@[expose] public section
namespace ThreeColour

lemma stock_total (x : Inventory) : Fintype.card (Stock x) = total x := by
  simp [Stock,total,mass]

noncomputable def stockEnumeration (x : Inventory) : Stock x ≃ Fin (total x) :=
  (Fintype.equivFin (Stock x)).trans (finCongr (stock_total x))

/-- Realise any inventory by an indexed family of the actual face colourings. -/
noncomputable def inventoryFamily (x : Inventory) (j : Fin (total x)) : Fin 6 → Colour :=
  sourceFaces ((stockEnumeration x).symm j).1

lemma inventoryFamily_uses_four (x : Inventory) : ∀ j, Uses 4 (inventoryFamily x j) :=
  fun _j => sources_use_four _

lemma inventoryFamily_source (x : Inventory) (j : Fin (total x)) :
    familySource (inventoryFamily x) j = ((stockEnumeration x).symm j).1 := by
  apply (familySource_eq_iff _ (inventoryFamily_uses_four x) j _).mpr
  have hid : ∃ r : Fin 24, ∀ f, ColourCubes.rotations r f = f := by decide +kernel
  obtain ⟨r,hr⟩ := hid
  exact ⟨r,fun f => by simp only [hr]; rfl⟩

lemma inventoryFamily_inventory (x : Inventory) : familyInventory (inventoryFamily x) = x := by
  classical
  funext i
  change Fintype.card {j : Fin (total x) // familySource (inventoryFamily x) j = i} = x i
  let e : {j : Fin (total x) // familySource (inventoryFamily x) j = i} ≃
      {q : Stock x // q.1 = i} :=
    Equiv.subtypeEquiv (stockEnumeration x).symm (fun j => by rw [inventoryFamily_source])
  rw [Fintype.card_congr e,Fintype.card_subtype]
  have he : (Finset.univ.filter fun q : Stock x => q.1 = i) =
      Finset.univ.filter (fun q : Stock x => q.1 ∈ ({i} : SourceSet)) := by simp
  rw [he,stock_card]
  simp [mass]

end ThreeColour
