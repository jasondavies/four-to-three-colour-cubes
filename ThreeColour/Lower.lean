module

public import ThreeColour.LowerData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour
lemma extremal_total : ∀ s : Fin 2, total (extremal s) = 28 := by decide +kernel
lemma extremal_deficiency : ∀ s : Fin 2, ∀ t : Target,
    mass (extremal s) (Finset.univ.filter fun i => ∃ k ∈ deficientSlots s t, fits t k i = true)
      < (deficientSlots s t).card := by decide +kernel
lemma extremal_not_solvable (s : Fin 2) : ¬ Solvable (extremal s) := by
  rintro ⟨t,ht⟩
  have hh := (hall_iff_builds (extremal s) (fits t)).mpr ht (deficientSlots s t)
  have := extremal_deficiency s t
  omega
lemma extremal_distinct : extremal 0 ≠ extremal 1 := by decide +kernel
end ThreeColour
