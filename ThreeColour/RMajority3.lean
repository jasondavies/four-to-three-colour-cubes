module
public import ThreeColour.FrameCertificates
public import ThreeColour.ConstructionDefs
@[expose] public section
namespace ThreeColour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Six repeated-colour corners, one minority corner, and one majority corner. -/
lemma r_majority_certificate_3 : ∀ b c d : Colour,
    (3 : Colour) ≠ b → (3 : Colour) ≠ c → b ≠ c →
    d ≠ 3 → d ≠ b → d ≠ c → ∀ s : Fin 2, ∀ u : Fin 3,
    Certificate (fits (rTarget 3 b c))
      (packGroups (tripleClass 3 s) (pair 3 ∩ ordinary s)
        (minorityPool s d) (ordinary s)) (packBounds (4+u.val) (2-u.val)) := by
  -- Split before kernel reduction so one check does not retain all colour cases.
  intro b c
  fin_cases b <;> fin_cases c <;> decide +kernel
end ThreeColour
