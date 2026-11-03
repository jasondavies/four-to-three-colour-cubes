module
public import ThreeColour.FrameCertificates
public import ThreeColour.ConstructionDefs
@[expose] public section
namespace ThreeColour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Six repeated-colour corners, one minority corner, and one majority corner. -/
lemma r_majority_certificate_2 : ∀ b c d : Colour,
    (2 : Colour) ≠ b → (2 : Colour) ≠ c → b ≠ c →
    d ≠ 2 → d ≠ b → d ≠ c → ∀ s : Fin 2, ∀ u : Fin 3,
    Certificate (fits (rTarget 2 b c))
      (packGroups (tripleClass 2 s) (pair 2 ∩ ordinary s)
        (minorityPool s d) (ordinary s)) (packBounds (4+u.val) (2-u.val)) := by
  decide +kernel
end ThreeColour
