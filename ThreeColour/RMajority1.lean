module
public import ThreeColour.FrameCertificates
public import ThreeColour.ConstructionDefs
@[expose] public section
namespace ThreeColour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Six repeated-colour corners, one minority corner, and one majority corner. -/
lemma r_majority_certificate_1 : ∀ b c d : Colour,
    (1 : Colour) ≠ b → (1 : Colour) ≠ c → b ≠ c →
    d ≠ 1 → d ≠ b → d ≠ c → ∀ s : Fin 2, ∀ u : Fin 3,
    Certificate (fits (rTarget 1 b c))
      (packGroups (tripleClass 1 s) (pair 1 ∩ ordinary s)
        (minorityPool s d) (ordinary s)) (packBounds (4+u.val) (2-u.val)) := by
  decide +kernel
end ThreeColour
