module

public import ThreeColour.Certificates.Q0
public import ThreeColour.Certificates.R0
public import ThreeColour.Certificates.Q1
public import ThreeColour.Certificates.R1
public import ThreeColour.Certificates.Q2
public import ThreeColour.Certificates.R2
public import ThreeColour.Certificates.Q3
public import ThreeColour.Certificates.R3
public import ThreeColour.Certificates.Opp

@[expose] public section

namespace ThreeColour
lemma q_certificate : ∀ a b c : Colour, a ≠ b → a ≠ c → b ≠ c →
    Certificate (fits (qTarget a b c)) (qGroups a b c) qBounds := by
  intro a
  fin_cases a
  · exact q_certificate_0
  · exact q_certificate_1
  · exact q_certificate_2
  · exact q_certificate_3

lemma r_single_certificate : ∀ a : Colour, ∀ j : Fin 6, ∀ s : Fin 2,
    Certificate (fits (rSingleTarget a j))
      (packGroups (triple a) ∅ (checker j) (ordinary s)) (packBounds 6 0) := by
  intro a
  fin_cases a
  · exact r_single_certificate_0
  · exact r_single_certificate_1
  · exact r_single_certificate_2
  · exact r_single_certificate_3

lemma r_pair_certificate : ∀ a b : Colour, ∀ j : Fin 6, ∀ s : Fin 2,
    a ≠ b → Good a b j → ∀ u : Fin 2,
    Certificate (fits (rPairTarget a b j))
      (packGroups (triple a) (pairSupport a b) (checker j) (ordinary s))
      (packBounds (4+u.val) (2-u.val)) := by
  intro a
  fin_cases a
  · exact r_pair_certificate_0
  · exact r_pair_certificate_1
  · exact r_pair_certificate_2
  · exact r_pair_certificate_3
lemma r_mixed_certificate : ∀ a b : Colour, ∀ s : Fin 2, a ≠ b →
    Certificate (fits (rMajorTarget a))
      (packGroups (triple a) ∅ (tripleClass b (flip s)) (ordinary s))
      (packBounds 6 0) := by
  intro a
  fin_cases a
  · exact r_mixed_certificate_0
  · exact r_mixed_certificate_1
  · exact r_mixed_certificate_2
  · exact r_mixed_certificate_3
end ThreeColour
