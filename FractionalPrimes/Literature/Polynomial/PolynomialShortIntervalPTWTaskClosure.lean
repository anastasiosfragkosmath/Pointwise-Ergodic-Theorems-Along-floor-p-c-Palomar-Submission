module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalAllXPTWSelection
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceBoundDataAssembly
public import FractionalPrimes.Literature.Polynomial.SelectedPTWSourceRangeFacts
public import Mathlib.Tactic

/-! Exact closure adapter from eventual source-aligned tag-II envelope
bounds to the approved restricted polynomial twisted task. The eventual
premises remain explicit and use a common threshold for both weights. -/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.DirichletMean

/-- If the source-aligned Möbius and von Mangoldt tag-II envelope bounds
hold eventually with one common `X₀` for each `(η,a)`, then the exact
restricted polynomial twisted task follows. The source threshold is the
unchanged `selectedMobiusPTWThreshold`. -/
theorem restrictedPolynomialTwistedTask_of_eventualTagIIEnvelopeBounds
    (heventual :
      ∀ η : ℝ, 0 < η → η < 3 / 16 →
        ∀ a : ℝ, (selectedMobiusPTWThreshold : ℝ) ≤ a →
          ∃ X₀ CmuInf ClambdaInf : ℝ,
            (2 : ℝ) ^ 120 ≤ X₀ ∧
            selectedMobiusPTWEventualTagIIEnvelopeBound X₀ a η CmuInf ∧
            selectedVonMangoldtPTWEventualTagIIEnvelopeBound
              X₀ a η ClambdaInf) :
    restrictedPolynomialTwistedTask := by
  intro η hη hηmax
  refine ⟨(selectedMobiusPTWThreshold : ℝ), ?_, ?_⟩
  · exact
      (selectedPTWSourceThreshold_facts
        (a := (selectedMobiusPTWThreshold : ℝ)) le_rfl).1
  · intro a ha
    rcases heventual η hη hηmax a ha with
      ⟨X₀, CmuInf, ClambdaInf, hX₀large, hμeventual, hΛeventual⟩
    exact exists_commonAllScalesRestrictedPTWSelections
      (selectedMobiusPTWThreshold : ℝ) a η CmuInf ClambdaInf X₀
      ((selectedPTWSourceThreshold_facts
        (a := (selectedMobiusPTWThreshold : ℝ)) le_rfl).1)
      ha hη hηmax hX₀large hμeventual hΛeventual

#print axioms restrictedPolynomialTwistedTask_of_eventualTagIIEnvelopeBounds

end FractionalPrimes.Literature.Polynomial

end
