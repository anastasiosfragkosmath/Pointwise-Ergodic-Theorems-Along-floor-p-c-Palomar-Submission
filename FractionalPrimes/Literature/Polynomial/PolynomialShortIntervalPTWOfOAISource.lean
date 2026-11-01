module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWEventualCanonicalEnvelope
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWLocalEnvelope
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalPTWTaskClosure
@[expose] public section

/-! The exact approved restricted polynomial twisted task from the
unconditional OAI-source Möbius estimate. The selected decomposition and
source ranges are preserved by the two checked eventual tag-II envelopes. -/

noncomputable section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Twisted

/-- The approved restricted polynomial twisted task, with no remaining
analytic or arithmetic premise. -/
theorem restrictedPolynomialTwistedTask_of_OAISource :
    restrictedPolynomialTwistedTask := by
  apply restrictedPolynomialTwistedTask_of_eventualTagIIEnvelopeBounds
  intro η hη hηmax a ha
  have ha2 : 2 ≤ a := (selectedPTWSourceThreshold_facts ha).2.1
  let Xμ := selectedMobiusPTWEventualCanonicalEnvelopeThreshold a η ha2
  let XΛ := selectedVonMangoldtPTWLocalEnvelopeThreshold a η ha2
  let X₀ : ℝ := max ((2 : ℝ) ^ 120) (max Xμ XΛ)
  refine ⟨X₀,
    selectedMobiusPTWEventualCanonicalEnvelopeConstant a,
    selectedMobiusPTWLongPrefixConstant a
      FractionalPrimes.polynomialKernelM1 prefixTwistMassScale
      selectedPTWSourceIntegralConstant,
    ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · have hμ :=
      selectedMobiusPTWEventualCanonicalTagIIEnvelopeBound_from_OAISource
        ha hη hηmax
    intro X hXlarge hX₀X
    have hXμ : Xμ ≤ (X : ℝ) :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hX₀X
    exact hμ X hXlarge hXμ
  · have hXΛ : XΛ ≤ X₀ :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact selectedVonMangoldtPTWEventualTagIIEnvelopeBound_of_OAISource
      ha hη hηmax hXΛ

#print axioms restrictedPolynomialTwistedTask_of_OAISource

end FractionalPrimes.Literature.Polynomial
