module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalCanonicalTaggedDecomposition
public import Mathlib.Tactic

/-! Assemble the large-scale source-tagged decomposition into the corrected
restricted PTW selection contract. The sole analytic premise is the exact
tag-II prefix-envelope bound for the same canonical tag and raw label. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.DirichletMean
open scoped BigOperators

namespace FractionalPrimes.Literature.Polynomial

/-- The exact componentwise analytic input needed to attach the restricted
twisted-prefix conclusion to a canonical Möbius tagged decomposition. It is
asked only when that decomposition's fixed designation is type II, and is
stated for the literal raw dyadic label component. -/
def selectedMobiusCanonicalTagIIEnvelopeBound
    (X : ℕ) (a η Ctw : ℝ)
    (C : SelectedMobiusPTWCanonicalTaggedDecomposition (X : ℝ)) : Prop :=
  ∀ i (hi : i ∈ C.elementary.indices),
    (C.designationTag i hi).val = 2 →
    ∀ H : ℕ,
      (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
      (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
      ∀ T : ℝ,
        (X : ℝ) / (H : ℝ) * (Real.log (X : ℝ)) ^ (50 * a) ≤ |T| →
        |T| ≤ (X : ℝ) ^ a →
        residuePrefixEnvelope X H
          (fun n => complexPositiveIntegerZeroExtension
              (selectedMobiusPTWRawDyadicComponent (C.label i)) n *
            archimedeanTwist T (n : ℝ))
          ((Real.log (X : ℝ)) ^ a) ≤
          Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a)

/-- The corresponding exact componentwise analytic premise for von
Mangoldt, with the canonical decomposition's own fixed tags. -/
def selectedVonMangoldtCanonicalTagIIEnvelopeBound
    (X : ℕ) (a η Ctw : ℝ)
    (C : SelectedVonMangoldtPTWCanonicalTaggedDecomposition (X : ℝ)) : Prop :=
  ∀ i (hi : i ∈ C.elementary.indices),
    (C.designationTag i hi).val = 2 →
    ∀ H : ℕ,
      (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
      (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
      ∀ T : ℝ,
        (X : ℝ) / (H : ℝ) * (Real.log (X : ℝ)) ^ (50 * a) ≤ |T| →
        |T| ≤ (X : ℝ) ^ a →
        residuePrefixEnvelope X H
          (fun n => complexPositiveIntegerZeroExtension
              (selectedVonMangoldtPTWRawDyadicComponent (C.label i)) n *
            archimedeanTwist T (n : ℝ))
          ((Real.log (X : ℝ)) ^ a) ≤
          Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a)

/-- Build the corrected large-(X) Möbius `RestrictedPTWSelection` from a
fixed canonical tagged decomposition and its per-raw-label tag-II envelope
bound. The threshold inequalities are explicit. The decomposition and tag
are fixed before the universally quantified (H,T). -/
def selectedMobiusLargeXRestrictedPTWSelectionOfCanonical
    (X : ℕ) (aStar a η Ctw : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (C : SelectedMobiusPTWCanonicalTaggedDecomposition (X : ℝ))
    (hbound : selectedMobiusCanonicalTagIIEnvelopeBound X a η Ctw C) :
    RestrictedPTWSelection X aStar a η Ctw mobiusComplexPositiveFunction := by
  refine ⟨haStar, haStarLe, C.elementary,
    C.designationTag, C.designationEvidence, ?_⟩
  intro H hHlower hHupper i hi
  change (if (C.designationTag i hi).val = 2 then _ else True)
  by_cases htag : (C.designationTag i hi).val = 2
  · simp [htag]
    intro T hTlower hTupper
    rw [C.component_eq_raw i hi]
    exact hbound i hi htag H hHlower hHupper T hTlower hTupper
  · simp [htag]

/-- Build the corrected large-(X) von Mangoldt `RestrictedPTWSelection`
from a fixed canonical tagged decomposition and its per-raw-label type-II
envelope bound. -/
def selectedVonMangoldtLargeXRestrictedPTWSelectionOfCanonical
    (X : ℕ) (aStar a η Ctw : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (C : SelectedVonMangoldtPTWCanonicalTaggedDecomposition (X : ℝ))
    (hbound : selectedVonMangoldtCanonicalTagIIEnvelopeBound X a η Ctw C) :
    RestrictedPTWSelection X aStar a η Ctw vonMangoldtComplexPositiveFunction := by
  refine ⟨haStar, haStarLe, C.elementary,
    C.designationTag, C.designationEvidence, ?_⟩
  intro H hHlower hHupper i hi
  change (if (C.designationTag i hi).val = 2 then _ else True)
  by_cases htag : (C.designationTag i hi).val = 2
  · simp [htag]
    intro T hTlower hTupper
    rw [C.component_eq_raw i hi]
    exact hbound i hi htag H hHlower hHupper T hTlower hTupper
  · simp [htag]

/-- Outer-decomposition entry point for Möbius. Its fixed canonical tags are
the same tags mentioned in `hbound`. -/
def selectedMobiusLargeXRestrictedPTWSelectionOfOuter
    (X : ℕ) (aStar a η Ctw : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (outer : SelectedMobiusPTWTaggedOuterDecomposition (X : ℝ))
    (hbound : selectedMobiusCanonicalTagIIEnvelopeBound X a η Ctw
      (selectedMobiusPTWCanonicalTaggedDecompositionOfOuter outer)) :
    RestrictedPTWSelection X aStar a η Ctw mobiusComplexPositiveFunction :=
  selectedMobiusLargeXRestrictedPTWSelectionOfCanonical X aStar a η Ctw
    haStar haStarLe (selectedMobiusPTWCanonicalTaggedDecompositionOfOuter outer)
    hbound

/-- Outer-decomposition entry point for von Mangoldt. -/
def selectedVonMangoldtLargeXRestrictedPTWSelectionOfOuter
    (X : ℕ) (aStar a η Ctw : ℝ)
    (haStar : 1 ≤ aStar) (haStarLe : aStar ≤ a)
    (outer : SelectedVonMangoldtPTWTaggedOuterDecomposition (X : ℝ))
    (hbound : selectedVonMangoldtCanonicalTagIIEnvelopeBound X a η Ctw
      (selectedVonMangoldtPTWCanonicalTaggedDecompositionOfOuter outer)) :
    RestrictedPTWSelection X aStar a η Ctw vonMangoldtComplexPositiveFunction :=
  selectedVonMangoldtLargeXRestrictedPTWSelectionOfCanonical X aStar a η Ctw
    haStar haStarLe
    (selectedVonMangoldtPTWCanonicalTaggedDecompositionOfOuter outer) hbound

#print axioms selectedMobiusLargeXRestrictedPTWSelectionOfCanonical
#print axioms selectedVonMangoldtLargeXRestrictedPTWSelectionOfCanonical
#print axioms selectedMobiusLargeXRestrictedPTWSelectionOfOuter
#print axioms selectedVonMangoldtLargeXRestrictedPTWSelectionOfOuter

end FractionalPrimes.Literature.Polynomial

end
