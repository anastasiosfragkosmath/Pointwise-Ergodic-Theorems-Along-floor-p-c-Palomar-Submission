module

public import FractionalPrimes.Literature.Uniformity.VonMangoldtDyadicComponentTypesTagged
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators
noncomputable section

/-- The source branch tag retained for one actual von Mangoldt dyadic
component. Its third branch includes the strict exponent cap. -/
structure SelectedVonMangoldtPTWTaggedComponentData
    {X : ℝ} (ν : VonMangoldtDyadicLabel X) where
  exponents : Fin (vonMangoldtLabelFactors ν).length → ℝ
  nonnegative : ∀ j, 0 ≤ exponents j
  sum_one : ∑ j : Fin (vonMangoldtLabelFactors ν).length, exponents j = 1
  scale_bounds : ∀ j,
    normalizedExponentConstant⁻¹ * X ^ exponents j ≤
        dyadicFactorScale ((vonMangoldtLabelFactors ν).get j) ∧
      dyadicFactorScale ((vonMangoldtLabelFactors ν).get j) ≤
        normalizedExponentConstant * X ^ exponents j
  mobius_exponent_bound : ∀ i j,
    (vonMangoldtLabelFactors ν).get i = .mobius j →
      exponents i ≤ (1 / 8 : ℝ)
  branch : largeDyadicComponentTaggedPackage
    (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
    (decompositionDelta X)
    (fun n : PositiveInteger =>
      ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))
    (vonMangoldtLabelFactors ν) exponents

def selectedVonMangoldtPTWRawDyadicComponent {X : ℝ}
    (ν : VonMangoldtDyadicLabel X) : ComplexPositiveIntegerFunction :=
  fun n =>
    ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)

/-- A parallel tag-preserving outer decomposition for the literal
von Mangoldt coefficient, without changing the approved untagged one. -/
structure SelectedVonMangoldtPTWTaggedOuterDecomposition (X : ℝ) where
  decomposition : ∀ n : PositiveInteger,
    X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
      vonMangoldtComplexPositiveFunction n =
        ∑ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
          selectedVonMangoldtPTWRawDyadicComponent ν n
  taggedComponent : ∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
    Nonempty (SelectedVonMangoldtPTWTaggedComponentData ν)
  count :
    ((vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)).card : ℝ) ≤
      decompositionDType X

theorem selectedVonMangoldtPTW_taggedComponentAPI
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    Nonempty (SelectedVonMangoldtPTWTaggedComponentData ν) := by
  obtain ⟨α, hα, hsum, hscale, hmob, hbranch⟩ :=
    largeVonMangoldtDyadicComponentTypesTagged hXlarge ν hν
  have hscaleGet : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((vonMangoldtLabelFactors ν).get j) ∧
        dyadicFactorScale ((vonMangoldtLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j := by
    intro j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hscale j
  have hmobGet : ∀ i j,
      (vonMangoldtLabelFactors ν).get i = .mobius j →
        α i ≤ (1 / 8 : ℝ) := by
    intro i j hij
    apply hmob i j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hij
  exact ⟨⟨α, hα, hsum, hscaleGet, hmobGet, hbranch⟩⟩

theorem selectedVonMangoldtPTW_taggedOuterDecomposition
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X) :
    Nonempty (SelectedVonMangoldtPTWTaggedOuterDecomposition X) := by
  classical
  have hX : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  let labels := vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)
  have hdecomp : ∀ n : PositiveInteger,
      X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
        vonMangoldtComplexPositiveFunction n =
          ∑ ν ∈ labels, selectedVonMangoldtPTWRawDyadicComponent ν n := by
    intro n hnlo hnhi
    have h := vonMangoldtDyadicDecomposition hX n.2 hnlo hnhi
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa [vonMangoldtComplexPositiveFunction, labels,
      selectedVonMangoldtPTWRawDyadicComponent,
      Complex.ofReal_sum] using hcast
  have htagged : ∀ ν ∈ labels,
      Nonempty (SelectedVonMangoldtPTWTaggedComponentData ν) := by
    intro ν hν
    exact selectedVonMangoldtPTW_taggedComponentAPI hXlarge ν
      (by simpa [labels] using hν)
  have hcount : (labels.card : ℝ) ≤ decompositionDType X := by
    simpa [labels] using (vonMangoldtDyadicLabels_typeCount hX)
  refine ⟨⟨?_, ?_, hcount⟩⟩
  · simpa [labels] using hdecomp
  · simpa [labels] using htagged

#print axioms selectedVonMangoldtPTW_taggedComponentAPI
#print axioms selectedVonMangoldtPTW_taggedOuterDecomposition
end
end FractionalPrimes.Literature.DirichletMean
