module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
public import Mathlib.Tactic

/-! A tag-preserving per-component API for the selected Möbius source.  The
three-way arithmetic-type disjunction is kept intact, including the exponent
cap attached to its third branch. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- All normalized finite data retained for one Möbius dyadic component,
including the source branch tag. In particular, the type-II branch stores
both its full type-II factorization and the strict bound on every original
factor exponent. -/
structure SelectedMobiusPTWTaggedComponentData
    {X : ℝ} (ν : MobiusDyadicLabel X) where
  exponents : Fin (mobiusLabelFactors ν).length → ℝ
  nonnegative : ∀ j, 0 ≤ exponents j
  sum_one : ∑ j : Fin (mobiusLabelFactors ν).length, exponents j = 1
  scale_bounds : ∀ j,
    normalizedExponentConstant⁻¹ * X ^ exponents j ≤
        dyadicFactorScale ((mobiusLabelFactors ν).get j) ∧
      dyadicFactorScale ((mobiusLabelFactors ν).get j) ≤
        normalizedExponentConstant * X ^ exponents j
  mobius_exponent_bound : ∀ i j,
    (mobiusLabelFactors ν).get i = .mobius j →
      exponents i ≤ (1 / 8 : ℝ)
  branch : largeDyadicComponentTaggedPackage
    (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
    (decompositionDelta X)
    (fun n : PositiveInteger =>
      ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))
    (mobiusLabelFactors ν) exponents

/-- The raw dyadic Möbius component, before passing to the untagged
`ElementaryArithmeticTypeDecomposition` projection. -/
def selectedMobiusPTWRawDyadicComponent {X : ℝ}
    (ν : MobiusDyadicLabel X) : ComplexPositiveIntegerFunction :=
  fun n =>
    ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)

/-- A parallel finite decomposition whose per-label data retains the full
tagged arithmetic-type disjunction. Its third branch therefore still carries
the type-II factorization and strict original-exponent cap. -/
structure SelectedMobiusPTWTaggedOuterDecomposition (X : ℝ) where
  decomposition : ∀ n : PositiveInteger,
    X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
      mobiusComplexPositiveFunction n =
        ∑ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
          selectedMobiusPTWRawDyadicComponent ν n
  taggedComponent : ∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
    Nonempty (SelectedMobiusPTWTaggedComponentData ν)
  count :
    ((mobiusDyadicLabels X (dyadicMobiusCutoff X)).card : ℝ) ≤
      decompositionDType X

/-- The checked tagged arithmetic-type theorem, packaged without projecting
to the untagged elementary component predicate. -/
theorem selectedMobiusPTW_taggedComponentAPI
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    Nonempty (SelectedMobiusPTWTaggedComponentData ν) := by
  obtain ⟨α, hα, hsum, hscale, hmob, hbranch⟩ :=
    largeMobiusDyadicComponentTypesTagged hXlarge ν hν
  have hscaleGet : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((mobiusLabelFactors ν).get j) ∧
        dyadicFactorScale ((mobiusLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j := by
    intro j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hscale j
  have hmobGet : ∀ i j,
      (mobiusLabelFactors ν).get i = .mobius j →
        α i ≤ (1 / 8 : ℝ) := by
    intro i j hij
    apply hmob i j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hij
  exact ⟨⟨α, hα, hsum, hscaleGet, hmobGet, hbranch⟩⟩

/-- The exact finite Möbius dyadic expansion together with a tagged branch
record for every retained label. This is a parallel source API: it does not
project through the existing untagged `ElementaryArithmeticTypeDecomposition`. -/
theorem selectedMobiusPTW_taggedOuterDecomposition
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X) :
    Nonempty (SelectedMobiusPTWTaggedOuterDecomposition X) := by
  classical
  have hX : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  let labels := mobiusDyadicLabels X (dyadicMobiusCutoff X)
  have hdecomp : ∀ n : PositiveInteger,
      X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
        mobiusComplexPositiveFunction n =
          ∑ ν ∈ labels, selectedMobiusPTWRawDyadicComponent ν n := by
    intro n hnlo hnhi
    have h := mobiusDyadicDecomposition hX n.2 hnlo hnhi
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa [mobiusComplexPositiveFunction, labels,
      selectedMobiusPTWRawDyadicComponent, Complex.ofReal_sum] using hcast
  have htagged : ∀ ν ∈ labels,
      Nonempty (SelectedMobiusPTWTaggedComponentData ν) := by
    intro ν hν
    exact selectedMobiusPTW_taggedComponentAPI hXlarge ν (by simpa [labels] using hν)
  have hcount : (labels.card : ℝ) ≤ decompositionDType X := by
    simpa [labels] using (mobiusDyadicLabels_typeCount hX)
  refine ⟨⟨?_, ?_, hcount⟩⟩
  · simpa [labels] using hdecomp
  · simpa [labels] using htagged

#print axioms selectedMobiusPTW_taggedComponentAPI
#print axioms selectedMobiusPTW_taggedOuterDecomposition

end FractionalPrimes.Literature.DirichletMean

end
