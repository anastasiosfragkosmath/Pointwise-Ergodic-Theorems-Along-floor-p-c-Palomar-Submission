module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWFullFrequencySourcePremises
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWCommonCutoffMellinIdentity
public import Mathlib.Tactic
@[expose] public section

/-! Source-facing common-cutoff Mellin identity for the selected von
Mangoldt type-II component. The underlying finite nonunit allocation identity
is generic; this adapter supplies the exact Λ component factorization,
residue-prefix coefficient, and source cutoff data. -/

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

set_option maxHeartbeats 3000000 in
/-- The actual selected von Mangoldt residue-prefix datum has exactly the
generic nonunit triple-character expansion, with the same residue, quotient,
Mellin shift, and selected groups `I/J/J'`. This is a finite identity only. -/
theorem selectedVonMangoldtPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_residuePrefix
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    {α : Fin (vonMangoldtLabelFactors ν).length → ℝ}
    (W : SelectedVonMangoldtPTWTypeIIWitness ν α)
    (H : ℝ) (hH : 0 < H) (hHX : H ≤ X)
    (q : ℕ) (residue : ℤ) (T : ℝ)
    {g Q : ℕ} (hq : 0 < q)
    (rchar : ℤ)
    (hGcd : Nat.gcd residue.natAbs q = g)
    (hQuotient : q / g = Q)
    (hReducedResidue : residue / (g : ℤ) = rchar)
    (t : ℝ) :
    let d := selectedVonMangoldtPTWFullFrequencyResidueData
      hXlarge hν H hH hHX q residue T
    fullFrequencyMellinPolynomial d t =
      ((g : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
        (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 g,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := dyadicMobiusCutoff X)
                (c := dyadicBinomialCoefficient ν.1)
                (vonMangoldtLabelFactors ν) (q := q) r χ T t
                W.gamma W.eta W.eta' W.I W.J W.J' := by
  classical
  let d := selectedVonMangoldtPTWFullFrequencyResidueData
    hXlarge hν H hH hHX q residue T
  have hX : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hrawCoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          toComplexArithmeticFunction
              (selectedVonMangoldtPTWRawDyadicComponent ν) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0 := by
    intro n hn
    change n ∈ fullFrequencySupportIndices X at hn
    change (selectedVonMangoldtPTWFullFrequencyResidueData
      hXlarge hν H hH hHX q residue T).a n = _
    exact selectedVonMangoldtPTWFullFrequencyResidueData_coefficient_eq
      hXlarge hν H hH hHX q residue T hn
  let a₁ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (groupedDyadicFactor (dyadicMobiusCutoff X)
      (dyadicBinomialCoefficient ν.1 : ℂ)
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.I))
  let a₂ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.J))
  let a₃ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.J'))
  have hprem := selectedVonMangoldtPTW_fullFrequencyAllocationPremises
    hX hν W d rfl residue T hrawCoeff
  dsimp [a₁, a₂, a₃] at hprem
  rcases hprem with
    ⟨hN₁, hN₂, hN₃, hsupp₁, hsupp₂, hsupp₃,
      hcoeff, hsourceSupport, hcutoff⟩
  exact selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff
    (d := d) (z := dyadicMobiusCutoff X)
    (c := dyadicBinomialCoefficient ν.1)
    (fs := vonMangoldtLabelFactors ν) W.I W.J W.J' hq residue rchar
    hGcd hQuotient hReducedResidue a₁ a₂ a₃ rfl rfl rfl
    W.gamma W.eta W.eta' T t hN₁ hN₂ hN₃
    hsupp₁ hsupp₂ hsupp₃ hcoeff hsourceSupport hcutoff

#print axioms selectedVonMangoldtPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_residuePrefix

end FractionalPrimes.Literature.DirichletMean

end
