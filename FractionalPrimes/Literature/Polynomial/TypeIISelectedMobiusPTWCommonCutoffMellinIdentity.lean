module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFiniteMellinIdentity
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFixedWitnessAssembly
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFullFrequencySourcePremises
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFullFrequencyResidueData
public import Mathlib.Tactic
@[expose] public section

/-! Source-facing finite identity connecting the selected-group common
cutoff term to the full-frequency polynomial. The coefficient, support,
cutoff, and gcd-reindexing facts remain explicit inputs; this file only
performs the exact nonunit allocation specialization and common-cutoff
identification. -/

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

set_option maxHeartbeats 1500000 in
/-- Under the exact source coefficient, support, cutoff, and residue/gcd
identities, the full-frequency polynomial is precisely the same character
and allocation sum of selected groups that appears in the live PTW aggregate.
The conclusion is an identity only: no estimate or cancellation is assumed. -/
theorem selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff
    (d : FullFrequencyMellinData)
    {z c : ℝ}
    {fs : List (DyadicArithmeticFactor d.X)}
    (I J J' : Finset (Fin fs.length))
    {g Q q : ℕ} (hq : 0 < q) (residue rchar : ℤ)
    (hGcd : Nat.gcd residue.natAbs q = g)
    (hQuotient : q / g = Q)
    (hReducedResidue : residue / (g : ℤ) = rchar)
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    (hA₁ : a₁ = toComplexArithmeticFunction
      (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I)))
    (hA₂ : a₂ = toComplexArithmeticFunction
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J)))
    (hA₃ : a₃ = toComplexArithmeticFunction
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J')))
    (γ η η' T t : ℝ)
    (hN₁ : 0 < Nat.ceil (decompositionC * d.X ^ γ))
    (hN₂ : 0 < Nat.ceil (decompositionC * d.X ^ η))
    (hN₃ : 0 < Nat.ceil (decompositionC * d.X ^ η'))
    (hsupp₁ : ∀ n, a₁ n ≠ 0 → n ≤ Nat.ceil (decompositionC * d.X ^ γ))
    (hsupp₂ : ∀ n, a₂ n ≠ 0 → n ≤ Nat.ceil (decompositionC * d.X ^ η))
    (hsupp₃ : ∀ n, a₃ n ≠ 0 → n ≤ Nat.ceil (decompositionC * d.X ^ η'))
    (hcoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          (a₁ * a₂ * a₃) n * (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0)
    (hsourceSupport : ∀ n, (a₁ * a₂ * a₃) n ≠ 0 →
      n ∈ fullFrequencySupportIndices d.X)
    (hcutoff : ∀ n ∈ fullFrequencySupportIndices d.X,
      n ≤ Nat.ceil (decompositionC * d.X ^ γ) *
        Nat.ceil (decompositionC * d.X ^ η) *
          Nat.ceil (decompositionC * d.X ^ η')) :
    fullFrequencyMellinPolynomial d t =
      ((g : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
        (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 g,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J' := by
  classical
  let N₁ : ℕ := Nat.ceil (decompositionC * d.X ^ γ)
  let N₂ : ℕ := Nat.ceil (decompositionC * d.X ^ η)
  let N₃ : ℕ := Nat.ceil (decompositionC * d.X ^ η')
  have hsource := fullFrequencyMellinPolynomial_eq_nonunitTripleCharacterAllocation
    d a₁ a₂ a₃ (by exact hN₁) (by exact hN₂)
    (by exact hN₃)
    (by simpa [N₁] using hsupp₁) (by simpa [N₂] using hsupp₂)
    (by simpa [N₃] using hsupp₃) hq residue T t hcoeff hsourceSupport
    (by simpa [N₁, N₂, N₃] using hcutoff)
  have hterm (r : divisorFactorTuples 3 g) (χ : BlueprintCharacter Q) :
      finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
          (q / orderedAllocationPrefix r.1 0)
          (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
        finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
          (q / orderedAllocationPrefix r.1 1)
          (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
        finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
          (q / orderedAllocationPrefix r.1 2)
          (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) =
        selectedMobiusPTWActualCommonCutoffTerm
          (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J' := by
    simp [selectedMobiusPTWActualCommonCutoffTerm,
      selectedMobiusPTWCommonCutoffPolynomial, N₁, N₂, N₃,
      hA₁, hA₂, hA₃]
  calc
    fullFrequencyMellinPolynomial d t =
        ((Nat.gcd residue.natAbs q : ℂ) ^
            (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
          ((q / Nat.gcd residue.natAbs q).totient : ℂ)) *
          ∑ r : divisorFactorTuples 3 (Nat.gcd residue.natAbs q),
            ∑ χ : BlueprintCharacter (q / Nat.gcd residue.natAbs q),
              star (evalInt χ
                  (residue / (Nat.gcd residue.natAbs q : ℤ))) *
                finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
                  (q / orderedAllocationPrefix r.1 0)
                  (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                  ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
                finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
                  (q / orderedAllocationPrefix r.1 1)
                  (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                  ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
                finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
                  (q / orderedAllocationPrefix r.1 2)
                  (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                  ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := hsource
    _ = ((g : ℂ) ^
          (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
        (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 g,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J' := by
      rw [hGcd, hQuotient, hReducedResidue]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro χ hχ
      have h := hterm r χ
      calc
        star (evalInt χ rchar) *
            finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
                (q / orderedAllocationPrefix r.1 0)
                (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
                (q / orderedAllocationPrefix r.1 1)
                (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
                (q / orderedAllocationPrefix r.1 2)
                (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) =
            star (evalInt χ rchar) *
              (finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
                  (q / orderedAllocationPrefix r.1 0)
                  (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                  ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
                finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
                  (q / orderedAllocationPrefix r.1 1)
                  (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                  ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
                finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
                  (q / orderedAllocationPrefix r.1 2)
                  (Finset.Icc 1 (N₁ * N₂ * N₃)) χ
                  ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) := by ring
        _ = star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J' := by
          exact congrArg (fun v : ℂ => star (evalInt χ rchar) * v) h

set_option maxHeartbeats 3000000 in
/-- The preceding identity applied to the actual three selected groups of a
source Möbius type-II witness. The source coefficient convention remains an
explicit premise; all factor support and product cutoff data are supplied by
the checked witness adapter. -/
theorem selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_witness
    (d : FullFrequencyMellinData) (hX : 3 ≤ d.X)
    {ν : MobiusDyadicLabel d.X}
    (hν : ν ∈ mobiusDyadicLabels d.X (dyadicMobiusCutoff d.X))
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α)
    {g Q q : ℕ}
    (hq : 0 < q) (residue rchar : ℤ) (T t : ℝ)
    (hGcd : Nat.gcd residue.natAbs q = g)
    (hQuotient : q / g = Q)
    (hReducedResidue : residue / (g : ℤ) = rchar)
    (hrawCoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0) :
    fullFrequencyMellinPolynomial d t =
      ((g : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
        (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 g,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := dyadicMobiusCutoff d.X)
                (c := dyadicBinomialCoefficient ν.1)
                (mobiusLabelFactors ν) (q := q) r χ T t
                W.gamma W.eta W.eta' W.I W.J W.J' := by
  classical
  let a₁ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (groupedDyadicFactor (dyadicMobiusCutoff d.X)
      (dyadicBinomialCoefficient ν.1 : ℂ)
      (selectedDyadicFactors (mobiusLabelFactors ν) W.I))
  let a₂ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff d.X)
      (selectedDyadicFactors (mobiusLabelFactors ν) W.J))
  let a₃ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff d.X)
      (selectedDyadicFactors (mobiusLabelFactors ν) W.J'))
  have hprem := selectedMobiusPTW_fullFrequencyAllocationPremises
    hX hν W d rfl residue T hrawCoeff
  dsimp [a₁, a₂, a₃] at hprem
  rcases hprem with
    ⟨hN₁, hN₂, hN₃, hsupp₁, hsupp₂, hsupp₃,
      hcoeff, hsourceSupport, hcutoff⟩
  exact selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff
    (d := d) (z := dyadicMobiusCutoff d.X)
    (c := dyadicBinomialCoefficient ν.1)
    (fs := mobiusLabelFactors ν) W.I W.J W.J' hq residue rchar
    hGcd hQuotient hReducedResidue a₁ a₂ a₃ rfl rfl rfl
    W.gamma W.eta W.eta' T t hN₁ hN₂ hN₃
    hsupp₁ hsupp₂ hsupp₃ hcoeff hsourceSupport hcutoff

set_option maxHeartbeats 3000000 in
/-- Source-facing full-frequency identity for the exact residue-prefix data
of one selected Möbius type-II component. The source coefficient convention
is discharged by the checked data constructor. -/
theorem selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_residuePrefix
    {X : ℝ} (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α)
    (H : ℝ) (hH : 0 < H) (hHX : H ≤ X)
    {g Q q : ℕ} (hq : 0 < q)
    (residue rchar : ℤ) (T t : ℝ)
    (hGcd : Nat.gcd residue.natAbs q = g)
    (hQuotient : q / g = Q)
    (hReducedResidue : residue / (g : ℤ) = rchar) :
    let d := selectedMobiusPTWFullFrequencyResidueData hXlarge hν H hH hHX
      q residue T
    fullFrequencyMellinPolynomial d t =
      ((g : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
        (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 g,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := dyadicMobiusCutoff X)
                (c := dyadicBinomialCoefficient ν.1)
                (mobiusLabelFactors ν) (q := q) r χ T t
                W.gamma W.eta W.eta' W.I W.J W.J' := by
  classical
  let d := selectedMobiusPTWFullFrequencyResidueData
    hXlarge hν H hH hHX q residue T
  have hX : 3 ≤ d.X := by
    change 3 ≤ X
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hrawCoeff : ∀ n ∈ fullFrequencySupportIndices d.X,
      d.a n =
        if (n : ZMod q) = (residue : ZMod q) then
          toComplexArithmeticFunction (selectedMobiusPTWRawDyadicComponent ν) n *
            (n : ℂ) ^ (Complex.I * (T : ℂ))
        else 0 := by
    intro n hn
    change n ∈ fullFrequencySupportIndices X at hn
    change (selectedMobiusPTWFullFrequencyResidueData
      hXlarge hν H hH hHX q residue T).a n = _
    exact selectedMobiusPTWFullFrequencyResidueData_coefficient_eq
      hXlarge hν H hH hHX q residue T hn
  exact selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_witness
    d hX hν W hq residue rchar T t hGcd hQuotient hReducedResidue hrawCoeff

#print axioms selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff
#print axioms selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_witness
#print axioms selectedMobiusPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_residuePrefix

end FractionalPrimes.Literature.DirichletMean

end
