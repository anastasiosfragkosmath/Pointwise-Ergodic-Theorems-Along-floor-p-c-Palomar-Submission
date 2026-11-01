module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFixedWitnessAssembly
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedLiveAggregate
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic
@[expose] public section

/-! Continuity of the exact finite allocated Mellin expressions used by the
selected-Möbius live aggregate.  No source coefficients, cutoffs, characters,
or frequency windows are changed. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- The negative Mellin exponent is continuous and never zero: its real part
is constantly `-1/2`. The nonzero assertion also covers a zero natural base
in the finite polynomial, where `Complex.cpow` is locally constant. -/
theorem selectedMobiusPTW_negativeMellinExponent_continuous (T : ℝ) :
    Continuous (fun t : ℝ =>
      -((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) := by
  fun_prop

theorem selectedMobiusPTW_negativeMellinExponent_ne_zero (T : ℝ) (t : ℝ) :
    -((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) ≠ 0 := by
  intro h
  have hre : Complex.re
      (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) = (-1 / 2 : ℝ) := by
    norm_num [Complex.neg_re, Complex.add_re, Complex.mul_re]
  rw [h] at hre
  norm_num at hre

/-- An allocated finite Dirichlet polynomial is continuous in its real
Mellin parameter. This is a finite sum; each complex power has a nonzero
exponent, even when its natural base is zero. -/
theorem finiteAllocatedDirichletPolynomial_mellinContinuous
    {Q : ℕ} (a : ArithmeticFunction ℂ) (r q : ℕ) (S : Finset ℕ)
    (χ : BlueprintCharacter Q) (T : ℝ) :
    Continuous (fun t : ℝ =>
      finiteAllocatedDirichletPolynomial a r q S χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) := by
  classical
  have hexp := selectedMobiusPTW_negativeMellinExponent_continuous T
  have hpow : ∀ m : ℕ, Continuous (fun t : ℝ =>
      (m : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)))) := by
    intro m
    exact hexp.const_cpow (Or.inr (selectedMobiusPTW_negativeMellinExponent_ne_zero T))
  unfold finiteAllocatedDirichletPolynomial
  refine continuous_finsetSum S ?_
  intro m hm
  have hmPow := hpow m
  fun_prop

/-- One allocated window polynomial has continuous Mellin parameter. -/
theorem selectedMobiusPTWAllocatedWindowPolynomial_continuous
    {Q : ℕ} (a : ArithmeticFunction ℂ) (r q : ℕ) (M : ℝ) (j : ℕ)
    (χ : BlueprintCharacter Q) (T : ℝ) :
    Continuous (fun t : ℝ =>
      selectedMobiusPTWAllocatedWindowPolynomial a r q M j χ T t) := by
  simpa [selectedMobiusPTWAllocatedWindowPolynomial] using
    (finiteAllocatedDirichletPolynomial_mellinContinuous
      (a := a) (r := r) (q := q)
      (S := factorExtractionRealInterval
        ((2 : ℝ) ^ j * (M / (4 * decompositionC * (r : ℝ))))
        (2 * ((2 : ℝ) ^ j * (M / (4 * decompositionC * (r : ℝ))))))
      (χ := χ) (T := T))

/-- The product of the three exact allocated window polynomials in the
source identity is continuous, for every fixed allocation and character. -/
theorem selectedMobiusPTWActualAllocatedWindowTerm_continuous
    {X z : ℝ} (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T γ η η' : ℝ) (j k l : ℕ) :
    Continuous (fun t : ℝ =>
      selectedMobiusPTWActualAllocatedWindowTerm
        (z := z) (q := q) (c := c) fs₁ fs₂ fs₃
        r χ T γ η η' j k l t) := by
  unfold selectedMobiusPTWActualAllocatedWindowTerm
  apply Continuous.mul
  · apply Continuous.mul
    · exact selectedMobiusPTWAllocatedWindowPolynomial_continuous
        (toComplexArithmeticFunction (groupedDyadicFactor z c fs₁))
        (r.1 0).1 (q / orderedAllocationPrefix r.1 0) (X ^ γ) j χ T
    · exact selectedMobiusPTWAllocatedWindowPolynomial_continuous
        (toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₂))
        (r.1 1).1 (q / orderedAllocationPrefix r.1 1) (X ^ η) k χ T
  · exact selectedMobiusPTWAllocatedWindowPolynomial_continuous
      (toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₃))
      (r.1 2).1 (q / orderedAllocationPrefix r.1 2) (X ^ η') l χ T

/-- Exact finite character/allocation integrand continuity required by the
live-conditional source theorem. The scalar Mellin factor and every term use
the original source exponents and coefficients. -/
theorem selectedMobiusPTWActualAllocatedIntegrand_continuous
    {X z : ℝ} {d Q q : ℕ} (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (rchar : ℤ) (T γ η η' : ℝ) (j k l : ℕ) :
    Continuous (fun t : ℝ =>
      ∑ r : divisorFactorTuples 3 d,
        ∑ χ : BlueprintCharacter Q,
          (((d : ℂ) ^
              (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
              (Q.totient : ℂ)) * (star (evalInt χ rchar) *
            selectedMobiusPTWActualAllocatedWindowTerm
              (z := z) (q := q) (c := c) fs₁ fs₂ fs₃
              r χ T γ η η' j k l t))) := by
  classical
  let exponent : ℝ → ℂ := fun t =>
    -((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))
  have hexp : Continuous exponent := by
    dsimp [exponent]
    fun_prop
  have hpow : Continuous (fun t : ℝ => (d : ℂ) ^ exponent t) :=
    hexp.const_cpow
      (Or.inr (fun t => selectedMobiusPTW_negativeMellinExponent_ne_zero T t))
  have hscalar : Continuous (fun t : ℝ =>
      (d : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
        (Q.totient : ℂ)) := by
    have hscalar' : Continuous (fun t : ℝ =>
        (d : ℂ) ^ exponent t * (Q.totient : ℂ)⁻¹) :=
      hpow.mul continuous_const
    convert hscalar' using 1
    ext t
    simp only [div_eq_mul_inv]
    congr 2
    dsimp [exponent]
    ring
  apply continuous_finsetSum (Finset.univ : Finset (divisorFactorTuples 3 d))
  intro r hr
  apply continuous_finsetSum (Finset.univ : Finset (BlueprintCharacter Q))
  intro χ hχ
  exact hscalar.mul
    ((continuous_const).mul
      (selectedMobiusPTWActualAllocatedWindowTerm_continuous
        c fs₁ fs₂ fs₃ r χ T γ η η' j k l))

/-- The exact `hcont` premise for a fixed selected Möbius type-II witness. -/
theorem selectedMobiusPTWActualAllocationContinuity_of_witness
    {X : ℝ} {ν : MobiusDyadicLabel X}
    {α : Fin (mobiusLabelFactors ν).length → ℝ}
    (W : SelectedMobiusPTWTypeIIWitness ν α)
    {d Q q : ℕ} (rchar : ℤ) (T : ℝ) :
    ∀ j k l,
      Continuous (fun t : ℝ =>
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            (((d : ℂ) ^
                (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
                (Q.totient : ℂ)) * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := dyadicMobiusCutoff X) (q := q)
                (c := (dyadicBinomialCoefficient ν.1 : ℂ))
                (selectedDyadicFactors (mobiusLabelFactors ν) W.I)
                (selectedDyadicFactors (mobiusLabelFactors ν) W.J)
                (selectedDyadicFactors (mobiusLabelFactors ν) W.J')
                r χ T W.gamma W.eta W.eta' j k l t))) := by
  intro j k l
  exact selectedMobiusPTWActualAllocatedIntegrand_continuous
    (z := dyadicMobiusCutoff X)
    (c := (dyadicBinomialCoefficient ν.1 : ℂ))
    (selectedDyadicFactors (mobiusLabelFactors ν) W.I)
    (selectedDyadicFactors (mobiusLabelFactors ν) W.J)
    (selectedDyadicFactors (mobiusLabelFactors ν) W.J')
    rchar T W.gamma W.eta W.eta' j k l

#print axioms finiteAllocatedDirichletPolynomial_mellinContinuous
#print axioms selectedMobiusPTWActualAllocationContinuity_of_witness

end FractionalPrimes.Literature.DirichletMean

end
