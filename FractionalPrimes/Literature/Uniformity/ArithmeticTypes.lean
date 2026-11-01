module

public import FractionalPrimes.Literature.Uniformity.DivisorFunctions
public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV

/-!
# Exact arithmetic type hypotheses

This file formalizes the function, convolution, support, moment, and
variation data in blueprint item `lu:types`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open ArithmeticFunction
open scoped ENNReal
noncomputable section

/-- Complex-valued functions on the positive integers.  This is separate
from `PositiveArithmeticFunction`, which is ℕ-valued. -/
abbrev ComplexPositiveIntegerFunction := PositiveInteger → ℂ

/-- Extend a complex-valued positive-integer function by zero to the
arithmetic-function domain. -/
def toComplexArithmeticFunction (f : ComplexPositiveIntegerFunction) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if hn : 0 < n then f ⟨n, hn⟩ else 0, by simp⟩

@[simp]
theorem toComplexArithmeticFunction_apply (f : ComplexPositiveIntegerFunction)
    (n : PositiveInteger) : toComplexArithmeticFunction f n.1 = f n := by
  simp [toComplexArithmeticFunction, Nat.ne_of_gt n.2]

/-- Exact Dirichlet convolution on complex-valued functions on positive
integers, transported from Mathlib's arithmetic-function convolution. -/
def complexPositiveDirichletConvolution
    (f g : ComplexPositiveIntegerFunction) : ComplexPositiveIntegerFunction :=
  fun n => (toComplexArithmeticFunction f * toComplexArithmeticFunction g) n.1

/-- Total form of a complex divisor-convolution summand. -/
def complexDivisorConvolutionSummand
    (f g : ComplexPositiveIntegerFunction) (n : PositiveInteger) (d : ℕ) : ℂ :=
  if hd : d ∈ n.1.divisors then
    f ⟨d, Nat.pos_of_mem_divisors hd⟩ *
      g ⟨n.1 / d,
        Nat.div_pos (Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1)
          (Nat.pos_of_mem_divisors hd)⟩
  else 0

@[simp]
theorem complexDivisorConvolutionSummand_of_mem
    (f g : ComplexPositiveIntegerFunction) (n : PositiveInteger) (d : ℕ)
    (hd : d ∈ n.1.divisors) :
    complexDivisorConvolutionSummand f g n d =
      f ⟨d, Nat.pos_of_mem_divisors hd⟩ *
        g ⟨n.1 / d,
          Nat.div_pos (Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1)
            (Nat.pos_of_mem_divisors hd)⟩ := by
  simp [complexDivisorConvolutionSummand, hd]

/-- Mathlib's antidiagonal convolution agrees exactly with the finite
divisor sum on positive inputs. -/
theorem complexPositiveDirichletConvolution_eq_divisor_sum
    (f g : ComplexPositiveIntegerFunction) (n : PositiveInteger) :
    complexPositiveDirichletConvolution f g n =
      ∑ d ∈ n.1.divisors, complexDivisorConvolutionSummand f g n d := by
  rw [complexPositiveDirichletConvolution, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun a b => toComplexArithmeticFunction f a *
      toComplexArithmeticFunction g b)]
  apply Finset.sum_congr rfl
  intro d hd
  simp [complexDivisorConvolutionSummand, toComplexArithmeticFunction, hd,
    Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1,
    Nat.pos_of_mem_divisors hd]

/-- The summand for the second moment up to a real cutoff.  It is total on
`ℕ`; the zero value at zero lets the finite cutoff use `Finset.Icc`. -/
def complexPositiveSecondMomentSummand
    (f : ComplexPositiveIntegerFunction) (n : ℕ) : ℝ :=
  if hn : 0 < n then ‖f ⟨n, hn⟩‖ ^ 2 else 0

/-- The finite second moment over the positive integers at most `B`. -/
def complexPositiveSecondMoment
    (f : ComplexPositiveIntegerFunction) (B : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor B), complexPositiveSecondMomentSummand f n

/-- The summand for the fourth moment up to a real cutoff. -/
def complexPositiveFourthMomentSummand
    (f : ComplexPositiveIntegerFunction) (n : ℕ) : ℝ :=
  if hn : 0 < n then ‖f ⟨n, hn⟩‖ ^ 4 else 0

/-- The finite fourth moment over the positive integers at most `B`. -/
def complexPositiveFourthMoment
    (f : ComplexPositiveIntegerFunction) (B : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor B), complexPositiveFourthMomentSummand f n

/-- Support on the real interval `[A,B]` in the positive-integer domain. -/
def complexPositiveSupportedOnInterval
    (f : ComplexPositiveIntegerFunction) (A B : ℝ) : Prop :=
  ∀ n, f n ≠ 0 → A ≤ (n.1 : ℝ) ∧ (n.1 : ℝ) ≤ B

/-- Extend a complex-valued positive-integer function by zero to all integers.
This is the extension used by the blueprint's residue-class variation. -/
def complexPositiveIntegerZeroExtension
    (f : ComplexPositiveIntegerFunction) : ℤ → ℂ := fun n =>
  if hn : 0 < n then f ⟨n.toNat, by omega⟩ else 0

@[simp]
theorem complexPositiveIntegerZeroExtension_natCast
    (f : ComplexPositiveIntegerFunction) (n : PositiveInteger) :
    complexPositiveIntegerZeroExtension f (n.1 : ℤ) = f n := by
  simp [complexPositiveIntegerZeroExtension, n.2]

/-- The second-moment hypothesis at every real cutoff `B ≥ 1`. -/
def complexPositiveSecondMomentBound
    (δ : ℝ) (f : ComplexPositiveIntegerFunction) : Prop :=
  ∀ B : ℝ, 1 ≤ B → complexPositiveSecondMoment f B ≤ δ⁻¹ * B

/-- The fourth-moment hypothesis at every real cutoff `B ≥ 1`. -/
def complexPositiveFourthMomentBound
    (δ : ℝ) (f : ComplexPositiveIntegerFunction) : Prop :=
  ∀ B : ℝ, 1 ≤ B → complexPositiveFourthMoment f B ≤ δ⁻¹ ^ 2 * B

/-- Residue-class inhomogeneous variation of the zero extension of a
positive-integer function. -/
def complexPositiveIntegerResidueVariation
    (f : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q) : ℝ≥0∞ :=
  positiveIntegerResidueTotalVariation (complexPositiveIntegerZeroExtension f) q hq

/-- A complex-valued positive-integer function is of type I with the exact
cutoff, moment, and residue-variation conditions of `lu:types`. -/
def typeIFunction (δ A_I : ℝ) (f : ComplexPositiveIntegerFunction) : Prop :=
  0 < δ ∧ δ < 1 ∧ 1 ≤ A_I ∧
    ∃ α β : ComplexPositiveIntegerFunction, ∃ q : ℕ, ∃ hq : 0 < q,
      f = complexPositiveDirichletConvolution α β ∧
      complexPositiveSupportedOnInterval α 1 A_I ∧
      complexPositiveSecondMomentBound δ α ∧
      1 ≤ q ∧ (q : ℝ) ≤ δ⁻¹ ∧
      complexPositiveIntegerResidueVariation β q hq ≤
        ENNReal.ofReal (δ⁻¹)

/-- A complex-valued positive-integer function is of type II with the exact
support, second-moment, and fourth-moment conditions of `lu:types`. -/
def typeIIFunction (δ A_II_minus A_II_plus : ℝ)
    (f : ComplexPositiveIntegerFunction) : Prop :=
  0 < δ ∧ δ < 1 ∧ 1 ≤ A_II_minus ∧ 1 ≤ A_II_plus ∧
    ∃ α β : ComplexPositiveIntegerFunction,
      f = complexPositiveDirichletConvolution α β ∧
      complexPositiveSupportedOnInterval α A_II_minus A_II_plus ∧
      (A_II_minus > A_II_plus → α = 0) ∧
      complexPositiveSecondMomentBound δ α ∧
      complexPositiveSecondMomentBound δ β ∧
      complexPositiveFourthMomentBound δ β

/-- A complex-valued positive-integer function is of type I₂.  Both factors
use one common residue modulus, as required by `lu:types`. -/
def typeI2Function (δ A_I2 : ℝ) (f : ComplexPositiveIntegerFunction) : Prop :=
  0 < δ ∧ δ < 1 ∧ 1 ≤ A_I2 ∧
    ∃ α β₁ β₂ : ComplexPositiveIntegerFunction, ∃ q : ℕ, ∃ hq : 0 < q,
      f = complexPositiveDirichletConvolution
        (complexPositiveDirichletConvolution α β₁) β₂ ∧
      complexPositiveSupportedOnInterval α 1 A_I2 ∧
      complexPositiveSecondMomentBound δ α ∧
      1 ≤ q ∧ (q : ℝ) ≤ δ⁻¹ ∧
      complexPositiveIntegerResidueVariation β₁ q hq ≤
        ENNReal.ofReal (δ⁻¹) ∧
      complexPositiveIntegerResidueVariation β₂ q hq ≤
        ENNReal.ofReal (δ⁻¹)

/-- Manifest-facing package for the exact arithmetic-type objects in
blueprint item `lu:types`. -/
structure ArithmeticTypesData where
  /-- Exact Dirichlet convolution on the function domain. -/
  convolution : ComplexPositiveIntegerFunction →
    ComplexPositiveIntegerFunction → ComplexPositiveIntegerFunction
  /-- The finite divisor-sum specification of convolution. -/
  convolution_spec : ∀ f g (n : PositiveInteger),
    convolution f g n =
      ∑ d ∈ n.1.divisors, complexDivisorConvolutionSummand f g n d
  /-- Support in a real interval. -/
  supportedOnInterval : ComplexPositiveIntegerFunction → ℝ → ℝ → Prop
  /-- The second moment bound at every real cutoff at least one. -/
  secondMomentBound : ℝ → ComplexPositiveIntegerFunction → Prop
  /-- The fourth moment bound at every real cutoff at least one. -/
  fourthMomentBound : ℝ → ComplexPositiveIntegerFunction → Prop
  /-- Residue-class total variation of the zero extension. -/
  residueVariation : ComplexPositiveIntegerFunction → (q : ℕ) →
    (hq : 0 < q) → ℝ≥0∞
  /-- The exact type I predicate. -/
  typeI : ℝ → ℝ → ComplexPositiveIntegerFunction → Prop
  /-- The exact type II predicate. -/
  typeII : ℝ → ℝ → ℝ → ComplexPositiveIntegerFunction → Prop
  /-- The exact type I₂ predicate. -/
  typeI2 : ℝ → ℝ → ComplexPositiveIntegerFunction → Prop

/-- The checked implementation of the exact arithmetic-type package. -/
def arithmeticTypes : ArithmeticTypesData where
  convolution := complexPositiveDirichletConvolution
  convolution_spec := complexPositiveDirichletConvolution_eq_divisor_sum
  supportedOnInterval := complexPositiveSupportedOnInterval
  secondMomentBound := complexPositiveSecondMomentBound
  fourthMomentBound := complexPositiveFourthMomentBound
  residueVariation := complexPositiveIntegerResidueVariation
  typeI := typeIFunction
  typeII := typeIIFunction
  typeI2 := typeI2Function

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.toComplexArithmeticFunction_apply
#print axioms FractionalPrimes.Literature.Uniformity.complexPositiveDirichletConvolution_eq_divisor_sum
#print FractionalPrimes.Literature.Uniformity.arithmeticTypes
#print axioms FractionalPrimes.Literature.Uniformity.arithmeticTypes
#print axioms FractionalPrimes.Literature.Uniformity.typeIFunction
#print axioms FractionalPrimes.Literature.Uniformity.typeIIFunction
#print axioms FractionalPrimes.Literature.Uniformity.typeI2Function
