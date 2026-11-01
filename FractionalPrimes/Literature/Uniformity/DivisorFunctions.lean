module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Divisor functions on positive integers

This module represents the blueprint's functions on `ℕ_{>0}` using Mathlib's
`ArithmeticFunction ℕ`, whose value at zero is forced to be zero.  The bridge
back to the positive-integer domain is explicit, and the convolution is shown
to equal the blueprint's divisor sum.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open ArithmeticFunction

abbrev PositiveInteger := {n : ℕ // 0 < n}
abbrev PositiveArithmeticFunction := PositiveInteger → ℕ

/-- Extend a function on positive integers by zero at zero, as required by
Mathlib's `ArithmeticFunction` representation. -/
def toArithmeticFunction (f : PositiveArithmeticFunction) : ArithmeticFunction ℕ :=
  ⟨fun n => if hn : 0 < n then f ⟨n, hn⟩ else 0, by simp⟩

@[simp]
theorem toArithmeticFunction_apply (f : PositiveArithmeticFunction)
    (n : PositiveInteger) : toArithmeticFunction f n.1 = f n := by
  simp [toArithmeticFunction, Nat.ne_of_gt n.2]

/-- The blueprint's constant-one function on positive integers. -/
def divisorOne : PositiveArithmeticFunction := fun _ => 1

/-- The blueprint's delta function at one on positive integers. -/
def divisorDeltaOne : PositiveArithmeticFunction := fun n => if n.1 = 1 then 1 else 0

/-- Dirichlet convolution, transported from Mathlib's exact arithmetic-function
convolution to the positive-integer domain. -/
def positiveDirichletConvolution (f g : PositiveArithmeticFunction) :
    PositiveArithmeticFunction :=
  fun n => (toArithmeticFunction f * toArithmeticFunction g) n.1

/-- Total version of the blueprint's summand `f(d) g(n/d)`; the divisor
membership test lets the positive-integer arguments be constructed without
changing the finite divisor sum's value. -/
def divisorConvolutionSummand (f g : PositiveArithmeticFunction)
    (n : PositiveInteger) (d : ℕ) : ℕ :=
  if hd : d ∈ n.1.divisors then
    f ⟨d, Nat.pos_of_mem_divisors hd⟩ *
      g ⟨n.1 / d,
        Nat.div_pos (Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1)
          (Nat.pos_of_mem_divisors hd)⟩
  else 0

@[simp]
theorem divisorConvolutionSummand_of_mem (f g : PositiveArithmeticFunction)
    (n : PositiveInteger) (d : ℕ) (hd : d ∈ n.1.divisors) :
    divisorConvolutionSummand f g n d =
      f ⟨d, Nat.pos_of_mem_divisors hd⟩ *
        g ⟨n.1 / d,
          Nat.div_pos (Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1)
            (Nat.pos_of_mem_divisors hd)⟩ := by
  simp [divisorConvolutionSummand, hd]

/-- Mathlib's antidiagonal convolution agrees exactly with the blueprint's
divisor-sum definition on positive inputs. -/
theorem positiveDirichletConvolution_eq_divisor_sum
    (f g : PositiveArithmeticFunction) (n : PositiveInteger) :
    positiveDirichletConvolution f g n =
      ∑ d ∈ n.1.divisors, divisorConvolutionSummand f g n d := by
  rw [positiveDirichletConvolution, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun a b => toArithmeticFunction f a * toArithmeticFunction g b)]
  apply Finset.sum_congr rfl
  intro d hd
  simp [divisorConvolutionSummand, toArithmeticFunction, hd,
    Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1,
    Nat.pos_of_mem_divisors hd]

/-- The `k`-fold divisor function, including its zeroth convolution power. -/
def divisorFunction (k : ℕ) : PositiveArithmeticFunction :=
  fun n => (ArithmeticFunction.zeta ^ k) n.1

theorem toArithmeticFunction_divisorOne :
    toArithmeticFunction divisorOne = ArithmeticFunction.zeta := by
  ext n
  cases n with
  | zero => simp [toArithmeticFunction, divisorOne, ArithmeticFunction.zeta]
  | succ n => simp [toArithmeticFunction, divisorOne, ArithmeticFunction.zeta]

theorem toArithmeticFunction_divisorFunction (k : ℕ) :
    toArithmeticFunction (divisorFunction k) = ArithmeticFunction.zeta ^ k := by
  ext n
  cases n with
  | zero => simp [toArithmeticFunction, divisorFunction, ArithmeticFunction.zeta]
  | succ n => simp [toArithmeticFunction, divisorFunction, ArithmeticFunction.zeta]

@[simp]
theorem divisorFunction_zero (n : PositiveInteger) :
    divisorFunction 0 n = divisorDeltaOne n := by
  simp [divisorFunction, divisorDeltaOne, ArithmeticFunction.one_apply]

/-- The successor recursion is Dirichlet convolution with the constant-one
function, with the exact positive-integer divisor-sum formula supplied above. -/
theorem divisorFunction_succ (k : ℕ) (n : PositiveInteger) :
    divisorFunction (k + 1) n = positiveDirichletConvolution (divisorFunction k) divisorOne n := by
  change (ArithmeticFunction.zeta ^ (k + 1)) n.1 =
    (toArithmeticFunction (divisorFunction k) * toArithmeticFunction divisorOne) n.1
  rw [toArithmeticFunction_divisorFunction, toArithmeticFunction_divisorOne, pow_succ]

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.toArithmeticFunction_apply
#print axioms FractionalPrimes.Literature.Uniformity.positiveDirichletConvolution_eq_divisor_sum
#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_zero
#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_succ
