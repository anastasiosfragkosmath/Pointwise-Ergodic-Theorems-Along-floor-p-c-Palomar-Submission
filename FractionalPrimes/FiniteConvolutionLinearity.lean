module

public import FractionalPrimes.FourierSequence

@[expose] public section

/-!
# Finite-support additivity of integer convolution

The input split in blueprint `lem:interpolation` needs convolution to respect
the sum of the low- and high-amplitude pieces.  This file proves that identity
for the project's finite-support sequence model by reducing it to its checked
finite-sum convolution formula.
-/

namespace FractionalPrimes

noncomputable section

/-- Truncating a sum of two sequences to one finite support set is additive. -/
theorem finiteIntegerSequenceL2_add
    (s : Finset ℤ) (f g : ℤ → ℂ) :
    finiteIntegerSequenceL2 s (fun k => f k + g k) =
      finiteIntegerSequenceL2 s f + finiteIntegerSequenceL2 s g := by
  apply lp.ext
  funext k
  by_cases hk : k ∈ s <;>
    simp [finiteIntegerSequenceL2_apply, hk]

/-- Convolution by an absolutely summable kernel is additive on two inputs
represented with the same finite support set. -/
theorem integerKernelConvolution_finiteIntegerSequenceL2_add
    (K : IntegerL1Kernel) (s : Finset ℤ) (f g : ℤ → ℂ) (x : ℤ) :
    integerKernelConvolution K (finiteIntegerSequenceL2 s (fun k => f k + g k)) x =
      integerKernelConvolution K (finiteIntegerSequenceL2 s f) x +
        integerKernelConvolution K (finiteIntegerSequenceL2 s g) x := by
  rw [integerKernelConvolution_eq_sum_finiteInputSupport K s (fun k => f k + g k) x,
    integerKernelConvolution_eq_sum_finiteInputSupport K s f x,
    integerKernelConvolution_eq_sum_finiteInputSupport K s g x]
  simp_rw [finiteIntegerSequenceL2_apply]
  calc
    _ = ∑ i ∈ s.image (fun j : ℤ => x - j),
        (K.coeff i * (if x - i ∈ s then f (x - i) else 0) +
          K.coeff i * (if x - i ∈ s then g (x - i) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hmem : x - i ∈ s := by
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        simpa using hj
      simp [hmem, mul_add]
    _ = _ := by rw [Finset.sum_add_distrib]

end

end FractionalPrimes
