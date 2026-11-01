module

public import FractionalPrimes.Literature.MSZ.FiniteGridPositiveMajorant
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

/-- A positive convolution of a summable nonnegative sequence is summable.
The proof views the kernel and input as a nonnegative summable product family
and exchanges the two sums. -/
theorem integerKernelPositiveConvolutionTsum_summable
    (K : IntegerL1Kernel) (g : ℤ → ℝ)
    (hg : Summable g) (hgnonneg : ∀ x, 0 ≤ g x) :
    Summable (fun x : ℤ => ∑' m : ℤ, ‖K.coeff m‖ * g (x - m)) := by
  classical
  have hcomp (m : ℤ) :
      (g ∘ Equiv.addLeft (-m)) = fun x : ℤ => g (x - m) := by
    funext x
    simp [Equiv.addLeft, sub_eq_add_neg, add_comm]
  have hshift (m : ℤ) : Summable (fun x : ℤ => g (x - m)) := by
    rw [← hcomp m]
    exact (Equiv.addLeft (-m)).summable_iff.mpr hg
  have hshiftTsum (m : ℤ) :
      (∑' x : ℤ, g (x - m)) = ∑' x : ℤ, g x := by
    rw [← hcomp m]
    exact Equiv.tsum_eq (Equiv.addLeft (-m)) g
  have hinner (m : ℤ) :
      Summable (fun x : ℤ => ‖K.coeff m‖ * g (x - m)) :=
    (hshift m).mul_left _
  have houter : Summable fun m : ℤ =>
      ∑' x : ℤ, ‖K.coeff m‖ * g (x - m) := by
    have heq : (fun m : ℤ => ∑' x : ℤ, ‖K.coeff m‖ * g (x - m)) =
        fun m => ‖K.coeff m‖ * ∑' x : ℤ, g x := by
      funext m
      rw [(hshift m).tsum_mul_left, hshiftTsum m]
    rw [heq]
    exact K.summable_norm.mul_right _
  have hdouble : Summable fun z : ℤ × ℤ =>
      ‖K.coeff z.1‖ * g (z.2 - z.1) := by
    apply (summable_prod_of_nonneg (fun z : ℤ × ℤ =>
      mul_nonneg (norm_nonneg _) (hgnonneg _))).2
    exact ⟨hinner, houter⟩
  have hdoubleSwap : Summable fun z : ℤ × ℤ =>
      ‖K.coeff z.2‖ * g (z.1 - z.2) := by
    change Summable (fun z : ℤ × ℤ =>
      (fun w : ℤ × ℤ => ‖K.coeff w.1‖ * g (w.2 - w.1))
        (Equiv.prodComm ℤ ℤ z))
    exact (Equiv.prodComm ℤ ℤ).summable_iff.mpr hdouble
  exact ((summable_prod_of_nonneg (fun z : ℤ × ℤ =>
    mul_nonneg (norm_nonneg _) (hgnonneg _))).mp hdoubleSwap).2

/-- Tonelli and translation invariance give the exact total mass of a
positive convolution on `ℤ`. -/
theorem integerKernelPositiveConvolutionTsum_eq_mass_mul_tsum
    (K : IntegerL1Kernel) (g : ℤ → ℝ)
    (hg : Summable g) (hgnonneg : ∀ x, 0 ≤ g x) :
    (∑' x : ℤ, ∑' m : ℤ, ‖K.coeff m‖ * g (x - m)) =
      integerKernelL1Mass K * ∑' x : ℤ, g x := by
  classical
  have hcomp (m : ℤ) :
      (g ∘ Equiv.addLeft (-m)) = fun x : ℤ => g (x - m) := by
    funext x
    simp [Equiv.addLeft, sub_eq_add_neg, add_comm]
  have hshift (m : ℤ) : Summable (fun x : ℤ => g (x - m)) := by
    rw [← hcomp m]
    exact (Equiv.addLeft (-m)).summable_iff.mpr hg
  have hshiftTsum (m : ℤ) :
      (∑' x : ℤ, g (x - m)) = ∑' x : ℤ, g x := by
    rw [← hcomp m]
    exact Equiv.tsum_eq (Equiv.addLeft (-m)) g
  have hinner (m : ℤ) :
      Summable (fun x : ℤ => ‖K.coeff m‖ * g (x - m)) :=
    (hshift m).mul_left _
  have houter : Summable fun m : ℤ =>
      ∑' x : ℤ, ‖K.coeff m‖ * g (x - m) := by
    have heq : (fun m : ℤ => ∑' x : ℤ, ‖K.coeff m‖ * g (x - m)) =
        fun m => ‖K.coeff m‖ * ∑' x : ℤ, g x := by
      funext m
      rw [(hshift m).tsum_mul_left, hshiftTsum m]
    rw [heq]
    exact K.summable_norm.mul_right _
  have hdouble : Summable fun z : ℤ × ℤ =>
      ‖K.coeff z.1‖ * g (z.2 - z.1) := by
    apply (summable_prod_of_nonneg (fun z : ℤ × ℤ =>
      mul_nonneg (norm_nonneg _) (hgnonneg _))).2
    exact ⟨hinner, houter⟩
  have hdoubleSwap : Summable fun z : ℤ × ℤ =>
      ‖K.coeff z.2‖ * g (z.1 - z.2) := by
    change Summable (fun z : ℤ × ℤ =>
      (fun w : ℤ × ℤ => ‖K.coeff w.1‖ * g (w.2 - w.1))
        (Equiv.prodComm ℤ ℤ z))
    exact (Equiv.prodComm ℤ ℤ).summable_iff.mpr hdouble
  calc
    _ = ∑' m : ℤ, ∑' x : ℤ, ‖K.coeff m‖ * g (x - m) :=
      hdoubleSwap.tsum_comm.symm
    _ = ∑' m : ℤ, ‖K.coeff m‖ * ∑' x : ℤ, g x := by
      apply tsum_congr
      intro m
      rw [(hshift m).tsum_mul_left, hshiftTsum m]
    _ = integerKernelL1Mass K * ∑' x : ℤ, g x := by
      rw [integerKernelL1Mass]
      exact K.summable_norm.tsum_mul_right _

end FractionalPrimes.Literature.MSZ

end
