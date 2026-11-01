module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import FractionalPrimes.Literature.MSZ.ConvolutionBounds
public import FractionalPrimes.Literature.MSZ.FiniteGridPositiveMajorant
public import FractionalPrimes.FiniteMomentExhaustion
public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

open scoped ENNReal
open scoped NNReal

namespace FractionalPrimes.Literature.MSZ

/-- Finite weighted Cauchy–Schwarz in the exact factorized form used for
the lower vector endpoint. -/
theorem weightedCauchySchwarzFinset {ι : Type*} (s : Finset ι)
    (a u g h : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hfactor : ∀ i ∈ s, (u i) ^ 2 = g i * h i) :
    (∑ i ∈ s, a i * u i) ^ 2 ≤
      (∑ i ∈ s, a i * g i) * ∑ i ∈ s, a i * h i := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := s) (r := fun i => a i * u i)
    (f := fun i => a i * g i) (g := fun i => a i * h i)
  · intro i hi
    exact mul_nonneg (ha i hi) (hg i hi)
  · intro i hi
    exact mul_nonneg (ha i hi) (hh i hi)
  · intro i hi
    calc
      (a i * u i) ^ 2 = (a i * g i) * (a i * h i) := by
        rw [mul_pow, hfactor i hi]
        ring
      _ ≤ (a i * g i) * (a i * h i) := le_rfl

/-- Weighted Cauchy–Schwarz for a summable-index calculation whose three
factor functions vanish off a finite set. This is the scalar inequality used
when a finitely supported input is convolved with an arbitrary `ℓ¹` kernel. -/
theorem weightedCauchySchwarzTsumFiniteSupport (s : Finset ℤ)
    (a u g h : ℤ → ℝ)
    (hs : ∀ m ∉ s, u m = 0 ∧ g m = 0 ∧ h m = 0)
    (ha : ∀ m, 0 ≤ a m)
    (hg : ∀ m ∈ s, 0 ≤ g m)
    (hh : ∀ m ∈ s, 0 ≤ h m)
    (hfactor : ∀ m ∈ s, (u m) ^ 2 = g m * h m) :
    (∑' m : ℤ, a m * u m) ^ 2 ≤
      (∑' m : ℤ, a m * g m) * ∑' m : ℤ, a m * h m := by
  rw [tsum_eq_sum (s := s) (fun m hm => by simp [hs m hm]),
    tsum_eq_sum (s := s) (fun m hm => by simp [hs m hm]),
    tsum_eq_sum (s := s) (fun m hm => by simp [hs m hm])]
  apply weightedCauchySchwarzFinset s a u g h
  · intro m hm
    exact ha m
  · exact hg
  · exact hh
  · exact hfactor

/-- The finite-support scalar factorization estimate for an arbitrary
absolutely summable complex kernel. This is the weighted Cauchy–Schwarz
step in the lower vector endpoint proof, written with the project's kernel
coefficients and their absolute values. -/
theorem integerKernelWeightedCauchyTsumFiniteSupport
    (K : IntegerL1Kernel) (x : ℤ) (s : Finset ℤ)
    (u g h : ℤ → ℝ)
    (hs : ∀ m ∉ s, u (x - m) = 0 ∧ g (x - m) = 0 ∧ h (x - m) = 0)
    (hg : ∀ y, 0 ≤ g y) (hh : ∀ y, 0 ≤ h y)
    (hfactor : ∀ y, (u y) ^ 2 = g y * h y) :
    (∑' m : ℤ, ‖K.coeff m‖ * u (x - m)) ^ 2 ≤
      (∑' m : ℤ, ‖K.coeff m‖ * g (x - m)) *
        ∑' m : ℤ, ‖K.coeff m‖ * h (x - m) := by
  exact weightedCauchySchwarzTsumFiniteSupport s
    (fun m => ‖K.coeff m‖) (fun m => u (x - m))
    (fun m => g (x - m)) (fun m => h (x - m)) hs
    (fun m => norm_nonneg _) (fun m hm => hg (x - m))
    (fun m hm => hh (x - m)) (fun m hm => hfactor (x - m))

/-- The pointwise maximum of a finite family of positive kernel convolutions.
The `ℝ≥0` supremum makes the empty-family value exactly zero. -/
noncomputable def integerKernelPositiveConvolutionMax
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
    (K : ι → IntegerL1Kernel) (h : lp (fun _ : ℤ => ℝ) p)
    (hh : ∀ x, 0 ≤ h x) : ℤ → ℝ :=
  fun x =>
    let c : ι → ℝ≥0 := fun i =>
      ⟨integerKernelPositiveConvolution (K i) h x,
        integerKernelPositiveConvolution_nonneg (K := K i) (h := h) hh x⟩
    ↑(Finset.univ.sup c)

end FractionalPrimes.Literature.MSZ

end
