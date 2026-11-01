module

public import FractionalPrimes.FiniteSupportLpNorm
public import FractionalPrimes.FiniteConvolutionWeakBounds
public import FractionalPrimes.DiscreteLpBridge
public import FractionalPrimes.FourierSequence

@[expose] public section

/-!
# Counting-measure `L¹` and `L²` inputs from finite sequences

The constructors retain the exact support convention `if k ∈ s then f k else 0`.
The `L²` construction reuses the project's existing finite sequence in `lp`;
the `L¹` construction uses Mathlib's `MemLp.toLp` after the checked finite
counting-measure norm identity.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The exact finite-support truncation belongs to counting-measure `L¹`. -/
theorem finiteSupportMemLpOne (s : Finset ℤ) (f : ℤ → ℂ) :
    MemLp (fun k : ℤ => if k ∈ s then f k else 0) 1 Measure.count := by
  rw [MeasureTheory.memLp_iff, eLpNorm_finiteSupport_one_eq_sum]
  apply ENNReal.sum_lt_top.2
  intro k hk
  exact enorm_lt_top

/-- Construct the counting-measure `L¹` class of a finite-support complex
sequence, using the approved truncation convention. -/
noncomputable def finiteSupportCountLpOne (s : Finset ℤ) (f : ℤ → ℂ) :
    Lp ℂ 1 (Measure.count : Measure ℤ) :=
  (finiteSupportMemLpOne s f).toLp (fun k : ℤ => if k ∈ s then f k else 0)

/-- The `L¹` constructor has the exact requested representative at every
integer (counting-measure a.e. equality is pointwise on `ℤ`). -/
theorem finiteSupportCountLpOne_apply
    (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    (finiteSupportCountLpOne s f : ℤ → ℂ) k = if k ∈ s then f k else 0 := by
  have h := MemLp.coeFn_toLp (finiteSupportMemLpOne s f)
  exact (ae_count_int_iff_forall.mp h) k

/-- Exact counting-measure `L¹` norm formula for the constructed class. -/
theorem finiteSupportCountLpOne_eLpNorm
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (finiteSupportCountLpOne s f : ℤ → ℂ) 1 Measure.count =
      ∑ k ∈ s, ‖f k‖ₑ := by
  have h := MemLp.coeFn_toLp (finiteSupportMemLpOne s f)
  change eLpNorm
      ((finiteSupportMemLpOne s f).toLp
        (fun k : ℤ => if k ∈ s then f k else 0) : ℤ → ℂ)
      1 Measure.count = _
  calc
    eLpNorm
        ((finiteSupportMemLpOne s f).toLp
          (fun k : ℤ => if k ∈ s then f k else 0) : ℤ → ℂ)
        1 Measure.count =
      eLpNorm (fun k : ℤ => if k ∈ s then f k else 0) 1 Measure.count :=
        eLpNorm_congr_ae h
    _ = ∑ k ∈ s, ‖f k‖ₑ := eLpNorm_finiteSupport_one_eq_sum s f

/-- Construct the counting-measure `L²` class using the existing finite
sequence `lp` constructor and its isometric identification with counting
measure `L²`. -/
noncomputable def finiteSupportCountLpTwo (s : Finset ℤ) (f : ℤ → ℂ) :
    Lp ℂ 2 (Measure.count : Measure ℤ) :=
  lpToCountLp (finiteIntegerSequenceL2 s f)

/-- The reused `L²` constructor has the exact finite-support representative
at every integer. -/
theorem finiteSupportCountLpTwo_apply
    (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    (finiteSupportCountLpTwo s f : ℤ → ℂ) k = if k ∈ s then f k else 0 := by
  rw [finiteSupportCountLpTwo, lpToCountLp_apply, finiteIntegerSequenceL2_apply]

/-- Exact counting-measure `L²` norm formula for the constructed class. -/
theorem finiteSupportCountLpTwo_eLpNorm
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (finiteSupportCountLpTwo s f : ℤ → ℂ) 2 Measure.count =
      (∑ k ∈ s, ‖f k‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have hpoint :
      (finiteSupportCountLpTwo s f : ℤ → ℂ) =
        (fun k : ℤ => if k ∈ s then f k else 0) := by
    funext k
    exact finiteSupportCountLpTwo_apply s f k
  rw [hpoint]
  exact eLpNorm_finiteSupport_two_eq_sum_sq_sqrt s f

/-- Instantiated weak `(1,1)` estimate for the exact finite-support input;
the right side is written as its finite first moment. -/
theorem finiteSupportCountLpOne_convolution_weak
    (K : IntegerL1Kernel) (s : Finset ℤ) (f : ℤ → ℂ)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ENNReal.ofReal threshold *
        Measure.count {k : ℤ | ENNReal.ofReal threshold <
          ‖integerKernelConvolution K (finiteSupportCountLpOne s f : ℤ → ℂ) k‖ₑ} ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) * (∑ k ∈ s, ‖f k‖ₑ) := by
  simpa only [finiteSupportCountLpOne_eLpNorm] using
    integerKernelConvolution_weakL1 K (finiteSupportCountLpOne s f) hthreshold

/-- Instantiated weak `(2,2)` estimate for the exact finite-support input;
the `L²` operator bound remains an explicit hypothesis. -/
theorem finiteSupportCountLpTwo_convolution_weak
    (K : IntegerL1Kernel) (s : Finset ℤ) (f : ℤ → ℂ)
    (epsilon : ℝ≥0∞)
    (hL2 : eLpNorm
      (integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ))
      2 Measure.count ≤
        epsilon * eLpNorm (finiteSupportCountLpTwo s f : ℤ → ℂ) 2 Measure.count)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ENNReal.ofReal threshold ^ 2 *
        Measure.count {k : ℤ | ENNReal.ofReal threshold <
          ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ₑ} ≤
      (epsilon * (∑ k ∈ s, ‖f k‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
  simpa only [finiteSupportCountLpTwo_eLpNorm] using
    integerKernelConvolution_weakL2_of_bound K (finiteSupportCountLpTwo s f)
      epsilon hL2 hthreshold

end

end FractionalPrimes
