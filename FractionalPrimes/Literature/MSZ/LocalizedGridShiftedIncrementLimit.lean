module

public import FractionalPrimes.DiscreteLpBridge
public import FractionalPrimes.LpConvolutionCLM
public import FractionalPrimes.Literature.MSZ.LocalizedGridShiftedResolution

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The full shifted symmetric-resolution conclusion in `lm:shiftedResolution`,
obtained by comparing shifted and centered windows and using the assumed
centered resolution from `AdmissibleData`. -/
theorem mszLocalizedShiftedSymmetricResolution
    (A : AdmissibleData) (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) (k : ℤ) :
    Tendsto
      (fun J : ℕ =>
        ‖(∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              A.projectionsL2 (k + j) f) - f‖)
      atTop (𝓝 0) := by
  have hcompare : Tendsto
      (fun J : ℕ =>
        ‖(∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              A.projectionsL2 (k + j) f) -
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f‖)
      atTop (𝓝 0) :=
    mszLocalizedShiftedSymmetricWindowComparison A f k
  have hcompareVec : Tendsto
      (fun J : ℕ =>
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            A.projectionsL2 (k + j) f) -
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f)
      atTop (𝓝 0) := (tendsto_zero_iff_norm_tendsto_zero).2 hcompare
  have hcenterVec : Tendsto
      (fun J : ℕ =>
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f) - f)
      atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 (A.symmetric_resolution f)
  have hsumVec : Tendsto
      (fun J : ℕ =>
        ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            A.projectionsL2 (k + j) f) -
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f) +
          ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f) - f))
      atTop (𝓝 0) := by
    simpa using hcompareVec.add hcenterVec
  have hEq :
      (fun J : ℕ =>
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            A.projectionsL2 (k + j) f) - f) =
      (fun J : ℕ =>
        ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            A.projectionsL2 (k + j) f) -
          ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f) +
          ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 j f) - f)) := by
    funext J
    abel
  have hshiftVec : Tendsto
      (fun J : ℕ =>
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            A.projectionsL2 (k + j) f) - f)
      atTop (𝓝 0) := by
    rw [hEq]
    exact hsumVec
  exact (tendsto_zero_iff_norm_tendsto_zero).1 hshiftVec

/-- The sequence-space continuous operator for a fixed grid increment, built
from the existing counting-measure convolution map and the isometric
sequence/counting-`L²` identifications. -/
noncomputable def mszGridIncrementLpCLM
    (A : AdmissibleData) (k : ℤ) (l m : ℕ) :
    lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  exact countLpToLpIsometry.toContinuousLinearMap.comp
    ((integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
        (mszGridIncrementKernel A.kernel k l m)).comp
      lpToCountLpIsometry.toContinuousLinearMap)

/-- On the canonical sequence representative, the continuous `ℓ²` increment
operator is exactly the source's raw grid increment. -/
theorem mszGridIncrementLpCLM_apply
    (A : AdmissibleData) (k : ℤ) (l m : ℕ)
    (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) (x : ℤ) :
    (mszGridIncrementLpCLM A k l m f : ℤ → ℂ) x =
      mszGridIncrement A.kernel k l m (f : ℤ → ℂ) x := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  change
    (countLpToLp
      (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
        (mszGridIncrementKernel A.kernel k l m) (lpToCountLp f)) : ℤ → ℂ) x = _
  rw [countLpToLp_apply, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  have hinput : (lpToCountLp f : ℤ → ℂ) = (f : ℤ → ℂ) := by
    funext n
    exact lpToCountLp_apply f n
  calc
    integerKernelConvolution (mszGridIncrementKernel A.kernel k l m)
        (lpToCountLp f : ℤ → ℂ) x =
      mszGridIncrement A.kernel k l m (lpToCountLp f : ℤ → ℂ) x :=
        (mszGridIncrement_eq_kernelConvolution
          (p := (2 : ℝ≥0∞)) (by norm_num) A.kernel k l m
          (lpToCountLp f) x).symm
    _ = mszGridIncrement A.kernel k l m (f : ℤ → ℂ) x := by
      rw [hinput]

/-- Applying a fixed increment convolution to the shifted symmetric
projection sums preserves their `ℓ²` convergence. This is the first operator
limit used in the proof of `lm:finiteVariationEstimate`. -/
theorem mszLocalizedGridIncrementShiftedResolution
    (A : AdmissibleData) (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞))
    (k : ℤ) (l m : ℕ) :
    Tendsto
      (fun J : ℕ =>
        ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          mszGridIncrementLpCLM A k l m (A.projectionsL2 (k + j) f))
      atTop (𝓝 (mszGridIncrementLpCLM A k l m f)) := by
  let T := mszGridIncrementLpCLM A k l m
  have hresolution := mszLocalizedShiftedSymmetricResolution A f k
  have hresolutionVec : Tendsto
      (fun J : ℕ =>
        ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          A.projectionsL2 (k + j) f)
      atTop (𝓝 f) := tendsto_iff_norm_sub_tendsto_zero.2 hresolution
  have hmap : Tendsto
      (fun J : ℕ => T
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 (k + j) f))
      atTop (𝓝 (T f)) := (T.continuous.tendsto f).comp hresolutionVec
  have hsumEq :
      (fun J : ℕ => T
        (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), A.projectionsL2 (k + j) f)) =
      (fun J : ℕ =>
        ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          T (A.projectionsL2 (k + j) f)) := by
    funext J
    simp
  rw [← hsumEq]
  exact hmap

end

end FractionalPrimes.Literature.MSZ

end
