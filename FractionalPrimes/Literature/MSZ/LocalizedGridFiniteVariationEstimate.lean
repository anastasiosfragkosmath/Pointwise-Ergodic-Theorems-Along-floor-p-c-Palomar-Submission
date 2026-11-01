module

public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteVariationLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem mszFiniteVariationEstimate_Kq_nonneg (A : AdmissibleData) :
    0 ≤ mszLocalizedGridKq A := by
  unfold mszLocalizedGridKq
  split_ifs with hq2
  · have hr_lt : localInterpolationR A.q < A.q := by
      unfold localInterpolationR
      rw [div_lt_iff₀ (by linarith [A.q_gt_one] : 0 < A.q + 1)]
      nlinarith [A.q_gt_one]
    have hqPrimePos : 0 < localInterpolationQPrime A.q := by
      unfold localInterpolationQPrime
      exact div_pos (lt_trans zero_lt_one A.q_gt_one)
        (sub_pos.mpr A.q_gt_one)
    have hqPrimeGtTwo : 2 < localInterpolationQPrime A.q := by
      unfold localInterpolationQPrime
      rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
      nlinarith [hq2]
    have hrPrimeEq : localInterpolationRPrime A.q =
        2 * localInterpolationQPrime A.q := by
      unfold localInterpolationRPrime localInterpolationQPrime
      field_simp [ne_of_gt (sub_pos.mpr A.q_gt_one)]
    have hden1 : 0 < A.q - localInterpolationR A.q := by linarith
    have hden2 : 0 < 2 - A.q := sub_pos.mpr hq2
    have hden3 : 0 < localInterpolationQPrime A.q - 2 := by linarith
    have hden4 : 0 < localInterpolationRPrime A.q -
        localInterpolationQPrime A.q := by
      rw [hrPrimeEq]
      linarith
    have hC : 0 ≤ localInterpolationC A.q := by
      unfold localInterpolationC
      positivity
    have hP : 0 ≤ (max 1 (max (A.P (localInterpolationR A.q))
        (A.P (localInterpolationRPrime A.q))) : ℝ) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hD : 0 ≤ 2 * max 1 A.D := by positivity
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hP _))
      (Real.rpow_nonneg hD _)
  · norm_num

/-- The finite-support conclusion of `lm:finiteVariation`: sum the
fixed-level bounds after the source pointwise `sqrt 2` chaining estimate.
The conclusion is stated with counting-measure `eLpNorm`, at exactly `q` or
`q/(q-1)` and with coefficient `sqrt 2 K_q B_{K,L}^alpha sigma_q`. -/
theorem mszFiniteVariationEstimate_finiteSupport
    (A : AdmissibleData) (K L : ℕ)
    (p : ℝ) (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm (fun x : ℤ => mszFiniteShortVariation A K L f x)
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
          (Real.sqrt 2 * mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            mszSigmaQ A) *
        eLpNorm f (ENNReal.ofReal p) Measure.count := by
  classical
  let levels : Finset ℕ := Finset.range (L + 1)
  let levelFunction : ℕ → ℤ → ℝ := fun l x =>
    mszFiniteVariationLevelSquareFunction A K l f x
  let pENN : ℝ≥0∞ := ENNReal.ofReal p
  let inputNorm : ℝ≥0∞ := eLpNorm f pENN Measure.count
  let C₀ : ℝ := mszLocalizedGridKq A *
      (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2)
  have hB : 0 ≤ mszFiniteGridMaximalConstant A K L := by
    dsimp [mszFiniteGridMaximalConstant]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact mul_nonneg (mszFiniteVariationEstimate_Kq_nonneg A)
      (Real.rpow_nonneg hB _)
  have hpPrime : 1 < A.q / (A.q - 1) := by
    rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
    linarith
  have hpENNNeg : 1 ≤ pENN := by
    rcases hp with hpq | hpq'
    · dsimp [pENN]
      rw [hpq]
      simpa using ENNReal.ofReal_le_ofReal A.q_gt_one.le
    · dsimp [pENN]
      rw [hpq']
      simpa using ENNReal.ofReal_le_ofReal hpPrime.le
  have hlevelBound (l : ℕ) (hl : l ∈ levels) :
      eLpNorm (levelFunction l) pENN Measure.count ≤
        ENNReal.ofReal (C₀ * mszSigmaQLevel A l) * inputNorm := by
    have hlL : l ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    simpa [levelFunction, pENN, inputNorm, C₀] using
      (mszFiniteVariationLevelSquare_eLpNorm_le A K L l hlL p hp f hf)
  have hsumOfReal :
      (∑ l ∈ levels, ENNReal.ofReal (C₀ * mszSigmaQLevel A l)) =
        ENNReal.ofReal (C₀ * ∑ l ∈ levels, mszSigmaQLevel A l) := by
    calc
      (∑ l ∈ levels, ENNReal.ofReal (C₀ * mszSigmaQLevel A l)) =
          ENNReal.ofReal (∑ l ∈ levels, C₀ * mszSigmaQLevel A l) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg
              (fun l hl => mul_nonneg hC₀ (mszSigmaQLevel_nonneg A l))
      _ = ENNReal.ofReal (C₀ * ∑ l ∈ levels, mszSigmaQLevel A l) := by
            rw [Finset.mul_sum]
  have hlevelSum :
      (∑ l ∈ levels, eLpNorm (levelFunction l) pENN Measure.count) ≤
        ENNReal.ofReal (C₀ * mszSigmaQ A) * inputNorm := by
    have hsumWeighted :
        (∑ l ∈ levels,
          ENNReal.ofReal (C₀ * mszSigmaQLevel A l) * inputNorm) =
          ENNReal.ofReal (C₀ * ∑ l ∈ levels, mszSigmaQLevel A l) * inputNorm := by
      calc
        _ = (∑ l ∈ levels,
              ENNReal.ofReal (C₀ * mszSigmaQLevel A l)) * inputNorm := by
                rw [← Finset.sum_mul]
        _ = _ := by rw [hsumOfReal]
    have hsigma := mszSigmaQ_finiteLevels_le A L
    have hsumReal :
        C₀ * (∑ l ∈ levels, mszSigmaQLevel A l) ≤ C₀ * mszSigmaQ A :=
      mul_le_mul_of_nonneg_left hsigma hC₀
    have hsumENN : ENNReal.ofReal
        (C₀ * ∑ l ∈ levels, mszSigmaQLevel A l) ≤
          ENNReal.ofReal (C₀ * mszSigmaQ A) :=
      ENNReal.ofReal_le_ofReal hsumReal
    calc
      _ ≤ ∑ l ∈ levels,
          ENNReal.ofReal (C₀ * mszSigmaQLevel A l) * inputNorm :=
            Finset.sum_le_sum fun l hl => hlevelBound l hl
      _ = ENNReal.ofReal
          (C₀ * ∑ l ∈ levels, mszSigmaQLevel A l) * inputNorm := hsumWeighted
      _ ≤ ENNReal.ofReal (C₀ * mszSigmaQ A) * inputNorm := by
            have hmul := mul_le_mul_left hsumENN inputNorm
            simpa [mul_comm] using hmul
  have hshortNonneg (x : ℤ) : 0 ≤ mszFiniteShortVariation A K L f x :=
    Real.sqrt_nonneg _
  have hmajorantNonneg (x : ℤ) :
      0 ≤ Real.sqrt 2 * ∑ l ∈ levels, levelFunction l x :=
    mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun l hl => Real.sqrt_nonneg _)
  have hpointwise (x : ℤ) :
      ‖mszFiniteShortVariation A K L f x‖ ≤
        Real.sqrt 2 * ∑ l ∈ levels, levelFunction l x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hshortNonneg x)]
    simpa [levels, levelFunction] using
      mszFiniteShortVariation_le_sqrtTwo_sumLevelSquareFunctions A K L f x
  have hshortLp := eLpNorm_mono_real
    ((measurable_of_countable
      (fun x : ℤ => mszFiniteShortVariation A K L f x)).aestronglyMeasurable)
    hpointwise (p := pENN) (μ := Measure.count)
  have hscale :
      eLpNorm
        (fun x : ℤ => Real.sqrt 2 * ∑ l ∈ levels, levelFunction l x)
        pENN Measure.count =
      ENNReal.ofReal (Real.sqrt 2) *
        eLpNorm (fun x : ℤ => ∑ l ∈ levels, levelFunction l x)
          pENN Measure.count := by
    have hsmul :
        (fun x : ℤ => Real.sqrt 2 * ∑ l ∈ levels, levelFunction l x) =
          Real.sqrt 2 • (fun x => ∑ l ∈ levels, levelFunction l x) := by
      funext x
      simp [smul_eq_mul]
    rw [hsmul, eLpNorm_const_smul,
      Real.enorm_eq_ofReal (Real.sqrt_nonneg (2 : ℝ))]
  have htriangle := eLpNorm_sum_le
    (f := fun l x => levelFunction l x) (s := levels)
    (μ := Measure.count) hpENNNeg
  have hsumFn :
      (fun x : ℤ => ∑ l ∈ levels, levelFunction l x) =
        (∑ l ∈ levels, fun x : ℤ => levelFunction l x) := by
    funext x
    simp
  have htrianglePointwise :
      eLpNorm (fun x : ℤ => ∑ l ∈ levels, levelFunction l x)
          pENN Measure.count ≤
        ∑ l ∈ levels, eLpNorm (levelFunction l) pENN Measure.count := by
    rw [hsumFn]
    exact htriangle
  have hfinal :
      eLpNorm (fun x : ℤ => mszFiniteShortVariation A K L f x)
        pENN Measure.count ≤
      ENNReal.ofReal
          (Real.sqrt 2 * mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            mszSigmaQ A) * inputNorm := by
    calc
      eLpNorm (fun x : ℤ => mszFiniteShortVariation A K L f x)
          pENN Measure.count ≤
      eLpNorm
        (fun x : ℤ => Real.sqrt 2 * ∑ l ∈ levels, levelFunction l x)
        pENN Measure.count := hshortLp
      _ = ENNReal.ofReal (Real.sqrt 2) *
        eLpNorm (fun x : ℤ => ∑ l ∈ levels, levelFunction l x)
          pENN Measure.count := hscale
      _ ≤ ENNReal.ofReal (Real.sqrt 2) *
        (∑ l ∈ levels, eLpNorm (levelFunction l) pENN Measure.count) := by
          simpa [mul_comm] using
            (mul_le_mul_left htrianglePointwise (ENNReal.ofReal (Real.sqrt 2)))
      _ ≤ ENNReal.ofReal (Real.sqrt 2) *
        (ENNReal.ofReal (C₀ * mszSigmaQ A) * inputNorm) := by
          simpa [mul_comm] using
            (mul_le_mul_left hlevelSum (ENNReal.ofReal (Real.sqrt 2)))
      _ = ENNReal.ofReal
        (Real.sqrt 2 * mszLocalizedGridKq A *
          (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
          mszSigmaQ A) * inputNorm := by
          calc
            _ = (ENNReal.ofReal (Real.sqrt 2) *
                  ENNReal.ofReal (C₀ * mszSigmaQ A)) * inputNorm := by
                    simp [mul_assoc]
            _ = ENNReal.ofReal
                  (Real.sqrt 2 * (C₀ * mszSigmaQ A)) * inputNorm := by
                    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
            _ = _ := by
                  congr 2
                  dsimp [C₀]
                  ring
  simpa [pENN, inputNorm] using hfinal

end

end FractionalPrimes.Literature.MSZ

end
