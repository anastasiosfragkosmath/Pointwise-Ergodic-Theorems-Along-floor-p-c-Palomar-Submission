module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortLongTransfer
public import FractionalPrimes.Literature.Polynomial.PolynomialOuterCutoffPreservesAverages
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor
public import Mathlib.Data.Int.ModEq

/-! A finite coefficient bridge from the checked bounded-coefficient
short-to-long transfer to a single residue-restricted `Λ - Cr_X` sequence.
The Dirichlet-mean envelope remains explicit; this file proves no analytic
bound for it. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial
open scoped BigOperators

/-- The source coefficient bound for the residue-restricted `Λ - Cr_X`
sequence after applying the fixed outer cutoff. -/
def unitResidueLambdaMinusCramerCoefficientBound (X : ℝ) : ℝ :=
  2 * Real.log X + paperCramerDensity (paperShortBlockCutoff X)

/-- The finite Mellin coefficient for `Λ - Cr_X`, restricted to one residue
class and multiplied by the source's fixed smooth outer cutoff. -/
noncomputable def unitResidueLambdaMinusCramerCoefficient
    (X : ℝ) (q : ℕ) (a : ℤ) (n : ℕ) : ℂ :=
  (((paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)) *
      polynomialOuterCutoff ((n : ℝ) / X) : ℝ) : ℂ) *
    if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0

theorem unitResidueLambdaMinusCramerCoefficient_support
    (X : ℝ) (q : ℕ) (a : ℤ) (hX : 3 ≤ X) :
    ∀ n, 0 < n →
      unitResidueLambdaMinusCramerCoefficient X q a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
  intro n hn hcoeff
  by_cases hmod : Int.ModEq (q : ℤ) (n : ℤ) a
  · have hcut : polynomialOuterCutoff ((n : ℝ) / X) ≠ 0 := by
      intro hz
      apply hcoeff
      simp [unitResidueLambdaMinusCramerCoefficient, hmod, hz]
    have hcutSupport := polynomialOuterCutoff_support_subset
      (by simpa [Function.mem_support] using hcut)
    have hXpos : 0 < X := by linarith
    have hmul : ((n : ℝ) / X) * X = (n : ℝ) := by field_simp
    constructor
    · nlinarith [hcutSupport.1]
    · have hupper : (n : ℝ) < 3 * X := by nlinarith [hcutSupport.2]
      exact hupper.le
  · simp [unitResidueLambdaMinusCramerCoefficient, hmod] at hcoeff

theorem unitResidueLambdaMinusCramerCoefficient_bound
    (X : ℝ) (q : ℕ) (a : ℤ) (hX : 3 ≤ X) :
    ∀ n, 0 < n →
      ‖unitResidueLambdaMinusCramerCoefficient X q a n‖ ≤
        unitResidueLambdaMinusCramerCoefficientBound X := by
  intro n hn
  have hR : 0 ≤ paperCramerDensity (paperShortBlockCutoff X) := by
    unfold paperCramerDensity
    positivity
  have hB : 0 ≤ unitResidueLambdaMinusCramerCoefficientBound X := by
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hX])
    unfold unitResidueLambdaMinusCramerCoefficientBound
    positivity
  have hcutNonneg := polynomialOuterCutoff_nonneg ((n : ℝ) / X)
  have hcutle := polynomialOuterCutoff_le_one ((n : ℝ) / X)
  by_cases hmod : Int.ModEq (q : ℤ) (n : ℤ) a
  · by_cases hcutZero : polynomialOuterCutoff ((n : ℝ) / X) = 0
    · simp [unitResidueLambdaMinusCramerCoefficient, hmod, hcutZero]
      exact hB
    · have hLambda := outerCutoffArithmeticWeight_abs_le paperLambda X n hX
        (Or.inl rfl) hn hcutZero
      have hCramer := cramerWeight_abs_le_density X (n : ℤ)
      have hdifference :
          |paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)| ≤
            unitResidueLambdaMinusCramerCoefficientBound X := by
        calc
          |paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)| =
              |paperLambda (n : ℤ) +
                -(paperShortBlockCramerWeight X (n : ℤ))| := by congr 1 <;> ring
          _ ≤ |paperLambda (n : ℤ)| +
                |-(paperShortBlockCramerWeight X (n : ℤ))| := abs_add_le _ _
          _ = |paperLambda (n : ℤ)| +
                |paperShortBlockCramerWeight X (n : ℤ)| := by rw [abs_neg]
          _ ≤ 2 * Real.log X + paperCramerDensity (paperShortBlockCutoff X) :=
                add_le_add hLambda hCramer
          _ = unitResidueLambdaMinusCramerCoefficientBound X := rfl
      have hnorm :
          ‖unitResidueLambdaMinusCramerCoefficient X q a n‖ =
            |paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)| *
              polynomialOuterCutoff ((n : ℝ) / X) := by
        change ‖
            ((((paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)) *
                polynomialOuterCutoff ((n : ℝ) / X) : ℝ) : ℂ) *
              (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0))‖ = _
        rw [if_pos hmod, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_mul, abs_of_nonneg hcutNonneg]
      rw [hnorm]
      calc
        |paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ)| *
            polynomialOuterCutoff ((n : ℝ) / X) ≤
          unitResidueLambdaMinusCramerCoefficientBound X *
            polynomialOuterCutoff ((n : ℝ) / X) :=
          mul_le_mul_of_nonneg_right hdifference hcutNonneg
        _ ≤ unitResidueLambdaMinusCramerCoefficientBound X * 1 :=
          mul_le_mul_of_nonneg_left hcutle hB
        _ = unitResidueLambdaMinusCramerCoefficientBound X := mul_one _
  · simp [unitResidueLambdaMinusCramerCoefficient, hmod]
    exact hB

/-- The residue-restricted normalized average of a real integer-indexed
coefficient on `(X,X+H]`. -/
noncomputable def unitResidueCoefficientAverage
    (X H : ℝ) (q : ℕ) (a : ℤ) (f : ℤ → ℝ) : ℂ :=
  ((H⁻¹ : ℝ) : ℂ) *
    ∑ n ∈ (mellinWindowAverageIndices X H).filter
      (fun n : ℕ => Int.ModEq (q : ℤ) (n : ℤ) a),
      (f (n : ℤ) : ℂ)

/-- The coefficient sequence's smoothed-window average is exactly the
original unit-residue average. The cutoff equals one on the full averaging
interval, including the source's open-left, closed-right endpoints. -/
theorem unitResidueLambdaMinusCramerWindowData_average
    (X H : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) :
    (mellinWindowData FractionalPrimes.polynomialKernelRho X H
      (unitResidueLambdaMinusCramerCoefficientBound X)
      (unitResidueLambdaMinusCramerCoefficient X q a)
      hX hH hHX (by
        have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hX])
        have hR : 0 ≤ paperCramerDensity (paperShortBlockCutoff X) := by
          unfold paperCramerDensity
          positivity
        unfold unitResidueLambdaMinusCramerCoefficientBound
        positivity)
      (unitResidueLambdaMinusCramerCoefficient_support X q a hX)
      (unitResidueLambdaMinusCramerCoefficient_bound X q a hX)).N_H =
      unitResidueCoefficientAverage X H q a
        (fun n => paperLambda n - paperShortBlockCramerWeight X n) := by
  classical
  let I := mellinWindowAverageIndices X H
  have hsum :
      (∑ n ∈ I,
        unitResidueLambdaMinusCramerCoefficient X q a n) =
      ∑ n ∈ I.filter
        (fun n : ℕ => Int.ModEq (q : ℤ) (n : ℤ) a),
        ((paperLambda (n : ℤ) - paperShortBlockCramerWeight X (n : ℤ) : ℝ) : ℂ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hnI : X < (n : ℝ) ∧ (n : ℝ) ≤ X + H := by
      apply (mellinIntervalIndices_mem_iff (by linarith [hX]) n).1
      simpa [I, mellinWindowAverageIndices] using hn
    have hXpos : 0 < X := by linarith
    have hlo : 1 ≤ (n : ℝ) / X := by
      apply (le_div_iff₀ hXpos).2
      linarith [hnI.1]
    have hhi : (n : ℝ) / X ≤ 2 := by
      have hupper : X + H ≤ 2 * X := by linarith
      apply (div_le_iff₀ hXpos).2
      exact hnI.2.trans hupper
    have hcut : polynomialOuterCutoff ((n : ℝ) / X) = 1 :=
      polynomialOuterCutoff_eq_one hlo hhi
    by_cases hmod : Int.ModEq (q : ℤ) (n : ℤ) a
    · simp [unitResidueLambdaMinusCramerCoefficient, hmod, hcut]
    · simp [unitResidueLambdaMinusCramerCoefficient, hmod]
  change ((H⁻¹ : ℝ) : ℂ) *
      (∑ n ∈ I, unitResidueLambdaMinusCramerCoefficient X q a n) = _
  rw [hsum]
  rfl

/-- Apply the checked bounded-coefficient short-to-long transfer to the
unit-residue `Λ - Cr_X` sequence. The Dirichlet-mean envelope remains the
explicit source term; this is a finite transport result, not a bound for that
envelope or an analytic cancellation theorem. -/
theorem unitResidueLambdaMinusCramerShortLongTransfer
    (X W H1 H2 : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) (hW : 2 ≤ W)
    (hWX : W ≤ Real.rpow X (1 / 100 : ℝ))
    (hH1 : Real.rpow X (1 / 2 : ℝ) ≤ H1)
    (hH12 : H1 ≤ H2) (hH2 : H2 ≤ X / W ^ 4) :
    let B := unitResidueLambdaMinusCramerCoefficientBound X
    let coeff := unitResidueLambdaMinusCramerCoefficient X q a
    let hB : 0 ≤ B := by
      have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hX])
      have hR : 0 ≤ paperCramerDensity (paperShortBlockCutoff X) := by
        unfold paperCramerDensity
        positivity
      dsimp [B, unitResidueLambdaMinusCramerCoefficientBound]
      positivity
    let hsupport := unitResidueLambdaMinusCramerCoefficient_support X q a hX
    let hbound := unitResidueLambdaMinusCramerCoefficient_bound X q a hX
    let hH1pos : 0 < H1 := by
      have hx : 0 < X := by linarith [hX]
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hH1
    let hW4 : 1 ≤ W ^ 4 := by nlinarith [sq_nonneg (W - 2)]
    let hW4pos : 0 < W ^ 4 := by positivity
    let hH2X : H2 ≤ X := by
      have hx : 0 ≤ X := by linarith [hX]
      have hXover : X / W ^ 4 ≤ X := by
        apply (div_le_iff₀ hW4pos).2
        nlinarith [mul_nonneg hx (sub_nonneg.mpr hW4)]
      exact hH2.trans hXover
    let hH1X : H1 ≤ X := le_trans hH12 hH2X
    let w1 := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H1 B coeff hX hH1pos hH1X hB hsupport hbound
    let w2 := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H2 B coeff hX (lt_of_lt_of_le hH1pos hH12) hH2X hB hsupport hbound
    let T0 := X / H1
    T0 ≥ W ∧
      ‖unitResidueCoefficientAverage X H1 q a
          (fun n => paperLambda n - paperShortBlockCramerWeight X n) -
        unitResidueCoefficientAverage X H2 q a
          (fun n => paperLambda n - paperShortBlockCramerWeight X n)‖ ≤
        128 * (1 + FractionalPrimes.polynomialKernelM1) *
          (B / W ^ 2 +
            ((1 + Real.log W) / Real.sqrt X) *
              dirichletMeanEnvelope w1 T0 W) := by
  classical
  dsimp only
  let B := unitResidueLambdaMinusCramerCoefficientBound X
  have hB : 0 ≤ B := by
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith [hX])
    have hR : 0 ≤ paperCramerDensity (paperShortBlockCutoff X) := by
      unfold paperCramerDensity
      positivity
    dsimp [B, unitResidueLambdaMinusCramerCoefficientBound]
    positivity
  let coeff := unitResidueLambdaMinusCramerCoefficient X q a
  let hsupport := unitResidueLambdaMinusCramerCoefficient_support X q a hX
  let hbound := unitResidueLambdaMinusCramerCoefficient_bound X q a hX
  let hH1pos : 0 < H1 := by
    have hx : 0 < X := by linarith [hX]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hH1
  have hW4 : 1 ≤ W ^ 4 := by nlinarith [sq_nonneg (W - 2)]
  have hW4pos : 0 < W ^ 4 := by positivity
  have hH2X : H2 ≤ X := by
    have hx : 0 ≤ X := by linarith [hX]
    have hXover : X / W ^ 4 ≤ X := by
      apply (div_le_iff₀ hW4pos).2
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hW4)]
    exact hH2.trans hXover
  have hH1X : H1 ≤ X := le_trans hH12 hH2X
  let w1 := mellinWindowData FractionalPrimes.polynomialKernelRho
    X H1 B coeff hX hH1pos hH1X hB hsupport hbound
  let w2 := mellinWindowData FractionalPrimes.polynomialKernelRho
    X H2 B coeff hX (lt_of_lt_of_le hH1pos hH12) hH2X hB hsupport hbound
  let T0 := X / H1
  have htransfer := shortLongTransferBoundedCoefficients
    X W H1 H2 B coeff hX hW hWX hH1 hH12 hH2 hB hsupport hbound
  have hmean1 := unitResidueLambdaMinusCramerWindowData_average
    X H1 q a hX hH1pos hH1X
  have hmean2 := unitResidueLambdaMinusCramerWindowData_average
    X H2 q a hX (lt_of_lt_of_le hH1pos hH12) hH2X
  refine ⟨?_, ?_⟩
  · simpa [T0] using htransfer.1
  · have hN := htransfer.2
    rw [← hmean1, ← hmean2]
    simpa [w1, w2, T0, coeff] using hN

#print axioms unitResidueLambdaMinusCramerWindowData_average
#print axioms unitResidueLambdaMinusCramerShortLongTransfer

end FractionalPrimes.Literature.Uniformity
