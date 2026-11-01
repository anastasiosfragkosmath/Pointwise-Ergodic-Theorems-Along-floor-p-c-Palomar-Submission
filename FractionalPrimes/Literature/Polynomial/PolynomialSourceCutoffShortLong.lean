module

public import FractionalPrimes.Literature.Polynomial.PolynomialOuterCutoffPreservesAverages
public import FractionalPrimes.Literature.Polynomial.PolynomialShortLongTransfer
public import FractionalPrimes.Literature.Polynomial.PolynomialDivisorResidueStability
public import FractionalPrimes.PolynomialKernelProperties

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open scoped BigOperators

/-- The exact source-cutoff short-to-long transfer after substituting the
Mellin-envelope estimate for the short length. The coefficient family is the
fixed outer cutoff `f(n) ζ(n/X) 1_(n ≡ a mod q)` used in `lup:outer-cutoff`.
The estimate remains in the normalized complex-average form of the Mellin
window data so the average-identification lemma can be applied without changing
the endpoint convention. -/
theorem outerCutoffShortLongTransfer_fromMeanEnvelope
    (X H₁ H₂ W A C_D : ℝ) (q : ℕ) (a : ℤ) (f : ℤ → ℝ)
    (hX : 3 ≤ X) (hW : 2 ≤ W)
    (hWX : W ≤ Real.rpow X (1 / 100 : ℝ))
    (hH₁ : Real.rpow X (1 / 2 : ℝ) ≤ H₁)
    (hH₁₂ : H₁ ≤ H₂) (hH₂ : H₂ ≤ X / W ^ 4)
    (hH₁pos : 0 < H₁) (hH₁X : H₁ ≤ X)
    (hH₂pos : 0 < H₂) (hH₂X : H₂ ≤ X)
    (hq : 0 < q)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ))
    (hMean : dirichletMeanEnvelope
        (outerCutoffWindowData polynomialKernelRho X H₁ q a f
          hX hH₁pos hH₁X hq hf)
        (X / H₁) W ≤ C_D * Real.sqrt X * (Real.log X) ^ (-A : ℝ)) :
    X / H₁ ≥ W ∧
      ‖(outerCutoffWindowData polynomialKernelRho X H₁ q a f
          hX hH₁pos hH₁X hq hf).N_H -
        (outerCutoffWindowData polynomialKernelRho X H₂ q a f
          hX hH₂pos hH₂X hq hf).N_H‖ ≤
        128 * (1 + polynomialKernelM1) *
          (2 * Real.log X / W ^ 2 +
            ((1 + Real.log W) / Real.sqrt X) *
              (C_D * Real.sqrt X * (Real.log X) ^ (-A : ℝ))) := by
  let coeff : ℕ → ℂ := outerCutoffResidueCoefficient f X q a
  let w₁ : MellinWindowData := outerCutoffWindowData polynomialKernelRho
    X H₁ q a f hX hH₁pos hH₁X hq hf
  let w₂ : MellinWindowData := outerCutoffWindowData polynomialKernelRho
    X H₂ q a f hX hH₂pos hH₂X hq hf
  have hXpos : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans hX
  have hB : 0 ≤ 2 * Real.log X := by positivity
  have hsupport : ∀ n, 0 < n → coeff n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
    intro n hn hnz
    have hs := outerCutoffResidueCoefficient_support f X q a hX n hn hnz
    exact ⟨hs.1, hs.2.le⟩
  have hbound : ∀ n, 0 < n → ‖coeff n‖ ≤ 2 * Real.log X := by
    intro n hn
    exact outerCutoffResidueCoefficient_bound f X q a hX hf n hn
  have htransfer := shortLongTransferBoundedCoefficients
    X W H₁ H₂ (2 * Real.log X) coeff hX hW hWX hH₁ hH₁₂ hH₂ hB
      hsupport hbound
  have htransfer' : X / H₁ ≥ W ∧
      ‖w₁.N_H - w₂.N_H‖ ≤
        128 * (1 + polynomialKernelM1) *
          (2 * Real.log X / W ^ 2 +
            ((1 + Real.log W) / Real.sqrt X) *
              dirichletMeanEnvelope w₁ (X / H₁) W) := by
    simpa [w₁, w₂, coeff, outerCutoffWindowData] using htransfer
  have hfactor : 0 ≤ (1 + Real.log W) / Real.sqrt X := by
    have hWpos : 0 < W := by linarith
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
    exact div_nonneg
      (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ W)]) hsqrt.le
  have hM1nonneg : 0 ≤ polynomialKernelM1 := by
    unfold polynomialKernelM1
    exact integral_nonneg fun u =>
      mul_nonneg (abs_nonneg u) (polynomialKernelRho_nonneg u)
  have htransferFactor : 0 ≤ 128 * (1 + polynomialKernelM1) := by positivity
  refine ⟨htransfer'.1, ?_⟩
  calc
    _ ≤ 128 * (1 + polynomialKernelM1) *
        (2 * Real.log X / W ^ 2 +
          ((1 + Real.log W) / Real.sqrt X) *
            dirichletMeanEnvelope w₁ (X / H₁) W) := htransfer'.2
    _ ≤ 128 * (1 + polynomialKernelM1) *
        (2 * Real.log X / W ^ 2 +
          ((1 + Real.log W) / Real.sqrt X) *
            (C_D * Real.sqrt X * (Real.log X) ^ (-A : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ htransferFactor
      exact add_le_add (le_refl (2 * Real.log X / W ^ 2))
        (mul_le_mul_of_nonneg_left hMean hfactor)

#print axioms FractionalPrimes.Literature.Polynomial.outerCutoffShortLongTransfer_fromMeanEnvelope

end FractionalPrimes.Literature.Polynomial

end
