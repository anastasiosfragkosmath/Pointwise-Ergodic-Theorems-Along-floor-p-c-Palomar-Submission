module

public import FractionalPrimes.Literature.Polynomial.TypeIICharacterAllocationIntegral
public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorCoefficientEnvelopes
public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorTrilinearBridge

/-! Exact per-allocation/per-character K bound for the selected-decomposition
PTW argument. The coefficient envelopes are kept in their source normalization
scales; applying the normalized ldm:uncapped bridge costs their exact product. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.LargeValues
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- A checked shifted divisor envelope for a positive dyadic convolution group
gives the exact normalized `C=20` coefficient hypothesis at a gcd allocation.
The scale `B` is retained so the source normalization can be restored later. -/
theorem selectedPositiveDyadicGroup_factorCoefficientBound
    {X z M B T : ℝ} (hX : 3 ≤ X) (hM : 0 < M)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (hweight : dyadicFactorsMassWeight fs ≤ Real.log (8 * X))
    {r : ℕ} (hr : 1 ≤ r)
    (hBscale : (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 r : ℝ) ^ 20 ≤ B)
    (hBpos : 0 < B) (χ : ℕ → ℂ) (hχ : ∀ n, ‖χ n‖ ≤ 1) :
    factorCoefficientBound 20 M
      (selectedGroupTrilinearCoeff B r
        (fun n => toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs) n) χ T) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hraw : ∀ n ∈ dirichletIndices M,
      ‖toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs) (r * n)‖ ≤
        B * (divisorCoefficient 2 n : ℝ) ^ 20 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnR : 0 < (n : ℝ) := lt_trans hM hmem.2
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hshift := dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
      (z := z) hX fs hlen hweight hr0 hn0
    have hsource :
        ‖toComplexArithmeticFunction
            (dyadicConvolutionPositiveComplex z fs) (r * n)‖ ≤
          (2 : ℝ) ^ 10 * Real.log (8 * X) *
            (divisorCoefficient 2 r : ℝ) ^ 20 *
              (divisorCoefficient 2 n : ℝ) ^ 20 := by
      rw [toComplexArithmeticFunction_apply
        (dyadicConvolutionPositiveComplex z fs)
        ⟨r * n, Nat.mul_pos hr0 hn0⟩]
      exact hshift
    calc
      ‖toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs) (r * n)‖ ≤
        ((2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r : ℝ) ^ 20) *
            (divisorCoefficient 2 n : ℝ) ^ 20 := by
          ring_nf at hsource ⊢
          exact hsource
      _ ≤ B * (divisorCoefficient 2 n : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hBscale (by positivity)
  exact selectedGroupTrilinearCoeff_factorCoefficientBound
    hBpos r
    (fun n => toComplexArithmeticFunction
      (dyadicConvolutionPositiveComplex z fs) n) χ hχ hraw

/-- The exact source-scale K for one selected three-factor block, allocation,
and character. The three shifted coefficient envelopes imply the normalized
`ldm:uncapped` coefficient hypotheses. Restoring the source scales costs
exactly `B₁ B₂ B₃`; the selected first-factor saving and its full frequency
window are unchanged. -/
theorem selectedAllocationTrilinearIntegral_bound
    (Y eps Tmean alpha beta gamma X a M B₁ B₂ B₃ Tfreq : ℝ)
    (E : Set ℝ)
    (r₁ r₂ r₃ : ℕ) (g₁ χ₁ g₂ χ₂ g₃ χ₃ : ℕ → ℂ)
    (hM : 0 < M) (hMpow : M = Y ^ alpha)
    (hB₁ : 1 ≤ B₁) (hB₁pos : 0 < B₁)
    (hB₂pos : 0 < B₂) (hB₃pos : 0 < B₃)
    (hX : (2 : ℝ) ^ 16 ≤ Y)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hTmean0 : 2 ≤ Tmean) (hTmean : Tmean ≤ Y ^ (3 / 8 - eps))
    (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta) (hc0 : 0 ≤ gamma)
    (hsum : alpha + beta + gamma = 1)
    (haLow : 1 / 4 - eps / 100 ≤ alpha)
    (haHigh : alpha ≤ 1 / 2 + eps / 100)
    (hbc : |beta - gamma| ≤ 1 / 4 + eps / 100)
    (hδ0 : 0 < (Real.log X) ^ (-20 * a))
    (hδ : (Real.log X) ^ (-20 * a) ≤ 1)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-Tmean) Tmean)
    (hχ₁ : ∀ n, ‖χ₁ n‖ ≤ 1) (hχ₂ : ∀ n, ‖χ₂ n‖ ≤ 1)
    (hχ₃ : ∀ n, ‖χ₃ n‖ ≤ 1)
    (hraw₁ : ∀ n ∈ dirichletIndices (Y ^ alpha),
      ‖g₁ (r₁ * n)‖ ≤ B₁ * (divisorCoefficient 2 n : ℝ) ^ 20)
    (hraw₂ : ∀ n ∈ dirichletIndices (Y ^ beta),
      ‖g₂ (r₂ * n)‖ ≤ B₂ * (divisorCoefficient 2 n : ℝ) ^ 20)
    (hraw₃ : ∀ n ∈ dirichletIndices (Y ^ gamma),
      ‖g₃ (r₃ * n)‖ ≤ B₃ * (divisorCoefficient 2 n : ℝ) ^ 20)
    (hfreq : ∀ t ∈ E,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
        g₁ (r₁ * n) * factorExtractionMellinWeight χ₁ s n‖ ≤
          (Real.log X) ^ (-20 * a) * Real.sqrt M) :
    (∫ t in E,
      ‖((B₁ * B₂ * B₃ : ℝ) : ℂ) *
        (factorPolynomial (Y ^ alpha)
            (selectedGroupTrilinearCoeff B₁ r₁ g₁ χ₁ Tfreq) t *
          factorPolynomial (Y ^ beta)
            (selectedGroupTrilinearCoeff B₂ r₂ g₂ χ₂ Tfreq) t *
          factorPolynomial (Y ^ gamma)
            (selectedGroupTrilinearCoeff B₃ r₃ g₃ χ₃ Tfreq) t)‖) ≤
      B₁ * B₂ * B₃ *
        (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y *
          (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ))) := by
  let c₁ := selectedGroupTrilinearCoeff B₁ r₁ g₁ χ₁ Tfreq
  let c₂ := selectedGroupTrilinearCoeff B₂ r₂ g₂ χ₂ Tfreq
  let c₃ := selectedGroupTrilinearCoeff B₃ r₃ g₃ χ₃ Tfreq
  have hcoeff₁ : factorCoefficientBound 20 (Y ^ alpha) c₁ := by
    dsimp [c₁]
    exact selectedGroupTrilinearCoeff_factorCoefficientBound
      hB₁pos r₁ g₁ χ₁ hχ₁ hraw₁
  have hcoeff₂ : factorCoefficientBound 20 (Y ^ beta) c₂ := by
    dsimp [c₂]
    exact selectedGroupTrilinearCoeff_factorCoefficientBound
      hB₂pos r₂ g₂ χ₂ hχ₂ hraw₂
  have hcoeff₃ : factorCoefficientBound 20 (Y ^ gamma) c₃ := by
    dsimp [c₃]
    exact selectedGroupTrilinearCoeff_factorCoefficientBound
      hB₃pos r₃ g₃ χ₃ hχ₃ hraw₃
  have htri := trilinearUncapped_of_selectedGroupMellinBlock
    Y eps Tmean alpha beta gamma X a M B₁ Tfreq E r₁ g₁ χ₁ c₂ c₃
    hM hMpow hB₁ hX heps0 heps hTmean0 hTmean ha0 hb0 hc0 hsum
    haLow haHigh hbc hδ0 hδ hE hEsub hcoeff₁ hcoeff₂ hcoeff₃ hfreq hblock
  have hBprod : 0 < B₁ * B₂ * B₃ := mul_pos (mul_pos hB₁pos hB₂pos) hB₃pos
  let p₁ := factorPolynomial (Y ^ alpha) c₁
  let p₂ := factorPolynomial (Y ^ beta) c₂
  let p₃ := factorPolynomial (Y ^ gamma) c₃
  have hscaled :
      (∫ t in E, ‖((B₁ * B₂ * B₃ : ℝ) : ℂ) *
          (p₁ t * p₂ t * p₃ t)‖) =
        (B₁ * B₂ * B₃) * (∫ t in E, ‖p₁ t * p₂ t * p₃ t‖) := by
    calc
      _ = ∫ t in E,
          (B₁ * B₂ * B₃) * ‖p₁ t * p₂ t * p₃ t‖ := by
            apply integral_congr_ae
            filter_upwards [] with t
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBprod]
      _ = _ := by rw [integral_const_mul]
  calc
    _ = (B₁ * B₂ * B₃) * (∫ t in E, ‖p₁ t * p₂ t * p₃ t‖) := hscaled
    _ ≤ (B₁ * B₂ * B₃) *
        (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y *
          (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ))) :=
      mul_le_mul_of_nonneg_left htri (le_of_lt hBprod)
    _ = _ := by ring

/-- The source-group specialization of the preceding K bound. The first
factor is the scalar-weighted selected group and the other two are positive
convolution groups. The three checked shifted divisor envelopes are applied
at the exact gcd allocations before invoking `ldm:uncapped`. -/
theorem selectedDyadicGroupAllocationTrilinearIntegral_bound
    (Y eps Tmean alpha beta gamma X a M B₁ B₂ B₃ Tfreq z : ℝ)
    (E : Set ℝ) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (r₁ r₂ r₃ : ℕ) (χ₁ χ₂ χ₃ : ℕ → ℂ)
    (hXsrc : 3 ≤ X) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : fs₁.length ≤ 20) (hlen₂ : fs₂.length ≤ 20)
    (hlen₃ : fs₃.length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight fs₁ ≤ Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight fs₂ ≤ Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight fs₃ ≤ Real.log (8 * X))
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hr₃ : 1 ≤ r₃)
    (hB₁scale : (2 : ℝ) ^ 10 * Real.log (8 * X) *
      (divisorCoefficient 2 r₁ : ℝ) ^ 20 ≤ B₁)
    (hB₂scale : (2 : ℝ) ^ 10 * Real.log (8 * X) *
      (divisorCoefficient 2 r₂ : ℝ) ^ 20 ≤ B₂)
    (hB₃scale : (2 : ℝ) ^ 10 * Real.log (8 * X) *
      (divisorCoefficient 2 r₃ : ℝ) ^ 20 ≤ B₃)
    (hM : 0 < M) (hMpow : M = Y ^ alpha)
    (hB₁ : 1 ≤ B₁) (hB₁pos : 0 < B₁)
    (hB₂pos : 0 < B₂) (hB₃pos : 0 < B₃)
    (hX : (2 : ℝ) ^ 16 ≤ Y)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hTmean0 : 2 ≤ Tmean) (hTmean : Tmean ≤ Y ^ (3 / 8 - eps))
    (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta) (hc0 : 0 ≤ gamma)
    (hsum : alpha + beta + gamma = 1)
    (haLow : 1 / 4 - eps / 100 ≤ alpha)
    (haHigh : alpha ≤ 1 / 2 + eps / 100)
    (hbc : |beta - gamma| ≤ 1 / 4 + eps / 100)
    (hδ0 : 0 < (Real.log X) ^ (-20 * a))
    (hδ : (Real.log X) ^ (-20 * a) ≤ 1)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-Tmean) Tmean)
    (hχ₁ : ∀ n, ‖χ₁ n‖ ≤ 1) (hχ₂ : ∀ n, ‖χ₂ n‖ ≤ 1)
    (hχ₃ : ∀ n, ‖χ₃ n‖ ≤ 1)
    (hfreq : ∀ t ∈ E,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
            (r₁ * n) * factorExtractionMellinWeight χ₁ s n‖ ≤
          (Real.log X) ^ (-20 * a) * Real.sqrt M) :
    (∫ t in E,
      ‖((B₁ * B₂ * B₃ : ℝ) : ℂ) *
        (factorPolynomial (Y ^ alpha)
            (selectedGroupTrilinearCoeff B₁ r₁
              (fun n => toComplexArithmeticFunction
                (groupedDyadicFactor z c fs₁) n) χ₁ Tfreq) t *
          factorPolynomial (Y ^ beta)
            (selectedGroupTrilinearCoeff B₂ r₂
              (fun n => toComplexArithmeticFunction
                (dyadicConvolutionPositiveComplex z fs₂) n) χ₂ Tfreq) t *
          factorPolynomial (Y ^ gamma)
            (selectedGroupTrilinearCoeff B₃ r₃
              (fun n => toComplexArithmeticFunction
                (dyadicConvolutionPositiveComplex z fs₃) n) χ₃ Tfreq) t)‖) ≤
      B₁ * B₂ * B₃ *
        (J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) *
          Real.sqrt Y *
          (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ))) := by
  let g₁ : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction (groupedDyadicFactor z c fs₁) n
  let g₂ : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₂) n
  let g₃ : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₃) n
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le (by decide) hr₁
  have hr₂pos : 0 < r₂ := lt_of_lt_of_le (by decide) hr₂
  have hr₃pos : 0 < r₃ := lt_of_lt_of_le (by decide) hr₃
  have hraw₁ : ∀ n ∈ dirichletIndices (Y ^ alpha),
      ‖g₁ (r₁ * n)‖ ≤ B₁ * (divisorCoefficient 2 n : ℝ) ^ 20 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnR : 0 < (n : ℝ) := lt_trans hM (by rw [hMpow]; exact hmem.2)
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hshift := groupedDyadicFactor_shifted_divisorEnvelope
      (z := z) hXsrc fs₁ hlen₁ hweight₁ c hc hr₁pos hn0
    have hsource :
        ‖g₁ (r₁ * n)‖ ≤
          (2 : ℝ) ^ 10 * Real.log (8 * X) *
            (divisorCoefficient 2 r₁ : ℝ) ^ 20 *
              (divisorCoefficient 2 n : ℝ) ^ 20 := by
      change ‖toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
        (r₁ * n)‖ ≤ _
      rw [toComplexArithmeticFunction_apply
        (groupedDyadicFactor z c fs₁) ⟨r₁ * n, Nat.mul_pos hr₁pos hn0⟩]
      exact hshift
    calc
      ‖g₁ (r₁ * n)‖ ≤
        ((2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r₁ : ℝ) ^ 20) *
            (divisorCoefficient 2 n : ℝ) ^ 20 := by
          ring_nf at hsource ⊢
          exact hsource
      _ ≤ B₁ * (divisorCoefficient 2 n : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hB₁scale (by positivity)
  have hraw₂ : ∀ n ∈ dirichletIndices (Y ^ beta),
      ‖g₂ (r₂ * n)‖ ≤ B₂ * (divisorCoefficient 2 n : ℝ) ^ 20 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hYpos : 0 < Y := by linarith [hX]
    have hMβ : 0 < Y ^ beta := Real.rpow_pos_of_pos hYpos beta
    have hnR : 0 < (n : ℝ) := lt_trans hMβ hmem.2
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hshift := dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
      (z := z) hXsrc fs₂ hlen₂ hweight₂ hr₂pos hn0
    have hsource :
        ‖g₂ (r₂ * n)‖ ≤
          (2 : ℝ) ^ 10 * Real.log (8 * X) *
            (divisorCoefficient 2 r₂ : ℝ) ^ 20 *
              (divisorCoefficient 2 n : ℝ) ^ 20 := by
      change ‖toComplexArithmeticFunction
        (dyadicConvolutionPositiveComplex z fs₂) (r₂ * n)‖ ≤ _
      rw [toComplexArithmeticFunction_apply
        (dyadicConvolutionPositiveComplex z fs₂)
        ⟨r₂ * n, Nat.mul_pos hr₂pos hn0⟩]
      exact hshift
    calc
      ‖g₂ (r₂ * n)‖ ≤
        ((2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r₂ : ℝ) ^ 20) *
            (divisorCoefficient 2 n : ℝ) ^ 20 := by
          ring_nf at hsource ⊢
          exact hsource
      _ ≤ B₂ * (divisorCoefficient 2 n : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hB₂scale (by positivity)
  have hraw₃ : ∀ n ∈ dirichletIndices (Y ^ gamma),
      ‖g₃ (r₃ * n)‖ ≤ B₃ * (divisorCoefficient 2 n : ℝ) ^ 20 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hYpos : 0 < Y := by linarith [hX]
    have hMγ : 0 < Y ^ gamma := Real.rpow_pos_of_pos hYpos gamma
    have hnR : 0 < (n : ℝ) := lt_trans hMγ hmem.2
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hshift := dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
      (z := z) hXsrc fs₃ hlen₃ hweight₃ hr₃pos hn0
    have hsource :
        ‖g₃ (r₃ * n)‖ ≤
          (2 : ℝ) ^ 10 * Real.log (8 * X) *
            (divisorCoefficient 2 r₃ : ℝ) ^ 20 *
              (divisorCoefficient 2 n : ℝ) ^ 20 := by
      change ‖toComplexArithmeticFunction
        (dyadicConvolutionPositiveComplex z fs₃) (r₃ * n)‖ ≤ _
      rw [toComplexArithmeticFunction_apply
        (dyadicConvolutionPositiveComplex z fs₃)
        ⟨r₃ * n, Nat.mul_pos hr₃pos hn0⟩]
      exact hshift
    calc
      ‖g₃ (r₃ * n)‖ ≤
        ((2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r₃ : ℝ) ^ 20) *
            (divisorCoefficient 2 n : ℝ) ^ 20 := by
          ring_nf at hsource ⊢
          exact hsource
      _ ≤ B₃ * (divisorCoefficient 2 n : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hB₃scale (by positivity)
  exact selectedAllocationTrilinearIntegral_bound
    Y eps Tmean alpha beta gamma X a M B₁ B₂ B₃ Tfreq E
    r₁ r₂ r₃ g₁ χ₁ g₂ χ₂ g₃ χ₃ hM hMpow hB₁ hB₁pos hB₂pos hB₃pos
    hX heps0 heps hTmean0 hTmean ha0 hb0 hc0 hsum haLow haHigh hbc
    hδ0 hδ hE hEsub hχ₁ hχ₂ hχ₃ hraw₁ hraw₂ hraw₃ hfreq hblock

#print axioms selectedPositiveDyadicGroup_factorCoefficientBound
#print axioms selectedAllocationTrilinearIntegral_bound
#print axioms selectedDyadicGroupAllocationTrilinearIntegral_bound

end FractionalPrimes.Literature.DirichletMean

end
