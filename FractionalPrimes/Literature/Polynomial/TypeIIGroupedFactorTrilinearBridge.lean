module

public import FractionalPrimes.Literature.Twisted.ShiftedConvolutionSmallFactor
public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearUncapped
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact finite bridge from a selected-group Mellin block to the normalized
Dirichlet polynomial used by ldm:uncapped. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.LargeValues
open FractionalPrimes.Literature.Twisted

/-- The normalized Dirichlet coefficients for a selected group at a gcd
allocation, including the exact source twist n^(iT) and scalar normalization. -/
def selectedGroupTrilinearCoeff
    (B : ℝ) (r : ℕ) (g χ : ℕ → ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  (g (r * n) * χ n * factorTwistMultiplier T n) / (B : ℂ)

private theorem positiveNatCpow_shift_phase
    {n : ℕ} (hn : 0 < n) (t T : ℝ) :
    (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * ((t - T : ℝ) : ℂ)) =
      ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        (factorTwistMultiplier T n *
          Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcpow :
      (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * ((t - T : ℝ) : ℂ)) =
        Complex.exp (((-(1 / 2 : ℂ)) -
          Complex.I * ((t - T : ℝ) : ℂ)) *
            (Real.log (n : ℝ) : ℂ)) := by
    calc
      (n : ℂ) ^ ((-(1 / 2 : ℂ)) -
          Complex.I * ((t - T : ℝ) : ℂ)) =
        (((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℂ)) -
          Complex.I * ((t - T : ℝ) : ℂ))) := by norm_cast
      _ = Complex.exp (((-(1 / 2 : ℂ)) -
            Complex.I * ((t - T : ℝ) : ℂ)) *
              (Real.log (n : ℝ) : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hnR.ne'),
          Complex.ofReal_log hnR.le]
        congr 1
        ring
  have hhalf :
      Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ)) =
        ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
    have hrpow := Real.rpow_def_of_pos hnR (-(1 / 2 : ℝ))
    have hroot : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) =
        1 / Real.sqrt (n : ℝ) := by
      calc
        Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) =
            (Real.rpow (n : ℝ) (1 / 2 : ℝ))⁻¹ :=
          Real.rpow_neg hnR.le (1 / 2 : ℝ)
        _ = (Real.sqrt (n : ℝ))⁻¹ := by
          have hsqrt := Real.sqrt_eq_rpow (n : ℝ)
          rw [hsqrt]
          rfl
        _ = 1 / Real.sqrt (n : ℝ) := by rw [one_div]
    have hreal :
        ((Real.log (n : ℝ) * (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          (-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ) := by
      push_cast
      ring
    calc
      Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ)) =
          (Real.exp (Real.log (n : ℝ) * (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
            rw [Complex.ofReal_exp]
            congr 1
            exact hreal.symm
      _ = ((Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
            congrArg (fun x : ℝ => (x : ℂ)) hrpow.symm
      _ = _ := congrArg (fun x : ℝ => (x : ℂ)) hroot
  calc
    _ = Complex.exp (((-(1 / 2 : ℂ)) -
          Complex.I * ((t - T : ℝ) : ℂ)) *
            (Real.log (n : ℝ) : ℂ)) := hcpow
    _ = Complex.exp ((-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ)) *
          Complex.exp ((-Complex.I * (t : ℂ) +
            Complex.I * (T : ℂ)) * (Real.log (n : ℝ) : ℂ)) := by
      rw [show ((-(1 / 2 : ℂ)) -
            Complex.I * ((t - T : ℝ) : ℂ)) *
              (Real.log (n : ℝ) : ℂ) =
          (-(1 / 2 : ℂ)) * (Real.log (n : ℝ) : ℂ) +
            (-Complex.I * (t : ℂ) + Complex.I * (T : ℂ)) *
              (Real.log (n : ℝ) : ℂ) by push_cast; ring,
        Complex.exp_add]
    _ = ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
          (factorTwistMultiplier T n *
            Complex.exp (-Complex.I * (t : ℂ) *
              (Real.log (n : ℝ) : ℂ))) := by
      rw [hhalf, factorTwistMultiplier]
      rw [show (-Complex.I * (t : ℂ) + Complex.I * (T : ℂ)) *
          (Real.log (n : ℝ) : ℂ) =
          (Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ)) +
            (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) by ring,
        Complex.exp_add]

/-- The exact endpoint match between the natural interval used by the
Dirichlet polynomial and the real half-open extraction interval. -/
theorem dirichletIndices_eq_factorExtractionRealInterval
    {M : ℝ} (hM : 0 ≤ M) :
    dirichletIndices M = factorExtractionRealInterval M (2 * M) := by
  classical
  ext n
  rw [dirichletIndices, Finset.mem_filter, Finset.mem_range,
    mem_factorExtractionRealInterval hM (by positivity)]
  constructor
  · rintro ⟨hnrange, hleft⟩
    have hfloor : (n : ℝ) ≤ Nat.floor (2 * M) := by
      exact_mod_cast (Nat.le_of_lt_succ hnrange)
    exact ⟨hleft, le_trans hfloor (Nat.floor_le (by positivity))⟩
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, hleft⟩
    have hfloor : n ≤ Nat.floor (2 * M) := Nat.le_floor hright
    omega

/-- Exact finite identity converting the selected-group Mellin block at
frequency t-T to the normalized Dirichlet polynomial with coefficient twist
n^(iT). -/
theorem factorPolynomial_eq_selectedGroupMellinBlock
    {M B t T : ℝ} (hM : 0 < M) (hB : 0 < B)
    (r : ℕ) (g χ : ℕ → ℂ) :
    factorPolynomial M (selectedGroupTrilinearCoeff B r g χ T) t =
      (∑ n ∈ factorExtractionRealInterval M (2 * M),
        g (r * n) * factorExtractionMellinWeight χ (t - T) n) /
          (B : ℂ) := by
  classical
  have hindices := dirichletIndices_eq_factorExtractionRealInterval hM.le
  rw [factorPolynomial, LargeValues.dirichletPolynomial, hindices]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [LargeValues.dirichletTerm,
    LargeValues.normalizedDirichletCoeff,
    selectedGroupTrilinearCoeff]
  have hnreal : 0 < (n : ℝ) := by
    have hmem := (mem_factorExtractionRealInterval hM.le (by positivity) n).mp hn
    exact lt_trans hM hmem.1
  have hnpos : 0 < n := by exact_mod_cast hnreal
  rw [factorExtractionMellinWeight, dif_pos hnpos]
  simp only [factorTwistMultiplier]
  have hphase := positiveNatCpow_shift_phase hnpos t T
  rw [hphase]
  have hroot : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hnreal))
  field_simp [Complex.ofReal_ne_zero.mpr hB.ne']
  simp [factorTwistMultiplier, hroot]

/-- A pointwise selected-group saving transfers to the exact hsmall
hypothesis of ldm:uncapped, with no loss when the source normalization
constant satisfies B≥1. -/
theorem selectedGroupSmallFactor_of_MellinBlock
    {M B δ t T : ℝ} (hM : 0 < M) (hB : 1 ≤ B)
    (r : ℕ) (g χ : ℕ → ℂ)
    (hblock : ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
        g (r * n) * factorExtractionMellinWeight χ (t - T) n‖ ≤
          δ * Real.sqrt M) :
    ‖factorPolynomial M (selectedGroupTrilinearCoeff B r g χ T) t‖ ≤
      δ * Real.sqrt M := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  rw [factorPolynomial_eq_selectedGroupMellinBlock hM hBpos]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hBpos]
  have hδsqrt : 0 ≤ δ * Real.sqrt M := by
    have := norm_nonneg (∑ n ∈ factorExtractionRealInterval M (2 * M),
      g (r * n) * factorExtractionMellinWeight χ (t - T) n)
    linarith [hblock]
  calc
    ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
        g (r * n) * factorExtractionMellinWeight χ (t - T) n‖ / B ≤
      (δ * Real.sqrt M) / B := div_le_div_of_nonneg_right hblock (le_of_lt hBpos)
    _ ≤ δ * Real.sqrt M := div_le_self hδsqrt hB

/-- A divisor-envelope bound for the unnormalized selected coefficients
implies the exact `C=20` coefficient hypothesis after division by the
source normalization `B`. -/
theorem selectedGroupTrilinearCoeff_factorCoefficientBound
    {M B T : ℝ} (hB : 0 < B) (r : ℕ) (g χ : ℕ → ℂ)
    (hχ : ∀ n, ‖χ n‖ ≤ 1)
    (hraw : ∀ n ∈ dirichletIndices M,
      ‖g (r * n)‖ ≤ B *
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ 20) :
    factorCoefficientBound 20 M
      (selectedGroupTrilinearCoeff B r g χ T) := by
  intro n hn
  have hnum : ‖g (r * n)‖ * ‖χ n‖ ≤ B *
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ 20 := by
    calc
      ‖g (r * n)‖ * ‖χ n‖ ≤ ‖g (r * n)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hχ n) (norm_nonneg _)
      _ = ‖g (r * n)‖ := by ring
      _ ≤ B *
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ 20 :=
        hraw n hn
  have hnorm :
      ‖selectedGroupTrilinearCoeff B r g χ T n‖ =
        (‖g (r * n)‖ * ‖χ n‖) / B := by
    rw [selectedGroupTrilinearCoeff, norm_div, norm_mul, norm_mul,
      factorTwistMultiplier_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hB]
  rw [hnorm]
  calc
    (‖g (r * n)‖ * ‖χ n‖) / B ≤
        (B *
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ 20) / B :=
      div_le_div_of_nonneg_right hnum hB.le
    _ = (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ 20 := by
      field_simp

/-- The literal frequency-window form used in the restricted-twist proof.
The interval estimates are supplied at exactly the source range
`log(X)^(45a) ≤ |s| ≤ X^(a+1)`, and the saved logarithmic power remains
`log(X)^(-20a)`. -/
theorem selectedGroupSmallFactor_of_frequencyWindow
    {M B X a T : ℝ} (hM : 0 < M) (hB : 1 ≤ B)
    (r : ℕ) (g χ : ℕ → ℂ) (E : Set ℝ)
    (hfreq : ∀ t ∈ E,
      (Real.log X) ^ (45 * a) ≤ |T - t| ∧
        |T - t| ≤ X ^ (a + 1))
    (hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
          g (r * n) * factorExtractionMellinWeight χ s n‖ ≤
            (Real.log X) ^ (-20 * a) * Real.sqrt M) :
    ∀ t ∈ E,
      ‖factorPolynomial M (selectedGroupTrilinearCoeff B r g χ T) t‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt M := by
  intro t ht
  have hlo : (Real.log X) ^ (45 * a) ≤ |t - T| := by
    simpa [abs_sub_comm] using (hfreq t ht).1
  have hhi : |t - T| ≤ X ^ (a + 1) := by
    simpa [abs_sub_comm] using (hfreq t ht).2
  exact selectedGroupSmallFactor_of_MellinBlock
    (M := M) (B := B) (δ := (Real.log X) ^ (-20 * a))
    (t := t) (T := T) hM hB r g χ (hblock (t - T) hlo hhi)

/-- The exact `ldm:uncapped` trilinear conclusion after inserting the
selected-group Mellin block as the distinguished polynomial. This is the
finite coefficient/phase assembly step in `ltw:ptw-of-muf`; the source
frequency window is retained in `hfreq`, and the saving is exactly
`log(X)^(-20a)`. -/
theorem trilinearUncapped_of_selectedGroupMellinBlock
    (Y eps Tmean alpha beta gamma X a M B Tfreq : ℝ) (E : Set ℝ)
    (r : ℕ) (g χ : ℕ → ℂ) (coeff₂ coeff₃ : ℕ → ℂ)
    (hM : 0 < M) (hMpow : M = Y ^ alpha) (hB : 1 ≤ B)
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
    (hcoeff₁ : factorCoefficientBound 20 (Y ^ alpha)
      (selectedGroupTrilinearCoeff B r g χ Tfreq))
    (hcoeff₂ : factorCoefficientBound 20 (Y ^ beta) coeff₂)
    (hcoeff₃ : factorCoefficientBound 20 (Y ^ gamma) coeff₃)
    (hfreq : ∀ t ∈ E,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval M (2 * M),
        g (r * n) * factorExtractionMellinWeight χ s n‖ ≤
          (Real.log X) ^ (-20 * a) * Real.sqrt M) :
    (∫ t in E,
      ‖factorPolynomial (Y ^ alpha)
          (selectedGroupTrilinearCoeff B r g χ Tfreq) t *
        factorPolynomial (Y ^ beta) coeff₂ t *
        factorPolynomial (Y ^ gamma) coeff₃ t‖) ≤
      J 20 * Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) * Real.sqrt Y *
        (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
          Y ^ (-eps / 16 : ℝ)) := by
  have hsmallM : ∀ t ∈ E,
      ‖factorPolynomial M (selectedGroupTrilinearCoeff B r g χ Tfreq) t‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt M := by
    intro t ht
    have hlo : (Real.log X) ^ (45 * a) ≤ |t - Tfreq| := by
      simpa [abs_sub_comm] using (hfreq t ht).1
    have hhi : |t - Tfreq| ≤ X ^ (a + 1) := by
      simpa [abs_sub_comm] using (hfreq t ht).2
    exact selectedGroupSmallFactor_of_MellinBlock hM hB r g χ
      (hblock (t - Tfreq) hlo hhi)
  have hsmall : ∀ t ∈ E,
      ‖factorPolynomial (Y ^ alpha)
          (selectedGroupTrilinearCoeff B r g χ Tfreq) t‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (Y ^ alpha) := by
    intro t ht
    simpa [hMpow] using hsmallM t ht
  exact trilinearUncapped 20 Y eps Tmean alpha beta gamma
    ((Real.log X) ^ (-20 * a)) E
    (selectedGroupTrilinearCoeff B r g χ Tfreq) coeff₂ coeff₃
    hX heps0 heps hTmean0 hTmean ha0 hb0 hc0 hsum haLow haHigh hbc
    hδ0 hδ hE hEsub hcoeff₁ hcoeff₂ hcoeff₃ hsmall

#print axioms dirichletIndices_eq_factorExtractionRealInterval
#print axioms factorPolynomial_eq_selectedGroupMellinBlock
#print axioms selectedGroupSmallFactor_of_MellinBlock
#print axioms selectedGroupTrilinearCoeff_factorCoefficientBound
#print axioms selectedGroupSmallFactor_of_frequencyWindow
#print axioms trilinearUncapped_of_selectedGroupMellinBlock

end FractionalPrimes.Literature.DirichletMean

end

