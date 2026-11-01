module

public import FractionalPrimes.Literature.Twisted.FullFrequencyMellinData
public import FractionalPrimes.Literature.Polynomial.SmoothedMellinIdentity
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The exact sharp logarithmic window for `(X,X+H]`. -/
noncomputable def fullFrequencySharpLogWindow
    (d : FullFrequencyMellinData) (u : ℝ) : ℝ :=
  Real.exp (u / 2) / d.H *
    if Real.log d.X < u ∧ u ≤ Real.log (d.X + d.H) then 1 else 0

/-- The Mellin kernel from `lup:window-data`. -/
noncomputable def fullFrequencyMellinKernel
    (d : FullFrequencyMellinData) (t : ℝ) : ℂ :=
  (Polynomial.mellinHalfItPower (d.X + d.H) t -
      Polynomial.mellinHalfItPower d.X t) /
    ((d.H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))

/-- The finite smoothed sum using the approved fixed density. -/
noncomputable def fullFrequencySmoothedSum
    (d : FullFrequencyMellinData) (T : ℝ) : ℂ :=
  ∑ n ∈ fullFrequencySupportIndices d.X,
    d.a n * (↑(Polynomial.mellinRealHalfPower n) : ℂ) *
      ↑(Polynomial.mellinRealConvolution
        (fullFrequencySharpLogWindow d)
        (FractionalPrimes.polynomialKernelRhoT T)
        (Real.log (n : ℝ)))

/-- The finite Mellin inversion identity for the full selected support.
Only positivity of the support indices is used; no pointwise bound on the
coefficients is imposed. -/
theorem fullFrequencySmoothedSum_formula
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T) :
    fullFrequencySmoothedSum d T = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t in Set.Icc (-T) T,
        fullFrequencyMellinPolynomial d t *
          fullFrequencyMellinKernel d t *
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) := by
  classical
  let S := fullFrequencySupportIndices d.X
  let h := fullFrequencySharpLogWindow d
  let K := fullFrequencyMellinKernel d
  let f : ℕ → ℝ → ℂ := fun n t =>
    (d.a n * Polynomial.mellinDirichletMonomial n t) * K t *
      FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)
  have hFcont : Continuous FractionalPrimes.polynomialKernelRhoAngularFourier := by
    have hFourierEval : Continuous (fun t : ℝ =>
        𝓕 Polynomial.polynomialKernelRhoComplexSchwartz
          (t / (2 * Real.pi))) := by
      fun_prop
    apply hFourierEval.congr
    intro t
    exact (Polynomial.polynomialKernelRhoAngularFourier_eq_fourier t).symm
  have hKnum : Continuous (fun t : ℝ =>
      Polynomial.mellinHalfItPower (d.X + d.H) t -
        Polynomial.mellinHalfItPower d.X t) := by
    unfold Polynomial.mellinHalfItPower
    fun_prop
  have hKden : Continuous (fun t : ℝ =>
      (d.H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hKden_ne (t : ℝ) :
      (d.H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast d.H_pos.ne'
    · exact Polynomial.mellinWindowDenominator_ne_zero t
  have hKcont : Continuous K := by
    dsimp [K, fullFrequencyMellinKernel]
    exact hKnum.div₀ hKden hKden_ne
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := by
    have hleft : 0 ≤ d.X / (2 : ℝ) ^ 21 := by
      exact div_nonneg (by linarith [d.X_lower]) (by positivity)
    have hmem := (Polynomial.mellinIntervalIndices_mem_iff hleft n).1 hn
    have hpos : 0 < (n : ℝ) := lt_of_le_of_lt hleft hmem.1
    exact_mod_cast hpos
  have hmonomial (n : ℕ) (t : ℝ) :
      (Polynomial.mellinRealHalfPower n : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) =
      Polynomial.mellinDirichletMonomial n t := by
    unfold Polynomial.mellinRealHalfPower Polynomial.mellinDirichletMonomial
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hDircont (n : ℕ) : Continuous (Polynomial.mellinDirichletMonomial n) := by
    unfold Polynomial.mellinDirichletMonomial
    fun_prop
  have hScalecont : Continuous (fun t : ℝ =>
      FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)) := by
    exact hFcont.comp (by fun_prop)
  have hfcont (n : ℕ) : Continuous (f n) := by
    dsimp [f]
    have hc : Continuous (fun t : ℝ =>
        (d.a n) * (Polynomial.mellinDirichletMonomial n t *
          (K t * FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)))) :=
      continuous_const.mul ((hDircont n).mul (hKcont.mul hScalecont))
    convert hc using 1
    ext t
    ring
  have hfint (n : ℕ) : IntegrableOn (f n) (Set.Icc (-T) T) :=
    (hfcont n).continuousOn.integrableOn_compact isCompact_Icc
  have hterm (n : ℕ) (hn : n ∈ S) :
      d.a n * (Polynomial.mellinRealHalfPower n : ℂ) *
          (Polynomial.mellinRealConvolution h
            (FractionalPrimes.polynomialKernelRhoT T)
            (Real.log (n : ℝ)) : ℂ) =
        ((2 * Real.pi)⁻¹ : ℂ) * ∫ t in Set.Icc (-T) T, f n t := by
    have hFour := Polynomial.mellinRealConvolution_fourier d.X d.H T n
      (by linarith [d.X_lower]) d.H_pos hT (hSpos n hn)
    calc
      _ = d.a n * (Polynomial.mellinRealHalfPower n : ℂ) *
          (((2 * Real.pi)⁻¹ : ℂ) *
            ∫ t in Set.Icc (-T) T,
              FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) *
                K t) := by
          convert congrArg
            (fun z : ℂ => d.a n * (Polynomial.mellinRealHalfPower n : ℂ) * z)
            hFour using 1
          all_goals simp [h, K, fullFrequencySharpLogWindow,
            fullFrequencyMellinKernel]
          left
          congr 1
          funext u
          by_cases hu : Real.log d.X < u ∧ u ≤ Real.log (d.X + d.H)
          · simp [fullFrequencySharpLogWindow, hu]
          · simp [fullFrequencySharpLogWindow, hu]
      _ = ((2 * Real.pi)⁻¹ : ℂ) *
          ((d.a n * (Polynomial.mellinRealHalfPower n : ℂ)) *
            ∫ t in Set.Icc (-T) T,
              FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) *
                K t) := by ring
      _ = ((2 * Real.pi)⁻¹ : ℂ) *
          ∫ t in Set.Icc (-T) T,
            (d.a n * (Polynomial.mellinRealHalfPower n : ℂ)) *
              (FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) * K t) := by
          congr 1
          rw [← integral_const_mul]
      _ = ((2 * Real.pi)⁻¹ : ℂ) * ∫ t in Set.Icc (-T) T, f n t := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          calc
            _ = (d.a n * ((Polynomial.mellinRealHalfPower n : ℂ) *
                Complex.exp (-Complex.I * (t : ℂ) *
                  (Real.log (n : ℝ) : ℂ)))) * K t *
                  FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) := by ring
            _ = f n t := by rw [hmonomial n t]
  have hsumTerms :
      (∑ n ∈ S, d.a n * (Polynomial.mellinRealHalfPower n : ℂ) *
          (Polynomial.mellinRealConvolution h
            (FractionalPrimes.polynomialKernelRhoT T)
            (Real.log (n : ℝ)) : ℂ)) =
        ((2 * Real.pi)⁻¹ : ℂ) * ∑ n ∈ S, ∫ t in Set.Icc (-T) T, f n t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n hn
  have hsumIntegral :
      (∑ n ∈ S, ∫ t in Set.Icc (-T) T, f n t) =
        ∫ t in Set.Icc (-T) T, ∑ n ∈ S, f n t := by
    rw [integral_finsetSum]
    intro n hn
    exact hfint n
  change (∑ n ∈ S, d.a n * (Polynomial.mellinRealHalfPower n : ℂ) *
      (Polynomial.mellinRealConvolution h
        (FractionalPrimes.polynomialKernelRhoT T)
        (Real.log (n : ℝ)) : ℂ)) = _
  rw [hsumTerms, hsumIntegral]
  rw [Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [f, S]
  simp [fullFrequencyMellinPolynomial, fullFrequencyMellinKernel, K,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The local mass hypothesis controls the symmetric difference of two
half-open integer windows by the lengths of their two endpoint bands. -/
theorem fullFrequencyIntervalDifferenceMass_le
    (d : FullFrequencyMellinData) {x y x' y' : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y') :
    (∑ n ∈ Polynomial.mellinIntervalDifferenceIndices x y x' y', ‖d.a n‖) ≤
      d.K * (|x - x'| + |y - y'| + 2 * d.h0) := by
  classical
  let A := Polynomial.mellinEndpointBandIndices x x'
  let B := Polynomial.mellinEndpointBandIndices y y'
  let D := Polynomial.mellinIntervalDifferenceIndices x y x' y'
  have hD : D ⊆ A ∪ B :=
    Polynomial.mellinIntervalDifference_subset_endpointBands hx hx' hy hy'
  have hband (u v : ℝ) :
      (∑ n ∈ Polynomial.mellinEndpointBandIndices u v, ‖d.a n‖) ≤
        d.K * (|u - v| + d.h0) := by
    have hlen : 0 ≤ max u v - min u v := sub_nonneg.mpr (min_le_max : min u v ≤ max u v)
    have hmass := d.local_mass (min u v) (max u v - min u v) hlen
    have hendpoint : min u v + (max u v - min u v) = max u v := by ring
    rw [hendpoint] at hmass
    have hwidth : max u v - min u v = |u - v| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    simpa [Polynomial.mellinEndpointBandIndices, hwidth] using hmass
  have hDle : (∑ n ∈ D, ‖d.a n‖) ≤ ∑ n ∈ A ∪ B, ‖d.a n‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg hD (by
      intro n hn hnD
      exact norm_nonneg _)
  have hUnion : (∑ n ∈ A ∪ B, ‖d.a n‖) ≤
      (∑ n ∈ A, ‖d.a n‖) + (∑ n ∈ B, ‖d.a n‖) := by
    have hdisj : Disjoint A (B \ A) := by
      apply Finset.disjoint_left.mpr
      intro n hnA hnBA
      exact (Finset.mem_sdiff.mp hnBA).2 hnA
    have hset : A ∪ B = A ∪ (B \ A) := by ext n; simp
    rw [hset, Finset.sum_union hdisj]
    exact add_le_add_right
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by
        intro n hn hnB
        exact norm_nonneg _)) _
  calc
    (∑ n ∈ D, ‖d.a n‖) ≤ ∑ n ∈ A ∪ B, ‖d.a n‖ := hDle
    _ ≤ (∑ n ∈ A, ‖d.a n‖) + (∑ n ∈ B, ‖d.a n‖) := hUnion
    _ ≤ d.K * (|x - x'| + d.h0) + d.K * (|y - y'| + d.h0) :=
      add_le_add (hband x x') (hband y y')
    _ = d.K * (|x - x'| + |y - y'| + 2 * d.h0) := by ring

/-- For a logarithmic displacement of size at most one, the two shifted
endpoint bands have the exact `9 X |v|` length allowance in the source. -/
theorem fullFrequencyShiftedWindowMass_le_small
    (d : FullFrequencyMellinData) {v : ℝ} (hv : |v| ≤ 1) :
    (∑ n ∈ Polynomial.mellinIntervalDifferenceIndices
      d.X (d.X + d.H) (d.X * Real.exp v)
      ((d.X + d.H) * Real.exp v), ‖d.a n‖) ≤
      d.K * (9 * d.X * |v| + 2 * d.h0) := by
  have hX0 : 0 ≤ d.X := by linarith [d.X_lower]
  have hY0 : 0 ≤ d.X + d.H := by linarith [d.H_pos]
  have hE0 : 0 ≤ Real.exp v := (Real.exp_pos v).le
  have hmass := fullFrequencyIntervalDifferenceMass_le d
    hX0 hY0 (mul_nonneg hX0 hE0) (mul_nonneg hY0 hE0)
  have hExp : |Real.exp v - 1| ≤ 2 * |v| := Real.abs_exp_sub_one_le hv
  have hmoveX : |d.X - d.X * Real.exp v| = d.X * |Real.exp v - 1| := by
    calc
      |d.X - d.X * Real.exp v| = |d.X * (1 - Real.exp v)| := by ring
      _ = d.X * |Real.exp v - 1| := by
        rw [abs_mul, abs_of_nonneg hX0, abs_sub_comm]
  have hmoveY : |d.X + d.H - (d.X + d.H) * Real.exp v| =
      (d.X + d.H) * |Real.exp v - 1| := by
    calc
      |d.X + d.H - (d.X + d.H) * Real.exp v| =
          |(d.X + d.H) * (1 - Real.exp v)| := by ring
      _ = (d.X + d.H) * |Real.exp v - 1| := by
        rw [abs_mul, abs_of_nonneg hY0, abs_sub_comm]
  have hdisp :
      |d.X - d.X * Real.exp v| +
        |d.X + d.H - (d.X + d.H) * Real.exp v| ≤
          9 * d.X * |v| := by
    rw [hmoveX, hmoveY]
    have hXexp := mul_le_mul_of_nonneg_left hExp hX0
    have hYexp := mul_le_mul_of_nonneg_left hExp hY0
    have hv0 : 0 ≤ |v| := abs_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr d.H_upper) hv0]
  calc
    (∑ n ∈ Polynomial.mellinIntervalDifferenceIndices
      d.X (d.X + d.H) (d.X * Real.exp v)
      ((d.X + d.H) * Real.exp v), ‖d.a n‖) ≤
        d.K * (|d.X - d.X * Real.exp v| +
          |d.X + d.H - (d.X + d.H) * Real.exp v| + 2 * d.h0) := hmass
    _ ≤ d.K * (9 * d.X * |v| + 2 * d.h0) := by
      apply mul_le_mul_of_nonneg_left _ d.K_nonneg
      linarith [hdisp]

/-- The approved local mass bound on the entire selected coefficient
support, used for the large logarithmic shifts. -/
theorem fullFrequencySupportMass_le
    (d : FullFrequencyMellinData) :
    (∑ n ∈ fullFrequencySupportIndices d.X, ‖d.a n‖) ≤
      ((2 : ℝ) ^ 22 + 1) * d.K * d.X := by
  let lo : ℝ := d.X / (2 : ℝ) ^ 21
  let hi : ℝ := (2 : ℝ) ^ 22 * d.X
  have hX0 : 0 ≤ d.X := by linarith [d.X_lower]
  have hlo : 0 ≤ lo := by dsimp [lo]; positivity
  have hlen : 0 ≤ hi - lo := by
    dsimp [hi, lo]
    nlinarith
  have hmass := d.local_mass lo (hi - lo) hlen
  have hendpoint : lo + (hi - lo) = hi := by ring
  rw [hendpoint] at hmass
  have hwidth : hi - lo + d.h0 ≤ ((2 : ℝ) ^ 22 + 1) * d.X := by
    dsimp [hi, lo]
    have := d.h0_upper
    nlinarith
  calc
    (∑ n ∈ fullFrequencySupportIndices d.X, ‖d.a n‖) ≤
        d.K * (hi - lo + d.h0) := by simpa [fullFrequencySupportIndices, lo, hi] using hmass
    _ ≤ d.K * (((2 : ℝ) ^ 22 + 1) * d.X) :=
      mul_le_mul_of_nonneg_left hwidth d.K_nonneg
    _ = ((2 : ℝ) ^ 22 + 1) * d.K * d.X := by ring

/-- Even for a large logarithmic shift, a coefficient in the approved
support can enter the shifted window only with weight at most `2^11`. -/
theorem fullFrequencyShiftedWindowWeight_le
    (d : FullFrequencyMellinData) (n : ℕ)
    (hn : n ∈ fullFrequencySupportIndices d.X) (v : ℝ) :
    0 ≤ Real.exp (-v / 2) *
        Polynomial.mellinIntervalIndicator
          (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n ∧
      Real.exp (-v / 2) *
        Polynomial.mellinIntervalIndicator
          (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n ≤
        (2 : ℝ) ^ 11 := by
  let c : ℝ := Real.exp (-v / 2)
  let A : ℝ := Polynomial.mellinIntervalIndicator
    (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n
  have hc : 0 < c := by dsimp [c]; exact Real.exp_pos _
  have hA01 : A = 0 ∨ A = 1 := by
    by_cases hwin : d.X * Real.exp v < (n : ℝ) ∧
        (n : ℝ) ≤ (d.X + d.H) * Real.exp v
    · right
      simp [A, Polynomial.mellinIntervalIndicator, hwin]
    · left
      simp [A, Polynomial.mellinIntervalIndicator, hwin]
  have hleft : 0 ≤ d.X / (2 : ℝ) ^ 21 := by
    exact div_nonneg (by linarith [d.X_lower]) (by positivity)
  have hmem := (Polynomial.mellinIntervalIndices_mem_iff hleft n).1 hn
  have hnreal : d.X / (2 : ℝ) ^ 21 < (n : ℝ) := hmem.1
  have hXH : d.X + d.H ≤ 2 * d.X := by linarith [d.H_upper]
  constructor
  · rcases hA01 with hA | hA
    · change 0 ≤ c * A
      rw [hA]
      positivity
    · change 0 ≤ c * A
      rw [hA]
      positivity
  · rcases hA01 with hA | hA
    · change c * A ≤ (2 : ℝ) ^ 11
      rw [hA]
      norm_num
    · change c * A ≤ (2 : ℝ) ^ 11
      rw [hA]
      have hwin : d.X * Real.exp v < (n : ℝ) ∧
          (n : ℝ) ≤ (d.X + d.H) * Real.exp v := by
        by_contra hnot
        have hzero : A = 0 := by
          simp [A, Polynomial.mellinIntervalIndicator, hnot]
        simp [hzero] at hA
      have hcSq : c ^ 2 = Real.exp (-v) := by
        dsimp [c]
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hexpcancel : Real.exp v * Real.exp (-v) = 1 := by
        rw [← Real.exp_add]
        simp
      have hupper : (n : ℝ) * Real.exp (-v) ≤ d.X + d.H := by
        have hmul := mul_le_mul_of_nonneg_right hwin.2
          (le_of_lt (Real.exp_pos (-v)))
        calc
          (n : ℝ) * Real.exp (-v) ≤
              ((d.X + d.H) * Real.exp v) * Real.exp (-v) := hmul
          _ = d.X + d.H := by rw [mul_assoc, hexpcancel, mul_one]
      have hnpos : 0 < (n : ℝ) := by linarith [d.X_lower, hnreal]
      have hcSqLe : c ^ 2 ≤ (d.X + d.H) / (n : ℝ) := by
        apply (le_div_iff₀ hnpos).2
        rw [hcSq]
        nlinarith [hupper]
      have hratio : (d.X + d.H) / (n : ℝ) < (2 : ℝ) ^ 22 := by
        apply (div_lt_iff₀ hnpos).2
        nlinarith [hnreal, hXH]
      have hcSqLt : c ^ 2 < (2 : ℝ) ^ 22 := lt_of_le_of_lt hcSqLe hratio
      have hcLe : c ≤ (2 : ℝ) ^ 11 := by
        norm_num at hcSqLt ⊢
        nlinarith [sq_nonneg (c - 2048)]
      simpa using hcLe

/-- The coefficient sum in a logarithmically shifted sharp window. -/
noncomputable def fullFrequencyShiftedWindowSum
    (d : FullFrequencyMellinData) (v : ℝ) : ℂ :=
  ∑ n ∈ fullFrequencySupportIndices d.X,
    d.a n * (↑(Real.exp (-v / 2) *
      Polynomial.mellinIntervalIndicator
        (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) : ℂ)

/-- Uniform large-shift bound before integrating the smoothing kernel. -/
theorem fullFrequencyShiftedWindowSum_norm_le
    (d : FullFrequencyMellinData) (v : ℝ) :
    ‖fullFrequencyShiftedWindowSum d v‖ ≤
      (2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1) * d.K * d.X := by
  classical
  let S := fullFrequencySupportIndices d.X
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖d.a n * (↑(Real.exp (-v / 2) *
        Polynomial.mellinIntervalIndicator
          (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) : ℂ)‖ ≤
        (2 : ℝ) ^ 11 * ‖d.a n‖ := by
    obtain ⟨hweight0, hweight⟩ :=
      fullFrequencyShiftedWindowWeight_le d n hn v
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hweight0]
    nlinarith [mul_le_mul_of_nonneg_left hweight (norm_nonneg (d.a n))]
  calc
    ‖fullFrequencyShiftedWindowSum d v‖ ≤
        ∑ n ∈ S, ‖d.a n * (↑(Real.exp (-v / 2) *
          Polynomial.mellinIntervalIndicator
            (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) : ℂ)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (2 : ℝ) ^ 11 * ‖d.a n‖ :=
      Finset.sum_le_sum fun n hn => hterm n hn
    _ = (2 : ℝ) ^ 11 * ∑ n ∈ S, ‖d.a n‖ := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ 11 * (((2 : ℝ) ^ 22 + 1) * d.K * d.X) := by
      exact mul_le_mul_of_nonneg_left (fullFrequencySupportMass_le d)
        (by positivity)
    _ = (2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1) * d.K * d.X := by ring

/-- The weighted indicator difference is exactly supported on the finite
symmetric difference of the two half-open windows. -/
theorem fullFrequencyIndicatorDifferenceMass_le
    (d : FullFrequencyMellinData) {x y x' y' : ℝ}
    (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    (∑ n ∈ fullFrequencySupportIndices d.X,
      ‖d.a n‖ * |Polynomial.mellinIntervalIndicator x y n -
        Polynomial.mellinIntervalIndicator x' y' n|) ≤
      ∑ n ∈ Polynomial.mellinIntervalDifferenceIndices x y x' y', ‖d.a n‖ := by
  classical
  let S := fullFrequencySupportIndices d.X
  let D := Polynomial.mellinIntervalDifferenceIndices x y x' y'
  have hpoint (n : ℕ) :
      ‖d.a n‖ * |Polynomial.mellinIntervalIndicator x y n -
        Polynomial.mellinIntervalIndicator x' y' n| =
        if n ∈ D then ‖d.a n‖ else 0 := by
    rw [Polynomial.mellinIntervalIndicator_abs_sub_eq]
    by_cases hn : n ∈ D
    · have htrue : Polynomial.mellinIntervalsDiffer x y x' y' n = true :=
        (Polynomial.mellinIntervalsDiffer_eq_true_iff_mem_difference hx hx' n).2 hn
      simp [hn, htrue]
    · have hfalse : Polynomial.mellinIntervalsDiffer x y x' y' n ≠ true := by
        intro hh
        exact hn ((Polynomial.mellinIntervalsDiffer_eq_true_iff_mem_difference hx hx' n).1 hh)
      simp [hn, hfalse]
  calc
    (∑ n ∈ S,
      ‖d.a n‖ * |Polynomial.mellinIntervalIndicator x y n -
        Polynomial.mellinIntervalIndicator x' y' n|) =
        ∑ n ∈ S.filter (· ∈ D), ‖d.a n‖ := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun n hn => hpoint n
    _ ≤ ∑ n ∈ D, ‖d.a n‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
      · intro n hn hnD
        exact norm_nonneg _

/-- Scalar comparison for the shifted indicator and its exponential
normalization. This is the pointwise algebra behind the small-shift error. -/
theorem fullFrequencyShiftedIndicator_scalar_le
    {v A D : ℝ} (hv : |v| ≤ 1) (hD : 0 ≤ D) :
    |Real.exp (-v / 2) * A - D| ≤
      3 * |A - D| + |v| * D := by
  let c : ℝ := Real.exp (-v / 2)
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hiden : c * A - D = c * (A - D) + (c - 1) * D := by ring
  have hscalar : |c * A - D| ≤ c * |A - D| + |c - 1| * D := by
    rw [hiden]
    calc
      |c * (A - D) + (c - 1) * D| ≤
          |c * (A - D)| + |(c - 1) * D| := abs_add_le _ _
      _ = c * |A - D| + |c - 1| * D := by
        rw [abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg hD]
  have hc3 : c ≤ 3 := Polynomial.mellinShiftPrefactor_le_three hv
  have hcm1 : |c - 1| ≤ |v| := Polynomial.mellinShiftPrefactor_sub_one_abs_le hv
  calc
    |Real.exp (-v / 2) * A - D| ≤
        c * |A - D| + |c - 1| * D := hscalar
    _ ≤ 3 * |A - D| + |v| * D :=
      add_le_add
        (mul_le_mul_of_nonneg_right hc3 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hcm1 hD)

/-- The finite shifted sharp-window sum obeys the source's `2^36`
small-shift allowance before convolution with the fixed density. -/
theorem fullFrequencyShiftedWindowSum_difference_le_small
    (d : FullFrequencyMellinData) {v : ℝ} (hv : |v| ≤ 1) :
    ‖fullFrequencyShiftedWindowSum d v - fullFrequencyShiftedWindowSum d 0‖ ≤
      (2 : ℝ) ^ 36 * d.K * (d.X * |v| + d.h0) := by
  classical
  let S := fullFrequencySupportIndices d.X
  let A : ℕ → ℝ := fun n => Polynomial.mellinIntervalIndicator
    (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n
  let D : ℕ → ℝ := fun n =>
    Polynomial.mellinIntervalIndicator d.X (d.X + d.H) n
  let c : ℝ := Real.exp (-v / 2)
  have hD01 (n : ℕ) : D n = 0 ∨ D n = 1 := by
    by_cases hn : d.X < (n : ℝ) ∧ (n : ℝ) ≤ d.X + d.H
    · right
      simp [D, Polynomial.mellinIntervalIndicator, hn]
    · left
      simp [D, Polynomial.mellinIntervalIndicator, hn]
  have hD0 (n : ℕ) : 0 ≤ D n := by
    rcases hD01 n with h | h <;> simp [h]
  have hsumRep :
      fullFrequencyShiftedWindowSum d v - fullFrequencyShiftedWindowSum d 0 =
        ∑ n ∈ S, d.a n * (↑(c * A n - D n) : ℂ) := by
    simp only [fullFrequencyShiftedWindowSum, Real.exp_zero, zero_div,
      neg_zero, mul_one, one_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [A, D, c]
    push_cast
    ring
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖d.a n * (↑(c * A n - D n) : ℂ)‖ ≤
        ‖d.a n‖ * (3 * |A n - D n| + |v| * D n) := by
    have hscalar := fullFrequencyShiftedIndicator_scalar_le
      (A := A n) (D := D n) hv (hD0 n)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hscalar (norm_nonneg _)
  have hX0 : 0 ≤ d.X := by linarith [d.X_lower]
  have hshift0 : 0 ≤ d.X * Real.exp v := by positivity
  have hshift1 : 0 ≤ (d.X + d.H) * Real.exp v :=
    mul_nonneg (by linarith [d.X_lower, d.H_pos]) (Real.exp_pos v).le
  have hdiffMass :
      (∑ n ∈ S, ‖d.a n‖ * |A n - D n|) ≤
        d.K * (9 * d.X * |v| + 2 * d.h0) := by
    have hfilter := fullFrequencyIndicatorDifferenceMass_le d
      (x := d.X) (y := d.X + d.H)
      (x' := d.X * Real.exp v)
      (y' := (d.X + d.H) * Real.exp v)
      hX0 hshift0
    have hmass := fullFrequencyShiftedWindowMass_le_small d hv
    simpa [S, A, D, abs_sub_comm] using hfilter.trans hmass
  have hDmass : (∑ n ∈ S, ‖d.a n‖ * D n) ≤
      ((2 : ℝ) ^ 22 + 1) * d.K * d.X := by
    calc
      (∑ n ∈ S, ‖d.a n‖ * D n) ≤ ∑ n ∈ S, ‖d.a n‖ := by
        apply Finset.sum_le_sum
        intro n hn
        rcases hD01 n with h | h <;> simp [h]
      _ ≤ _ := fullFrequencySupportMass_le d
  have hsumBound :
      (∑ n ∈ S, ‖d.a n‖ * (3 * |A n - D n| + |v| * D n)) =
        3 * (∑ n ∈ S, ‖d.a n‖ * |A n - D n|) +
          |v| * (∑ n ∈ S, ‖d.a n‖ * D n) := by
    calc
      _ = ∑ n ∈ S,
          (3 * (‖d.a n‖ * |A n - D n|) +
            |v| * (‖d.a n‖ * D n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hnonneg : 0 ≤ |v| := abs_nonneg _
  have hK0 : 0 ≤ d.K := d.K_nonneg
  have hh0 : 0 ≤ d.h0 := d.h0_pos.le
  calc
    ‖fullFrequencyShiftedWindowSum d v - fullFrequencyShiftedWindowSum d 0‖ =
        ‖∑ n ∈ S, d.a n * (↑(c * A n - D n) : ℂ)‖ := by rw [hsumRep]
    _ ≤ ∑ n ∈ S, ‖d.a n * (↑(c * A n - D n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖d.a n‖ * (3 * |A n - D n| + |v| * D n) :=
      Finset.sum_le_sum fun n hn => hterm n hn
    _ = 3 * (∑ n ∈ S, ‖d.a n‖ * |A n - D n|) +
          |v| * (∑ n ∈ S, ‖d.a n‖ * D n) := hsumBound
    _ ≤ 3 * (d.K * (9 * d.X * |v| + 2 * d.h0)) +
          |v| * (((2 : ℝ) ^ 22 + 1) * d.K * d.X) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdiffMass (by norm_num))
        (mul_le_mul_of_nonneg_left hDmass hnonneg)
    _ ≤ (2 : ℝ) ^ 36 * d.K * (d.X * |v| + d.h0) := by
      nlinarith [mul_nonneg (mul_nonneg hK0 hX0) hnonneg,
        mul_nonneg hK0 hh0]

/-- The same source allowance for shifts larger than one follows from the
uniform full-support bound on each finite shifted window sum. -/
theorem fullFrequencyShiftedWindowSum_difference_le_large
    (d : FullFrequencyMellinData) {v : ℝ} (hv : 1 < |v|) :
    ‖fullFrequencyShiftedWindowSum d v - fullFrequencyShiftedWindowSum d 0‖ ≤
      (2 : ℝ) ^ 36 * d.K * (d.X * |v| + d.h0) := by
  have hKX : 0 ≤ d.K * d.X :=
    mul_nonneg d.K_nonneg (by linarith [d.X_lower])
  have hC : 2 * ((2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1)) ≤ (2 : ℝ) ^ 36 := by
    norm_num
  calc
    ‖fullFrequencyShiftedWindowSum d v - fullFrequencyShiftedWindowSum d 0‖ ≤
        ‖fullFrequencyShiftedWindowSum d v‖ +
          ‖fullFrequencyShiftedWindowSum d 0‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1) * d.K * d.X +
          (2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1) * d.K * d.X :=
      add_le_add (fullFrequencyShiftedWindowSum_norm_le d v)
        (fullFrequencyShiftedWindowSum_norm_le d 0)
    _ = (2 * ((2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1))) * (d.K * d.X) := by ring
    _ ≤ (2 : ℝ) ^ 36 * (d.K * d.X) :=
      mul_le_mul_of_nonneg_right hC hKX
    _ ≤ (2 : ℝ) ^ 36 * d.K * (d.X * |v| + d.h0) := by
      nlinarith [mul_nonneg hKX (sub_nonneg.mpr hv.le),
        mul_nonneg d.K_nonneg d.h0_pos.le]

/-- Uniform finite-sum shift comparison, with the exact error constant in
the approved full-frequency Mellin statement. -/
theorem fullFrequencyShiftedWindowSum_difference_le
    (d : FullFrequencyMellinData) (v : ℝ) :
    ‖fullFrequencyShiftedWindowSum d v - fullFrequencyShiftedWindowSum d 0‖ ≤
      (2 : ℝ) ^ 36 * d.K * (d.X * |v| + d.h0) := by
  by_cases hv : |v| ≤ 1
  · exact fullFrequencyShiftedWindowSum_difference_le_small d hv
  · exact fullFrequencyShiftedWindowSum_difference_le_large d (lt_of_not_ge hv)

/-- The shifted finite sum is measurable as a function of its shift. -/
theorem fullFrequencyShiftedWindowSum_measurable
    (d : FullFrequencyMellinData) :
    Measurable (fullFrequencyShiftedWindowSum d) := by
  unfold fullFrequencyShiftedWindowSum
  apply Finset.measurable_sum
  intro n hn
  have hA : Measurable (fun v : ℝ =>
      Polynomial.mellinIntervalIndicator
        (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) := by
    unfold Polynomial.mellinIntervalIndicator
    have hleft : Measurable (fun v : ℝ => d.X * Real.exp v) := by fun_prop
    have hright : Measurable (fun v : ℝ => (d.X + d.H) * Real.exp v) := by
      fun_prop
    have hset : MeasurableSet {v : ℝ |
        d.X * Real.exp v < (n : ℝ) ∧
          (n : ℝ) ≤ (d.X + d.H) * Real.exp v} :=
      (measurableSet_lt hleft measurable_const).inter
        (measurableSet_le measurable_const hright)
    exact Measurable.ite hset measurable_const measurable_const
  exact measurable_const.mul
    (Complex.measurable_ofReal.comp ((by fun_prop :
      Measurable (fun v : ℝ => Real.exp (-v / 2))).mul hA))

/-- The fixed smoothing density times the shifted finite sum is Bochner
integrable. The bound uses local mass on the entire selected support. -/
theorem fullFrequencyShiftedWindowSum_kernel_integrable
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T) :
    Integrable (fun v : ℝ =>
      (FractionalPrimes.polynomialKernelRhoT T v : ℂ) *
        fullFrequencyShiftedWindowSum d v) := by
  have hρ : Integrable (fun v : ℝ =>
      (FractionalPrimes.polynomialKernelRhoT T v : ℂ)) :=
    (Polynomial.polynomialKernelRhoT_integrable T hT).ofReal
  have hbound : ∀ v : ℝ,
      ‖fullFrequencyShiftedWindowSum d v‖ ≤
        (2 : ℝ) ^ 11 * ((2 : ℝ) ^ 22 + 1) * d.K * d.X :=
    fullFrequencyShiftedWindowSum_norm_le d
  exact hρ.mul_bdd
    (fullFrequencyShiftedWindowSum_measurable d).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Each term of the finite shifted sum is integrable against the fixed
Mellin smoothing density. -/
theorem fullFrequencyShiftedWindowTerm_kernel_integrable
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : n ∈ fullFrequencySupportIndices d.X) :
    Integrable (fun v : ℝ =>
      (FractionalPrimes.polynomialKernelRhoT T v : ℂ) *
        (d.a n * (↑(Real.exp (-v / 2) *
          Polynomial.mellinIntervalIndicator
            (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) : ℂ))) := by
  let q : ℝ → ℂ := fun v =>
    d.a n * (↑(Real.exp (-v / 2) *
      Polynomial.mellinIntervalIndicator
        (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) : ℂ)
  have hA : Measurable (fun v : ℝ =>
      Polynomial.mellinIntervalIndicator
        (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) := by
    unfold Polynomial.mellinIntervalIndicator
    have hleft : Measurable (fun v : ℝ => d.X * Real.exp v) := by fun_prop
    have hright : Measurable (fun v : ℝ => (d.X + d.H) * Real.exp v) := by
      fun_prop
    have hset : MeasurableSet {v : ℝ |
        d.X * Real.exp v < (n : ℝ) ∧
          (n : ℝ) ≤ (d.X + d.H) * Real.exp v} :=
      (measurableSet_lt hleft measurable_const).inter
        (measurableSet_le measurable_const hright)
    exact Measurable.ite hset measurable_const measurable_const
  have hq : Measurable q := by
    dsimp [q]
    exact measurable_const.mul
      (Complex.measurable_ofReal.comp ((by fun_prop :
        Measurable (fun v : ℝ => Real.exp (-v / 2))).mul hA))
  have hqbound : ∀ v : ℝ, ‖q v‖ ≤ (2 : ℝ) ^ 11 * ‖d.a n‖ := by
    intro v
    obtain ⟨hnonneg, hle⟩ := fullFrequencyShiftedWindowWeight_le d n hn v
    dsimp [q]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
    nlinarith [mul_le_mul_of_nonneg_left hle (norm_nonneg (d.a n))]
  have hρ : Integrable (fun v : ℝ =>
      (FractionalPrimes.polynomialKernelRhoT T v : ℂ)) :=
    (Polynomial.polynomialKernelRhoT_integrable T hT).ofReal
  exact hρ.mul_bdd hq.aestronglyMeasurable
    (Filter.Eventually.of_forall hqbound)

/-- Finite Fubini and the exact logarithmic substitution express the
smoothed sum as the fixed-kernel integral of the shifted sharp sum. -/
theorem fullFrequencySmoothedSum_eq_shiftIntegral
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T) :
    fullFrequencySmoothedSum d T =
      (↑(d.H⁻¹) : ℂ) * ∫ v : ℝ,
        (FractionalPrimes.polynomialKernelRhoT T v : ℂ) *
          fullFrequencyShiftedWindowSum d v := by
  classical
  let S := fullFrequencySupportIndices d.X
  let ρ : ℝ → ℂ := fun v =>
    (FractionalPrimes.polynomialKernelRhoT T v : ℂ)
  let q : ℕ → ℝ → ℂ := fun n v =>
    d.a n * (↑(Real.exp (-v / 2) *
      Polynomial.mellinIntervalIndicator
        (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n) : ℂ)
  let r : ℕ → ℝ → ℝ := fun n v =>
    FractionalPrimes.polynomialKernelRhoT T v *
      (Real.exp (-v / 2) * Polynomial.mellinIntervalIndicator
        (d.X * Real.exp v) ((d.X + d.H) * Real.exp v) n)
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := by
    have hleft : 0 ≤ d.X / (2 : ℝ) ^ 21 :=
      div_nonneg (by linarith [d.X_lower]) (by positivity)
    have hmem := (Polynomial.mellinIntervalIndices_mem_iff hleft n).1 hn
    have hpos : 0 < (n : ℝ) := lt_of_le_of_lt hleft hmem.1
    exact_mod_cast hpos
  have hterm (n : ℕ) (hn : n ∈ S) :
      d.a n * (Polynomial.mellinRealHalfPower n : ℂ) *
          (Polynomial.mellinRealConvolution
            (fullFrequencySharpLogWindow d)
            (FractionalPrimes.polynomialKernelRhoT T)
            (Real.log (n : ℝ)) : ℂ) =
        (↑(d.H⁻¹) : ℂ) * ∫ v : ℝ, ρ v * q n v := by
    have hbase := Polynomial.mellinWindowConvolution_shiftedIntegral
      d.X d.H T n (by linarith [d.X_lower]) d.H_pos (hSpos n hn)
    have hwindow : fullFrequencySharpLogWindow d =
        fun u => Real.exp (u / 2) / d.H *
          if Real.log d.X < u ∧ u ≤ Real.log (d.X + d.H) then (1 : ℝ) else 0 :=
      rfl
    rw [hwindow]
    calc
      _ = d.a n *
          ((Polynomial.mellinRealHalfPower n *
            Polynomial.mellinRealConvolution
              (fun u => Real.exp (u / 2) / d.H *
                if Real.log d.X < u ∧ u ≤ Real.log (d.X + d.H) then
                  (1 : ℝ) else 0)
              (FractionalPrimes.polynomialKernelRhoT T)
              (Real.log (n : ℝ)) : ℝ) : ℂ) := by
            push_cast
            ring
      _ = d.a n *
          (((d.H⁻¹ * ∫ v : ℝ, r n v : ℝ) : ℝ) : ℂ) := by
            rw [hbase]
      _ = d.a n *
          ((↑(d.H⁻¹) : ℂ) * ∫ v : ℝ, (r n v : ℂ)) := by
            congr 1
            rw [Complex.ofReal_mul, ← integral_complex_ofReal]
      _ = (↑(d.H⁻¹) : ℂ) *
          (d.a n * ∫ v : ℝ, (r n v : ℂ)) := by ring
      _ = (↑(d.H⁻¹) : ℂ) *
          ∫ v : ℝ, d.a n * (r n v : ℂ) := by
            congr 1
            rw [← integral_const_mul]
      _ = (↑(d.H⁻¹) : ℂ) *
          ∫ v : ℝ, ρ v * q n v := by
            congr 1
            apply integral_congr_ae
            filter_upwards with v
            dsimp [ρ, q, r]
            push_cast
            ring
  have hsumIntegral :
      (∑ n ∈ S, ∫ v : ℝ, ρ v * q n v) =
        ∫ v : ℝ, ρ v * fullFrequencyShiftedWindowSum d v := by
    calc
      _ = ∫ v : ℝ, ∑ n ∈ S, ρ v * q n v := by
        rw [integral_finsetSum]
        intro n hn
        simpa [ρ, q] using
          fullFrequencyShiftedWindowTerm_kernel_integrable d hT n hn
      _ = ∫ v : ℝ, ρ v * fullFrequencyShiftedWindowSum d v := by
        congr 1
        funext v
        dsimp [fullFrequencyShiftedWindowSum, ρ, q, S]
        rw [Finset.mul_sum]
  unfold fullFrequencySmoothedSum
  calc
    (∑ n ∈ S, d.a n * (Polynomial.mellinRealHalfPower n : ℂ) *
        (Polynomial.mellinRealConvolution
          (fullFrequencySharpLogWindow d)
          (FractionalPrimes.polynomialKernelRhoT T)
          (Real.log (n : ℝ)) : ℂ)) =
        ∑ n ∈ S, (↑(d.H⁻¹) : ℂ) * ∫ v : ℝ, ρ v * q n v := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hterm n hn
    _ = (↑(d.H⁻¹) : ℂ) *
        ∑ n ∈ S, ∫ v : ℝ, ρ v * q n v := by rw [Finset.mul_sum]
    _ = (↑(d.H⁻¹) : ℂ) *
        ∫ v : ℝ, ρ v * fullFrequencyShiftedWindowSum d v := by
          rw [hsumIntegral]

/-- The zero-shift sharp sum is exactly the unnormalized mean on the
approved half-open interval. -/
theorem fullFrequencyMellinMean_eq_zeroShift
    (d : FullFrequencyMellinData) :
    fullFrequencyMellinMean d =
      (↑(d.H⁻¹) : ℂ) * fullFrequencyShiftedWindowSum d 0 := by
  classical
  let S := fullFrequencySupportIndices d.X
  let M := Polynomial.mellinWindowAverageIndices d.X d.H
  have hMsubset : M ⊆ S := by
    intro n hn
    have hm := (Polynomial.mellinIntervalIndices_mem_iff
      (x := d.X) (y := d.X + d.H)
      (by linarith [d.X_lower]) n).1 hn
    apply (Polynomial.mellinIntervalIndices_mem_iff
      (x := d.X / (2 : ℝ) ^ 21)
      (y := (2 : ℝ) ^ 22 * d.X)
      (div_nonneg (by linarith [d.X_lower]) (by positivity)) n).2
    constructor
    · have hfactor : d.X / (2 : ℝ) ^ 21 ≤ d.X := by
        have hX : 0 ≤ d.X := by linarith [d.X_lower]
        nlinarith
      linarith [hm.1]
    · have hX : 0 ≤ d.X := by linarith [d.X_lower]
      nlinarith [hm.2, d.H_upper]
  have hsum : fullFrequencyShiftedWindowSum d 0 = ∑ n ∈ M, d.a n := by
    let D : ℕ → ℝ := fun n =>
      Polynomial.mellinIntervalIndicator d.X (d.X + d.H) n
    have hfilter : S.filter (fun n => n ∈ M) = M := by
      ext n
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hMsubset h, h⟩⟩
    calc
      fullFrequencyShiftedWindowSum d 0 =
          ∑ n ∈ S, if n ∈ M then d.a n else 0 := by
            unfold fullFrequencyShiftedWindowSum
            apply Finset.sum_congr rfl
            intro n hn
            have hmem := Polynomial.mellinIntervalIndices_mem_iff
              (x := d.X) (y := d.X + d.H)
              (by linarith [d.X_lower]) n
            by_cases hnM : n ∈ M
            · have hcond := hmem.1 hnM
              simp [D, Polynomial.mellinIntervalIndicator, hnM, hcond]
            · have hcond : ¬(d.X < (n : ℝ) ∧ (n : ℝ) ≤ d.X + d.H) := by
                intro h
                exact hnM (hmem.mpr h)
              simp [D, Polynomial.mellinIntervalIndicator, hnM, hcond]
      _ = ∑ n ∈ S.filter (fun n => n ∈ M), d.a n := by
            rw [← Finset.sum_filter]
      _ = ∑ n ∈ M, d.a n := by rw [hfilter]
  unfold fullFrequencyMellinMean
  rw [hsum]

/-- Integrating the all-shift finite-sum comparison against the fixed
nonnegative kernel gives the exact source numerator before division by
the window length. -/
theorem fullFrequencyShiftedWindowError_integral_le
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T) :
    ‖∫ v : ℝ, (FractionalPrimes.polynomialKernelRhoT T v : ℂ) *
        (fullFrequencyShiftedWindowSum d v -
          fullFrequencyShiftedWindowSum d 0)‖ ≤
      (2 : ℝ) ^ 36 * d.K *
        (d.X * (FractionalPrimes.polynomialKernelM1 / T) + d.h0) := by
  let ρ : ℝ → ℝ := FractionalPrimes.polynomialKernelRhoT T
  let ρC : ℝ → ℂ := fun v => (ρ v : ℂ)
  let G : ℝ → ℂ := fullFrequencyShiftedWindowSum d
  let D : ℂ := G 0
  let E : ℝ → ℂ := fun v => G v - D
  let major : ℝ → ℝ := fun v =>
    ρ v * ((2 : ℝ) ^ 36 * d.K * (d.X * |v| + d.h0))
  have hρnonneg (v : ℝ) : 0 ≤ ρ v := by
    dsimp [ρ, FractionalPrimes.polynomialKernelRhoT]
    exact mul_nonneg hT.le
      (FractionalPrimes.polynomialKernelRho_nonneg _)
  have hρint : Integrable ρ :=
    Polynomial.polynomialKernelRhoT_integrable T hT
  have hρCint : Integrable ρC := hρint.ofReal
  have hGint : Integrable (fun v : ℝ => ρC v * G v) := by
    simpa [ρC, ρ, G] using
      fullFrequencyShiftedWindowSum_kernel_integrable d hT
  have hDint : Integrable (fun v : ℝ => ρC v * D) :=
    hρCint.mul_const D
  have hEint : Integrable (fun v : ℝ => ρC v * E v) := by
    have hsub := hGint.sub hDint
    have heq : (fun v : ℝ => ρC v * E v) =
        fun v => ρC v * G v - ρC v * D := by
      funext v
      dsimp [E]
      ring
    exact hsub.congr (Filter.Eventually.of_forall fun v =>
      (congrFun heq v).symm)
  have hmajorEq : major = fun v : ℝ =>
      ((2 : ℝ) ^ 36 * d.K) *
        (d.X * (|v| * ρ v) + d.h0 * ρ v) := by
    funext v
    dsimp [major]
    ring
  have hfirstInt : Integrable (fun v : ℝ => d.X * (|v| * ρ v)) := by
    exact (Polynomial.polynomialKernelRhoT_moment_integrable T hT).const_mul d.X
  have hsecondInt : Integrable (fun v : ℝ => d.h0 * ρ v) :=
    hρint.const_mul d.h0
  have hmajorInt : Integrable major := by
    rw [hmajorEq]
    exact (hfirstInt.add hsecondInt).const_mul ((2 : ℝ) ^ 36 * d.K)
  have hmajorValue : (∫ v : ℝ, major v) =
      (2 : ℝ) ^ 36 * d.K *
        (d.X * (FractionalPrimes.polynomialKernelM1 / T) + d.h0) := by
    rw [hmajorEq]
    calc
      _ = ((2 : ℝ) ^ 36 * d.K) *
          (∫ v : ℝ, d.X * (|v| * ρ v) + d.h0 * ρ v) := by
            rw [integral_const_mul]
      _ = ((2 : ℝ) ^ 36 * d.K) *
          ((∫ v : ℝ, d.X * (|v| * ρ v)) +
            ∫ v : ℝ, d.h0 * ρ v) := by
            rw [integral_add hfirstInt hsecondInt]
      _ = _ := by
            rw [integral_const_mul, integral_const_mul,
              FractionalPrimes.polynomialKernelRhoT_firstMoment T hT,
              Polynomial.polynomialKernelRhoT_integral T hT]
            ring
  have hmajorBound (v : ℝ) : ‖ρC v * E v‖ ≤ major v := by
    dsimp [ρC, E, major]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hρnonneg v)]
    exact mul_le_mul_of_nonneg_left
      (fullFrequencyShiftedWindowSum_difference_le d v) (hρnonneg v)
  calc
    ‖∫ v : ℝ, ρC v * E v‖ ≤
        ∫ v : ℝ, ‖ρC v * E v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, major v :=
      integral_mono_ae hEint.norm hmajorInt
        (Filter.Eventually.of_forall hmajorBound)
    _ = _ := hmajorValue

/-- The exact full-frequency local-mass smoothing error in the approved
`ltw:mass-mellin` statement. -/
theorem fullFrequencySmoothedSum_error_le
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T) :
    ‖fullFrequencyMellinMean d - fullFrequencySmoothedSum d T‖ ≤
      (2 : ℝ) ^ 36 * d.K *
        (FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) +
          d.h0 / d.H) := by
  let ρC : ℝ → ℂ := fun v =>
    (FractionalPrimes.polynomialKernelRhoT T v : ℂ)
  let G : ℝ → ℂ := fullFrequencyShiftedWindowSum d
  let D : ℂ := G 0
  let E : ℝ → ℂ := fun v => G v - D
  have hρint : Integrable ρC :=
    (Polynomial.polynomialKernelRhoT_integrable T hT).ofReal
  have hGint : Integrable (fun v : ℝ => ρC v * G v) := by
    simpa [ρC, G] using
      fullFrequencyShiftedWindowSum_kernel_integrable d hT
  have hDint : Integrable (fun v : ℝ => ρC v * D) :=
    hρint.mul_const D
  have hmass : (∫ v : ℝ, ρC v) = 1 := by
    calc
      _ = ((∫ v : ℝ, FractionalPrimes.polynomialKernelRhoT T v : ℝ) : ℂ) := by
        dsimp [ρC]
        rw [integral_complex_ofReal]
      _ = 1 := by
        rw [Polynomial.polynomialKernelRhoT_integral T hT]
        norm_num
  have hDintValue : (∫ v : ℝ, ρC v * D) = D := by
    calc
      _ = ∫ v : ℝ, D * ρC v := by
        apply integral_congr_ae
        filter_upwards with v
        ring
      _ = D * ∫ v : ℝ, ρC v := by rw [integral_const_mul]
      _ = D := by rw [hmass]; ring
  have hEintValue : (∫ v : ℝ, ρC v * E v) =
      (∫ v : ℝ, ρC v * G v) - D := by
    calc
      _ = ∫ v : ℝ, ρC v * G v - ρC v * D := by
        apply integral_congr_ae
        filter_upwards with v
        dsimp [E]
        ring
      _ = (∫ v : ℝ, ρC v * G v) -
          (∫ v : ℝ, ρC v * D) := integral_sub hGint hDint
      _ = _ := by rw [hDintValue]
  have hdiff : fullFrequencyMellinMean d - fullFrequencySmoothedSum d T =
      -((↑(d.H⁻¹) : ℂ) * ∫ v : ℝ, ρC v * E v) := by
    rw [fullFrequencyMellinMean_eq_zeroShift,
      fullFrequencySmoothedSum_eq_shiftIntegral d hT]
    dsimp [D, G, ρC] at *
    rw [hEintValue]
    ring
  have hInvnorm : ‖(↑(d.H⁻¹) : ℂ)‖ = d.H⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_pos.mpr d.H_pos).le]
  have hInv : 0 ≤ d.H⁻¹ := (inv_pos.mpr d.H_pos).le
  have hbound := fullFrequencyShiftedWindowError_integral_le d hT
  calc
    ‖fullFrequencyMellinMean d - fullFrequencySmoothedSum d T‖ =
        d.H⁻¹ * ‖∫ v : ℝ, ρC v * E v‖ := by
          rw [hdiff, norm_neg, norm_mul, hInvnorm]
    _ ≤ d.H⁻¹ * ((2 : ℝ) ^ 36 * d.K *
          (d.X * (FractionalPrimes.polynomialKernelM1 / T) + d.h0)) :=
      mul_le_mul_of_nonneg_left (by simpa [ρC, E, G, D] using hbound) hInv
    _ = (2 : ℝ) ^ 36 * d.K *
          (FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) +
            d.h0 / d.H) := by
      field_simp [ne_of_gt d.H_pos, ne_of_gt hT]

/-- The complete approved full-frequency Mellin smoothing lemma: exact
finite Fourier inversion and the local-mass error with constant `2^36`. -/
theorem smoothedMellinFromLocalMass
    (d : FullFrequencyMellinData) {T : ℝ} (hT : 0 < T) :
    fullFrequencySmoothedSum d T = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t in Set.Icc (-T) T,
        fullFrequencyMellinPolynomial d t *
          fullFrequencyMellinKernel d t *
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) ∧
    ‖fullFrequencyMellinMean d - fullFrequencySmoothedSum d T‖ ≤
      (2 : ℝ) ^ 36 * d.K *
        (FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) +
          d.h0 / d.H) := by
  exact ⟨fullFrequencySmoothedSum_formula d hT,
    fullFrequencySmoothedSum_error_le d hT⟩

end

end FractionalPrimes.Literature.Twisted

end
