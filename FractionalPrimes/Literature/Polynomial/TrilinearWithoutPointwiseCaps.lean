module

public import FractionalPrimes.Literature.Polynomial.DirichletMeanConstants
public import FractionalPrimes.Literature.Uniformity.DivisorMomentBound
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Removing the unit pointwise caps from the scalar trilinear mean

This file proves the divisor-moment envelope and the cap-removal argument for
`ldm:uncapped`. The exact capped trilinear estimate is an explicit premise,
so this module is independent of the still-separate `ldm:trilinear` proof.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

private theorem real_div_sqrt_eq_sqrt {N : ℝ} (hN : 0 < N) :
    N / Real.sqrt N = Real.sqrt N := by
  have hsquare : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  field_simp [ne_of_gt (Real.sqrt_pos.2 hN)]
  nlinarith

/-- The specified logarithmic divisor-moment loss `Z_C` from `ldm:uncapped`. -/
noncomputable def Z (C : ℕ) (X : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 ^ C + 1) * (Real.log (4 * X)) ^ (2 ^ C - 1)

private theorem dirichletIndices_subset_momentRange {N : ℝ} (hN : 2 ≤ N) :
    FractionalPrimes.Literature.LargeValues.dirichletIndices N ⊆
      Finset.Icc 1 (Nat.floor (2 * N)) := by
  intro n hn
  rw [FractionalPrimes.Literature.LargeValues.dirichletIndices,
    Finset.mem_filter, Finset.mem_range] at hn
  rcases hn with ⟨hnrange, hleft⟩
  rw [Finset.mem_Icc]
  constructor
  · have hnpos : 0 < (n : ℝ) := lt_trans (by linarith) hleft
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hnpos.ne')
  · exact Nat.le_of_lt_succ hnrange

private theorem divisorMomentSumOnIndices_le
    (C : ℕ) (N : ℝ) (hN : 2 ≤ N) :
    (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
      2 * N * (1 + Real.log (2 * N)) ^ (2 ^ C - 1) := by
  classical
  let S := FractionalPrimes.Literature.LargeValues.dirichletIndices N
  have hsubset : S ⊆ Finset.Icc 1 (Nat.floor (2 * N)) := by
    exact dirichletIndices_subset_momentRange hN
  by_cases hC : C = 0
  · subst C
    have hsum :
        (∑ n ∈ S,
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ 0) =
          (S.card : ℝ) := by simp
    have hcard := Finset.card_le_card hsubset
    have htarget : (Finset.Icc 1 (Nat.floor (2 * N))).card ≤ Nat.floor (2 * N) := by
      rw [Nat.card_Icc]
      omega
    have hcard' : (S.card : ℝ) ≤ (Nat.floor (2 * N) : ℝ) := by
      exact_mod_cast hcard.trans htarget
    have hfloor : (Nat.floor (2 * N) : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
    calc
      _ = (S.card : ℝ) := hsum
      _ ≤ (Nat.floor (2 * N) : ℝ) := hcard'
      _ ≤ 2 * N := hfloor
      _ = 2 * N * (1 + Real.log (2 * N)) ^ (2 ^ 0 - 1) := by simp
  · have hCpos : 1 ≤ C := by omega
    have h2N : 1 ≤ 2 * N := by nlinarith
    have hmoment := FractionalPrimes.Literature.Uniformity.divisorMomentBound
      2 C (by norm_num) hCpos (2 * N) h2N
    have hsumSubset :
        (∑ n ∈ S,
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
          ∑ n ∈ Finset.Icc 1 (Nat.floor (2 * N)),
            (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro n hn hnot
        positivity)
    simpa [S] using hsumSubset.trans hmoment

private theorem dirichletTerm_norm_eq_coeff_norm
    (coeff : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖FractionalPrimes.Literature.LargeValues.dirichletTerm coeff n t‖ = ‖coeff n‖ := by
  rw [FractionalPrimes.Literature.LargeValues.dirichletTerm, norm_mul]
  have hphase :
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) =
        factorTwistMultiplier (-t) n := by
    congr 1
    have hcast : ((-t : ℝ) : ℂ) = -(t : ℂ) := by norm_num
    rw [hcast]
    noncomm_ring
  rw [hphase, factorTwistMultiplier_norm, mul_one]

private theorem normalizedDirichletCoeff_norm_eq
    (coeff : ℕ → ℂ) (n : ℕ) :
    ‖FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff n‖ =
      ‖coeff n‖ / Real.sqrt (n : ℝ) := by
  dsimp [FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- A factor with coefficients bounded by `d₂(n)^C` has the divisor-moment
pointwise envelope used to remove the unit caps. -/
theorem factorPolynomial_norm_le_Z_sqrt
    (C : ℕ) {X N : ℝ} (coeff : ℕ → ℂ)
    (hX : (2 : ℝ) ^ 16 ≤ X) (hNlow : 2 ≤ N) (hNhigh : N ≤ X)
    (hcoeff : factorCoefficientBound C N coeff) :
    ∀ t : ℝ, ‖factorPolynomial N coeff t‖ ≤ Z C X * Real.sqrt N := by
  classical
  let L := Real.log (4 * X)
  have hXone : 1 ≤ X := by
    have hpow : (1 : ℝ) ≤ 2 ^ 16 := by norm_num
    exact hpow.trans hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  have hExp : Real.exp 1 ≤ 4 * X := by
    calc
      Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ 4 * X := by nlinarith
  have hLone : 1 ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hExp
    simpa [L] using hlog
  have hNpos : 0 < N := by linarith
  have hNle : 0 ≤ N := hNpos.le
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hlog2Nnonneg : 0 ≤ Real.log (2 * N) :=
    Real.log_nonneg (by nlinarith)
  have hlogMono : Real.log (2 * N) ≤ L := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have hlogBound : 1 + Real.log (2 * N) ≤ 2 * L := by
    linarith
  have hMomentSum := divisorMomentSumOnIndices_le C N hNlow
  have hcoeffTerm :
      ∀ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        ‖FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff n‖ ≤
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C /
            Real.sqrt N := by
    intro n hn
    rw [normalizedDirichletCoeff_norm_eq]
    have hNn : N < (n : ℝ) := by
      rw [FractionalPrimes.Literature.LargeValues.dirichletIndices,
        Finset.mem_filter] at hn
      exact hn.2
    have hsqrt : Real.sqrt N ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hNn.le
    calc
      ‖coeff n‖ / Real.sqrt (n : ℝ) ≤
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C /
            Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right (hcoeff n hn) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hsqrtNpos
        · exact hsqrt
  intro t
  have hsumNorm :
      ‖factorPolynomial N coeff t‖ ≤
        ∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
          ‖FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff n‖ := by
    unfold factorPolynomial FractionalPrimes.Literature.LargeValues.dirichletPolynomial
    calc
      _ ≤ ∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
            ‖FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
              n t‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact dirichletTerm_norm_eq_coeff_norm _ _ _
  have hsumTerms :
      (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        ‖FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff n‖) ≤
        ∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
          ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C /
            Real.sqrt N) := by
    apply Finset.sum_le_sum
    intro n hn
    exact hcoeffTerm n hn
  have hsumDiv :
      (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C /
          Real.sqrt N)) =
        (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) /
            Real.sqrt N := by
    rw [← Finset.sum_div]
  have hsumUpper :
      (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) /
          Real.sqrt N ≤
        2 * Real.sqrt N * (1 + Real.log (2 * N)) ^ (2 ^ C - 1) := by
    calc
      _ ≤ (2 * N * (1 + Real.log (2 * N)) ^ (2 ^ C - 1)) /
          Real.sqrt N := by
            exact div_le_div_of_nonneg_right hMomentSum hsqrtNpos.le
      _ = 2 * Real.sqrt N * (1 + Real.log (2 * N)) ^ (2 ^ C - 1) := by
        calc
          _ = 2 * (N / Real.sqrt N) *
              (1 + Real.log (2 * N)) ^ (2 ^ C - 1) := by
                field_simp [ne_of_gt hsqrtNpos]
          _ = 2 * Real.sqrt N *
              (1 + Real.log (2 * N)) ^ (2 ^ C - 1) := by
                rw [real_div_sqrt_eq_sqrt hNpos]
  have hpow :
      (1 + Real.log (2 * N)) ^ (2 ^ C - 1) ≤
        (2 * L) ^ (2 ^ C - 1) :=
    pow_le_pow_left₀ (by positivity) hlogBound _
  have hpowEq : (2 * L) ^ (2 ^ C - 1) =
      2 ^ (2 ^ C - 1) * L ^ (2 ^ C - 1) := by rw [mul_pow]
  have hconst : (2 : ℝ) ^ (2 ^ C - 1 + 1) ≤
      (2 : ℝ) ^ (2 ^ C + 1) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hpowC : 1 ≤ 2 ^ C :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero C (by omega))
    omega
  have hZ : 0 ≤ Z C X := by
    dsimp [Z]
    positivity
  calc
    ‖factorPolynomial N coeff t‖ ≤
        ∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
          ‖FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff n‖ := hsumNorm
    _ ≤ (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
          ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C /
            Real.sqrt N)) := hsumTerms
    _ = (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) /
            Real.sqrt N := hsumDiv
    _ ≤ 2 * Real.sqrt N * (1 + Real.log (2 * N)) ^ (2 ^ C - 1) := hsumUpper
    _ ≤ 2 * Real.sqrt N * (2 * L) ^ (2 ^ C - 1) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 2 ^ (2 ^ C - 1 + 1) * L ^ (2 ^ C - 1) * Real.sqrt N := by
      rw [hpowEq]
      ring
    _ ≤ 2 ^ (2 ^ C + 1) * L ^ (2 ^ C - 1) * Real.sqrt N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst
          (by positivity)) (by positivity)
    _ = Z C X * Real.sqrt N := by
      simp [Z, L, mul_assoc]

/-- The exact capped estimate from `ldm:trilinear`, specialized to a fixed
valid scalar trilinear context and measurable set. This is an explicit
premise until the separate capped theorem is imported. -/
def CappedTrilinearEstimate
    (C : ℕ) (X ε T alpha beta gamma δ : ℝ) (E : Set ℝ) : Prop :=
  (2 : ℝ) ^ 16 ≤ X →
    0 < ε → ε ≤ 3 / 16 → 2 ≤ T → T ≤ X ^ (3 / 8 - ε) →
    0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → alpha + beta + gamma = 1 →
    1 / 4 - ε / 100 ≤ alpha → alpha ≤ 1 / 2 + ε / 100 →
    |beta - gamma| ≤ 1 / 4 + ε / 100 →
    0 < δ → δ ≤ 1 → MeasurableSet E → E ⊆ Set.Icc (-T) T →
  ∀ (coeff₁ coeff₂ coeff₃ : ℕ → ℂ),
    factorCoefficientBound C (X ^ alpha) coeff₁ →
    factorCoefficientBound C (X ^ beta) coeff₂ →
    factorCoefficientBound C (X ^ gamma) coeff₃ →
    (∀ t ∈ E, ‖factorPolynomial (X ^ alpha) coeff₁ t‖ ≤ Real.sqrt (X ^ alpha)) →
    (∀ t ∈ E, ‖factorPolynomial (X ^ beta) coeff₂ t‖ ≤ Real.sqrt (X ^ beta)) →
    (∀ t ∈ E, ‖factorPolynomial (X ^ gamma) coeff₃ t‖ ≤ Real.sqrt (X ^ gamma)) →
    (∀ t ∈ E, ‖factorPolynomial (X ^ alpha) coeff₁ t‖ ≤ δ * Real.sqrt (X ^ alpha)) →
      (∫ t in E,
        ‖factorPolynomial (X ^ alpha) coeff₁ t *
          factorPolynomial (X ^ beta) coeff₂ t *
          factorPolynomial (X ^ gamma) coeff₃ t‖) ≤
        J C * (Real.log (4 * X)) ^ (b C + 3) * Real.sqrt X *
          (δ ^ (1 / 16 : ℝ) + X ^ (-ε / 16 : ℝ))

private theorem factorPolynomial_div_const
    (N : ℝ) (coeff : ℕ → ℂ) (z : ℂ) :
    factorPolynomial N (fun n => coeff n / z) =
      fun t => factorPolynomial N coeff t / z := by
  classical
  funext t
  unfold factorPolynomial FractionalPrimes.Literature.LargeValues.dirichletPolynomial
  calc
    (∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (fun n => coeff n / z)) n t) =
      ∑ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) n t / z := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [FractionalPrimes.Literature.LargeValues.dirichletTerm,
          FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff,
          div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by rw [Finset.sum_div]

private theorem trilinearLengthBounds
    {X ε alpha beta gamma : ℝ}
    (hX : (2 : ℝ) ^ 16 ≤ X) (hε : ε ≤ 3 / 16)
    (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta) (_hc0 : 0 ≤ gamma)
    (hsum : alpha + beta + gamma = 1)
    (haLow : 1 / 4 - ε / 100 ≤ alpha)
    (haHigh : alpha ≤ 1 / 2 + ε / 100)
    (hbc : |beta - gamma| ≤ 1 / 4 + ε / 100) :
    2 ≤ X ^ alpha ∧ X ^ alpha ≤ X ∧
    2 ≤ X ^ beta ∧ X ^ beta ≤ X ∧
    2 ≤ X ^ gamma ∧ X ^ gamma ≤ X := by
  have hXone : 1 ≤ X := by
    have hpow : (1 : ℝ) ≤ 2 ^ 16 := by norm_num
    exact hpow.trans hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXone
  have hdiffLow : -(1 / 4 + ε / 100) ≤ beta - gamma := (abs_le.mp hbc).1
  have hdiffHigh : beta - gamma ≤ 1 / 4 + ε / 100 := (abs_le.mp hbc).2
  have hbLow : 1 / 8 - ε / 100 ≤ beta := by linarith
  have hcLow : 1 / 8 - ε / 100 ≤ gamma := by linarith
  have hbHigh : beta ≤ 1 / 2 + ε / 100 := by linarith
  have hcHigh : gamma ≤ 1 / 2 + ε / 100 := by linarith
  have haLow' : 1 / 16 ≤ alpha := by linarith
  have hbLow' : 1 / 16 ≤ beta := by linarith
  have hcLow' : 1 / 16 ≤ gamma := by linarith
  have haHigh' : alpha ≤ 1 := by linarith
  have hbHigh' : beta ≤ 1 := by linarith
  have hcHigh' : gamma ≤ 1 := by linarith
  have hroot : 2 ≤ X ^ (1 / 16 : ℝ) := by
    have hbase : (2 : ℝ) = ((2 : ℝ) ^ 16) ^ (1 / 16 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 16 (1 / 16 : ℝ)]
      norm_num
    rw [hbase]
    exact Real.rpow_le_rpow (by positivity) hX (by norm_num)
  constructor
  · exact (hroot.trans (Real.rpow_le_rpow_of_exponent_le hXone haLow'))
  constructor
  · calc
      X ^ alpha ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone haHigh'
      _ = X := Real.rpow_one X
  constructor
  · exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hXone hbLow')
  constructor
  · calc
      X ^ beta ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hbHigh'
      _ = X := Real.rpow_one X
  constructor
  · exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hXone hcLow')
  · calc
      X ^ gamma ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hcHigh'
      _ = X := Real.rpow_one X

private theorem Z_ge_one {C : ℕ} {X : ℝ}
    (hX : (2 : ℝ) ^ 16 ≤ X) : 1 ≤ Z C X := by
  have hXone : 1 ≤ X := by
    have hpow : (1 : ℝ) ≤ 2 ^ 16 := by norm_num
    exact hpow.trans hX
  have hLone : 1 ≤ Real.log (4 * X) := by
    have hExp : Real.exp 1 ≤ 4 * X := by
      calc
        Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
        _ ≤ 4 * X := by nlinarith
    have := Real.log_le_log (Real.exp_pos 1) hExp
    simpa using this
  have htwo : 1 ≤ (2 : ℝ) ^ (2 ^ C + 1) := one_le_pow₀ (by norm_num)
  have hlog : 1 ≤ (Real.log (4 * X)) ^ (2 ^ C - 1) := one_le_pow₀ hLone
  rw [Z]
  exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
    (mul_le_mul htwo hlog (by positivity) (by positivity))

private theorem norm_div_real_const_le
    {z : ℝ} (hz : 1 ≤ z) (w : ℂ) :
    ‖w / (z : ℂ)‖ ≤ ‖w‖ := by
  have hzpos : 0 < z := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
  exact div_le_self (norm_nonneg _) hz

/-- Removing the three auxiliary unit caps costs exactly the divisor-moment
factor `Z_C^3`, as in `ldm:uncapped`. The capped trilinear estimate remains
an explicit premise so this file is independent of its separate proof. -/
theorem trilinearWithoutPointwiseCaps
    (C : ℕ) (X ε T alpha beta gamma δ : ℝ) (E : Set ℝ)
    (coeff₁ coeff₂ coeff₃ : ℕ → ℂ)
    (hX : (2 : ℝ) ^ 16 ≤ X)
    (hε0 : 0 < ε) (hε : ε ≤ 3 / 16)
    (hT0 : 2 ≤ T) (hT : T ≤ X ^ (3 / 8 - ε))
    (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta) (hc0 : 0 ≤ gamma)
    (hsum : alpha + beta + gamma = 1)
    (haLow : 1 / 4 - ε / 100 ≤ alpha)
    (haHigh : alpha ≤ 1 / 2 + ε / 100)
    (hbc : |beta - gamma| ≤ 1 / 4 + ε / 100)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-T) T)
    (hcoeff₁ : factorCoefficientBound C (X ^ alpha) coeff₁)
    (hcoeff₂ : factorCoefficientBound C (X ^ beta) coeff₂)
    (hcoeff₃ : factorCoefficientBound C (X ^ gamma) coeff₃)
    (hsmall : ∀ t ∈ E,
      ‖factorPolynomial (X ^ alpha) coeff₁ t‖ ≤ δ * Real.sqrt (X ^ alpha))
    (hCapped : CappedTrilinearEstimate C X ε T alpha beta gamma δ E) :
    (∫ t in E,
      ‖factorPolynomial (X ^ alpha) coeff₁ t *
        factorPolynomial (X ^ beta) coeff₂ t *
        factorPolynomial (X ^ gamma) coeff₃ t‖) ≤
      J C * Z C X ^ 3 * (Real.log (4 * X)) ^ (b C + 3) * Real.sqrt X *
        (δ ^ (1 / 16 : ℝ) + X ^ (-ε / 16 : ℝ)) := by
  classical
  obtain ⟨hN₁low, hN₁high, hN₂low, hN₂high, hN₃low, hN₃high⟩ :=
    trilinearLengthBounds hX hε ha0 hb0 hc0 hsum haLow haHigh hbc
  have hZone : 1 ≤ Z C X := Z_ge_one hX
  have hZpos : 0 < Z C X := lt_of_lt_of_le (by norm_num) hZone
  let z : ℂ := (Z C X : ℂ)
  have hz : z ≠ 0 := by
    dsimp [z]
    exact Complex.ofReal_ne_zero.mpr hZpos.ne'
  let coeff₁' : ℕ → ℂ := fun n => coeff₁ n / z
  let coeff₂' : ℕ → ℂ := fun n => coeff₂ n / z
  let coeff₃' : ℕ → ℂ := fun n => coeff₃ n / z
  have hcoeff₁' : factorCoefficientBound C (X ^ alpha) coeff₁' :=
    factorCoefficientBound_of_norm_le hcoeff₁ (by
      intro n hn
      dsimp [coeff₁']
      exact norm_div_real_const_le hZone (coeff₁ n))
  have hcoeff₂' : factorCoefficientBound C (X ^ beta) coeff₂' :=
    factorCoefficientBound_of_norm_le hcoeff₂ (by
      intro n hn
      dsimp [coeff₂']
      exact norm_div_real_const_le hZone (coeff₂ n))
  have hcoeff₃' : factorCoefficientBound C (X ^ gamma) coeff₃' :=
    factorCoefficientBound_of_norm_le hcoeff₃ (by
      intro n hn
      dsimp [coeff₃']
      exact norm_div_real_const_le hZone (coeff₃ n))
  have henvelope₁ := factorPolynomial_norm_le_Z_sqrt C coeff₁ hX hN₁low hN₁high hcoeff₁
  have henvelope₂ := factorPolynomial_norm_le_Z_sqrt C coeff₂ hX hN₂low hN₂high hcoeff₂
  have henvelope₃ := factorPolynomial_norm_le_Z_sqrt C coeff₃ hX hN₃low hN₃high hcoeff₃
  have hcap₁ : ∀ t ∈ E,
      ‖factorPolynomial (X ^ alpha) coeff₁' t‖ ≤ Real.sqrt (X ^ alpha) := by
    intro t ht
    rw [show coeff₁' = fun n => coeff₁ n / z by rfl, factorPolynomial_div_const]
    have hnorm :
        ‖factorPolynomial (X ^ alpha) coeff₁ t / z‖ =
          ‖factorPolynomial (X ^ alpha) coeff₁ t‖ / Z C X := by
      dsimp [z]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpos]
    rw [hnorm]
    calc
      _ ≤ (Z C X * Real.sqrt (X ^ alpha)) / Z C X :=
        div_le_div_of_nonneg_right (henvelope₁ t) hZpos.le
      _ = Real.sqrt (X ^ alpha) := by field_simp [ne_of_gt hZpos]
  have hcap₂ : ∀ t ∈ E,
      ‖factorPolynomial (X ^ beta) coeff₂' t‖ ≤ Real.sqrt (X ^ beta) := by
    intro t ht
    rw [show coeff₂' = fun n => coeff₂ n / z by rfl, factorPolynomial_div_const]
    have hnorm :
        ‖factorPolynomial (X ^ beta) coeff₂ t / z‖ =
          ‖factorPolynomial (X ^ beta) coeff₂ t‖ / Z C X := by
      dsimp [z]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpos]
    rw [hnorm]
    calc
      _ ≤ (Z C X * Real.sqrt (X ^ beta)) / Z C X :=
        div_le_div_of_nonneg_right (henvelope₂ t) hZpos.le
      _ = Real.sqrt (X ^ beta) := by field_simp [ne_of_gt hZpos]
  have hcap₃ : ∀ t ∈ E,
      ‖factorPolynomial (X ^ gamma) coeff₃' t‖ ≤ Real.sqrt (X ^ gamma) := by
    intro t ht
    rw [show coeff₃' = fun n => coeff₃ n / z by rfl, factorPolynomial_div_const]
    have hnorm :
        ‖factorPolynomial (X ^ gamma) coeff₃ t / z‖ =
          ‖factorPolynomial (X ^ gamma) coeff₃ t‖ / Z C X := by
      dsimp [z]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpos]
    rw [hnorm]
    calc
      _ ≤ (Z C X * Real.sqrt (X ^ gamma)) / Z C X :=
        div_le_div_of_nonneg_right (henvelope₃ t) hZpos.le
      _ = Real.sqrt (X ^ gamma) := by field_simp [ne_of_gt hZpos]
  have hsmall' : ∀ t ∈ E,
      ‖factorPolynomial (X ^ alpha) coeff₁' t‖ ≤ δ * Real.sqrt (X ^ alpha) := by
    intro t ht
    rw [show coeff₁' = fun n => coeff₁ n / z by rfl, factorPolynomial_div_const]
    have hnorm :
        ‖factorPolynomial (X ^ alpha) coeff₁ t / z‖ =
          ‖factorPolynomial (X ^ alpha) coeff₁ t‖ / Z C X := by
      dsimp [z]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZpos]
    rw [hnorm]
    calc
      _ ≤ (δ * Real.sqrt (X ^ alpha)) / Z C X :=
        div_le_div_of_nonneg_right (hsmall t ht) hZpos.le
      _ ≤ δ * Real.sqrt (X ^ alpha) :=
        div_le_self (by positivity) hZone
  have hscaled := hCapped hX hε0 hε hT0 hT ha0 hb0 hc0 hsum haLow haHigh hbc
    hδ0 hδ hE hEsub coeff₁' coeff₂' coeff₃' hcoeff₁' hcoeff₂' hcoeff₃'
    hcap₁ hcap₂ hcap₃ hsmall'
  have hpoint : ∀ t : ℝ,
      ‖factorPolynomial (X ^ alpha) coeff₁ t *
        factorPolynomial (X ^ beta) coeff₂ t *
        factorPolynomial (X ^ gamma) coeff₃ t‖ =
      (Z C X) ^ 3 * ‖factorPolynomial (X ^ alpha) coeff₁' t *
        factorPolynomial (X ^ beta) coeff₂' t *
        factorPolynomial (X ^ gamma) coeff₃' t‖ := by
    intro t
    have hcomplex :
        factorPolynomial (X ^ alpha) coeff₁ t *
          factorPolynomial (X ^ beta) coeff₂ t *
          factorPolynomial (X ^ gamma) coeff₃ t =
        z ^ 3 * (factorPolynomial (X ^ alpha) coeff₁' t *
          factorPolynomial (X ^ beta) coeff₂' t *
          factorPolynomial (X ^ gamma) coeff₃' t) := by
      rw [show coeff₁' = fun n => coeff₁ n / z by rfl,
        show coeff₂' = fun n => coeff₂ n / z by rfl,
        show coeff₃' = fun n => coeff₃ n / z by rfl,
        factorPolynomial_div_const, factorPolynomial_div_const,
        factorPolynomial_div_const]
      field_simp [hz]
    rw [hcomplex, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hZpos]
  have hIntegral :
      (∫ t in E,
        ‖factorPolynomial (X ^ alpha) coeff₁ t *
          factorPolynomial (X ^ beta) coeff₂ t *
          factorPolynomial (X ^ gamma) coeff₃ t‖) =
      (Z C X) ^ 3 * (∫ t in E,
        ‖factorPolynomial (X ^ alpha) coeff₁' t *
          factorPolynomial (X ^ beta) coeff₂' t *
          factorPolynomial (X ^ gamma) coeff₃' t‖) := by
    calc
      _ = ∫ t in E,
          (Z C X) ^ 3 * ‖factorPolynomial (X ^ alpha) coeff₁' t *
            factorPolynomial (X ^ beta) coeff₂' t *
            factorPolynomial (X ^ gamma) coeff₃' t‖ := by
        apply integral_congr_ae
        filter_upwards with t
        exact hpoint t
      _ = _ := by rw [integral_const_mul]
  have hscaled' := mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ (Z C X) ^ 3)
  rw [hIntegral]
  calc
    (Z C X) ^ 3 *
        (∫ t in E,
          ‖factorPolynomial (X ^ alpha) coeff₁' t *
            factorPolynomial (X ^ beta) coeff₂' t *
            factorPolynomial (X ^ gamma) coeff₃' t‖) ≤
      (Z C X) ^ 3 *
        (J C * (Real.log (4 * X)) ^ (b C + 3) * Real.sqrt X *
          (δ ^ (1 / 16 : ℝ) + X ^ (-ε / 16 : ℝ))) := hscaled'
    _ = J C * Z C X ^ 3 * (Real.log (4 * X)) ^ (b C + 3) * Real.sqrt X *
          (δ ^ (1 / 16 : ℝ) + X ^ (-ε / 16 : ℝ)) := by ring

#print axioms FractionalPrimes.Literature.DirichletMean.factorPolynomial_norm_le_Z_sqrt
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearWithoutPointwiseCaps

