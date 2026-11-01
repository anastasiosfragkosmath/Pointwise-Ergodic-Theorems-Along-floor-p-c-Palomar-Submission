module

public import FractionalPrimes.CramerBlockPhaseReplacement

/-! The finite analytic assembly for the approved `ar:cramer-block` lemma.
The source proof combines the Rosser phase replacement with interval
progression estimates and the exact sieve density comparison. -/

@[expose] public section

namespace FractionalPrimes

/-- An integer-centred interval `(X,X+H]` has exactly `H` integer points. -/
theorem realIntegerInterval_nat_card (X H : ℕ) :
    (realIntegerInterval (X : ℝ) (H : ℝ)).card = H := by
  by_cases hH : H = 0
  · subst H
    simp [realIntegerInterval]
  · have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
    have hcard := realIntegerInterval_card (X : ℝ) (H : ℝ) hHpos
    have hfloorX : ⌊(X : ℝ)⌋ = (X : ℤ) := by simp
    have hfloorTop : ⌊(X : ℝ) + (H : ℝ)⌋ = ((X + H : ℕ) : ℤ) := by
      rw [← Nat.cast_add]
      simp
    rw [hfloorX, hfloorTop] at hcard
    push_cast at hcard
    omega

/-- Factor the common phase integral out of the finite reciprocal-modulus
sum, preserving the real sieve coefficient mean. -/
theorem weightedReciprocalIntegral_eq
    (D : Finset ℕ) (coeff : ℕ → ℝ) (I : ℂ) :
    (∑ d ∈ D, (coeff d : ℂ) * (((d : ℝ)⁻¹ : ℂ) * I)) =
      ((∑ d ∈ D, coeff d / (d : ℝ) : ℝ) : ℂ) * I := by
  calc
    _ = ∑ d ∈ D, ((coeff d : ℂ) * (((d : ℝ)⁻¹ : ℂ))) * I := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = (∑ d ∈ D, (coeff d : ℂ) * (((d : ℝ)⁻¹ : ℂ))) * I := by
      rw [Finset.sum_mul]
    _ = ((∑ d ∈ D, coeff d / (d : ℝ) : ℝ) : ℂ) * I := by
      congr 1
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Complex.ofReal_natCast,
        Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]

/-- Four-step complex triangle inequality for the source's sequence of
sieve replacement, progression, coefficient mean, and unweighted error. -/
theorem norm_sub_le_four_steps (A B C D E : ℂ) :
    ‖A - E‖ ≤ ‖A - B‖ + ‖B - C‖ + ‖C - D‖ + ‖D - E‖ := by
  have h₁ : ‖A - E‖ ≤ ‖A - B‖ + ‖B - E‖ := by
    calc
      ‖A - E‖ = ‖(A - B) + (B - E)‖ := by congr 1; ring
      _ ≤ ‖A - B‖ + ‖B - E‖ := norm_add_le _ _
  have h₂ : ‖B - E‖ ≤ ‖B - C‖ + ‖C - E‖ := by
    calc
      ‖B - E‖ = ‖(B - C) + (C - E)‖ := by congr 1; ring
      _ ≤ ‖B - C‖ + ‖C - E‖ := norm_add_le _ _
  have h₃ : ‖C - E‖ ≤ ‖C - D‖ + ‖D - E‖ := by
    calc
      ‖C - E‖ = ‖(C - D) + (D - E)‖ := by congr 1; ring
      _ ≤ ‖C - D‖ + ‖D - E‖ := norm_add_le _ _
  linarith

/-- The source's trivial unit-modulus bound for the continuous phase
integral over an interval of length `H`. -/
theorem norm_phase_interval_integral_le
    (c ξ X H : ℝ) (hH : 0 ≤ H) :
    ‖∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c)‖ ≤ H := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := X) (b := X + H) (C := 1)
    (f := fun t : ℝ => unitFrequencyPhase (ξ * t ^ c))
    (by intro t ht; exact (norm_unitFrequencyPhase _).le)
  simpa [sub_eq_add_neg, abs_of_nonneg hH] using h

/-- The `d=1` instance of the checked interval progression estimate is the
unweighted comparison used at the end of `ar:cramer-block`. -/
theorem unweightedIntervalPhaseApproximation {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ K : ℝ, 3 ≤ K →
      ∀ X H : ℝ, K ≤ X → X < X + H → X + H ≤ 2 * K →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖(∑ n ∈ realIntegerInterval X H,
            unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
          (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))‖ ≤
          Cc * K ^ (1 - δ) := by
  dsimp only
  obtain ⟨Cc, hCc, hmain⟩ := intervalProgressionApproximation hc hcNon
  refine ⟨Cc, hCc, ?_⟩
  intro K hK X H hKX hXH hEnd ξ hξlo hξhi
  have hdcut : (1 : ℝ) ≤ Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) := by
    have hX : 1 ≤ X := by linarith
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hX) _)
  have hdcut' : ((1 : ℕ) : ℝ) ≤
      Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) := by
    simpa only [Nat.cast_one] using hdcut
  have h := hmain K hK X H hKX hXH hEnd 1 (by omega) hdcut' ξ hξlo hξhi
  simpa using h

/-- The actual strict-cutoff Cramér weight may be replaced by the upper
Rosser divisor sum on an integer-centred full block. -/
theorem rosserUpperCramerReplacementOnNatBlock
    (c ξ w y : ℝ) (X H : ℕ) (hH : 1 ≤ H)
    (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyH : y ≤ (H : ℝ) ^ (1 / 10 : ℝ)) :
    ‖(∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        (paperCramerWeight w n : ℂ) *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
      (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        ((paperCramerDensity w *
          ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d : ℝ) : ℂ) *
          unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)))‖ ≤
      (H : ℝ) * sieveConstant * Real.exp (-Real.log y / Real.log w) := by
  let J : Set ℝ := Set.Ioc (X : ℝ) ((X : ℝ) + (H : ℝ))
  let S : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  have hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J := by
    intro n
    simpa only [S, J, Set.mem_Ioc] using
      (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) n)
  have hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J := by
    intro x hx y hy t hxt hty
    change (X : ℝ) < x ∧ x ≤ (X : ℝ) + (H : ℝ) at hx
    change (X : ℝ) < y ∧ y ≤ (X : ℝ) + (H : ℝ) at hy
    change (X : ℝ) < t ∧ t ≤ (X : ℝ) + (H : ℝ)
    constructor <;> linarith
  have hcard : S.card = H := realIntegerInterval_nat_card X H
  have hphase : ∀ n ∈ S,
      ‖unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤ 1 := by
    intro n hn
    exact (norm_unitFrequencyPhase _).le
  have h := rosserUpperCramerPhaseReplacement S hS hJconv
    hcard hH hw hwy hyH
    (fun n => unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)))
    hphase
  convert h using 1
  simp only [S, paperCramerWeight, paperCramerDensity,
    paperPrimeProduct, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]
  congr 1

/-- The source's four analytic errors combine without changing their sizes.
Here `B` is the Rosser phase sum, `μ` its reciprocal-modulus mean, and
`I` the common continuous phase integral. -/
theorem cramerBlock_four_error_assembly
    (A B I U : ℂ) (R μ H E Kp logFactor Cs Cp Cd Cu : ℝ)
    (hE : 0 ≤ E) (hCd : 0 ≤ Cd)
    (hrep : ‖A - B‖ ≤ H * Cs * E)
    (hprog : ‖B - ((R * μ : ℝ) : ℂ) * I‖ ≤ R * Cp * Kp * logFactor)
    (hmean : |R * μ - 1| ≤ Cd * E)
    (hI : ‖I‖ ≤ H)
    (hunw : ‖I - U‖ ≤ Cu * Kp) :
    ‖A - U‖ ≤ H * Cs * E + R * Cp * Kp * logFactor +
      Cd * E * H + Cu * Kp := by
  have hmid : ‖((R * μ : ℝ) : ℂ) * I - I‖ ≤ Cd * E * H := by
    calc
      ‖((R * μ : ℝ) : ℂ) * I - I‖ = |R * μ - 1| * ‖I‖ := by
        have heq : (((R * μ : ℝ) : ℂ) * I - I) =
            (((R * μ - 1 : ℝ) : ℂ) * I) := by
          push_cast
          ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (Cd * E) * H := by
        exact mul_le_mul hmean hI (norm_nonneg _) (by positivity)
      _ = Cd * E * H := by ring
  have hfour := norm_sub_le_four_steps A B (((R * μ : ℝ) : ℂ) * I) I U
  linarith

/-- Pull a real density multiplier outside the finite upper-Rosser
phase sum without changing any coefficient or endpoint convention. -/
theorem realDensity_mul_phase_sum
    (S : Finset ℤ) (a : ℤ → ℝ) (phase : ℤ → ℂ) (R : ℝ) :
    (∑ n ∈ S, ((R * a n : ℝ) : ℂ) * phase n) =
      (R : ℂ) * ∑ n ∈ S, (a n : ℂ) * phase n := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

/-- Weighted interval progression estimate for the actual upper Rosser
coefficients, after exact divisor reindexing. The harmonic modulus sum
is bounded by its source value `1 + log y`. -/
theorem rosserUpperWeightedProgressionBound {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ K : ℝ, 3 ≤ K →
      ∀ X H : ℝ, K ≤ X → X < X + H → X + H ≤ 2 * K →
      ∀ w y : ℝ, 2 ≤ w → w ≤ y →
        y ≤ Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
      ‖(∑ n ∈ realIntegerInterval X H,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d : ℝ) : ℂ) *
            unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
        (∑ d ∈ rosserAllSModuli y,
          (rosserAllSUpperCoefficient w y d : ℂ) *
            (((d : ℝ)⁻¹ : ℂ) *
              (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))))‖ ≤
        Cc * K ^ (1 - δ) * (1 + Real.log y) := by
  dsimp only
  obtain ⟨Cc, hCc, hmain⟩ := weightedIntervalProgressionApproximation hc hcNon
  refine ⟨Cc, hCc, ?_⟩
  intro K hK X H hKX hXH hEnd w y hw hwy hycut ξ hξlo hξhi
  let D : Finset ℕ := rosserAllSModuli y
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2.1
  have hDcut : ∀ d ∈ D,
      (d : ℝ) ≤ Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) := by
    intro d hd
    exact le_trans (le_of_lt (Finset.mem_filter.mp hd).2.2) hycut
  have hDcoeff : ∀ d ∈ D, |rosserAllSUpperCoefficient w y d| ≤ 1 := by
    intro d hd
    have hb := rosserAllSCoefficient_bounds (z := w) (y := y) d
    exact abs_le.mpr ⟨hb.2.2.1, hb.2.2.2⟩
  have hprog := hmain K hK X H hKX hXH hEnd D
    (rosserAllSUpperCoefficient w y) hDpos hDcut hDcoeff ξ hξlo hξhi
  have hphaseEq := rosserUpperDivisorPhase_sum_scaled X H w y hw hwy
    (fun n => unitFrequencyPhase
      (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)))
  have hprog' :
      ‖(∑ n ∈ realIntegerInterval X H,
          ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d : ℝ) : ℂ) *
            unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))) -
        (∑ d ∈ D,
          (rosserAllSUpperCoefficient w y d : ℂ) *
            (((d : ℝ)⁻¹ : ℂ) *
              (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))))‖ ≤
        Cc * K ^ (1 -
          ((1 / 100 : ℝ) /
            (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4) *
          ∑ d ∈ D, (d : ℝ)⁻¹ := by
    rw [hphaseEq]
    simpa only [Int.cast_mul, Int.cast_natCast] using hprog
  have hsubset : D ⊆ Finset.range (⌊y⌋₊ + 1) :=
    Finset.filter_subset _ _
  have hsum : (∑ d ∈ D, (d : ℝ)⁻¹) ≤ 1 + Real.log y := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro d hd₁ hd₂; positivity :
        ∀ d ∈ Finset.range (⌊y⌋₊ + 1), d ∉ D →
          0 ≤ (d : ℝ)⁻¹)
    exact hle.trans (sum_range_floor_inv_le_one_add_log y
      (by linarith))
  calc
    _ ≤ Cc * K ^ (1 -
          ((1 / 100 : ℝ) /
            (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4) *
          ∑ d ∈ D, (d : ℝ)⁻¹ := hprog'
    _ ≤ Cc * K ^ (1 -
          ((1 / 100 : ℝ) /
            (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4) *
          (1 + Real.log y) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The checked all-S Rosser density estimate gives the coefficient mean
needed in `ar:cramer-block`, with a stronger bound than the interval-count
route since no `R*y/H` term is required. -/
theorem rosserUpperCoefficientMeanBound {w y : ℝ}
    (hw : 2 ≤ w) (hwy : w ≤ y) :
    |((sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ)) *
        (∑ d ∈ rosserAllSModuli y,
          rosserAllSUpperCoefficient w y d / (d : ℝ)) - 1| ≤
      sieveD * Real.exp (-(Real.log y / Real.log w)) := by
  let V : ℝ := sieveDensityProduct w
  have hV : 0 < V := sieveDensityProduct_pos
  have hVne : V ≠ 0 := ne_of_gt hV
  have hD := (rosserAllSDensityError hw hwy).2
  rw [(rosserAllSDensitySum_eq_moduli hw hwy).2] at hD
  have hR : (sievePrimeProduct w : ℝ) /
        (Nat.totient (sievePrimeProduct w) : ℝ) = V⁻¹ :=
    sievePrimeRatio_eq_inv_density
  rw [hR]
  calc
    |V⁻¹ * (∑ d ∈ rosserAllSModuli y,
        rosserAllSUpperCoefficient w y d / (d : ℝ)) - 1| =
      |V⁻¹ * ((∑ d ∈ rosserAllSModuli y,
        rosserAllSUpperCoefficient w y d / (d : ℝ)) - V)| := by
      rw [mul_sub, inv_mul_cancel₀ hVne]
    _ = V⁻¹ * |(∑ d ∈ rosserAllSModuli y,
        rosserAllSUpperCoefficient w y d / (d : ℝ)) - V| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hV)]
    _ ≤ V⁻¹ * (sieveD * V *
        Real.exp (-(Real.log y / Real.log w))) :=
      mul_le_mul_of_nonneg_left hD (inv_pos.mpr hV).le
    _ = sieveD * Real.exp (-(Real.log y / Real.log w)) := by
      field_simp [hVne]

/-- The exact analytic estimate behind `ar:cramer-block` for every
admissible full integer block and sieve cutoffs. The following source
specialization fixes `w` and `y` as functions of `X`. -/
theorem cramerBlockCorrelationForCutoffs {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cp Cu : ℝ, 0 ≤ Cp ∧ 0 ≤ Cu ∧
      ∀ K X H : ℕ, 3 ≤ K → K ≤ X → X + H ≤ 2 * K → 1 ≤ H →
      ∀ w y : ℝ, 2 ≤ w → w ≤ y →
        y ≤ Real.exp ((Real.log (X : ℝ)) ^ (3 / 10 : ℝ)) →
        y ≤ (H : ℝ) ^ (1 / 10 : ℝ) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperCramerWeight w n - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        (H : ℝ) * sieveConstant * Real.exp (-Real.log y / Real.log w) +
          paperCramerDensity w * Cp * (K : ℝ) ^ (1 - δ) *
            (1 + Real.log y) +
          sieveD * Real.exp (-Real.log y / Real.log w) * (H : ℝ) +
          Cu * (K : ℝ) ^ (1 - δ) := by
  dsimp only
  obtain ⟨Cp, hCp, hprogression⟩ := rosserUpperWeightedProgressionBound hc hcNon
  obtain ⟨Cu, hCu, hunweighted⟩ := unweightedIntervalPhaseApproximation hc hcNon
  refine ⟨Cp, Cu, hCp, hCu, ?_⟩
  intro K X H hK hKX hEnd hH w y hw hwy hycut hyH ξ hξlo hξhi
  let S : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  let phase : ℤ → ℂ := fun n =>
    unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))
  let a : ℤ → ℝ := fun n =>
    ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      rosserAllSUpperCoefficient w y d
  let R : ℝ := paperCramerDensity w
  let μ : ℝ := ∑ d ∈ rosserAllSModuli y,
    rosserAllSUpperCoefficient w y d / (d : ℝ)
  let I : ℂ := ∫ t in (X : ℝ)..((X : ℝ) + (H : ℝ)),
    unitFrequencyPhase (ξ * t ^ c)
  let A : ℂ := ∑ n ∈ S, (paperCramerWeight w n : ℂ) * phase n
  let B : ℂ := ∑ n ∈ S, ((R * a n : ℝ) : ℂ) * phase n
  let P : ℂ := ∑ n ∈ S, (a n : ℂ) * phase n
  let U : ℂ := ∑ n ∈ S, phase n
  let E : ℝ := Real.exp (-Real.log y / Real.log w)
  let Kp : ℝ := (K : ℝ) ^ (1 -
    ((1 / 100 : ℝ) /
      (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4)
  have hKreal : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hKXreal : (K : ℝ) ≤ X := by exact_mod_cast hKX
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hXHreal : (X : ℝ) < (X : ℝ) + (H : ℝ) := by linarith
  have hEndreal : (X : ℝ) + (H : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast hEnd
  have hRpos : 0 < R := by
    have hratio := sievePrimeRatio_eq_inv_density (w := w)
    change (sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ) =
        (sieveDensityProduct w)⁻¹ at hratio
    change 0 < (sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ)
    rw [hratio]
    exact inv_pos.mpr sieveDensityProduct_pos
  have hrep : ‖A - B‖ ≤ (H : ℝ) * sieveConstant * E := by
    simpa only [A, B, S, R, a, phase, E] using
      (rosserUpperCramerReplacementOnNatBlock c ξ w y X H hH hw hwy hyH)
  have hP : ‖P - (μ : ℂ) * I‖ ≤ Cp * Kp * (1 + Real.log y) := by
    have h := hprogression (K : ℝ) hKreal (X : ℝ) (H : ℝ)
      hKXreal hXHreal hEndreal w y hw hwy hycut ξ hξlo hξhi
    rw [weightedReciprocalIntegral_eq] at h
    simpa only [P, μ, I, S, a, phase, Kp] using h
  have hB : B = (R : ℂ) * P := by
    exact realDensity_mul_phase_sum S a phase R
  have hprog : ‖B - ((R * μ : ℝ) : ℂ) * I‖ ≤
      R * Cp * Kp * (1 + Real.log y) := by
    rw [hB]
    have heq : (((R * μ : ℝ) : ℂ) * I) =
        (R : ℂ) * ((μ : ℂ) * I) := by
      push_cast
      ring
    rw [heq, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hRpos]
    calc
      R * ‖P - (μ : ℂ) * I‖ ≤ R * (Cp * Kp * (1 + Real.log y)) :=
        mul_le_mul_of_nonneg_left hP hRpos.le
      _ = R * Cp * Kp * (1 + Real.log y) := by ring
  have hmean : |R * μ - 1| ≤ sieveD * E := by
    simpa only [R, μ, E, paperCramerDensity, paperPrimeProduct,
      neg_div] using rosserUpperCoefficientMeanBound hw hwy
  have hI : ‖I‖ ≤ (H : ℝ) := by
    exact norm_phase_interval_integral_le c ξ (X : ℝ) (H : ℝ)
      hHreal.le
  have hU : ‖I - U‖ ≤ Cu * Kp := by
    have h := hunweighted (K : ℝ) hKreal (X : ℝ) (H : ℝ)
      hKXreal hXHreal hEndreal ξ hξlo hξhi
    simpa only [U, I, S, phase, Kp, norm_sub_rev] using h
  have hbase := cramerBlock_four_error_assembly A B I U R μ
    (H : ℝ) E Kp (1 + Real.log y) sieveConstant Cp sieveD Cu
    (Real.exp_pos _).le
    (by dsimp [sieveD]; positivity)
    hrep hprog hmean hI hU
  have hcenter :
      (∑ n ∈ S, ((paperCramerWeight w n - 1 : ℝ) : ℂ) * phase n) =
        A - U := by
    simp only [A, U, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [← hcenter] at hbase
  simpa only [S, phase, R, E, Kp] using hbase

/-- The source's two fixed short-block cutoffs are ordered for every
block start `X≥3`. -/
theorem cramerBlockFixedCutoffs_le (X : ℝ) (hX : 3 ≤ X) :
    Real.exp ((Real.log X) ^ (1 / 10 : ℝ)) ≤
      Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) := by
  have hXpos : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2
      (Real.exp_one_lt_three.le.trans hX)
  apply Real.exp_le_exp.mpr
  exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)

/-- The Rosser exponential error at the approved fixed cutoffs is
exactly `E=exp(-(log X)^(1/5))`. -/
theorem cramerBlockFixedCutoffs_error_eq (X : ℝ) (hX : 3 ≤ X) :
    Real.exp (-Real.log
      (Real.exp ((Real.log X) ^ (3 / 10 : ℝ))) /
      Real.log (Real.exp ((Real.log X) ^ (1 / 10 : ℝ)))) =
      Real.exp (-(Real.log X) ^ (1 / 5 : ℝ)) := by
  have ht : 0 < Real.log X := by
    apply Real.log_pos
    linarith
  rw [Real.log_exp, Real.log_exp]
  congr 1
  have hdiv : (Real.log X) ^ (3 / 10 : ℝ) /
      (Real.log X) ^ (1 / 10 : ℝ) =
      (Real.log X) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_sub ht]
    norm_num
  calc
    -(Real.log X) ^ (3 / 10 : ℝ) /
        (Real.log X) ^ (1 / 10 : ℝ) =
      -((Real.log X) ^ (3 / 10 : ℝ) /
        (Real.log X) ^ (1 / 10 : ℝ)) := by ring
    _ = -((Real.log X) ^ (1 / 5 : ℝ)) := by rw [hdiv]

/-- The approved Cramér correlation bound at the centered frequency
representative for every full block from `ar:partition`. The block
property `y≤H^(1/10)` is exactly its sieve-level conclusion. -/
theorem cramerBlockCorrelation_centered {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ K X H : ℕ, 3 ≤ K → K ≤ X → X + H ≤ 2 * K → 1 ≤ H →
        Real.exp ((Real.log (X : ℝ)) ^ (3 / 10 : ℝ)) ≤
          (H : ℝ) ^ (1 / 10 : ℝ) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
      let w : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (1 / 10 : ℝ))
      let y : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (3 / 10 : ℝ))
      let R : ℝ := paperCramerDensity w
      let E : ℝ := Real.exp (-(Real.log (X : ℝ)) ^ (1 / 5 : ℝ))
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperCramerWeight w n - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        Cc * ((H : ℝ) * E + R * y +
          R * (K : ℝ) ^ (1 - δ) * (1 + Real.log y) +
          (K : ℝ) ^ (1 - δ)) := by
  dsimp only
  obtain ⟨Cp, Cu, hCp, hCu, hgen⟩ :=
    cramerBlockCorrelationForCutoffs hc hcNon
  let Cc : ℝ := sieveConstant + sieveD + Cp + Cu + 1
  have hD : 0 ≤ sieveD := by
    dsimp [sieveD]
    exact (Real.exp_pos 2).le.trans (le_max_right _ _)
  have hCs : 0 ≤ sieveConstant := by
    dsimp [sieveConstant]
    positivity
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  refine ⟨Cc, hCc, ?_⟩
  intro K X H hK hKX hEnd hH hyH ξ hξlo hξhi
  let w : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (1 / 10 : ℝ))
  let y : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (3 / 10 : ℝ))
  let R : ℝ := paperCramerDensity w
  let E : ℝ := Real.exp (-(Real.log (X : ℝ)) ^ (1 / 5 : ℝ))
  let Kp : ℝ := (K : ℝ) ^ (1 -
    ((1 / 100 : ℝ) /
      (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4)
  have hX : (3 : ℝ) ≤ X := by
    exact_mod_cast le_trans hK hKX
  have hlog : 1 ≤ Real.log (X : ℝ) :=
    (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < X)).2
      (Real.exp_one_lt_three.le.trans hX)
  have hw : 2 ≤ w := by
    have hpow : 1 ≤ (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) :=
      Real.one_le_rpow hlog (by norm_num)
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp 1]
    exact he.trans (Real.exp_le_exp.mpr hpow)
  have hwy : w ≤ y := cramerBlockFixedCutoffs_le (X : ℝ) hX
  have hEeq : Real.exp (-Real.log y / Real.log w) = E := by
    simpa only [w, y, E] using
      cramerBlockFixedCutoffs_error_eq (X : ℝ) hX
  have hbase := hgen K X H hK hKX hEnd hH w y hw hwy
    (by exact le_rfl) hyH ξ hξlo hξhi
  rw [hEeq] at hbase
  have hRpos : 0 < R := by
    have hratio := sievePrimeRatio_eq_inv_density (w := w)
    change 0 < (sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ)
    rw [hratio]
    exact inv_pos.mpr sieveDensityProduct_pos
  have hYpos : 0 < y := Real.exp_pos _
  have hLog : 0 ≤ 1 + Real.log y := by
    have hy1 : 1 ≤ y := by linarith
    linarith [Real.log_nonneg hy1]
  have hKp : 0 ≤ Kp := by dsimp [Kp]; positivity
  let A : ℝ := (H : ℝ) * E
  let B : ℝ := R * y
  let C : ℝ := R * Kp * (1 + Real.log y)
  let D : ℝ := Kp
  have hA : 0 ≤ A := by dsimp [A, E]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD' : 0 ≤ D := hKp
  have hCsD : sieveConstant + sieveD ≤ Cc := by
    dsimp [Cc]
    linarith
  have hCpCc : Cp ≤ Cc := by dsimp [Cc]; linarith
  have hCuCc : Cu ≤ Cc := by dsimp [Cc]; linarith
  have h1 := mul_le_mul_of_nonneg_right hCsD hA
  have h2 := mul_le_mul_of_nonneg_right hCpCc hC
  have h3 := mul_le_mul_of_nonneg_right hCuCc hD'
  have h4 : 0 ≤ Cc * B := mul_nonneg hCc hB
  have hbound :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperCramerWeight w n - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        (sieveConstant + sieveD) * A + Cp * C + Cu * D := by
    convert hbase using 1
    dsimp [A, C, D, R, E, Kp]
    ring
  calc
    _ ≤ (sieveConstant + sieveD) * A + Cp * C + Cu * D := hbound
    _ ≤ Cc * (A + B + C + D) := by nlinarith [h1, h2, h3, h4]
    _ = Cc * ((H : ℝ) * E + R * y + R * Kp *
          (1 + Real.log y) + Kp) := by rfl

/-- Integer-valued floor phases are unchanged when the frequency is
replaced by its centered representative modulo one. -/
theorem unitFrequencyPhase_mul_int_centered (ξ : ℝ) (k : ℤ) :
    unitFrequencyPhase (ξ * (k : ℝ)) =
      unitFrequencyPhase (centeredFrequency ξ * (k : ℝ)) := by
  have hξ : ξ = centeredFrequency ξ + (⌊ξ + 1 / 2⌋ : ℝ) := by
    dsimp [centeredFrequency]
    ring
  have hcast : (⌊ξ + 1 / 2⌋ : ℝ) * (k : ℝ) =
      ((⌊ξ + 1 / 2⌋ * k : ℤ) : ℝ) := by push_cast; ring
  calc
    unitFrequencyPhase (ξ * (k : ℝ)) =
        unitFrequencyPhase
          ((centeredFrequency ξ + (⌊ξ + 1 / 2⌋ : ℝ)) * (k : ℝ)) := by
            rw [← hξ]
    _ = unitFrequencyPhase (centeredFrequency ξ * (k : ℝ)) := by
      rw [add_mul, unitFrequencyPhase_add, hcast,
        unitFrequencyPhase_int, mul_one]

/-- The exact `ar:cramer-block` statement, uniform in every real
frequency. The full-block sieve-level bound is supplied by `ar:partition`. -/
theorem cramerBlockCorrelation {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ K X H : ℕ, 3 ≤ K → K ≤ X → X + H ≤ 2 * K → 1 ≤ H →
        Real.exp ((Real.log (X : ℝ)) ^ (3 / 10 : ℝ)) ≤
          (H : ℝ) ^ (1 / 10 : ℝ) →
      ∀ ξ : ℝ,
      let w : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (1 / 10 : ℝ))
      let y : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (3 / 10 : ℝ))
      let R : ℝ := paperCramerDensity w
      let E : ℝ := Real.exp (-(Real.log (X : ℝ)) ^ (1 / 5 : ℝ))
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperCramerWeight w n - 1 : ℝ) : ℂ) *
            unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖ ≤
        Cc * ((H : ℝ) * E + R * y +
          R * (K : ℝ) ^ (1 - δ) * (1 + Real.log y) +
          (K : ℝ) ^ (1 - δ)) := by
  dsimp only
  obtain ⟨Cc, hCc, hmain⟩ := cramerBlockCorrelation_centered hc hcNon
  refine ⟨Cc, hCc, ?_⟩
  intro K X H hK hKX hEnd hH hyH ξ
  have hfreq := centeredFrequency_mem ξ
  have h := hmain K X H hK hKX hEnd hH hyH
    (centeredFrequency ξ) hfreq.1 hfreq.2
  have hphase : ∀ n : ℤ,
      unitFrequencyPhase (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) =
        unitFrequencyPhase
          (centeredFrequency ξ * (Int.floor ((n : ℝ) ^ c) : ℝ)) := by
    intro n
    exact unitFrequencyPhase_mul_int_centered ξ _
  simpa only [hphase] using h

end FractionalPrimes

#print axioms FractionalPrimes.rosserUpperWeightedProgressionBound
#print axioms FractionalPrimes.rosserUpperCoefficientMeanBound
#print axioms FractionalPrimes.realIntegerInterval_nat_card
#print axioms FractionalPrimes.weightedReciprocalIntegral_eq
#print axioms FractionalPrimes.norm_sub_le_four_steps
#print axioms FractionalPrimes.norm_phase_interval_integral_le
#print axioms FractionalPrimes.unweightedIntervalPhaseApproximation
#print axioms FractionalPrimes.rosserUpperCramerReplacementOnNatBlock
#print axioms FractionalPrimes.cramerBlock_four_error_assembly
#print axioms FractionalPrimes.realDensity_mul_phase_sum
#print axioms FractionalPrimes.cramerBlockCorrelationForCutoffs
#print axioms FractionalPrimes.cramerBlockFixedCutoffs_le
#print axioms FractionalPrimes.cramerBlockFixedCutoffs_error_eq
#print axioms FractionalPrimes.cramerBlockCorrelation_centered
#print axioms FractionalPrimes.unitFrequencyPhase_mul_int_centered
#print axioms FractionalPrimes.cramerBlockCorrelation
