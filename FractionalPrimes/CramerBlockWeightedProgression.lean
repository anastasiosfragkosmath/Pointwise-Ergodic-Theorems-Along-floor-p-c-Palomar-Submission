module

public import FractionalPrimes.ArithmeticBasics

/-!
The finite weighted progression estimate in the proof of
`ar:cramer-block`. The source proof first applies the unweighted
progression estimate separately to each sieve modulus and then sums
the errors with the coefficient bound `|λ_d| ≤ 1`.
-/

@[expose] public section

namespace FractionalPrimes

/-- Finite weighted summation of per-modulus progression errors. This is
the algebraic error step in the Cramér block correlation proof. -/
theorem norm_weighted_progression_error_le
    (S : Finset ℕ) (coeff : ℕ → ℝ) (z : ℕ → ℂ) (I : ℂ) (E : ℝ)
    (hpos : ∀ d ∈ S, 0 < d)
    (hcoeff : ∀ d ∈ S, |coeff d| ≤ 1)
    (hz : ∀ d ∈ S,
      ‖z d - (((d : ℝ)⁻¹ : ℂ) * I)‖ ≤ E / (d : ℝ)) :
    ‖(∑ d ∈ S, (coeff d : ℂ) * z d) -
      (∑ d ∈ S, (coeff d : ℂ) * (((d : ℝ)⁻¹ : ℂ) * I))‖ ≤
      E * ∑ d ∈ S, (d : ℝ)⁻¹ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    ‖∑ d ∈ S, (coeff d : ℂ) *
        (z d - (((d : ℝ)⁻¹ : ℂ) * I))‖ ≤
      ∑ d ∈ S, ‖(coeff d : ℂ) *
        (z d - (((d : ℝ)⁻¹ : ℂ) * I))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ S, E * (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast hpos d hd
      have hcoef : ‖(coeff d : ℂ)‖ ≤ 1 := by simpa using hcoeff d hd
      have herr := hz d hd
      calc
        ‖(coeff d : ℂ) * (z d - (((d : ℝ)⁻¹ : ℂ) * I))‖ ≤
          ‖(coeff d : ℂ)‖ * ‖z d - (((d : ℝ)⁻¹ : ℂ) * I)‖ := norm_mul_le _ _
        _ ≤ 1 * (E / (d : ℝ)) :=
          mul_le_mul hcoef herr (norm_nonneg _) (by norm_num)
        _ = E * (d : ℝ)⁻¹ := by rw [one_mul, div_eq_mul_inv]
    _ = E * ∑ d ∈ S, (d : ℝ)⁻¹ := by rw [Finset.mul_sum]

/-- The checked progression estimate summed over a finite family of sieve
moduli with coefficients of absolute value at most one. -/
theorem weightedIntervalProgressionApproximation {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ K : ℝ, 3 ≤ K →
      ∀ X H : ℝ, K ≤ X → X < X + H → X + H ≤ 2 * K →
      ∀ S : Finset ℕ, ∀ coeff : ℕ → ℝ,
        (∀ d ∈ S, 0 < d) →
        (∀ d ∈ S, (d : ℝ) ≤ Real.exp ((Real.log X) ^ (3 / 10 : ℝ))) →
        (∀ d ∈ S, |coeff d| ≤ 1) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
      ‖(∑ d ∈ S, (coeff d : ℂ) *
          ∑ n ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
        (∑ d ∈ S, (coeff d : ℂ) *
          (((d : ℝ)⁻¹ : ℂ) *
            (∫ t in X..(X + H), unitFrequencyPhase (ξ * t ^ c))))‖ ≤
        Cc * K ^ (1 - δ) * ∑ d ∈ S, (d : ℝ)⁻¹ := by
  dsimp only
  obtain ⟨Cc, hCc, hmain⟩ := intervalProgressionApproximation hc hcNon
  refine ⟨Cc, hCc, ?_⟩
  intro K hK X H hKX hXH hEnd S coeff hpos hcut hcoeff ξ hξlo hξhi
  apply norm_weighted_progression_error_le S coeff _ _ _ hpos hcoeff
  intro d hd
  simpa only [div_eq_mul_inv, mul_assoc] using
    hmain K hK X H hKX hXH hEnd d (hpos d hd) (hcut d hd) ξ hξlo hξhi

/-- Algebraic mean comparison in `ar:cramer-block`: replacing each exact
multiple count by `H/d` costs at most one per supported modulus. -/
theorem sieve_weighted_mean_from_multiple_counts
    (S : Finset ℕ) (coeff count : ℕ → ℝ) (R H C E y : ℝ)
    (hR : 0 ≤ R) (hH : 0 < H) (hcard : (S.card : ℝ) ≤ y)
    (hcoeff : ∀ d ∈ S, |coeff d| ≤ 1)
    (hcount : ∀ d ∈ S, |count d - H / (d : ℝ)| ≤ 1)
    (hmean : |(R / H) * (∑ d ∈ S, coeff d * count d) - 1| ≤ C * E) :
    |R * (∑ d ∈ S, coeff d / (d : ℝ)) - 1| ≤
      C * E + R * y / H := by
  have hterm :
      |∑ d ∈ S, coeff d * (count d - H / (d : ℝ))| ≤
        (S.card : ℝ) := by
    calc
      _ ≤ ∑ d ∈ S, |coeff d * (count d - H / (d : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul]
        calc
          |coeff d| * |count d - H / (d : ℝ)| ≤ 1 * 1 :=
            mul_le_mul (hcoeff d hd) (hcount d hd)
              (abs_nonneg _) (by norm_num)
          _ = 1 := by ring
      _ = (S.card : ℝ) := by simp
  have hscale :
      (R / H) * (∑ d ∈ S, coeff d * (H / (d : ℝ))) =
        R * (∑ d ∈ S, coeff d / (d : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    field_simp [ne_of_gt hH]
  have hdiff :
      (R / H) * (∑ d ∈ S, coeff d * count d) -
        R * (∑ d ∈ S, coeff d / (d : ℝ)) =
      (R / H) * (∑ d ∈ S, coeff d * (count d - H / (d : ℝ))) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, mul_sub, hscale]
  have hRH : 0 ≤ R / H := div_nonneg hR hH.le
  have hgap :
      |(R / H) * (∑ d ∈ S, coeff d * count d) -
        R * (∑ d ∈ S, coeff d / (d : ℝ))| ≤ R * y / H := by
    rw [hdiff, abs_mul, abs_of_nonneg hRH]
    calc
      (R / H) * |∑ d ∈ S, coeff d * (count d - H / (d : ℝ))| ≤
          (R / H) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hterm hRH
      _ ≤ (R / H) * y := mul_le_mul_of_nonneg_left hcard hRH
      _ = R * y / H := by ring
  calc
    _ ≤ |R * (∑ d ∈ S, coeff d / (d : ℝ)) -
          (R / H) * (∑ d ∈ S, coeff d * count d)| +
          |(R / H) * (∑ d ∈ S, coeff d * count d) - 1| :=
      abs_sub_le _ _ _
    _ ≤ R * y / H + C * E :=
      add_le_add (by simpa only [abs_sub_comm] using hgap) hmean
    _ = C * E + R * y / H := by ring

/-- A pointwise unit-modulus phase cannot increase the finite `L¹` error
of replacing one real arithmetic weight by another. -/
theorem norm_phase_weight_replacement_le_L1
    (S : Finset ℤ) (u v : ℤ → ℝ) (phase : ℤ → ℂ)
    (hphase : ∀ n ∈ S, ‖phase n‖ ≤ 1) :
    ‖(∑ n ∈ S, (u n : ℂ) * phase n) -
      (∑ n ∈ S, (v n : ℂ) * phase n)‖ ≤
      ∑ n ∈ S, |u n - v n| := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, ← Complex.ofReal_sub]
  calc
    ‖∑ n ∈ S, ((u n - v n : ℝ) : ℂ) * phase n‖ ≤
      ∑ n ∈ S, ‖((u n - v n : ℝ) : ℂ) * phase n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, |u n - v n| := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ‖((u n - v n : ℝ) : ℂ) * phase n‖ ≤
          ‖((u n - v n : ℝ) : ℂ)‖ * ‖phase n‖ := norm_mul_le _ _
        _ ≤ |u n - v n| * 1 := by
          simpa only [Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left
              (hphase n hn) (abs_nonneg (u n - v n))
        _ = |u n - v n| := by simp

/-- The exact harmonic bound for the sieve modulus range, including
the zero index whose reciprocal is zero. -/
theorem sum_range_floor_inv_le_one_add_log (y : ℝ) (hy : 1 ≤ y) :
    (∑ d ∈ Finset.range (⌊y⌋₊ + 1), (d : ℝ)⁻¹) ≤
      1 + Real.log y := by
  let n : ℕ := ⌊y⌋₊
  have hset : Finset.range (n + 1) =
      insert 0 (Finset.Icc 1 n) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hEq : (∑ d ∈ Finset.range (n + 1), (d : ℝ)⁻¹) =
      (harmonic n : ℝ) := by
    rw [hset, Finset.sum_insert (by simp)]
    simp only [Nat.cast_zero, inv_zero, zero_add]
    symm
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [show ⌊y⌋₊ = n from rfl, hEq]
  exact_mod_cast harmonic_floor_le_one_add_log y hy

end FractionalPrimes

#print axioms FractionalPrimes.norm_weighted_progression_error_le
#print axioms FractionalPrimes.weightedIntervalProgressionApproximation
#print axioms FractionalPrimes.sieve_weighted_mean_from_multiple_counts
#print axioms FractionalPrimes.norm_phase_weight_replacement_le_L1
#print axioms FractionalPrimes.sum_range_floor_inv_le_one_add_log
