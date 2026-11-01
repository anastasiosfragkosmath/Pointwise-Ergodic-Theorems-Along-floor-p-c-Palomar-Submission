module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorTailIntegral
public import FractionalPrimes.Literature.Uniformity.LogAbsorption

/-! The polylogarithmic scale absorption in the `lda:type-i` branch. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The Type-I frequency-range and long-factor scale assumptions reduce
the quadrature error ratio to one explicit polylogarithmic factor. -/
theorem smoothLongFactor_scale_ratio_le_polylog
    (X W U N η B D : ℝ) (q : ℕ)
    (hX : 3 ≤ X) (hW : W = (Real.log X) ^ D)
    (hUone : 1 ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hN : (2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ) ≤ N)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (q : ℝ) * (1 + U) / N ≤
      (2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) * X ^ (-η) := by
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hNpos : 0 < N := by
    have hlow : 0 < (2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ) := by positivity
    linarith
  have hW4 : W ^ (4 : ℕ) = (Real.log X) ^ (4 * D) := by
    calc
      W ^ (4 : ℕ) = ((Real.log X) ^ D) ^ (4 : ℝ) := by
        simpa [hW] using (Real.rpow_natCast ((Real.log X) ^ D) 4).symm
      _ = (Real.log X) ^ (D * 4) := (Real.rpow_mul hLpos.le D 4).symm
      _ = (Real.log X) ^ (4 * D) := by congr 1; ring
  have hXpow : X ^ ((3 / 8 : ℝ) - η) =
      X ^ (3 / 8 : ℝ) * X ^ (-η) := by
    rw [sub_eq_add_neg, Real.rpow_add hXpos]
  have hLpow : (Real.log X) ^ B * (Real.log X) ^ (4 * D) =
      (Real.log X) ^ (B + 4 * D) :=
    (Real.rpow_add hLpos B (4 * D)).symm
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hUpos : 0 ≤ U := by linarith
  have hnum : (q : ℝ) * (1 + U) ≤
      2 * (Real.log X) ^ B *
        (X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ)) := by
    calc
      (q : ℝ) * (1 + U) ≤ 2 * (q : ℝ) * U := by nlinarith
      _ ≤ 2 * (Real.log X) ^ B *
            (X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ)) := by
          gcongr
  have hscale :
      2 * (Real.log X) ^ B *
          (X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ)) =
        ((2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) * X ^ (-η)) *
          ((2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ)) := by
    rw [hW4, hXpow]
    have htwo : (2 : ℝ) ^ (23 : ℕ) * (2 : ℝ) ^ (-(22 : ℝ)) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← hLpow]
    calc
      2 * (Real.log X) ^ B *
          ((X ^ (3 / 8 : ℝ) * X ^ (-η)) * (Real.log X) ^ (4 * D)) =
        ((2 : ℝ) ^ (23 : ℕ) * (2 : ℝ) ^ (-(22 : ℝ))) *
          ((Real.log X) ^ B * (Real.log X) ^ (4 * D)) *
            X ^ (-η) * X ^ (3 / 8 : ℝ) := by rw [htwo]; ring
      _ = _ := by ring
  apply (div_le_iff₀ hNpos).mpr
  calc
    (q : ℝ) * (1 + U) ≤
        2 * (Real.log X) ^ B *
          (X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ)) := hnum
    _ = ((2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) * X ^ (-η)) *
          ((2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ)) := hscale
    _ ≤ ((2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) * X ^ (-η)) * N :=
      mul_le_mul_of_nonneg_left hN (by positivity)

/-- The exact power saving required by the Type-I quadrature term,
with the explicit logarithmic threshold from `lu:elementary-growth`. -/
theorem smoothLongFactor_scale_ratio_le_power
    (X W U N η B D : ℝ) (q : ℕ)
    (hX : 3 ≤ X) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hW : W = (Real.log X) ^ D)
    (hUone : 1 ≤ U)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hN : (2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ) ≤ N)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B)
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X) :
    (q : ℝ) * (1 + U) / N ≤ X ^ (-(η / 4)) := by
  have hXpos : 0 < X := by linarith
  have ha : 0 < 3 * η / 4 := by positivity
  have hb : 0 ≤ B + 4 * D := by linarith
  have hAbs := Uniformity.log_absorption_bound
    (a := 3 * η / 4) (b := B + 4 * D)
    (K := (2 : ℝ) ^ (23 : ℕ)) (X := X)
    ha hb (by norm_num) (by linarith) hlarge
  have hpow : X ^ (3 * η / 4) * X ^ (-η) = X ^ (-(η / 4)) := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  calc
    (q : ℝ) * (1 + U) / N ≤
        (2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) * X ^ (-η) :=
      smoothLongFactor_scale_ratio_le_polylog X W U N η B D q hX hW hUone hU hN hq
    _ ≤ X ^ (3 * η / 4) * X ^ (-η) :=
      mul_le_mul_of_nonneg_right hAbs (by positivity)
    _ = X ^ (-(η / 4)) := hpow

/-- Under the same polylogarithmic absorption, the paper's upper
frequency endpoint is at most `X`. -/
theorem smoothLongFactor_frequency_upper_le_X
    (X W U η B D : ℝ)
    (hX : 3 ≤ X) (hη : 0 < η) (hB : 0 ≤ B)
    (hlog : 1 ≤ Real.log X)
    (hW : W = (Real.log X) ^ D)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hAbs : (2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) ≤
      X ^ (3 * η / 4)) :
    U ≤ X := by
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := by linarith
  have hW4 : W ^ (4 : ℕ) = (Real.log X) ^ (4 * D) := by
    calc
      W ^ (4 : ℕ) = ((Real.log X) ^ D) ^ (4 : ℝ) := by
        simpa [hW] using (Real.rpow_natCast ((Real.log X) ^ D) 4).symm
      _ = (Real.log X) ^ (D * 4) := (Real.rpow_mul hLpos.le D 4).symm
      _ = (Real.log X) ^ (4 * D) := by congr 1; ring
  have hWle : W ^ (4 : ℕ) ≤ X ^ (3 * η / 4) := by
    rw [hW4]
    have h1 : (Real.log X) ^ (4 * D) ≤
        (Real.log X) ^ (B + 4 * D) :=
      Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
    have h2 : (Real.log X) ^ (B + 4 * D) ≤
        (2 : ℝ) ^ (23 : ℕ) * (Real.log X) ^ (B + 4 * D) := by
      have hp : 0 ≤ (Real.log X) ^ (B + 4 * D) := by positivity
      nlinarith [hp]
    exact h1.trans (h2.trans hAbs)
  have hpow : X ^ ((3 / 8 : ℝ) - η) * X ^ (3 * η / 4) =
      X ^ ((3 / 8 : ℝ) - η / 4) := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  have hexp : (3 / 8 : ℝ) - η / 4 ≤ 1 := by linarith
  calc
    U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ) := hU
    _ ≤ X ^ ((3 / 8 : ℝ) - η) * X ^ (3 * η / 4) :=
      mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = X ^ ((3 / 8 : ℝ) - η / 4) := hpow
    _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = X := by simp

/-- The explicit threshold form of the frequency cap, reusing the
same `lu:elementary-growth` condition as the scale-ratio estimate. -/
theorem smoothLongFactor_frequency_upper_le_X_of_threshold
    (X W U η B D : ℝ)
    (hX : 3 ≤ X) (hXexp : Real.exp 1 ≤ X)
    (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hW : W = (Real.log X) ^ D)
    (hU : U ≤ X ^ ((3 / 8 : ℝ) - η) * W ^ (4 : ℕ))
    (hlarge :
      (2 / (3 * η / 4)) * Real.log
        ((2 : ℝ) ^ (23 : ℕ) *
          Uniformity.logAbsorptionM (3 * η / 4) (B + 4 * D)) ≤ Real.log X) :
    U ≤ X := by
  have hlog : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hXexp
    simpa only [Real.log_exp] using h
  have hAbs := Uniformity.log_absorption_bound
    (a := 3 * η / 4) (b := B + 4 * D)
    (K := (2 : ℝ) ^ (23 : ℕ)) (X := X)
    (by positivity) (by linarith) (by norm_num) (by linarith) hlarge
  exact smoothLongFactor_frequency_upper_le_X X W U η B D
    hX hη hB hlog hW hU hAbs

#print axioms smoothLongFactor_scale_ratio_le_polylog
#print axioms smoothLongFactor_scale_ratio_le_power
#print axioms smoothLongFactor_frequency_upper_le_X
#print axioms smoothLongFactor_frequency_upper_le_X_of_threshold

end FractionalPrimes.Literature.DirichletAdapter

end
