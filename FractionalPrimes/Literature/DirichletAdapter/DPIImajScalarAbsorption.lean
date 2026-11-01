module

public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
noncomputable section

/-- The single possible logarithmic Heath--Brown factor and the residue
count cost are paid by asking the IImaj branch for `A+22` savings. -/
theorem dpIImajScalarAbsorption
    {L A B c : ℝ} {k : ℕ} (hL : 1 ≤ L) (hk : k ≤ 1)
    (hc : |c| ≤ (2 : ℝ) ^ 10) :
    ‖(c : ℂ) * (((4 * L) ^ k : ℝ) : ℂ)‖ *
      L ^ (20 * B) * L ^ (-(A + 22 + 20 * B)) ≤
        (2 : ℝ) ^ 12 * L ^ (-(A + 21)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hfour : 0 ≤ 4 * L := by positivity
  have hscalar : ‖(c : ℂ) * (((4 * L) ^ k : ℝ) : ℂ)‖ ≤
      (2 : ℝ) ^ 12 * L := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hfour _)]
    have hc' : ‖c‖ ≤ (2 : ℝ) ^ 10 := by simpa [Real.norm_eq_abs] using hc
    interval_cases k
    · simp only [pow_zero, mul_one]
      nlinarith
    · simp only [pow_one]
      nlinarith
  have hpow : 0 ≤ L ^ (20 * B) * L ^ (-(A + 22 + 20 * B)) := by positivity
  calc
    _ ≤ ((2 : ℝ) ^ 12 * L) *
        (L ^ (20 * B) * L ^ (-(A + 22 + 20 * B))) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hscalar hpow
    _ = (2 : ℝ) ^ 12 * L ^ (-(A + 21)) := by
      calc
        (2 : ℝ) ^ 12 * L *
            (L ^ (20 * B) * L ^ (-(A + 22 + 20 * B))) =
            (2 : ℝ) ^ 12 *
              (L ^ (1 : ℝ) *
                (L ^ (20 * B) * L ^ (-(A + 22 + 20 * B)))) := by
          rw [Real.rpow_one]
          ring
        _ = (2 : ℝ) ^ 12 *
            L ^ (1 + (20 * B + -(A + 22 + 20 * B))) := by
          rw [Real.rpow_add hLpos, Real.rpow_add hLpos]
        _ = _ := by congr 1; ring_nf

#print axioms dpIImajScalarAbsorption
end
end FractionalPrimes.Literature.DirichletAdapter
