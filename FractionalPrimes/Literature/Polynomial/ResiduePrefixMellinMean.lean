module
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixMellinIndices
public import FractionalPrimes.Literature.Twisted.FullFrequencyMellinData
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.Polynomial
open scoped BigOperators
open FractionalPrimes.Literature.Twisted

theorem fullFrequencyMellinMean_eq_residuePrefix
    (d : FullFrequencyMellinData) (X H q b : ℕ) (w : ℤ → ℂ)
    (hX : d.X = (X : ℝ)) (hH : d.H = (H : ℝ))
    (hcoeff : ∀ n : ℕ, d.a n = w (n : ℤ) *
      (if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0)) :
    fullFrequencyMellinMean d = ((H : ℝ)⁻¹ : ℂ) * residuePrefixSum X H q b w := by
  unfold fullFrequencyMellinMean
  rw [hX, hH, residuePrefixSum_eq_mellinWindowSum, Complex.ofReal_inv]
  congr 1
  exact Finset.sum_congr rfl (fun n hn => hcoeff n)

/-- Recovery of the unnormalized prefix bound from the exact normalized mean. -/
theorem residuePrefixSum_norm_le_of_fullFrequencyMean
    (d : FullFrequencyMellinData) (X H q b : ℕ) (w : ℤ → ℂ)
    (hHpos : 0 < H) (hX : d.X = (X : ℝ)) (hH : d.H = (H : ℝ))
    (hcoeff : ∀ n : ℕ, d.a n = w (n : ℤ) *
      (if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0))
    {B : ℝ} (hmean : ‖fullFrequencyMellinMean d‖ ≤ B) :
    ‖residuePrefixSum X H q b w‖ ≤ (H : ℝ) * B := by
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hHpos
  have hEq := fullFrequencyMellinMean_eq_residuePrefix d X H q b w hX hH hcoeff
  have hnorm : ‖fullFrequencyMellinMean d‖ =
      (H : ℝ)⁻¹ * ‖residuePrefixSum X H q b w‖ := by
    rw [hEq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hHR]
  calc
    _ = (H : ℝ) * ‖fullFrequencyMellinMean d‖ := by
      rw [hnorm]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean hHR.le

#print axioms fullFrequencyMellinMean_eq_residuePrefix
#print axioms residuePrefixSum_norm_le_of_fullFrequencyMean
end FractionalPrimes.Literature.Polynomial
end
