module

public import FractionalPrimes.ShortVariation
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
namespace FractionalPrimes
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The exact bounded-input gap estimate used between the slow subsequence
scales in `er:mobius-dense`. -/
theorem boundedPrefixAverage_gap_le
    (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) {M N : ℕ}
    (hM : 0 < M) (hMN : M ≤ N)
    (ha : ∀ n ∈ Finset.Ioc 0 N, ‖a n‖ ≤ B) :
    ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.Ioc 0 N, a n) -
      (M : ℂ)⁻¹ * (∑ n ∈ Finset.Ioc 0 M, a n)‖ ≤
        2 * ((N : ℝ) - M) / N * B := by
  have hN : 0 < N := hM.trans_le hMN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMNReal : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  let V : ℂ := (M : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 M, a n
  have hprefix : ‖∑ n ∈ Finset.Ioc 0 M, a n‖ ≤ (M : ℝ) * B := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc 0 M, ‖a n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc 0 M, B := by
        apply Finset.sum_le_sum
        intro n hn
        exact ha n (Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hMN⟩)
      _ = _ := by simp
  have hV : ‖V‖ ≤ B := by
    dsimp [V]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (M : ℝ)⁻¹ * ((M : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hprefix (inv_nonneg.mpr hMR.le)
      _ = B := by field_simp
  have htail : ‖∑ n ∈ Finset.Ioc M N, a n‖ ≤ ((N : ℝ) - M) * B := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc M N, ‖a n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc M N, B := by
        apply Finset.sum_le_sum
        intro n hn
        exact ha n (Finset.mem_Ioc.mpr
          ⟨hM.trans_le (Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
      _ = _ := by simp [Nat.cast_sub hMN]
  have hid : (N : ℂ)⁻¹ * (∑ n ∈ Finset.Ioc 0 N, a n) - V =
      (N : ℂ)⁻¹ * ((∑ n ∈ Finset.Ioc M N, a n) - ((N - M : ℕ) : ℂ) * V) := by
    rw [← Finset.sum_Ioc_consecutive a (Nat.zero_le M) hMN]
    dsimp [V]
    push_cast [Nat.cast_sub hMN]
    field_simp
    <;> ring
  change ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.Ioc 0 N, a n) - V‖ ≤ _
  rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
  have htailDiff : ‖(∑ n ∈ Finset.Ioc M N, a n) - ((N - M : ℕ) : ℂ) * V‖ ≤
      2 * ((N : ℝ) - M) * B := by
    calc
      _ ≤ ‖∑ n ∈ Finset.Ioc M N, a n‖ + ‖((N - M : ℕ) : ℂ) * V‖ := norm_sub_le _ _
      _ ≤ ((N : ℝ) - M) * B + ((N : ℝ) - M) * B := by
        rw [norm_mul, Complex.norm_natCast, Nat.cast_sub hMN]
        exact add_le_add htail (mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr hMNReal))
      _ = _ := by ring
  calc
    _ ≤ (N : ℝ)⁻¹ * (2 * ((N : ℝ) - M) * B) :=
      mul_le_mul_of_nonneg_left htailDiff (inv_nonneg.mpr hNR.le)
    _ = _ := by ring

#print axioms boundedPrefixAverage_gap_le
end
end FractionalPrimes
