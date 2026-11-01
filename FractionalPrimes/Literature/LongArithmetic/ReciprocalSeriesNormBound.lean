module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.LSeries.Basic
public import FractionalPrimes.Literature.LongArithmetic.ReciprocalSeriesTransferScalar

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.LongArithmetic

/-- A bounded Dirichlet series on a real line to the right of one is bounded
by the elementary integral-test estimate `1 + 1/(v-1)`. -/
theorem LSeries_norm_le_integral_test
    {f : ℕ → ℂ} (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ 1)
    {v t : ℝ} (hv : 1 < v) :
    ‖LSeries f ((v : ℂ) + Complex.I * (t : ℂ))‖ ≤
      1 + 1 / (v - 1) := by
  let s : ℂ := (v : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s.re = v := by simp [s]
  have hseries : LSeriesSummable f s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      exact hf n hn
    · simpa [s] using hv
  have hnormSeries : Summable (fun n : ℕ => ‖LSeries.term f s n‖) := hseries.norm
  have hpower : Summable (fun n : ℕ => (n : ℝ) ^ (-v)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm (n : ℕ) :
      ‖LSeries.term f s n‖ ≤ (n : ℝ) ^ (-v) := by
    by_cases hn : n = 0
    · subst n
      simp [Real.zero_rpow (by linarith : -v ≠ 0)]
    · rw [LSeries.norm_term_eq, if_neg hn, hsRe]
      have hcoeff : ‖f n‖ ≤ 1 := hf n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      calc
        ‖f n‖ / (n : ℝ) ^ v ≤ 1 / (n : ℝ) ^ v :=
          div_le_div_of_nonneg_right hcoeff (Real.rpow_nonneg hnpos.le _)
        _ = (n : ℝ) ^ (-v) := by
          rw [Real.rpow_neg hnpos.le]
          simp [one_div]
  have hsumBound : (∑' n : ℕ, (n : ℝ) ^ (-v)) ≤ 1 + 1 / (v - 1) := by
    have hanti : AntitoneOn (fun y : ℝ => y ^ (-v))
        (Set.Ici (↑(1 : ℕ) : ℝ)) := by
      intro y hy z hz hyz
      have hyI : (1 : ℝ) ≤ y := by simpa using hy
      have hzI : (1 : ℝ) ≤ z := by simpa using hz
      have hy' : 0 < y := lt_of_lt_of_le zero_lt_one hyI
      have hz' : 0 < z := lt_of_lt_of_le zero_lt_one hzI
      exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -v ≤ 0))
        hy' hz' hyz
    have hint : IntegrableOn (fun y : ℝ => y ^ (-v))
        (Set.Ioi (↑(1 : ℕ) : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    have hnonneg : ∀ y ∈ Set.Ioi (↑(1 : ℕ) : ℝ), 0 ≤ y ^ (-v) := by
      intro y hy
      have hyI : (1 : ℝ) < y := by simpa using hy
      exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hyI)) _
    have htail := AntitoneOn.tsum_comp_add_le_integral
      (f := fun y : ℝ => y ^ (-v)) (1 : ℕ) hanti hint hnonneg
    have hsplit := hpower.sum_add_tsum_nat_add 2
    have hfinite : (∑ n ∈ Finset.range 2, (n : ℝ) ^ (-v)) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp only [Nat.cast_zero, Nat.cast_one, Real.zero_rpow (by linarith : -v ≠ 0),
        zero_add]
      norm_num
    have hinterval : (∫ y : ℝ in Set.Ioi (↑(1 : ℕ) : ℝ), y ^ (-v)) =
        1 / (v - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
      norm_num
      simpa only [one_div] using transfer_integral_denominator_identity hv
    rw [hfinite] at hsplit
    rw [← hsplit]
    have htail' : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-v)) ≤ 1 / (v - 1) := by
      calc
        _ ≤ ∫ y : ℝ in Set.Ioi (↑(1 : ℕ) : ℝ), y ^ (-v) := by
          simpa [Nat.add_assoc] using htail
        _ = 1 / (v - 1) := hinterval
    simpa [add_comm] using add_le_add_left htail' 1
  change ‖∑' n : ℕ, LSeries.term f s n‖ ≤ 1 + 1 / (v - 1)
  exact (norm_tsum_le_tsum_norm hnormSeries).trans
    ((Summable.tsum_le_tsum hterm hnormSeries hpower).trans hsumBound)

end FractionalPrimes.Literature.LongArithmetic

#print axioms FractionalPrimes.Literature.LongArithmetic.LSeries_norm_le_integral_test

end
