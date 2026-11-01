module

public import FractionalPrimes.ArithmeticBasics
public import FractionalPrimes.WeightedLpAverages

/-!
# Finite von Mangoldt averages in `L^p`

This is the first quantitative estimate in the blueprint. It combines the
elementary coefficient bound with measure-preserving isometry and finite
Minkowski; it does not use the main variation theorem.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Each von Mangoldt coefficient through scale `N` is bounded by `log (2N)`. -/
theorem enorm_vonMangoldtWeight_le_log_two_mul {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖(vonMangoldtWeight n : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.log (2 * (N : ℝ))) := by
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hcast : ((vonMangoldtWeight n : ℝ) : ℂ) =
      (vonMangoldtWeight n : ℂ) := by norm_cast
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldtWeight_nonneg n)]
  apply (vonMangoldtWeight_le_log (n := n)).trans
  apply Real.log_le_log
  · exact_mod_cast hn
  · exact_mod_cast (le_trans hnN (by omega : N ≤ 2 * N))

/-- The finite von Mangoldt average has the blueprint's elementary logarithmic
`L^p` bound. -/
theorem eLpNorm_vonMangoldtAverage_le_log_two_mul
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (vonMangoldtAverage S c f N) p S.μ ≤
      ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) * eLpNorm f p S.μ := by
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.log (2 * (N.1 : ℝ)))
  calc
    eLpNorm (vonMangoldtAverage S c f N) p S.μ ≤
        ‖(N.1 : ℂ)⁻¹‖ₑ *
          ∑ n ∈ Finset.Icc 1 N.1,
            ‖(vonMangoldtWeight n : ℂ)‖ₑ * eLpNorm f p S.μ := by
          simpa only [vonMangoldtAverage] using
            (eLpNorm_weightedAverage_le S c
              (fun n => (vonMangoldtWeight n : ℂ)) f N hp hf)
    _ ≤ ‖(N.1 : ℂ)⁻¹‖ₑ *
          ∑ n ∈ Finset.Icc 1 N.1, L * eLpNorm f p S.μ := by
          apply mul_le_mul_of_nonneg_left _ bot_le
          apply Finset.sum_le_sum
          intro n hn
          apply mul_le_mul_of_nonneg_right _ bot_le
          exact enorm_vonMangoldtWeight_le_log_two_mul
            (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    _ = ‖(N.1 : ℂ)⁻¹‖ₑ *
          ((N.1 : ℝ≥0∞) * L * eLpNorm f p S.μ) := by
          rw [Finset.sum_const]
          simp [Nat.card_Icc, L, mul_assoc]
    _ = L * eLpNorm f p S.μ := by
          have hN : (N.1 : ℕ) ≠ 0 := N.2.ne'
          have hNc : (N.1 : ℂ) ≠ 0 := by exact_mod_cast hN
          have hNenn : (N.1 : ℝ≥0∞) ≠ 0 := by exact_mod_cast N.2.ne'
          have hnorm : ‖(N.1 : ℂ)‖ₑ = (N.1 : ℝ≥0∞) := by simp [enorm]
          rw [enorm_inv hNc, hnorm]
          calc
            (N.1 : ℝ≥0∞)⁻¹ *
                ((N.1 : ℝ≥0∞) * L * eLpNorm f p S.μ) =
              ((N.1 : ℝ≥0∞)⁻¹ * (N.1 : ℝ≥0∞)) *
                L * eLpNorm f p S.μ := by simp only [mul_assoc]
            _ = L * eLpNorm f p S.μ := by
              rw [ENNReal.inv_mul_cancel hNenn ENNReal.coe_ne_top]
              simp

/-- The finite von Mangoldt average has the exact endpoint bound prescribed
by the blueprint. -/
theorem eLpNorm_vonMangoldtAverage_le_log
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (vonMangoldtAverage S c f N) p S.μ ≤
      ENNReal.ofReal (Real.log (N.1 : ℝ)) * eLpNorm f p S.μ := by
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hnorm (n : ℕ) : ‖(vonMangoldtWeight n : ℂ)‖ₑ =
      ENNReal.ofReal (vonMangoldtWeight n) := by
    rw [← ofReal_norm]
    have hcast : ((vonMangoldtWeight n : ℝ) : ℂ) =
        (vonMangoldtWeight n : ℂ) := by norm_cast
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vonMangoldtWeight_nonneg n)]
  have hsumENN :
      (∑ n ∈ Finset.Icc 1 N.1, ‖(vonMangoldtWeight n : ℂ)‖ₑ) =
        ENNReal.ofReal (∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) := by
    calc
      (∑ n ∈ Finset.Icc 1 N.1, ‖(vonMangoldtWeight n : ℂ)‖ₑ) =
          ∑ n ∈ Finset.Icc 1 N.1, ENNReal.ofReal (vonMangoldtWeight n) := by
            apply Finset.sum_congr rfl
            intro n _
            exact hnorm n
      _ = ENNReal.ofReal (∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) := by
            symm
            apply ENNReal.ofReal_sum_of_nonneg
            intro n _
            exact vonMangoldtWeight_nonneg n
  have hN : (N.1 : ℕ) ≠ 0 := by omega
  have hInv : ‖(N.1 : ℂ)⁻¹‖ₑ = ENNReal.ofReal ((N.1 : ℝ)⁻¹) := by
    have hNc : (N.1 : ℂ) ≠ 0 := by exact_mod_cast hN
    rw [enorm_inv hNc, ENNReal.ofReal_inv_of_pos hNpos]
    congr 1
    simp [enorm]
  calc
    eLpNorm (vonMangoldtAverage S c f N) p S.μ ≤
        ‖(N.1 : ℂ)⁻¹‖ₑ * ∑ n ∈ Finset.Icc 1 N.1,
          ‖(vonMangoldtWeight n : ℂ)‖ₑ * eLpNorm f p S.μ := by
      simpa only [vonMangoldtAverage] using
        eLpNorm_weightedAverage_le S c (fun n => (vonMangoldtWeight n : ℂ)) f N hp hf
    _ = ENNReal.ofReal ((N.1 : ℝ)⁻¹ *
          ∑ n ∈ Finset.Icc 1 N.1, vonMangoldtWeight n) * eLpNorm f p S.μ := by
      rw [← Finset.sum_mul, hsumENN, hInv, ← mul_assoc,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hNpos.le)]
    _ ≤ ENNReal.ofReal (Real.log (N.1 : ℝ)) * eLpNorm f p S.μ := by
      gcongr
      exact normalizedVonMangoldtWeight_sum_le_log N

/-- The two scalar coefficients in the consecutive von Mangoldt average
increment have the exact summable majorant used in the blueprint. -/
theorem vonMangoldt_increment_coeff_le (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ)⁻¹ - (m + 1 : ℝ)⁻¹) *
        (∑ n ∈ Finset.Icc 1 m, vonMangoldtWeight n) +
      (m + 1 : ℝ)⁻¹ * vonMangoldtWeight (m + 1) ≤
    2 * Real.log (2 * (m : ℝ)) / (m + 1 : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
  have hm1pos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
  have hsum := vonMangoldtWeight_sum_le_size_mul_log (⟨m, by omega⟩ : Scale)
  have hsum' : (∑ n ∈ Finset.Icc 1 m, vonMangoldtWeight n) ≤
      (m : ℝ) * Real.log (m : ℝ) := by simpa using hsum
  have hendpoint : vonMangoldtWeight (m + 1) ≤ Real.log (m + 1 : ℝ) := by
    simpa using (vonMangoldtWeight_le_log (n := m + 1))
  have hinv_diff : (m : ℝ)⁻¹ - (m + 1 : ℝ)⁻¹ =
      (m : ℝ)⁻¹ * (m + 1 : ℝ)⁻¹ := by
    field_simp
    <;> ring
  have hdiff : 0 ≤ (m : ℝ)⁻¹ - (m + 1 : ℝ)⁻¹ := by
    rw [hinv_diff]
    positivity
  have hsum_bound := mul_le_mul_of_nonneg_left hsum' hdiff
  have hendpoint_bound :=
    mul_le_mul_of_nonneg_left hendpoint (le_of_lt (inv_pos.mpr hm1pos))
  have hmle : (m : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have hm1le : (m + 1 : ℝ) ≤ 2 * (m : ℝ) := by
    have hm1nat : m + 1 ≤ 2 * m := by omega
    exact_mod_cast hm1nat
  have hlogm : Real.log (m : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log hmpos hmle
  have hlogm1 : Real.log (m + 1 : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log hm1pos hm1le
  have hlogs : Real.log (m : ℝ) + Real.log (m + 1 : ℝ) ≤
      2 * Real.log (2 * (m : ℝ)) := by linarith
  have hcombine :
      ((m : ℝ)⁻¹ - (m + 1 : ℝ)⁻¹) * ((m : ℝ) * Real.log (m : ℝ)) +
        (m + 1 : ℝ)⁻¹ * Real.log (m + 1 : ℝ) ≤
      2 * Real.log (2 * (m : ℝ)) / (m + 1 : ℝ) := by
    have hidentity :
        ((m : ℝ)⁻¹ - (m + 1 : ℝ)⁻¹) * ((m : ℝ) * Real.log (m : ℝ)) +
          (m + 1 : ℝ)⁻¹ * Real.log (m + 1 : ℝ) =
        (m + 1 : ℝ)⁻¹ * (Real.log (m : ℝ) + Real.log (m + 1 : ℝ)) := by
      rw [hinv_diff]
      field_simp
      <;> ring
    rw [hidentity]
    calc
      (m + 1 : ℝ)⁻¹ * (Real.log (m : ℝ) + Real.log (m + 1 : ℝ)) ≤
          (m + 1 : ℝ)⁻¹ * (2 * Real.log (2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogs (le_of_lt (inv_pos.mpr hm1pos))
      _ = 2 * Real.log (2 * (m : ℝ)) / (m + 1 : ℝ) := by ring
  calc
    _ ≤ ((m : ℝ)⁻¹ - (m + 1 : ℝ)⁻¹) * ((m : ℝ) * Real.log (m : ℝ)) +
          (m + 1 : ℝ)⁻¹ * Real.log (m + 1 : ℝ) :=
      add_le_add hsum_bound hendpoint_bound
    _ ≤ _ := hcombine

end

end FractionalPrimes

end
