module

public import FractionalPrimes.ShortVariation

/-!
# Consecutive arithmetic-average increments

This module proves the source's operator-norm increment bounds for the
von Mangoldt and Möbius averages on every invertible measure-preserving
system, including the endpoint exponents.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem enorm_vonMangoldtWeight_succ_le_log_two_mul {m : ℕ}
    (hm : 1 ≤ m) :
    ‖(vonMangoldtWeight (m + 1) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.log (2 * (m : ℝ))) := by
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hcast : ((vonMangoldtWeight (m + 1) : ℝ) : ℂ) =
      (vonMangoldtWeight (m + 1) : ℂ) := by norm_cast
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldtWeight_nonneg (m + 1))]
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hle : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (by omega : m + 1 ≤ 2 * m)
  exact (vonMangoldtWeight_le_log (n := m + 1)).trans
    (Real.log_le_log hpos hle)

private theorem eLpNorm_vonMangoldtAverage_increment_term_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (m : ℕ) (hm : 1 ≤ m) {p : ℝ≥0∞}
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    eLpNorm ((vonMangoldtWeight (m + 1) : ℂ) •
      S.shift (floorPower c (m + 1)) f) p S.μ ≤
        ENNReal.ofReal (Real.log (2 * (m : ℝ))) * eLpNorm f p S.μ := by
  rw [eLpNorm_const_smul,
    eLpNorm_shift_floorPower S c (m + 1) hf.aestronglyMeasurable]
  exact mul_le_mul_of_nonneg_right
    (enorm_vonMangoldtWeight_succ_le_log_two_mul hm) bot_le

private theorem enorm_inv_natCast_succ (m : ℕ) :
    ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ =
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ)⁻¹) := by
  simpa using enorm_inv_natCast_scale (⟨m + 1, by omega⟩ : Scale)

private theorem mangoldtIncrementCoefficient {m : ℕ} (hm : 1 ≤ m) :
    ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * (m : ℝ)))) =
      ENNReal.ofReal
        (2 * Real.log (2 * (m : ℝ)) / ((m + 1 : ℕ) : ℝ)) := by
  rw [enorm_inv_natCast_succ,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_comm,
    ← ENNReal.ofReal_mul (by
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hlog : 0 ≤ Real.log (2 * (m : ℝ)) :=
        Real.log_nonneg (by nlinarith)
      positivity)]
  congr 1

private theorem eLpNorm_vonMangoldtAverage_increment_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) (m : ℕ) (hm : 1 ≤ m)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : X → ℂ) (hf : MemLp f p S.μ) :
    eLpNorm
      (vonMangoldtAverage S c.value f ⟨m + 1, by omega⟩ -
        vonMangoldtAverage S c.value f ⟨m, hm⟩) p S.μ ≤
      ENNReal.ofReal
        (2 * Real.log (2 * (m : ℝ)) / ((m + 1 : ℕ) : ℝ)) *
        eLpNorm f p S.μ := by
  have hfmeas := hf.aestronglyMeasurable
  have hidentity :
      vonMangoldtAverage S c.value f ⟨m + 1, by omega⟩ -
        vonMangoldtAverage S c.value f ⟨m, hm⟩ =
      ((m + 1 : ℂ)⁻¹) •
        ((vonMangoldtWeight (m + 1) : ℂ) •
          S.shift (floorPower c.value (m + 1)) f -
          vonMangoldtAverage S c.value f ⟨m, hm⟩) := by
    simpa only [vonMangoldtAverage] using
      (weightedAverage_succ_sub_endpoint S c.value
        (fun n => (vonMangoldtWeight n : ℂ)) f m hm)
  have haverage :
      eLpNorm (vonMangoldtAverage S c.value f ⟨m, hm⟩) p S.μ ≤
        ENNReal.ofReal (Real.log (2 * (m : ℝ))) * eLpNorm f p S.μ := by
    exact eLpNorm_vonMangoldtAverage_le_log_two_mul S c.value f
      ⟨m, hm⟩ hp hfmeas
  have hterm := eLpNorm_vonMangoldtAverage_increment_term_le
    S c.value m hm f hf
  have hdiff :
      eLpNorm
        ((vonMangoldtWeight (m + 1) : ℂ) •
          S.shift (floorPower c.value (m + 1)) f -
          vonMangoldtAverage S c.value f ⟨m, hm⟩) p S.μ ≤
        2 * ENNReal.ofReal (Real.log (2 * (m : ℝ))) *
          eLpNorm f p S.μ := by
    calc
      _ ≤ eLpNorm ((vonMangoldtWeight (m + 1) : ℂ) •
            S.shift (floorPower c.value (m + 1)) f) p S.μ +
          eLpNorm (vonMangoldtAverage S c.value f ⟨m, hm⟩) p S.μ :=
        eLpNorm_sub_le hp
      _ ≤ ENNReal.ofReal (Real.log (2 * (m : ℝ))) * eLpNorm f p S.μ +
          ENNReal.ofReal (Real.log (2 * (m : ℝ))) * eLpNorm f p S.μ :=
        add_le_add hterm haverage
      _ = _ := by ring
  calc
    _ = ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ *
        eLpNorm
          ((vonMangoldtWeight (m + 1) : ℂ) •
            S.shift (floorPower c.value (m + 1)) f -
            vonMangoldtAverage S c.value f ⟨m, hm⟩) p S.μ := by
          rw [hidentity, eLpNorm_const_smul]
          congr 2
          push_cast
          rfl
    _ ≤ ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * (m : ℝ))) *
          eLpNorm f p S.μ) := mul_le_mul_of_nonneg_left hdiff bot_le
    _ = _ := by
      rw [← mul_assoc, mangoldtIncrementCoefficient hm]

private theorem mobiusIncrementCoefficient {m : ℕ} :
    ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ * 2 =
      ENNReal.ofReal (2 / ((m + 1 : ℕ) : ℝ)) := by
  rw [enorm_inv_natCast_succ,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    mul_comm, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  congr 1

private theorem eLpNorm_mobiusAverage_increment_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) (m : ℕ) (hm : 1 ≤ m)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : X → ℂ) (hf : MemLp f p S.μ) :
    eLpNorm
      (mobiusAverage S c.value f ⟨m + 1, by omega⟩ -
        mobiusAverage S c.value f ⟨m, hm⟩) p S.μ ≤
      ENNReal.ofReal (2 / ((m + 1 : ℕ) : ℝ)) * eLpNorm f p S.μ := by
  have hfmeas := hf.aestronglyMeasurable
  have hidentity :
      mobiusAverage S c.value f ⟨m + 1, by omega⟩ -
        mobiusAverage S c.value f ⟨m, hm⟩ =
      ((m + 1 : ℂ)⁻¹) •
        ((mobiusWeight (m + 1) : ℂ) •
          S.shift (floorPower c.value (m + 1)) f -
          mobiusAverage S c.value f ⟨m, hm⟩) := by
    simpa only [mobiusAverage] using
      (weightedAverage_succ_sub_endpoint S c.value
        (fun n => (mobiusWeight n : ℂ)) f m hm)
  have haverage := eLpNorm_mobiusAverage_le_self S c.value f ⟨m, hm⟩ hp hfmeas
  have hterm :
      eLpNorm ((mobiusWeight (m + 1) : ℂ) •
        S.shift (floorPower c.value (m + 1)) f) p S.μ ≤ eLpNorm f p S.μ := by
    rw [eLpNorm_const_smul,
      eLpNorm_shift_floorPower S c.value (m + 1) hfmeas]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (enorm_mobiusWeight_le_one (m + 1)) bot_le)
  have hdiff :
      eLpNorm
        ((mobiusWeight (m + 1) : ℂ) •
          S.shift (floorPower c.value (m + 1)) f -
          mobiusAverage S c.value f ⟨m, hm⟩) p S.μ ≤
        2 * eLpNorm f p S.μ := by
    calc
      _ ≤ eLpNorm ((mobiusWeight (m + 1) : ℂ) •
            S.shift (floorPower c.value (m + 1)) f) p S.μ +
          eLpNorm (mobiusAverage S c.value f ⟨m, hm⟩) p S.μ :=
        eLpNorm_sub_le hp
      _ ≤ eLpNorm f p S.μ + eLpNorm f p S.μ := add_le_add hterm haverage
      _ = _ := by ring
  calc
    _ = ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ *
        eLpNorm
          ((mobiusWeight (m + 1) : ℂ) •
            S.shift (floorPower c.value (m + 1)) f -
            mobiusAverage S c.value f ⟨m, hm⟩) p S.μ := by
          rw [hidentity, eLpNorm_const_smul]
          congr 2
          push_cast
          rfl
    _ ≤ ‖((m + 1 : ℕ) : ℂ)⁻¹‖ₑ *
        (2 * eLpNorm f p S.μ) := mul_le_mul_of_nonneg_left hdiff bot_le
    _ = _ := by rw [← mul_assoc, mobiusIncrementCoefficient]

/-- The exact consecutive increment bounds for the von Mangoldt and Möbius
averages. These are the source's operator-norm inequalities, expressed on
`Lᵖ` representatives; the exponent range includes `p=∞`. -/
theorem weightedAverageIncrementBounds
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) (m : ℕ) (hm : 1 ≤ m)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : X → ℂ) (hf : MemLp f p S.μ) :
    eLpNorm
        (vonMangoldtAverage S c.value f ⟨m + 1, by omega⟩ -
          vonMangoldtAverage S c.value f ⟨m, hm⟩) p S.μ ≤
      ENNReal.ofReal
        (2 * Real.log (2 * (m : ℝ)) / ((m + 1 : ℕ) : ℝ)) *
        eLpNorm f p S.μ ∧
    eLpNorm
        (mobiusAverage S c.value f ⟨m + 1, by omega⟩ -
          mobiusAverage S c.value f ⟨m, hm⟩) p S.μ ≤
      ENNReal.ofReal (2 / ((m + 1 : ℕ) : ℝ)) * eLpNorm f p S.μ := by
  exact ⟨eLpNorm_vonMangoldtAverage_increment_le S c m hm hp f hf,
    eLpNorm_mobiusAverage_increment_le S c m hm hp f hf⟩

end

end FractionalPrimes

end
