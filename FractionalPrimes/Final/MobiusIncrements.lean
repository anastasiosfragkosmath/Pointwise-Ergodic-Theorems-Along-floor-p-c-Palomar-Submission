module
public import FractionalPrimes.Final.WeightedLpAverages
public import FractionalPrimes.ShortVariation
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open scoped ENNReal
noncomputable section
theorem eLpNorm_mobiusAverage_le_self
    {X : Type*} [MeasurableSpace X] (S : System X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (mobiusAverage S c f N) p S.μ ≤ eLpNorm f p S.μ := by
  have hbound := eLpNorm_weightedAverage_le S c
    (fun n => (mobiusWeight n : ℂ)) f N hp hf
  have hsum :
      ∑ n ∈ Finset.Icc 1 N.1,
        ‖(mobiusWeight n : ℂ)‖ₑ * eLpNorm f p S.μ ≤
      ∑ _n ∈ Finset.Icc 1 N.1, eLpNorm f p S.μ := by
    apply Finset.sum_le_sum
    intro n hn
    calc
      ‖(mobiusWeight n : ℂ)‖ₑ * eLpNorm f p S.μ ≤
          1 * eLpNorm f p S.μ :=
        mul_le_mul_of_nonneg_right (enorm_mobiusWeight_le_one n) bot_le
      _ = eLpNorm f p S.μ := one_mul _
  calc
    eLpNorm (mobiusAverage S c f N) p S.μ ≤
        ‖(N.1 : ℂ)⁻¹‖ₑ *
          ∑ n ∈ Finset.Icc 1 N.1,
            ‖(mobiusWeight n : ℂ)‖ₑ * eLpNorm f p S.μ := by
          simpa only [mobiusAverage] using hbound
    _ ≤ ‖(N.1 : ℂ)⁻¹‖ₑ *
          ∑ _n ∈ Finset.Icc 1 N.1, eLpNorm f p S.μ :=
        mul_le_mul_of_nonneg_left hsum bot_le
    _ = eLpNorm f p S.μ := by
      rw [enorm_inv_natCast_scale]
      have hNreal : (0 : ℝ) < (N.1 : ℝ) := by exact_mod_cast N.2
      have hNenn : (N.1 : ℝ≥0∞) ≠ 0 := by exact_mod_cast N.2.ne'
      rw [ENNReal.ofReal_inv_of_pos hNreal]
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [ENNReal.ofReal_natCast]
      rw [show N.1 + 1 - 1 = N.1 by omega]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hNenn ENNReal.coe_ne_top]
      simp

/-- A single Möbius-average increment has the blueprint's uniform
`2/(N+1)` operator bound on every measure-preserving system. -/
theorem eLpNorm_mobiusAverage_scaleSucc_sub_le
    {X : Type*} [MeasurableSpace X] (S : System X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (mobiusAverage S c f (scaleSucc N) - mobiusAverage S c f N)
      (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal (2 / ((scaleSucc N).1 : ℝ)) *
        eLpNorm f (ENNReal.ofReal p) S.μ := by
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hfmeas := hf.aestronglyMeasurable
  have hidentity :
      mobiusAverage S c f (scaleSucc N) - mobiusAverage S c f N =
        ((scaleSucc N).1 : ℂ)⁻¹ •
          ((mobiusWeight (N.1 + 1) : ℂ) •
            S.shift (floorTime c (N.1 + 1)) f - mobiusAverage S c f N) := by
    simpa [mobiusAverage, scaleSucc] using
      (weightedAverage_succ_sub_endpoint S c
        (fun n => (mobiusWeight n : ℂ)) f N.1 N.2)
  have hMbound := eLpNorm_mobiusAverage_le_self S c f N hpENN hfmeas
  have hendpoint :
      eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
          S.shift (floorTime c (N.1 + 1)) f)
        (ENNReal.ofReal p) S.μ ≤ eLpNorm f (ENNReal.ofReal p) S.μ := by
    rw [eLpNorm_const_smul,
      eLpNorm_shift_floorPower S c (N.1 + 1) hfmeas]
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (enorm_mobiusWeight_le_one (N.1 + 1)) bot_le)
      (by simp)
  have hterm :
      eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
          S.shift (floorTime c (N.1 + 1)) f - mobiusAverage S c f N)
        (ENNReal.ofReal p) S.μ ≤
      2 * eLpNorm f (ENNReal.ofReal p) S.μ := by
    calc
      _ ≤ eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
            S.shift (floorTime c (N.1 + 1)) f) (ENNReal.ofReal p) S.μ +
          eLpNorm (mobiusAverage S c f N) (ENNReal.ofReal p) S.μ :=
        eLpNorm_sub_le hpENN
      _ ≤ eLpNorm f (ENNReal.ofReal p) S.μ +
          eLpNorm f (ENNReal.ofReal p) S.μ := add_le_add hendpoint hMbound
      _ = _ := by ring
  have hcoeff :
      ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ * 2 =
        ENNReal.ofReal (2 / ((scaleSucc N).1 : ℝ)) := by
    rw [enorm_inv_natCast_scale,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    rw [mul_comm, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
  calc
    _ = ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
          S.shift (floorTime c (N.1 + 1)) f - mobiusAverage S c f N)
        (ENNReal.ofReal p) S.μ := by
          rw [hidentity, eLpNorm_const_smul]
    _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * eLpNorm f (ENNReal.ofReal p) S.μ) :=
        mul_le_mul_of_nonneg_left hterm bot_le
    _ = _ := by rw [← mul_assoc, hcoeff]


#print axioms eLpNorm_mobiusAverage_scaleSucc_sub_le
end
end FractionalPrimes.Final
