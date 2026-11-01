module

public import FractionalPrimes.VonMangoldtLpAverages
public import FractionalPrimes.VariationBlocks
public import FractionalPrimes.SparseScales
public import FractionalPrimes.ScalePartitions
public import FractionalPrimes.MixedNorm

/-!
# Short variation estimates for von Mangoldt averages

This module develops the elementary increment estimates needed for the
short-block term in the paper's long/short decomposition.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The next positive averaging scale after `N`. -/
def scaleSucc (N : Scale) : Scale := ⟨N.1 + 1, by omega⟩

/-- The ENNReal norm of the reciprocal of a positive natural scale. -/
theorem enorm_inv_natCast_scale (N : Scale) :
    ‖((N.1 : ℂ)⁻¹)‖ₑ = ENNReal.ofReal ((N.1 : ℝ)⁻¹) := by
  have hN : (N.1 : ℂ) ≠ 0 := by exact_mod_cast N.2.ne'
  rw [enorm_inv hN, ENNReal.ofReal_inv_of_pos (by exact_mod_cast N.2)]
  congr 1
  simp [enorm]

/-- Mathlib's Möbius coefficient bound, expressed in the complex norm used by
the weighted averages. -/
theorem enorm_mobiusWeight_le_one (n : ℕ) :
    ‖(mobiusWeight n : ℂ)‖ₑ ≤ 1 := by
  rw [← ENNReal.ofReal_one, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [mobiusWeight_def, Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The Möbius weighted averages are `Lᵖ` contractions for `p≥1`. -/
theorem eLpNorm_mobiusAverage_le_self
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
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
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
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
            S.shift (floorPower c (N.1 + 1)) f - mobiusAverage S c f N) := by
    simpa [mobiusAverage, scaleSucc] using
      (weightedAverage_succ_sub_endpoint S c
        (fun n => (mobiusWeight n : ℂ)) f N.1 N.2)
  have hMbound := eLpNorm_mobiusAverage_le_self S c f N hpENN hfmeas
  have hendpoint :
      eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f)
        (ENNReal.ofReal p) S.μ ≤ eLpNorm f (ENNReal.ofReal p) S.μ := by
    rw [eLpNorm_const_smul,
      eLpNorm_shift_floorPower S c (N.1 + 1) hfmeas]
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (enorm_mobiusWeight_le_one (N.1 + 1)) bot_le)
      (by simp)
  have hterm :
      eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f - mobiusAverage S c f N)
        (ENNReal.ofReal p) S.μ ≤
      2 * eLpNorm f (ENNReal.ofReal p) S.μ := by
    calc
      _ ≤ eLpNorm ((mobiusWeight (N.1 + 1) : ℂ) •
            S.shift (floorPower c (N.1 + 1)) f) (ENNReal.ofReal p) S.μ +
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
          S.shift (floorPower c (N.1 + 1)) f - mobiusAverage S c f N)
        (ENNReal.ofReal p) S.μ := by
          rw [hidentity, eLpNorm_const_smul]
    _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * eLpNorm f (ENNReal.ofReal p) S.μ) :=
        mul_le_mul_of_nonneg_left hterm bot_le
    _ = _ := by rw [← mul_assoc, hcoeff]

/-- The unnormalized von Mangoldt numerator at scale `N`. -/
def vonMangoldtNumerator {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  fun x => ∑ n ∈ Finset.Icc 1 N.1,
    (vonMangoldtWeight n : ℂ) * f (S.iterate (floorPower c n) x)

/-- The numerator at `N+1` splits into the old numerator and its last term. -/
theorem vonMangoldtNumerator_scaleSucc {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) :
    vonMangoldtNumerator S c f (scaleSucc N) =
      vonMangoldtNumerator S c f N +
        (vonMangoldtWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f := by
  have hset : Finset.Icc 1 (N.1 + 1) =
      insert (N.1 + 1) (Finset.Icc 1 N.1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : N.1 + 1 ∉ Finset.Icc 1 N.1 := by
    simp only [Finset.mem_Icc]
    omega
  funext x
  change (∑ n ∈ Finset.Icc 1 (N.1 + 1),
      (vonMangoldtWeight n : ℂ) * f (S.iterate (floorPower c n) x)) =
    (∑ n ∈ Finset.Icc 1 N.1,
      (vonMangoldtWeight n : ℂ) * f (S.iterate (floorPower c n) x)) +
      (vonMangoldtWeight (N.1 + 1) : ℂ) *
        f (S.iterate (floorPower c (N.1 + 1)) x)
  rw [hset, Finset.sum_insert hnot]
  exact add_comm _ _

/-- The von Mangoldt average is the normalized numerator. -/
theorem vonMangoldtAverage_eq_normalizedNumerator {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) :
    vonMangoldtAverage S c f N = (N.1 : ℂ)⁻¹ •
      vonMangoldtNumerator S c f N := by
  funext x
  simp [vonMangoldtAverage, weightedAverage, vonMangoldtNumerator]

/-- The increment from `N` to `N+1` is the last weighted term minus the old
average, divided by `N+1`. -/
theorem vonMangoldtAverage_scaleSucc_sub {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) :
    vonMangoldtAverage S c f (scaleSucc N) - vonMangoldtAverage S c f N =
      ((scaleSucc N).1 : ℂ)⁻¹ •
        ((vonMangoldtWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f - vonMangoldtAverage S c f N) := by
  rw [vonMangoldtAverage_eq_normalizedNumerator,
    vonMangoldtAverage_eq_normalizedNumerator,
    vonMangoldtNumerator_scaleSucc]
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hN : (N.1 : ℂ) ≠ 0 := by exact_mod_cast N.2.ne'
  have hNs : ((scaleSucc N).1 : ℂ) ≠ 0 := by
    change (↑(N.1 + 1 : ℕ) : ℂ) ≠ 0
    exact_mod_cast (Nat.succ_ne_zero N.1)
  simp only [scaleSucc]
  field_simp [hN, hNs]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, InvertibleSystem.shift]
  push_cast
  ring

/-- A single von Mangoldt-average increment has the elementary logarithmic
operator bound used for short variation. -/
theorem eLpNorm_vonMangoldtAverage_scaleSucc_sub_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (vonMangoldtAverage S c f (scaleSucc N) -
      vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ ≤
      ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) S.μ) := by
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hfmeas : AEStronglyMeasurable f S.μ := hf.aestronglyMeasurable
  have hNbound := eLpNorm_vonMangoldtAverage_le_log_two_mul S c f N
    hpENN hfmeas
  have hNsbound := enorm_vonMangoldtWeight_le_log_two_mul
    (n := N.1 + 1) (N := (scaleSucc N).1) (by omega) (by rfl)
  have hNreal : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hlogmono : ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) ≤
      ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.log_le_log
    · exact mul_pos (by norm_num) hNreal
    · apply mul_le_mul_of_nonneg_left
      · exact_mod_cast (Nat.le_succ N.1)
      · norm_num
  calc
    eLpNorm (vonMangoldtAverage S c f (scaleSucc N) -
      vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ =
        ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ * eLpNorm
          ((vonMangoldtWeight (N.1 + 1) : ℂ) •
            S.shift (floorPower c (N.1 + 1)) f - vonMangoldtAverage S c f N)
          (ENNReal.ofReal p) S.μ := by
            rw [vonMangoldtAverage_scaleSucc_sub, eLpNorm_const_smul]
    _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (eLpNorm ((vonMangoldtWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f) (ENNReal.ofReal p) S.μ +
          eLpNorm (vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ) := by
            exact mul_le_mul_of_nonneg_left (eLpNorm_sub_le hpENN) bot_le
    _ = ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (‖(vonMangoldtWeight (N.1 + 1) : ℂ)‖ₑ *
          eLpNorm f (ENNReal.ofReal p) S.μ +
          eLpNorm (vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ) := by
            rw [eLpNorm_const_smul,
              eLpNorm_shift_floorPower S c (N.1 + 1) hfmeas]
    _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) S.μ) := by
            have hsum := add_le_add
              (mul_le_mul_of_nonneg_right hNsbound
                (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm f (ENNReal.ofReal p) S.μ))
              (hNbound.trans (mul_le_mul_of_nonneg_right hlogmono bot_le))
            calc
              _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
                  (ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) *
                    eLpNorm f (ENNReal.ofReal p) S.μ +
                    ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) *
                    eLpNorm f (ENNReal.ofReal p) S.μ) :=
                mul_le_mul_of_nonneg_left hsum bot_le
              _ = ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
                  (2 * ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) *
                    eLpNorm f (ENNReal.ofReal p) S.μ) := by ring

/-- The same increment estimate with its coefficient written as the scalar
`2 log(2N)/N`, ready for summation over a finite block. -/
theorem eLpNorm_vonMangoldtAverage_scaleSucc_sub_le_normalized
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (vonMangoldtAverage S c f (scaleSucc N) -
      vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal (2 * Real.log (2 * ((scaleSucc N).1 : ℝ)) /
        ((scaleSucc N).1 : ℝ)) * eLpNorm f (ENNReal.ofReal p) S.μ := by
  have hNge1 : (1 : ℝ) ≤ ((scaleSucc N).1 : ℝ) := by
    change (1 : ℝ) ≤ ((N.1 + 1 : ℕ) : ℝ)
    have hnat : 1 ≤ N.1 + 1 := by omega
    exact_mod_cast hnat
  have hNpos : 0 < ((scaleSucc N).1 : ℝ) := lt_of_lt_of_le zero_lt_one hNge1
  have hlognonneg : 0 ≤ Real.log (2 * ((scaleSucc N).1 : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hcoeff : ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
      (2 * ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ)))) =
      ENNReal.ofReal (2 * Real.log (2 * ((scaleSucc N).1 : ℝ)) /
        ((scaleSucc N).1 : ℝ)) := by
    rw [enorm_inv_natCast_scale,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
      ← ENNReal.ofReal_mul
        (by positivity : 0 ≤ (((scaleSucc N).1 : ℝ)⁻¹))]
    congr 1
    field_simp
  calc
    _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) S.μ) :=
      eLpNorm_vonMangoldtAverage_scaleSucc_sub_le S c f N hp hf
    _ = (‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * ((scaleSucc N).1 : ℝ))))) *
          eLpNorm f (ENNReal.ofReal p) S.μ := by ac_rfl
    _ = _ := by rw [hcoeff]

/-- Sharp successor increment estimate with the logarithm at the previous
scale, matching the paper's `2 log(2m)/(m+1)` bound. -/
theorem eLpNorm_vonMangoldtAverage_scaleSucc_sub_le_previous_log
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (vonMangoldtAverage S c f (scaleSucc N) -
      vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal (2 * Real.log (2 * (N.1 : ℝ)) /
        ((scaleSucc N).1 : ℝ)) * eLpNorm f (ENNReal.ofReal p) S.μ := by
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hfmeas : AEStronglyMeasurable f S.μ := hf.aestronglyMeasurable
  have hNbound := eLpNorm_vonMangoldtAverage_le_log_two_mul S c f N
    hpENN hfmeas
  have hNreal : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hNsreal : 0 < ((scaleSucc N).1 : ℝ) := by
    change 0 < ((N.1 + 1 : ℕ) : ℝ)
    exact_mod_cast (Nat.succ_pos N.1)
  have hNsle : ((scaleSucc N).1 : ℝ) ≤ 2 * (N.1 : ℝ) := by
    change ((N.1 + 1 : ℕ) : ℝ) ≤ 2 * (N.1 : ℝ)
    have hnat : N.1 + 1 ≤ 2 * N.1 := by omega
    exact_mod_cast hnat
  have hNsbound : ‖(vonMangoldtWeight (N.1 + 1) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) := by
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hcast : ((vonMangoldtWeight (N.1 + 1) : ℝ) : ℂ) =
        (vonMangoldtWeight (N.1 + 1) : ℂ) := by norm_cast
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vonMangoldtWeight_nonneg (N.1 + 1))]
    exact (vonMangoldtWeight_le_log (n := N.1 + 1)).trans
      (Real.log_le_log hNsreal hNsle)
  have hNge1 : (1 : ℝ) ≤ (N.1 : ℝ) := by exact_mod_cast N.2
  have hlognonneg : 0 ≤ Real.log (2 * (N.1 : ℝ)) :=
    Real.log_nonneg (by nlinarith [hNge1])
  have hterm :
      eLpNorm ((vonMangoldtWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f - vonMangoldtAverage S c f N)
        (ENNReal.ofReal p) S.μ ≤
        2 * ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) S.μ := by
    calc
      _ ≤ eLpNorm ((vonMangoldtWeight (N.1 + 1) : ℂ) •
            S.shift (floorPower c (N.1 + 1)) f) (ENNReal.ofReal p) S.μ +
          eLpNorm (vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ :=
        eLpNorm_sub_le hpENN
      _ = ‖(vonMangoldtWeight (N.1 + 1) : ℂ)‖ₑ *
            eLpNorm f (ENNReal.ofReal p) S.μ +
          eLpNorm (vonMangoldtAverage S c f N) (ENNReal.ofReal p) S.μ := by
        rw [eLpNorm_const_smul,
          eLpNorm_shift_floorPower S c (N.1 + 1) hfmeas]
      _ ≤ ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) S.μ +
          ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) S.μ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hNsbound bot_le) hNbound
      _ = _ := by ring
  have hcoeff :
      ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * (N.1 : ℝ)))) =
      ENNReal.ofReal (2 * Real.log (2 * (N.1 : ℝ)) /
        ((scaleSucc N).1 : ℝ)) := by
    rw [enorm_inv_natCast_scale,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
      ← ENNReal.ofReal_mul (by positivity :
        0 ≤ (((scaleSucc N).1 : ℝ)⁻¹))]
    congr 1
    field_simp
  calc
    _ = ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        eLpNorm ((vonMangoldtWeight (N.1 + 1) : ℂ) •
          S.shift (floorPower c (N.1 + 1)) f - vonMangoldtAverage S c f N)
        (ENNReal.ofReal p) S.μ := by
          rw [vonMangoldtAverage_scaleSucc_sub, eLpNorm_const_smul]
    _ ≤ ‖((scaleSucc N).1 : ℂ)⁻¹‖ₑ *
        (2 * ENNReal.ofReal (Real.log (2 * (N.1 : ℝ))) *
          eLpNorm f (ENNReal.ofReal p) S.μ) :=
        mul_le_mul_of_nonneg_left hterm bot_le
    _ = _ := by rw [← mul_assoc, hcoeff]

/-- A finite block variation is bounded by the sum of its consecutive
von Mangoldt-average increment bounds. -/
theorem eLpNorm_vonMangoldtBlock_le_incrementSum
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) (a b : Scale) (hab : a ≤ b) :
    eLpNorm (rVariationOnFun 2 (fun N => vonMangoldtAverage S c f N)
      (Set.Icc a b)) (ENNReal.ofReal p) S.μ ≤
      ∑ i ∈ Finset.range (b.1 - a.1),
        ‖((scaleSucc (scaleOffset a i)).1 : ℂ)⁻¹‖ₑ *
          (2 * ENNReal.ofReal (Real.log
            (2 * ((scaleSucc (scaleOffset a i)).1 : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) S.μ) := by
  have hF : ∀ N, MemLp (vonMangoldtAverage S c f N)
      (ENNReal.ofReal p) S.μ := by
    intro N
    simpa [vonMangoldtAverage] using
      (memLp_weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ)) f N hf)
  calc
    eLpNorm (rVariationOnFun 2 (fun N => vonMangoldtAverage S c f N)
      (Set.Icc a b)) (ENNReal.ofReal p) S.μ ≤
      ∑ i ∈ Finset.range (b.1 - a.1),
        eLpNorm (fun x => vonMangoldtAverage S c f (scaleOffset a (i + 1)) x -
          vonMangoldtAverage S c f (scaleOffset a i) x)
          (ENNReal.ofReal p) S.μ :=
      eLpNorm_rVariationOnFun_scaleInterval_le_sum S p 2
        (by linarith) (by norm_num) (fun N => vonMangoldtAverage S c f N)
        a b hab hF
    _ ≤ ∑ i ∈ Finset.range (b.1 - a.1),
        ‖((scaleSucc (scaleOffset a i)).1 : ℂ)⁻¹‖ₑ *
          (2 * ENNReal.ofReal (Real.log
            (2 * ((scaleSucc (scaleOffset a i)).1 : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) S.μ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hscale : scaleSucc (scaleOffset a i) = scaleOffset a (i + 1) := by
        apply Subtype.ext
        simp [scaleSucc, scaleOffset]
        omega
      change eLpNorm
        (vonMangoldtAverage S c f (scaleOffset a (i + 1)) -
          vonMangoldtAverage S c f (scaleOffset a i))
        (ENNReal.ofReal p) S.μ ≤ _
      simpa [hscale] using
        eLpNorm_vonMangoldtAverage_scaleSucc_sub_le S c f (scaleOffset a i) hp hf
  

/-- The same finite-block estimate after collecting `‖f‖ₚ` and expressing
each scalar increment coefficient in normalized real form. -/
theorem eLpNorm_vonMangoldtBlock_le_normalizedIncrementSum
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) (a b : Scale) (hab : a ≤ b) :
    eLpNorm (rVariationOnFun 2 (fun N => vonMangoldtAverage S c f N)
      (Set.Icc a b)) (ENNReal.ofReal p) S.μ ≤
      (∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal
          (2 * Real.log (2 * ((scaleOffset a (i + 1)).1 : ℝ)) /
            ((scaleOffset a (i + 1)).1 : ℝ))) *
        eLpNorm f (ENNReal.ofReal p) S.μ := by
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hF : ∀ N, MemLp (vonMangoldtAverage S c f N)
      (ENNReal.ofReal p) S.μ := by
    intro N
    simpa [vonMangoldtAverage] using
      (memLp_weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ)) f N hf)
  calc
    eLpNorm (rVariationOnFun 2 (fun N => vonMangoldtAverage S c f N)
      (Set.Icc a b)) (ENNReal.ofReal p) S.μ ≤
      ∑ i ∈ Finset.range (b.1 - a.1),
        eLpNorm (fun x => vonMangoldtAverage S c f (scaleOffset a (i + 1)) x -
          vonMangoldtAverage S c f (scaleOffset a i) x)
          (ENNReal.ofReal p) S.μ :=
      eLpNorm_rVariationOnFun_scaleInterval_le_sum S p 2
        (by linarith) (by norm_num) (fun N => vonMangoldtAverage S c f N)
        a b hab hF
    _ ≤ ∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal
          (2 * Real.log (2 * ((scaleOffset a (i + 1)).1 : ℝ)) /
            ((scaleOffset a (i + 1)).1 : ℝ)) *
          eLpNorm f (ENNReal.ofReal p) S.μ := by
      apply Finset.sum_le_sum
      intro i hi
      have hscale : scaleSucc (scaleOffset a i) = scaleOffset a (i + 1) := by
        apply Subtype.ext
        simp [scaleSucc, scaleOffset]
        omega
      change eLpNorm
        (vonMangoldtAverage S c f (scaleOffset a (i + 1)) -
          vonMangoldtAverage S c f (scaleOffset a i))
        (ENNReal.ofReal p) S.μ ≤ _
      simpa [hscale] using
        eLpNorm_vonMangoldtAverage_scaleSucc_sub_le_normalized
          S c f (scaleOffset a i) hp hf
    _ = (∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal
          (2 * Real.log (2 * ((scaleOffset a (i + 1)).1 : ℝ)) /
            ((scaleOffset a (i + 1)).1 : ℝ))) *
        eLpNorm f (ENNReal.ofReal p) S.μ := by
      rw [Finset.sum_mul]

/-- The short variation of the von Mangoldt averages on one sparse block is
bounded by its logarithmic block error times the input norm. -/
theorem eLpNorm_vonMangoldtSparseBlock_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) (k : ℕ) :
    eLpNorm (rVariationOnFun 2 (fun N => vonMangoldtAverage S c f N)
      (Set.Icc ⟨sparseScale p k, by
        have hmin : 1 ≤ sparseScale p k := by
          calc
            1 = sparseScale p 0 := (sparseScale_zero hp).symm
            _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
        omega⟩ ⟨sparseScale p (k + 1), by
        have hmin : 1 ≤ sparseScale p (k + 1) := by
          calc
            1 = sparseScale p 0 := (sparseScale_zero hp).symm
            _ ≤ sparseScale p (k + 1) := sparseScale_monotone hp (Nat.zero_le _)
        omega⟩)) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal (4 * sparseScaleBlockError p k) *
        eLpNorm f (ENNReal.ofReal p) S.μ := by
  let a : Scale := ⟨sparseScale p k, by
    have hmin : 1 ≤ sparseScale p k := by
      calc
        1 = sparseScale p 0 := (sparseScale_zero hp).symm
        _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
    omega⟩
  let b : Scale := ⟨sparseScale p (k + 1), by
    have hmin : 1 ≤ sparseScale p (k + 1) := by
      calc
        1 = sparseScale p 0 := (sparseScale_zero hp).symm
        _ ≤ sparseScale p (k + 1) := sparseScale_monotone hp (Nat.zero_le _)
    omega⟩
  have hab : a ≤ b := by
    change a.1 ≤ b.1
    exact sparseScale_monotone hp (Nat.le_succ k)
  have hcoeff :
      (∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal
          (2 * Real.log (2 * ((scaleOffset a (i + 1)).1 : ℝ)) /
            ((scaleOffset a (i + 1)).1 : ℝ))) ≤
        ENNReal.ofReal (4 * sparseScaleBlockError p k) := by
    have hsumEq :
        (∑ i ∈ Finset.range (b.1 - a.1),
          ENNReal.ofReal
            (2 * Real.log (2 * ((scaleOffset a (i + 1)).1 : ℝ)) /
              ((scaleOffset a (i + 1)).1 : ℝ))) =
        (∑ i ∈ Finset.range
          (sparseScale p (k + 1) - sparseScale p k),
          ENNReal.ofReal
            (2 * Real.log
              (2 * (((sparseScale p k + i : ℕ) : ℝ) + 1)) /
                (((sparseScale p k + i : ℕ) : ℝ) + 1))) := by
      apply Finset.sum_congr
      · simp [a, b]
      · intro i hi
        congr 1
        simp [a, scaleOffset, Nat.cast_add]
        ring_nf
    rw [hsumEq]
    exact sparseScaleIncrementCoeffSum_le hp k
  have hblock := eLpNorm_vonMangoldtBlock_le_normalizedIncrementSum
    S c f hp hf a b hab
  simpa [a, b] using
    (hblock.trans (mul_le_mul_of_nonneg_right hcoeff bot_le))

/-- The complete sparse-block short-variation square function is bounded by
the finite ENNReal coefficient series times the input `L^p` norm. -/
theorem eLpNorm_vonMangoldtShortSquare_le
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (fun x =>
      (∑' k, (rVariationOnFun 2
        (fun N => vonMangoldtAverage S c f N)
        (Set.Icc (sparseScaleAsScale hp k)
          (sparseScaleAsScale hp (k + 1))) x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) S.μ ≤
      (∑' k, (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
        sparseScaleQ p) ^ (1 / sparseScaleQ p) *
        eLpNorm f (ENNReal.ofReal p) S.μ := by
  let s : ℕ → Scale := sparseScaleAsScale hp
  let F : Scale → X → ℂ := fun N => vonMangoldtAverage S c f N
  let Block : ℕ → X → ℝ≥0∞ := fun k =>
    rVariationOnFun 2 F (Set.Icc (s k) (s (k + 1)))
  have hFmem : ∀ N, MemLp (F N) (ENNReal.ofReal p) S.μ := by
    intro N
    dsimp [F]
    simpa [vonMangoldtAverage] using
      (memLp_weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ)) f N hf)
  have hFae : ∀ N, AEMeasurable (F N) S.μ := by
    intro N
    exact (hFmem N).aemeasurable
  have hqpos : 0 < sparseScaleQ p :=
    lt_trans zero_lt_one (sparseScaleQ_gt_one hp)
  have hqnonneg : 0 ≤ sparseScaleQ p := hqpos.le
  have hqInvNonneg : 0 ≤ (1 / sparseScaleQ p) := by positivity
  have hmix := eLpNorm_sparseBlockSquare_mixed S.μ s F hp hFae
  rw [← sparseScaleQ_eq_min p] at hmix
  have hblock (k : ℕ) :
      eLpNorm (Block k) (ENNReal.ofReal p) S.μ ≤
        ENNReal.ofReal (4 * sparseScaleBlockError p k) *
          eLpNorm f (ENNReal.ofReal p) S.μ := by
    dsimp [Block, s, F]
    exact eLpNorm_vonMangoldtSparseBlock_le S c f hp hf k
  have hsum :
      (∑' k, (eLpNorm (Block k) (ENNReal.ofReal p) S.μ) ^
        sparseScaleQ p) ≤
      (∑' k, (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
        sparseScaleQ p) *
        (eLpNorm f (ENNReal.ofReal p) S.μ) ^ sparseScaleQ p := by
    calc
      _ ≤ ∑' k,
          (ENNReal.ofReal (4 * sparseScaleBlockError p k) *
            eLpNorm f (ENNReal.ofReal p) S.μ) ^ sparseScaleQ p :=
        ENNReal.tsum_le_tsum (fun k =>
          ENNReal.rpow_le_rpow (hblock k) hqnonneg)
      _ = ∑' k,
          ((ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^ sparseScaleQ p *
            (eLpNorm f (ENNReal.ofReal p) S.μ) ^ sparseScaleQ p) := by
        apply tsum_congr
        intro k
        rw [ENNReal.mul_rpow_of_nonneg _ _ hqnonneg]
      _ = (∑' k,
          (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^ sparseScaleQ p) *
            (eLpNorm f (ENNReal.ofReal p) S.μ) ^ sparseScaleQ p :=
        ENNReal.tsum_mul_right
  have hpow := ENNReal.rpow_le_rpow hsum hqInvNonneg
  calc
    _ ≤ (∑' k, (eLpNorm (Block k) (ENNReal.ofReal p) S.μ) ^
          sparseScaleQ p) ^ (1 / sparseScaleQ p) := by
      simpa [s, F, Block] using hmix
    _ ≤ ((∑' k,
          (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^ sparseScaleQ p) *
          (eLpNorm f (ENNReal.ofReal p) S.μ) ^ sparseScaleQ p) ^
          (1 / sparseScaleQ p) := hpow
    _ = (∑' k,
          (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^ sparseScaleQ p) ^
          (1 / sparseScaleQ p) * eLpNorm f (ENNReal.ofReal p) S.μ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqInvNonneg]
      congr 1
      rw [← ENNReal.rpow_mul]
      have hexp : sparseScaleQ p * (1 / sparseScaleQ p) = 1 := by
        field_simp
      rw [hexp, ENNReal.rpow_one]

/-- Long/short reduction for the full von Mangoldt variation, with the
short-block contribution already bounded by the explicit summable constant. -/
theorem eLpNorm_vonMangoldtVariation_le_longSparse_and_short
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) {p r : ℝ} (hp : 1 < p) (hr2 : 2 ≤ r)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (rVariationFun r (fun N => vonMangoldtAverage S c f N))
      (ENNReal.ofReal p) S.μ ≤
      3 * eLpNorm (rVariationFun r (fun K : Scale =>
        vonMangoldtAverage S c f (sparseScaleAsScale hp (K.1 - 1))))
        (ENNReal.ofReal p) S.μ +
      3 * (∑' k, (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
        sparseScaleQ p) ^ (1 / sparseScaleQ p) *
        eLpNorm f (ENNReal.ofReal p) S.μ := by
  let s : ℕ → Scale := sparseScaleAsScale hp
  let F : Scale → X → ℂ := fun N => vonMangoldtAverage S c f N
  have hFmem : ∀ N, MemLp (F N) (ENNReal.ofReal p) S.μ := by
    intro N
    dsimp [F]
    simpa [vonMangoldtAverage] using
      (memLp_weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ)) f N hf)
  have hFae : ∀ N, AEMeasurable (F N) S.μ := by
    intro N
    exact (hFmem N).aemeasurable
  have hred := eLpNorm_longShort_reduction_direct S.μ s
    (sparseScaleAsScale_zero hp) (sparseScaleAsScale_monotone hp)
    (sparseScaleAsScale_tendsto_atTop hp) F hp hr2 hFae
  have hshort := eLpNorm_vonMangoldtShortSquare_le S c f hp hf
  have hred' :
      eLpNorm (rVariationFun r (fun N => vonMangoldtAverage S c f N))
        (ENNReal.ofReal p) S.μ ≤
        3 * eLpNorm (rVariationFun r (fun K : Scale =>
          vonMangoldtAverage S c f (sparseScaleAsScale hp (K.1 - 1))))
          (ENNReal.ofReal p) S.μ +
        3 * eLpNorm (fun x =>
          (∑' k, (rVariationOnFun 2
            (fun N => vonMangoldtAverage S c f N)
            (Set.Icc (sparseScaleAsScale hp k)
              (sparseScaleAsScale hp (k + 1))) x) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) (ENNReal.ofReal p) S.μ := by
    simpa [s, F] using hred
  calc
    _ ≤ 3 * eLpNorm (rVariationFun r (fun K : Scale =>
          vonMangoldtAverage S c f (sparseScaleAsScale hp (K.1 - 1))))
          (ENNReal.ofReal p) S.μ +
        3 * eLpNorm (fun x =>
          (∑' k, (rVariationOnFun 2
            (fun N => vonMangoldtAverage S c f N)
            (Set.Icc (sparseScaleAsScale hp k)
              (sparseScaleAsScale hp (k + 1))) x) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) (ENNReal.ofReal p) S.μ := hred'
    _ ≤ _ := by
      apply add_le_add_right
      calc
        3 * eLpNorm (fun x =>
            (∑' k, (rVariationOnFun 2
              (fun N => vonMangoldtAverage S c f N)
              (Set.Icc (sparseScaleAsScale hp k)
                (sparseScaleAsScale hp (k + 1))) x) ^ (2 : ℝ)) ^
              (1 / 2 : ℝ)) (ENNReal.ofReal p) S.μ ≤
            3 * ((∑' k,
              (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
                sparseScaleQ p) ^ (1 / sparseScaleQ p) *
              eLpNorm f (ENNReal.ofReal p) S.μ) :=
          mul_le_mul_of_nonneg_left hshort (by norm_num)
        _ = 3 * (∑' k,
            (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
              sparseScaleQ p) ^ (1 / sparseScaleQ p) *
            eLpNorm f (ENNReal.ofReal p) S.μ := by ac_rfl

end

end FractionalPrimes
