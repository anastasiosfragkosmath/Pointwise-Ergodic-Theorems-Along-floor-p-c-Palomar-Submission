module

public import FractionalPrimes.LpAverages

/-!
# Finite weighted averages on `L^p`

These are the finite-sum estimates shared by the von Mangoldt and Möbius
averages.  The weights remain explicit, so this file does not assume an
unproved bound for either arithmetic family.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- A weighted average is a scalar multiple of the finite sum of weighted translates. -/
theorem weightedAverage_eq_smul_sum_weightedShift {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ) (N : Scale) :
    weightedAverage S c w f N = (N.1 : ℂ)⁻¹ •
      ∑ n ∈ Finset.Icc 1 N.1, w n • S.shift (floorPower c n) f := by
  funext x
  simp [weightedAverage, InvertibleSystem.shift]

/-- Exact successor identity for normalized weighted averages. The endpoint
term is separated from the previous inclusive sum, so the formula also
preserves the paper's `[1,m]` indexing convention. -/
theorem weightedAverage_succ_sub_apply {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (x : X) :
    weightedAverage S c w f ⟨m + 1, by omega⟩ x -
        weightedAverage S c w f ⟨m, hm⟩ x =
      ((m + 1 : ℂ)⁻¹ - (m : ℂ)⁻¹) *
          (∑ n ∈ Finset.Icc 1 m, w n * f (S.iterate (floorPower c n) x)) +
        (m + 1 : ℂ)⁻¹ * (w (m + 1) * f (S.iterate (floorPower c (m + 1)) x)) := by
  simp only [weightedAverage]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega)]
  push_cast
  ring

/-- Function-valued form of `weightedAverage_succ_sub_apply`, arranged as a
sum of a previous-block term and the new endpoint term for `Lᵖ` estimates. -/
theorem weightedAverage_succ_sub {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ)
    (m : ℕ) (hm : 1 ≤ m) :
    weightedAverage S c w f ⟨m + 1, by omega⟩ -
        weightedAverage S c w f ⟨m, hm⟩ =
      ((m + 1 : ℂ)⁻¹ - (m : ℂ)⁻¹) •
          (∑ n ∈ Finset.Icc 1 m, w n • S.shift (floorPower c n) f) +
        (m + 1 : ℂ)⁻¹ • (w (m + 1) • S.shift (floorPower c (m + 1)) f) := by
  funext x
  simpa [InvertibleSystem.shift, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul] using weightedAverage_succ_sub_apply S c w f m hm x

/-- The same successor increment written as the new endpoint minus the old
average, divided by the new scale. This form is useful when the old averages
are contractions on `Lᵖ`. -/
theorem weightedAverage_succ_sub_endpoint {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ)
    (m : ℕ) (hm : 1 ≤ m) :
    weightedAverage S c w f ⟨m + 1, by omega⟩ -
        weightedAverage S c w f ⟨m, hm⟩ =
      (m + 1 : ℂ)⁻¹ •
        (w (m + 1) • S.shift (floorPower c (m + 1)) f -
          weightedAverage S c w f ⟨m, hm⟩) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hm))
  have hm1C : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, weightedAverage,
    InvertibleSystem.shift]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega)]
  push_cast
  field_simp [hmC, hm1C]
  <;> ring

/-- A finite weighted average of an almost strongly measurable function is almost strongly
measurable. -/
theorem aestronglyMeasurable_weightedAverage {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ) (N : Scale)
    (hf : AEStronglyMeasurable f S.μ) :
    AEStronglyMeasurable (weightedAverage S c w f N) S.μ := by
  rw [weightedAverage_eq_smul_sum_weightedShift]
  apply AEStronglyMeasurable.const_smul
  have hsum := Finset.aestronglyMeasurable_fun_sum (Finset.Icc 1 N.1)
    (fun n _ => (aestronglyMeasurable_shift_floorPower S c n hf).const_smul (w n))
  convert hsum using 1
  ext x
  simp only [Finset.sum_apply]

/-- A finite weighted average of an `L^p` function remains in `L^p`. -/
theorem memLp_weightedAverage {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ) (N : Scale)
    {p : ℝ≥0∞} (hf : MemLp f p S.μ) :
    MemLp (weightedAverage S c w f N) p S.μ := by
  rw [weightedAverage_eq_smul_sum_weightedShift]
  apply MemLp.const_smul
  have hsum := memLp_finsetSum (Finset.Icc 1 N.1)
    (fun n _ => (memLp_shift_floorPower S c n hf).const_smul (w n))
  convert hsum using 1
  ext x
  simp only [Finset.sum_apply]

/-- Minkowski's inequality for a finite weighted average. -/
theorem eLpNorm_weightedAverage_le {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ) (N : Scale)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (weightedAverage S c w f N) p S.μ ≤ ‖(N.1 : ℂ)⁻¹‖ₑ *
      ∑ n ∈ Finset.Icc 1 N.1, ‖w n‖ₑ * eLpNorm f p S.μ := by
  rw [weightedAverage_eq_smul_sum_weightedShift, eLpNorm_const_smul]
  calc
    ‖(N.1 : ℂ)⁻¹‖ₑ * eLpNorm (∑ n ∈ Finset.Icc 1 N.1,
        w n • S.shift (floorPower c n) f) p S.μ ≤
        ‖(N.1 : ℂ)⁻¹‖ₑ * ∑ n ∈ Finset.Icc 1 N.1,
          eLpNorm (w n • S.shift (floorPower c n) f) p S.μ :=
      mul_le_mul_of_nonneg_left (eLpNorm_sum_le hp) bot_le
    _ = ‖(N.1 : ℂ)⁻¹‖ₑ * ∑ n ∈ Finset.Icc 1 N.1,
          ‖w n‖ₑ * eLpNorm f p S.μ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      rw [eLpNorm_const_smul]
      exact congrArg (fun z : ℝ≥0∞ => ‖w n‖ₑ * z)
        (eLpNorm_shift_floorPower S c n hf)

end

end FractionalPrimes

end
