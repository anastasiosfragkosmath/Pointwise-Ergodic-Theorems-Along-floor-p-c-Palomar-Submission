module

public import FractionalPrimes.Literature.MSZ.LocalizedGridProjectionL2Energy

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open Filter
open scoped ENNReal Topology

noncomputable section

/-- The two-sided tail clause of `lm:shiftedResolution`. Positive and
negative integer projections both tend to zero in `ℓ²` norm, obtained by
restricting the summable projection-energy family to the two natural rays. -/
theorem mszLocalizedProjectionL2Norm_tendsto_zero
    (A : AdmissibleData) (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) :
    Tendsto (fun n : ℕ => ‖A.projectionsL2 (n : ℤ) f‖)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ‖A.projectionsL2 (-(n : ℤ)) f‖)
      atTop (𝓝 0) := by
  obtain ⟨hEnergy, _hEnergyBound⟩ := mszLocalizedProjectionL2Energy A f
  have hposInj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro m n h
    exact Int.ofNat_inj.mp h
  have hposEnergy :
      Summable (fun n : ℕ => ‖A.projectionsL2 (n : ℤ) f‖ ^ 2) :=
    hEnergy.comp_injective hposInj
  have hnegInj : Function.Injective (fun n : ℕ => -(n : ℤ)) := by
    intro m n h
    exact Int.ofNat_inj.mp (Int.neg_inj.mp h)
  have hnegEnergy :
      Summable (fun n : ℕ => ‖A.projectionsL2 (-(n : ℤ)) f‖ ^ 2) :=
    hEnergy.comp_injective hnegInj
  have hposSq :
      Tendsto (fun n : ℕ => ‖A.projectionsL2 (n : ℤ) f‖ ^ 2)
        atTop (𝓝 0) :=
    hposEnergy.tendsto_atTop_zero
  have hnegSq :
      Tendsto (fun n : ℕ => ‖A.projectionsL2 (-(n : ℤ)) f‖ ^ 2)
        atTop (𝓝 0) :=
    hnegEnergy.tendsto_atTop_zero
  have hposNorm :
      Tendsto (fun n : ℕ => ‖A.projectionsL2 (n : ℤ) f‖)
        atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ =>
        Real.sqrt (‖A.projectionsL2 (n : ℤ) f‖ ^ 2))
        atTop (𝓝 0) := by
      simpa using hposSq.sqrt
    have heq : (fun n : ℕ =>
        Real.sqrt (‖A.projectionsL2 (n : ℤ) f‖ ^ 2)) =
          fun n : ℕ => ‖A.projectionsL2 (n : ℤ) f‖ := by
      funext n
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [heq] at hsqrt
    exact hsqrt
  have hnegNorm :
      Tendsto (fun n : ℕ => ‖A.projectionsL2 (-(n : ℤ)) f‖)
        atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ =>
        Real.sqrt (‖A.projectionsL2 (-(n : ℤ)) f‖ ^ 2))
        atTop (𝓝 0) := by
      simpa using hnegSq.sqrt
    have heq : (fun n : ℕ =>
        Real.sqrt (‖A.projectionsL2 (-(n : ℤ)) f‖ ^ 2)) =
          fun n : ℕ => ‖A.projectionsL2 (-(n : ℤ)) f‖ := by
      funext n
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [heq] at hsqrt
    exact hsqrt
  exact ⟨hposNorm, hnegNorm⟩

end

end FractionalPrimes.Literature.MSZ

end
