module

public import FractionalPrimes.FourierSequence

@[expose] public section

/-!
# Finite low/high input split for interpolation

The definitions use the blueprint's exact convention: values with norm at
most the cutoff belong to the low part, and values strictly above it belong
to the high part. Both parts are restricted to the specified finite support.
-/

namespace FractionalPrimes

open scoped BigOperators

noncomputable section

/-- The low part of a finite-support sequence at cutoff `c`, supported on
`s`. The cutoff equality case belongs to this part. -/
def finiteLowPart (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) (k : ℤ) : ℂ :=
  if k ∈ s ∧ ‖f k‖ ≤ c then f k else 0

/-- The high part of a finite-support sequence at cutoff `c`, supported on
`s`. The cutoff equality case does not belong to this part. -/
def finiteHighPart (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) (k : ℤ) : ℂ :=
  if k ∈ s ∧ c < ‖f k‖ then f k else 0

theorem finiteLowPart_eq_zero_of_not_mem
    (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) {k : ℤ} (hk : k ∉ s) :
    finiteLowPart s c f k = 0 := by
  simp [finiteLowPart, hk]

theorem finiteHighPart_eq_zero_of_not_mem
    (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) {k : ℤ} (hk : k ∉ s) :
    finiteHighPart s c f k = 0 := by
  simp [finiteHighPart, hk]

/-- The two finite parts reconstruct the finite truncation pointwise. -/
theorem finiteIntegerSequenceL2_eq_finiteLowPart_add_finiteHighPart
    (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) (k : ℤ) :
    finiteIntegerSequenceL2 s f k =
      finiteLowPart s c f k + finiteHighPart s c f k := by
  classical
  by_cases hk : k ∈ s
  · by_cases hlow : ‖f k‖ ≤ c
    · simp [finiteIntegerSequenceL2_apply, finiteLowPart, finiteHighPart,
        hk, hlow, not_lt_of_ge hlow]
    · have hhigh : c < ‖f k‖ := lt_of_not_ge hlow
      simp [finiteIntegerSequenceL2_apply, finiteLowPart, finiteHighPart,
        hk, hlow, hhigh]
  · simp [finiteIntegerSequenceL2_apply, finiteLowPart, finiteHighPart, hk]

/-- Exact finite squared-mass formula for the low part, with the equality
threshold retained on the low side. -/
theorem sum_norm_sq_finiteLowPart
    (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) :
    (∑ k ∈ s, ‖finiteLowPart s c f k‖ ^ 2) =
      ∑ k ∈ s.filter (fun k => ‖f k‖ ≤ c), ‖f k‖ ^ 2 := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : ‖f k‖ ≤ c <;> simp [finiteLowPart, hk, h]

/-- Exact finite first-moment formula for the high part, with strict
threshold, as in the blueprint. -/
theorem sum_norm_finiteHighPart
    (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) :
    (∑ k ∈ s, ‖finiteHighPart s c f k‖) =
      ∑ k ∈ s.filter (fun k => c < ‖f k‖), ‖f k‖ := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : c < ‖f k‖ <;> simp [finiteHighPart, hk, h]

end

end FractionalPrimes
