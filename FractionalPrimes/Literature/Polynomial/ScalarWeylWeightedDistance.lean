module

public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- Distance to the integer lattice is subadditive under finite
integer-weighted sums. The weights are integral so their lattice witnesses
remain integral after multiplication. -/
theorem realDistanceToIntegers_intWeightedSum_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (m : ι → ℤ) (x ε : ι → ℝ)
    (hε : ∀ i ∈ S, realDistanceToIntegers (x i) ≤ ε i) :
    realDistanceToIntegers
      (∑ i ∈ S, (m i : ℝ) * x i) ≤
    ∑ i ∈ S, |(m i : ℝ)| * ε i := by
  classical
  let k : ι → ℤ := fun i =>
    if hi : i ∈ S then
      Classical.choose
        (exists_int_abs_sub_le_of_realDistanceToIntegers_le (hε i hi))
    else 0
  have hk (i : ι) (hi : i ∈ S) :
      |x i - (k i : ℝ)| ≤ ε i := by
    dsimp [k]
    rw [dif_pos hi]
    exact Classical.choose_spec
      (exists_int_abs_sub_le_of_realDistanceToIntegers_le (hε i hi))
  let z : ℤ := ∑ i ∈ S, m i * k i
  have hcast : (z : ℝ) = ∑ i ∈ S, (m i : ℝ) * (k i : ℝ) := by
    dsimp [z]
    norm_cast
  have herror :
      (∑ i ∈ S, (m i : ℝ) * x i) - (z : ℝ) =
        ∑ i ∈ S, (m i : ℝ) * (x i - (k i : ℝ)) := by
    rw [hcast, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have happrox :
      |(∑ i ∈ S, (m i : ℝ) * x i) - (z : ℝ)| ≤
        ∑ i ∈ S, |(m i : ℝ)| * ε i := by
    rw [herror]
    calc
      |∑ i ∈ S, (m i : ℝ) * (x i - (k i : ℝ))| ≤
          ∑ i ∈ S, |(m i : ℝ) * (x i - (k i : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |(m i : ℝ)| * |x i - (k i : ℝ)| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
      _ ≤ ∑ i ∈ S, |(m i : ℝ)| * ε i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hk i hi) (abs_nonneg _)
  have hzmem : (z : ℝ) ∈ Set.range fun w : ℤ => (w : ℝ) :=
    ⟨z, rfl⟩
  have hdist :
      realDistanceToIntegers (∑ i ∈ S, (m i : ℝ) * x i) ≤
        |(∑ i ∈ S, (m i : ℝ) * x i) - (z : ℝ)| := by
    unfold realDistanceToIntegers
    calc
      Metric.infDist (∑ i ∈ S, (m i : ℝ) * x i)
          (Set.range fun w : ℤ => (w : ℝ)) ≤
        dist (∑ i ∈ S, (m i : ℝ) * x i) (z : ℝ) :=
          Metric.infDist_le_dist_of_mem
            (x := ∑ i ∈ S, (m i : ℝ) * x i) hzmem
      _ = |(∑ i ∈ S, (m i : ℝ) * x i) - (z : ℝ)| := by
        rw [Real.dist_eq]
  exact hdist.trans happrox

end FractionalPrimes.Literature.Polynomial
