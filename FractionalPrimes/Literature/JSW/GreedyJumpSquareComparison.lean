module

public import FractionalPrimes.Literature.Variation.GreedyJumpBound

/-!
# Completed greedy stops dominate the separated jump count

This is the pointwise arithmetic step after the completed stopped
blocks have been identified with the greedy increments.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

open FractionalPrimes.Literature.Variation

/-- The square sum of completed greedy increments dominates the
separated jump count at the original threshold. -/
theorem greedyJumpCount_mul_threshold_le_squareSum
    {I : Type*} [LinearOrder I] [Fintype I]
    (u : I → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold)
    {G : ℕ} (run : GreedyStopRun u threshold G) :
    threshold ^ 2 * (finiteSeparatedJumpCount u threshold : ℝ) ≤
      4 * ∑ i : Fin G,
        ‖u (run.point i.succ) - u (run.point i.castSucc)‖ ^ 2 := by
  classical
  have hcount : (finiteSeparatedJumpCount u threshold : ℝ) ≤ G := by
    exact_mod_cast jumpCountLeGreedy u threshold hthreshold run
  have hterms : ∀ i : Fin G,
      (threshold / 2) ^ 2 ≤
        ‖u (run.point i.succ) - u (run.point i.castSucc)‖ ^ 2 := by
    intro i
    have hcross := run.crosses i
    have hnorm : 0 ≤ ‖u (run.point i.succ) - u (run.point i.castSucc)‖ :=
      norm_nonneg _
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi => hterms i)
  have hsum' : (G : ℝ) * (threshold / 2) ^ 2 ≤
      ∑ i : Fin G,
        ‖u (run.point i.succ) - u (run.point i.castSucc)‖ ^ 2 := by
    simpa [nsmul_eq_mul, mul_comm] using hsum
  have hsq : 0 ≤ threshold ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hcount hsq]

/-- The form used by the dyadic martingale jump inequality. -/
theorem greedyJumpCountSqrt_le_completedSquare
    {I : Type*} [LinearOrder I] [Fintype I]
    (u : I → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold)
    {G : ℕ} (run : GreedyStopRun u threshold G) :
    threshold * Real.sqrt (finiteSeparatedJumpCount u threshold : ℝ) ≤
      2 * Real.sqrt (∑ i : Fin G,
        ‖u (run.point i.succ) - u (run.point i.castSucc)‖ ^ 2) := by
  have hsum0 : 0 ≤ ∑ i : Fin G,
      ‖u (run.point i.succ) - u (run.point i.castSucc)‖ ^ 2 := by
    positivity
  have hcount0 : 0 ≤ (finiteSeparatedJumpCount u threshold : ℝ) := by
    positivity
  have hsqrtCount := Real.sq_sqrt hcount0
  have hsqrtSum := Real.sq_sqrt hsum0
  have hbound := greedyJumpCount_mul_threshold_le_squareSum u threshold hthreshold run
  have hleft0 : 0 ≤ threshold * Real.sqrt (finiteSeparatedJumpCount u threshold : ℝ) :=
    mul_nonneg hthreshold.le (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ 2 * Real.sqrt (∑ i : Fin G,
      ‖u (run.point i.succ) - u (run.point i.castSucc)‖ ^ 2) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  nlinarith

end FractionalPrimes.Literature.JSW

end
