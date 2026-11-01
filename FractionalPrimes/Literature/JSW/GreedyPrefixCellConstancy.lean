module

public import FractionalPrimes.Literature.JSW.GreedyPrefixPredictability

/-!
# Predictability of greedy prefix labels on dyadic cells

The greedy label active before a martingale difference is determined by
averages at coarser scales. Those averages are constant on the cell on
which the difference is predicted.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

/-- The number of greedy crossings already seen at time `t` is constant
on the dyadic cell of the next martingale difference. -/
theorem greedyPrefixStopCount_eq_on_predictable_cell
    (L : ℤ) (t : ℕ) (f : ℝ → ℂ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (j : ℤ) {x y : ℝ}
    (hx : x ∈ dyadicInterval (1 - (L + ((t + 1 : ℕ) : ℤ))) j)
    (hy : y ∈ dyadicInterval (1 - (L + ((t + 1 : ℕ) : ℤ))) j) :
    greedyPrefixStopCount (fun k => dyadicAverage (-(L + (k : ℤ))) f x)
      threshold hthreshold t =
    greedyPrefixStopCount (fun k => dyadicAverage (-(L + (k : ℤ))) f y)
      threshold hthreshold t := by
  apply greedyPrefixStopCount_congr_prefix
  intro k hkt
  apply dyadicAverage_eq_on_finer_cell (r := 1 - (L + ((t + 1 : ℕ) : ℤ)))
    (s := -(L + (k : ℤ))) (j := j) (f := f)
  · omega
  · exact hx
  · exact hy

end FractionalPrimes.Literature.JSW

end
