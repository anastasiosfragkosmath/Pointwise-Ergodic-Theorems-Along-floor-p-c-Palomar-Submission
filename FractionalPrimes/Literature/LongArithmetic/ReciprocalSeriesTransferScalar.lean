module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

namespace FractionalPrimes.Literature.LongArithmetic

/-- Scalar identity used when evaluating the reciprocal-power tail integral. -/
theorem transfer_integral_denominator_identity {v : ℝ} (_hv : 1 < v) :
    -1 / (-v + 1) = 1 / (v - 1) := by
  rw [show -v + 1 = -(v - 1) by ring]
  rw [neg_div_neg_eq]

end FractionalPrimes.Literature.LongArithmetic

end
