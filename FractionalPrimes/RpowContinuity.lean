module

public import FractionalPrimes.Core

/-!
# Continuity of positive real powers on the real line

The P1 Mathlib continuity theorem requires the nonnegative-exponent side
condition explicitly. The fractional-power results in this project already
assume an exponent greater than one, so this lemma packages that consequence.
-/

@[expose] public section

namespace FractionalPrimes

theorem continuous_real_rpow_of_one_lt {c : ℝ} (hc : 1 < c) :
    Continuous (fun t : ℝ => t ^ c) :=
  Real.continuous_rpow_const (le_of_lt (lt_trans zero_lt_one hc))

end FractionalPrimes

end
