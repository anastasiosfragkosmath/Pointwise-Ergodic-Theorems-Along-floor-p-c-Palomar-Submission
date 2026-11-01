module

public import FractionalPrimes.Literature.JSW.PositiveMaximalVectorBounds

/-!
# Exponents for the positive-vector adjoint argument

The lower-`p` part of `lj:positivity` applies the upper-`p` estimate to the
conjugate exponent.  This file checks the exact rational identity needed to
use the source maximal hypothesis, including all denominator side conditions.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

/-- For `1 < p < 2`, the conjugate exponent lies above two and its positive
maximal exponent is exactly the exponent in the source statement. -/
theorem positiveVectorAdjointExponent
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    2 < p / (p - 1) ∧
      (p / (p - 1)) / (p / (p - 1) - 2) = p / (2 - p) := by
  have hden : 0 < p - 1 := by linarith
  have hgap : 0 < 2 - p := by linarith
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith
  · have hden2 : p / (p - 1) - 2 = (2 - p) / (p - 1) := by
      field_simp [ne_of_gt hden]
      ring
    rw [hden2]
    field_simp [ne_of_gt hden, ne_of_gt hgap]

#print axioms positiveVectorAdjointExponent

end FractionalPrimes.Literature.JSW

end
