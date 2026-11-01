module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLowFrequency

/-!
# Exact decay bookkeeping for the low-frequency Type-II branch

This isolates the final scalar step after the residue-prefix bound in
`lupo:conditional-integer`.  The input prefix estimate is the one supplied
by the polynomial major-arc task at exponent `a₀`; the output retains the
source gain `H L^(-A)` and the exact source choice
`a₀ = A + 2E + 50a + 3`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators

/-- The low-frequency Type-II variation cost followed by the exact
major-arc prefix estimate gives the source's strict `H L^(-A)` bound. -/
theorem lowFrequencyTypeII_majorArcDecay
    (A a₀ L C H R S : ℝ) (E a : ℕ)
    (_hA : 0 < A) (hL : 2 ≤ L) (hH : 0 < H)
    (ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3)
    (hCpos : 0 < C) (hC : 2 * C < L ^ 2)
    (hPrefix : R ≤ C * H * L ^ (-a₀))
    (hVariation : S ≤ R * L ^ (2 * E + 50 * a + 1)) :
    S < H * L ^ (-A) := by
  have hLpos : 0 < L := by linarith
  have hexp :
      -a₀ + ((2 * E + 50 * a + 1 : ℕ) : ℝ) = -A - 2 := by
    rw [ha₀]
    push_cast
    ring
  have hcancel : L ^ (-a₀) * L ^ (2 * E + 50 * a + 1) =
      L ^ (-A - 2) := by
    rw [← Real.rpow_natCast L (2 * E + 50 * a + 1),
      ← Real.rpow_add hLpos, hexp]
  have hrestore : L ^ 2 * L ^ (-A - 2) = L ^ (-A) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hLpos]
    congr 1
    ring
  have hfactorPos : 0 < H * L ^ (-A - 2) := by positivity
  have hCsmall : C < L ^ 2 := by nlinarith [hCpos, hC]
  calc
    S ≤ R * L ^ (2 * E + 50 * a + 1) := hVariation
    _ ≤ (C * H * L ^ (-a₀)) * L ^ (2 * E + 50 * a + 1) :=
      mul_le_mul_of_nonneg_right hPrefix (by positivity)
    _ = C * (H * L ^ (-A - 2)) := by
      calc
        (C * H * L ^ (-a₀)) * L ^ (2 * E + 50 * a + 1) =
            C * H * (L ^ (-a₀) * L ^ (2 * E + 50 * a + 1)) := by ring
        _ = C * (H * L ^ (-A - 2)) := by rw [hcancel]; ring
    _ < L ^ 2 * (H * L ^ (-A - 2)) :=
      mul_lt_mul_of_pos_right hCsmall hfactorPos
    _ = H * L ^ (-A) := by
      calc
        L ^ 2 * (H * L ^ (-A - 2)) = H * (L ^ 2 * L ^ (-A - 2)) := by ring
        _ = H * L ^ (-A) := by rw [hrestore]

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.lowFrequencyTypeII_majorArcDecay
