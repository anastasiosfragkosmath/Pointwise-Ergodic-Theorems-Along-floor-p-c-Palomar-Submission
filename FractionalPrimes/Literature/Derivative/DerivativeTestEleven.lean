module

public import FractionalPrimes.ArithmeticBasics

@[expose] public section

namespace FractionalPrimes.Literature.Derivative

/-- Manifest-facing name for the approved constant-11 derivative test.

The half-open regularity data, floor-length condition, derivative bounds,
normalization, and all three exponents are exactly those of
`FractionalPrimes.externalDerivativeTest`; this declaration only places the
already checked result at the name specified by blueprint `ld:main`. -/
theorem derivativeTestEleven
    {x L lam R : ℝ} {j : ℕ}
    (data : FractionalPrimes.HalfOpenCkData x L j)
    (hj : 3 ≤ j) (hfloor : (j : ℝ) < (Int.floor L : ℝ))
    (hR : 1 ≤ R) (hlam : 0 < lam)
    (hlower : ∀ t ∈ Set.Ioc x (x + L),
      lam ≤ |data.derivative j t|)
    (hupper : ∀ t ∈ Set.Ioc x (x + L),
      |data.derivative j t| ≤ R * lam) :
    ‖∑ n ∈ FractionalPrimes.realIntegerInterval x L,
      FractionalPrimes.realExponentialPhase (data.derivative 0) n‖ / L ≤
    11 * max ((R / L) ^ (2 / (2 : ℝ) ^ j))
      (max ((R ^ 2 * lam) ^ (1 / ((2 : ℝ) ^ j - 2)))
        ((lam * L ^ j) ^ (-2 / (2 : ℝ) ^ j))) := by
  exact FractionalPrimes.externalDerivativeTest
    data hj hfloor hR hlam hlower hupper

#print axioms derivativeTestEleven

end FractionalPrimes.Literature.Derivative
