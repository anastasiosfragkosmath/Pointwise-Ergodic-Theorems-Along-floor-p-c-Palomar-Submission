module

@[expose] public section

namespace FractionalPrimes.Literature.JSW

/-!
# JSW foundation boundary

This documents the source's allowed foundational interfaces:

* F1: finite and countable arithmetic, elementary inequalities,
  finite-dimensional inner-product identities, and geometric series.
* F2: real and complex calculus, integration by parts, changes of variables,
  and smooth cutoffs.
* F3: Lebesgue measure and regularity, scalar `L^p` density, Tonelli, Fubini,
  Hölder, Minkowski, Chebyshev, Fatou, monotone and dominated convergence,
  scalar `L^p` completeness, and duality.
* F4: Schwartz Fourier inversion and its elementary convolution identities.

The list is documentary. This file adds no logical postulate, certificate parameter, or
structure carrying unproved theorem fields. The named proposition is only a
proved marker for the blueprint metadata; analytical statements used later
remain separate proof obligations.
-/

/-- Proved marker for the documentary F1--F4 inventory. -/
theorem FoundationBoundary : True := trivial

end FractionalPrimes.Literature.JSW

end
