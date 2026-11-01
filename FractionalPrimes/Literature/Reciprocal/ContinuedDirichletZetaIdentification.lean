module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletData
public import FractionalPrimes.Literature.Reciprocal.ZetaFloorBlueprintIdentification

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The `Z` introduced in `lrc:dirichlet-data` is definitionally the same
pole-excluded floor-correction function used in the Mathlib identification. -/
theorem continuedDirichletZ_eq_blueprintZeta {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    continuedDirichletZ s hs hs1 = blueprintZeta ⟨s, hs1⟩ := by
  rfl

/-- The continued-data definition of the principal `Z(s)` agrees with
Mathlib's Riemann zeta function throughout its pole-excluded domain. -/
theorem continuedDirichletZ_eq_riemannZeta {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    continuedDirichletZ s hs hs1 = riemannZeta s := by
  rw [continuedDirichletZ_eq_blueprintZeta hs hs1]
  exact blueprintZeta_eq_riemannZeta (s := ⟨s, hs1⟩) hs

#print axioms continuedDirichletZ_eq_riemannZeta

end FractionalPrimes.Literature.Reciprocal
