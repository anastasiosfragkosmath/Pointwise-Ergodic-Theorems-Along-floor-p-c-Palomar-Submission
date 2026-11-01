module

public import Mathlib.Data.Nat.Factorization.PrimePow

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

/-- A prime power is determined by its unique prime base and the exponent in
its `Nat.factorization` at that base. -/
theorem primePowerMinFacExponent_injective {n m : ℕ}
    (hn : IsPrimePow n) (hm : IsPrimePow m)
    (hbase : n.minFac = m.minFac)
    (hexponent : n.factorization n.minFac = m.factorization m.minFac) :
    n = m := by
  calc
    n = n.minFac ^ n.factorization n.minFac := hn.minFac_pow_factorization_eq.symm
    _ = m.minFac ^ m.factorization m.minFac := by rw [hexponent, hbase]
    _ = m := hm.minFac_pow_factorization_eq

end FractionalPrimes.Literature.MobiusToLong

end
