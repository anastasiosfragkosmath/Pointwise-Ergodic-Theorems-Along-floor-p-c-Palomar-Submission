module

public import FractionalPrimes.Core
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace FractionalPrimes.Literature.LongArithmetic

/-- A residue class with nontrivial integer gcd cannot contain an integer
coprime to the modulus. -/
theorem nonunitResidue_not_coprime
    {n q : ℕ} {a : ℤ}
    (ha : 1 < Int.gcd a (q : ℤ))
    (hmod : (n : ℤ) ≡ a [ZMOD (q : ℤ)]) :
    ¬ Nat.Coprime n q := by
  intro hcop
  have hcopInt : IsCoprime (n : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hmod
  have hcopA : IsCoprime a (q : ℤ) := by
    rw [hk]
    exact hcopInt.add_mul_left_left k
  have hgcd : Int.gcd a (q : ℤ) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcopA
  omega

end FractionalPrimes.Literature.LongArithmetic

#print axioms FractionalPrimes.Literature.LongArithmetic.nonunitResidue_not_coprime
