module

public import FractionalPrimes.Literature.Polynomial.PolynomialCramerCentreChangeInterval

/-! The exact three-clause real-centre change of `lc:model-difference`. -/

@[expose] public section

namespace FractionalPrimes.Literature.Centres

/-- Blueprint `lc:model-difference`: the integer samples of `(x,x+h]`
are precisely those between the floor endpoints, their count differs from
`h` by less than one, and the two Cramér models have the displayed
`K_A` error on those samples. -/
theorem cramerChangeCentre {A x h : ℝ}
    (hA : 0 < A) (hx : 4 ≤ x) (hh : x ^ (5 / 8 : ℝ) ≤ h) :
    FractionalPrimes.realIntegerInterval x h =
        Finset.Ioc (Int.floor x) (Int.floor (x + h)) ∧
      |((Int.floor (x + h) - Int.floor x : ℤ) : ℝ) - h| < 1 ∧
      (∑ n ∈ FractionalPrimes.realIntegerInterval x h,
        |FractionalPrimes.paperCramerWeight
              (FractionalPrimes.paperShortBlockCutoff x) n -
            FractionalPrimes.paperCramerWeight
              (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) n|) ≤
        Real.exp 13 * 2 ^ A *
          (8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
            4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5)) *
          h * (Real.log x) ^ (-A : ℝ) := by
  exact ⟨Polynomial.realIntegerInterval_eq_floor_Ioc x h,
    Polynomial.floorEndpointLength_error_abs_lt_one x h,
    Polynomial.paperCramerChangeCentre_realIntegerInterval_bound hA hx hh⟩

#print axioms cramerChangeCentre

end FractionalPrimes.Literature.Centres

end
