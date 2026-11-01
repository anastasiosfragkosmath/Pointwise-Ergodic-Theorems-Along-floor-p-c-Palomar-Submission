module

public import FractionalPrimes.Literature.Polynomial.PolynomialCramerCentreChange

/-!
# Cramér centre change on the source integer interval

This module transfers the checked natural-floor-index estimate to the exact
integer interval `(x, x + h]` used in blueprint `lc:model-difference`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

/-- Reindex a floor-bounded natural sum as a sum over the corresponding
integer floor interval. The endpoint floors agree under the casts when the
real endpoints are nonnegative. -/
theorem natFloorIoc_sum_eq_intFloorIoc
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {α : Type*} [AddCommMonoid α] (f : ℤ → α) :
    (∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y), f (n : ℤ)) =
      ∑ z ∈ Finset.Ioc (Int.floor x) (Int.floor y), f z := by
  classical
  have hxfloor : ((Nat.floor x : ℕ) : ℤ) = Int.floor x :=
    Int.natCast_floor_eq_floor hx
  have hyfloor : ((Nat.floor y : ℕ) : ℤ) = Int.floor y :=
    Int.natCast_floor_eq_floor hy
  have hset : Finset.Ioc (Int.floor x) (Int.floor y) =
      (Finset.Ioc (Nat.floor x) (Nat.floor y)).map Nat.castEmbedding := by
    ext z
    simp only [Finset.mem_map, Finset.mem_Ioc, Nat.castEmbedding_apply]
    constructor
    · intro hz
      have hz0 : 0 ≤ z := by
        have hfloor0 : (0 : ℤ) ≤ Int.floor x := by
          rw [← hxfloor]
          exact_mod_cast (Nat.zero_le (Nat.floor x))
        exact le_trans hfloor0 (le_of_lt hz.1)
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
      refine ⟨z.toNat, ?_, hzcast⟩
      constructor
      · have hleft : Int.floor x < (z.toNat : ℤ) := by
          rw [hzcast]
          exact hz.1
        rw [← hxfloor] at hleft
        exact_mod_cast hleft
      · have hright : (z.toNat : ℤ) ≤ Int.floor y := by
          rw [hzcast]
          exact hz.2
        rw [← hyfloor] at hright
        exact_mod_cast hright
    · rintro ⟨n, hn, hcast⟩
      rw [← hcast]
      constructor
      · have hleft : (Nat.floor x : ℤ) < (n : ℤ) := by
          exact_mod_cast hn.1
        rw [hxfloor] at hleft
        exact hleft
      · have hright : (n : ℤ) ≤ (Nat.floor y : ℤ) := by
          exact_mod_cast hn.2
        rw [hyfloor] at hright
        exact hright
  calc
    _ = ∑ z ∈ (Finset.Ioc (Nat.floor x) (Nat.floor y)).map Nat.castEmbedding, f z := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ z ∈ Finset.Ioc (Int.floor x) (Int.floor y), f z := by
      rw [← hset]

/-- The exact `lc:model-difference` Cramér-model estimate summed over the
source integer interval `(x, x + h]`. The constant is unchanged from the
natural-index estimate. -/
theorem paperCramerChangeCentre_realIntegerInterval_bound {A x h : ℝ}
    (hA : 0 < A) (hx : 4 ≤ x) (hh : x ^ (5 / 8 : ℝ) ≤ h) :
    (∑ n ∈ FractionalPrimes.realIntegerInterval x h,
      |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff x) n -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) n|) ≤
      Real.exp 13 * 2 ^ A *
        (8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
          4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5)) *
        h * (Real.log x) ^ (-A : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hxnonneg : 0 ≤ x := le_of_lt hxpos
  have hhpos : 0 < h :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hh
  have hypos : 0 < x + h := by linarith
  calc
    _ = ∑ n ∈ Finset.Ioc (Int.floor x) (Int.floor (x + h)),
          |FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff x) n -
            FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) n| := by
          rw [realIntegerInterval_eq_floor_Ioc]
    _ = ∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + h)),
          |FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
            FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)| := by
          symm
          exact natFloorIoc_sum_eq_intFloorIoc hxnonneg (le_of_lt hypos)
            (fun n : ℤ =>
              |FractionalPrimes.paperCramerWeight
                    (FractionalPrimes.paperShortBlockCutoff x) n -
                FractionalPrimes.paperCramerWeight
                    (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) n|)
    _ ≤ Real.exp 13 * 2 ^ A *
          (8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
            4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5)) *
          h * (Real.log x) ^ (-A : ℝ) :=
        paperCramerChangeCentre_floor_bound hA hx hh

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.natFloorIoc_sum_eq_intFloorIoc
#print axioms FractionalPrimes.Literature.Polynomial.paperCramerChangeCentre_realIntegerInterval_bound
