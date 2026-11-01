module

public import FractionalPrimes.Literature.Twisted.SmoothDyadicCutoff
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic

/-!
# The finite smooth dyadic partition used by the smooth Heath--Brown expansion

This file proves the exact finite partition of unity in `lda:smooth-hb`,
before distributing its factors through the truncated Heath--Brown identity.
The profile's integral and derivative constants are not used here.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open Finset

noncomputable section

/-- The exact terminal index `ceil(log₂(4X))` in the smooth partition. -/
def smoothHeathBrownDepth (X : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (4 * X))

private theorem dyadicEta_telescoping (η : ℝ → ℝ) (x : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
      (η (x / (2 : ℝ) ^ j) - η (2 * x / (2 : ℝ) ^ j))) =
        η (x / (2 : ℝ) ^ J) - η (2 * x) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ]
      have hcancel :
          2 * x / (2 : ℝ) ^ (J + 1) = x / (2 : ℝ) ^ J := by
        rw [pow_succ]
        field_simp
      rw [ih, hcancel]
      ring_nf

/-- The exact telescope for the source smooth cutoff
`theta(u) = eta(u) - eta(2u)`. -/
theorem smoothDyadicTheta_telescoping (x : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
      FractionalPrimes.Literature.Twisted.smoothDyadicTheta
        (x / (2 : ℝ) ^ j)) =
      FractionalPrimes.Literature.Twisted.smoothDyadicEta
        (x / (2 : ℝ) ^ J) -
        FractionalPrimes.Literature.Twisted.smoothDyadicEta (2 * x) := by
  calc
    (∑ j ∈ Finset.range (J + 1),
        FractionalPrimes.Literature.Twisted.smoothDyadicTheta
          (x / (2 : ℝ) ^ j)) =
      ∑ j ∈ Finset.range (J + 1),
        (FractionalPrimes.Literature.Twisted.smoothDyadicEta
            (x / (2 : ℝ) ^ j) -
          FractionalPrimes.Literature.Twisted.smoothDyadicEta
            (2 * x / (2 : ℝ) ^ j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [FractionalPrimes.Literature.Twisted.smoothDyadicTheta]
              congr 1
              rw [← mul_div_assoc]
    _ = _ := dyadicEta_telescoping
      FractionalPrimes.Literature.Twisted.smoothDyadicEta x J

/-- The source's exact finite smooth dyadic partition: for every positive
integer `n ≤ 3X`, the scales `2^j`, `0 ≤ j ≤ ceil(log₂(4X))`, sum to one. -/
theorem smoothDyadicTheta_partition {X : ℝ} (hX : 3 ≤ X) {n : ℕ}
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    (∑ j ∈ Finset.range (smoothHeathBrownDepth X + 1),
      FractionalPrimes.Literature.Twisted.smoothDyadicTheta
        ((n : ℝ) / (2 : ℝ) ^ j)) = 1 := by
  let J := smoothHeathBrownDepth X
  have hXpos : 0 < X := by linarith
  have hlog : Real.logb 2 (4 * X) ≤ (J : ℝ) := by
    dsimp [J, smoothHeathBrownDepth]
    exact Nat.le_ceil _
  have hpowReal : 4 * X ≤ (2 : ℝ) ^ (J : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ))
      (by positivity : 0 < 4 * X)).mp hlog
  have hpow : 4 * X ≤ (2 : ℝ) ^ J := by
    simpa only [Real.rpow_natCast] using hpowReal
  have hn4X : (n : ℝ) ≤ 4 * X := by linarith
  have hden : 0 < (2 : ℝ) ^ J := by positivity
  have hsmall : (n : ℝ) / (2 : ℝ) ^ J ≤ 1 :=
    (div_le_iff₀ hden).2 (by nlinarith [le_trans hn4X hpow])
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlarge : 2 ≤ 2 * (n : ℝ) := by linarith
  rw [smoothDyadicTheta_telescoping]
  rw [FractionalPrimes.Literature.Twisted.smoothDyadicEta_eq_one_of_le_one hsmall,
    FractionalPrimes.Literature.Twisted.smoothDyadicEta_eq_zero_of_two_le hlarge]
  norm_num

end

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothDyadicTheta_partition
