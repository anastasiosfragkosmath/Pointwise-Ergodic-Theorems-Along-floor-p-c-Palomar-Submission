module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylWeightedDistance
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- After the affine-recurrence and degree-induction steps, the source
denominator `q = s * r^(d-1)` has the approved recursive cap and its top
coefficient has the corresponding distance bound. The premise `hR` records
the `R ≥ 1` fact needed to pass from `R^(d-2)` to `R^(d-1)`; at the consumer
it must be discharged from the recursive constants evaluated at
`δ⁻¹` (and also follows from `1 ≤ r ≤ R`). -/
theorem scalarWeyl_topCoefficientAndDenominator
    {d N r s : ℕ} {D R αd : ℝ}
    (hd : 2 ≤ d) (hN : 1 ≤ N)
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrR : (r : ℝ) ≤ R) (hsD : (s : ℝ) ≤ D)
    (hR : 1 ≤ R)
    (hnear : realDistanceToIntegers ((r : ℝ) * αd) ≤
      R / ((N : ℝ) ^ d)) :
    1 ≤ s * r ^ (d - 1) ∧
      ((s * r ^ (d - 1) : ℕ) : ℝ) ≤ D * R ^ (d - 1) ∧
      realDistanceToIntegers (((s * r ^ (d - 1) : ℕ) : ℝ) * αd) ≤
        D * R ^ (d - 1) / ((N : ℝ) ^ d) := by
  have hd' : d - 1 = (d - 2) + 1 := by omega
  have hRnonneg : 0 ≤ R := by linarith
  have hDnonneg : 0 ≤ D := by
    have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hrnonneg : 0 ≤ (r : ℝ) := by positivity
  have hrCast : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hNposNat : 0 < N := by omega
  have hrPosNat : 0 < r := by omega
  have hsPosNat : 0 < s := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hNpowpos : 0 < (N : ℝ) ^ d := pow_pos hNpos _
  have hpowR : (r : ℝ) ^ (d - 1) ≤ R ^ (d - 1) :=
    pow_le_pow_left₀ hrnonneg hrR _
  have hqCast : ((s * r ^ (d - 1) : ℕ) : ℝ) =
      (s : ℝ) * (r : ℝ) ^ (d - 1) := by
    push_cast
    ring
  have hqUpper : ((s * r ^ (d - 1) : ℕ) : ℝ) ≤
      D * R ^ (d - 1) := by
    rw [hqCast]
    calc
      (s : ℝ) * (r : ℝ) ^ (d - 1) ≤
          D * (r : ℝ) ^ (d - 1) :=
        mul_le_mul_of_nonneg_right hsD (pow_nonneg hrnonneg _)
      _ ≤ D * R ^ (d - 1) :=
        mul_le_mul_of_nonneg_left hpowR hDnonneg
  have hqpos : 0 < s * r ^ (d - 1) :=
    Nat.mul_pos hsPosNat (Nat.pow_pos hrPosNat)
  have hqLower : 1 ≤ s * r ^ (d - 1) := by omega
  let k : ℕ := s * r ^ (d - 2)
  have hqFactor : s * r ^ (d - 1) = k * r := by
    dsimp [k]
    rw [hd', pow_succ]
    ring
  have hqPhase :
      ((s * r ^ (d - 1) : ℕ) : ℝ) * αd =
        (k : ℝ) * ((r : ℝ) * αd) := by
    rw [hqFactor]
    push_cast
    ring
  let S : Finset Unit := {()}
  have hweighted := realDistanceToIntegers_intWeightedSum_le
      S (fun _ : Unit => (k : ℤ))
      (fun _ : Unit => (r : ℝ) * αd)
      (fun _ : Unit => R / ((N : ℝ) ^ d)) (by
        intro i hi
        exact hnear)
  have hscaled :
      realDistanceToIntegers ((k : ℝ) * ((r : ℝ) * αd)) ≤
        (k : ℝ) * (R / ((N : ℝ) ^ d)) := by
    simpa [S] using hweighted
  have hkCast : (k : ℝ) ≤ D * R ^ (d - 2) := by
    dsimp [k]
    push_cast
    calc
      (s : ℝ) * (r : ℝ) ^ (d - 2) ≤
          D * (r : ℝ) ^ (d - 2) :=
        mul_le_mul_of_nonneg_right hsD (pow_nonneg hrnonneg _)
      _ ≤ D * R ^ (d - 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hrnonneg hrR _) hDnonneg
  have hpowStep : R ^ (d - 2) * R = R ^ (d - 1) := by
    rw [hd', pow_succ]
  have hscale :
      (k : ℝ) * (R / ((N : ℝ) ^ d)) ≤
        D * R ^ (d - 1) / ((N : ℝ) ^ d) := by
    calc
      (k : ℝ) * (R / ((N : ℝ) ^ d)) ≤
          (D * R ^ (d - 2)) * (R / ((N : ℝ) ^ d)) :=
        mul_le_mul_of_nonneg_right hkCast
          (div_nonneg hRnonneg (le_of_lt hNpowpos))
      _ = D * R ^ (d - 1) / ((N : ℝ) ^ d) := by
        field_simp [ne_of_gt hNpowpos]
        rw [mul_assoc, hpowStep]
  refine ⟨hqLower, hqUpper, ?_⟩
  rw [hqPhase]
  exact hscaled.trans hscale

end FractionalPrimes.Literature.Polynomial
