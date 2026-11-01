module

public import FractionalPrimes.Literature.JSW.SignMomentLowerBound

/-!
# The finite sign moment estimate from `ha:signs`

The recursive Boolean product space in the JSW foundation carries precisely
independent uniform signs. This module exposes its checked lower-moment bound
under the source-facing harmonic declaration name and in the unrooted
expectation form used by the blueprint.
-/

@[expose] public section

open scoped BigOperators

namespace FractionalPrimes

open FractionalPrimes.Literature.JSW

noncomputable section

private theorem signMomentRootConstant_pow {p A : ℝ} (hp : 0 < p)
    (hA : 0 ≤ A) :
    (Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) *
        Real.rpow A (1 / 2)) ^ p =
      Real.rpow 2 (-p / 2) / 12 * Real.rpow A (p / 2) := by
  have h2 :
      (Real.rpow 2 (-1 / 2)) ^ p = Real.rpow 2 (-p / 2) := by
    calc
      (Real.rpow 2 (-1 / 2)) ^ p = Real.rpow 2 ((-1 / 2) * p) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = Real.rpow 2 (-p / 2) := by congr 1 <;> ring
  have h12 : (Real.rpow 12 (-1 / p)) ^ p = (1 / 12 : ℝ) := by
    calc
      (Real.rpow 12 (-1 / p)) ^ p = Real.rpow 12 ((-1 / p) * p) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 12) _ _).symm
      _ = Real.rpow 12 (-1) := by congr 1; field_simp
      _ = (1 / 12 : ℝ) := by
        calc
          Real.rpow 12 (-1) = (12 : ℝ)⁻¹ := Real.rpow_neg_one 12
          _ = (1 / 12 : ℝ) := by norm_num
  have hAroot :
      (Real.rpow A (1 / 2)) ^ p = Real.rpow A (p / 2) := by
    calc
      (Real.rpow A (1 / 2)) ^ p = Real.rpow A ((1 / 2) * p) :=
        (Real.rpow_mul hA _ _).symm
      _ = Real.rpow A (p / 2) := by congr 1 <;> ring
  have hprod :
      (Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) *
          Real.rpow A (1 / 2)) ^ p =
        (Real.rpow 2 (-1 / 2)) ^ p *
          (Real.rpow 12 (-1 / p)) ^ p * (Real.rpow A (1 / 2)) ^ p := by
    rw [Real.mul_rpow
      (x := Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p))
      (y := Real.rpow A (1 / 2)) (z := p)
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 12) _))
      (Real.rpow_nonneg hA _),
      Real.mul_rpow (x := Real.rpow 2 (-1 / 2))
        (y := Real.rpow 12 (-1 / p)) (z := p)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 12) _)]
  calc
    (Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) *
        Real.rpow A (1 / 2)) ^ p =
      (Real.rpow 2 (-1 / 2)) ^ p *
        (Real.rpow 12 (-1 / p)) ^ p * (Real.rpow A (1 / 2)) ^ p := hprod
    _ = Real.rpow 2 (-p / 2) / 12 * Real.rpow A (p / 2) := by
      rw [h2, h12, hAroot]
      ring

/-- The blueprint's finite-sign lower moment estimate. The average is over
the recursive product of `n` independent uniform Boolean signs. The case
`n=0` is included: both the moment and coefficient energy vanish. -/
theorem finiteSignLowerMoment (n : ℕ) (z : Fin n → ℂ) {p : ℝ}
    (hp : 0 < p) :
    Finset.expect (Finset.univ : Finset (jswSignSpace n))
        (fun ω => Real.rpow ‖jswSignSum n ω z‖ p) ≥
      Real.rpow 2 (-p / 2) / 12 *
        Real.rpow (∑ i, ‖z i‖ ^ 2) (p / 2) := by
  let M : ℝ := Finset.expect (Finset.univ : Finset (jswSignSpace n))
    (fun ω => Real.rpow ‖jswSignSum n ω z‖ p)
  let A : ℝ := ∑ i, ‖z i‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi => sq_nonneg ‖z i‖
  have hM : 0 ≤ M := by
    dsimp [M]
    rw [Finset.expect_eq_sum_div_card]
    exact div_nonneg
      (Finset.sum_nonneg fun ω hω => Real.rpow_nonneg (norm_nonneg _) _)
      (by positivity)
  let C : ℝ := Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) *
    Real.rpow A (1 / 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 12) _))
      (Real.rpow_nonneg hA _)
  have hroot : Real.rpow M (1 / p) ≥ C := by
    simpa [M, A, C] using signMomentLowerBound n z hp
  have hrootPow := Real.rpow_le_rpow hC hroot hp.le
  have hleft :
      (Real.rpow M (1 / p)) ^ p = M := by
    calc
      (Real.rpow M (1 / p)) ^ p = Real.rpow M ((1 / p) * p) :=
        (Real.rpow_mul hM _ _).symm
      _ = M := by
        calc
          Real.rpow M ((1 / p) * p) = Real.rpow M 1 := by
            congr 1
            field_simp [hp.ne']
          _ = M := Real.rpow_one M
  rw [hleft] at hrootPow
  have hright := signMomentRootConstant_pow hp hA
  simpa [M, A] using hright.symm.le.trans hrootPow

end

end FractionalPrimes

end
