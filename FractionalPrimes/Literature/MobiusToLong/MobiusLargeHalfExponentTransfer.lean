module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

/-- The modulus range for the large half of the hyperbola transfers from
logarithmic exponent `B` at `x` to exponent `B + 1` at every intermediate
scale `u ∈ [sqrt x, x]`. This is the exponent-transfer step in
`lml:large-half`. -/
theorem mobius_log_exponent_transfer
    {x u : ℝ} {q : ℕ} {B : ℝ}
    (hx : 9 ≤ x) (hB : 0 < B)
    (hlog : (2 : ℝ) ^ (B + 1) ≤ Real.log x)
    (huLower : Real.sqrt x ≤ u) (_huUpper : u ≤ x)
    (hq : (q : ℝ) ≤ (Real.log x) ^ B) :
    (q : ℝ) ≤ (Real.log u) ^ (B + 1) := by
  have hxpos : 0 < x := by linarith
  have hxgt1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hxgt1
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsqrt3 : (3 : ℝ) ≤ Real.sqrt x := by
    have hroot9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc
      (3 : ℝ) = Real.sqrt 9 := hroot9.symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hu3 : (3 : ℝ) ≤ u := hsqrt3.trans huLower
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hhalf : (2 : ℝ) ^ B ≤ Real.log x / 2 := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) B 1,
      Real.rpow_one] at hlog
    linarith
  have hhalfpos : 0 < Real.log x / 2 := by positivity
  have hmid : (Real.log x) ^ B ≤ (Real.log x / 2) ^ (B + 1) := by
    have hfactor : (Real.log x) ^ B =
        (2 : ℝ) ^ B * (Real.log x / 2) ^ B := by
      calc
        (Real.log x) ^ B = (2 * (Real.log x / 2)) ^ B := by congr 1 <;> ring
        _ = (2 : ℝ) ^ B * (Real.log x / 2) ^ B :=
          Real.mul_rpow (by norm_num) (by positivity)
    have hcompare :
        (2 : ℝ) ^ B * (Real.log x / 2) ^ B ≤
          (Real.log x / 2) * (Real.log x / 2) ^ B :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hhalfpos.le B)
    have hsplit : (Real.log x / 2) ^ (B + 1) =
        (Real.log x / 2) ^ B * (Real.log x / 2) := by
      rw [Real.rpow_add hhalfpos B 1, Real.rpow_one]
    calc
      (Real.log x) ^ B =
          (2 : ℝ) ^ B * (Real.log x / 2) ^ B := hfactor
      _ ≤ (Real.log x / 2) * (Real.log x / 2) ^ B := hcompare
      _ = (Real.log x / 2) ^ B * (Real.log x / 2) := by ring
      _ = (Real.log x / 2) ^ (B + 1) := hsplit.symm
  have hloglower : Real.log x / 2 ≤ Real.log u := by
    calc
      Real.log x / 2 = Real.log (Real.sqrt x) := by
        rw [Real.log_sqrt hxpos.le]
      _ ≤ Real.log u := Real.log_le_log hsqrtpos huLower
  have hpower : (Real.log x / 2) ^ (B + 1) ≤ (Real.log u) ^ (B + 1) :=
    Real.rpow_le_rpow hhalfpos.le hloglower (by linarith)
  exact hq.trans (hmid.trans hpower)

end FractionalPrimes.Literature.MobiusToLong
