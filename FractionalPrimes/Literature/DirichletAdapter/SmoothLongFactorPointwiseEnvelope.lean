module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorTypeIComponentAssembly
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorScaleThreshold
public import Mathlib.Tactic

/-! The elementary pointwise error comparison in the Type-I mean estimate. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- Replace the residue-quadrature error by the blueprint's power saving,
using only the exact scale-ratio threshold and `|t|≤U`. -/
theorem smoothLongFactor_quadratureError_le_power
    (X N U η t : ℝ) (q j : ℕ)
    (hX : 0 < X) (hN : 0 < N) (hU : 0 ≤ U)
    (hq : 0 < q) (hj : 1 ≤ j) (ht : |t| ≤ U)
    (hratio : (q : ℝ) * (1 + U) / N ≤ X ^ (-(η / 4))) :
    (q : ℝ) ^ (j - 1) * ((1 + |t|) / N) ^ j ≤
      X ^ (-(j : ℝ) * η / 4) := by
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hbase : 0 ≤ (1 + |t|) / N := by positivity
  have hbase' : (1 + |t|) / N ≤ (1 + U) / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    linarith
  have hqpow : (q : ℝ) ^ (j - 1) ≤ (q : ℝ) ^ j := by
    exact pow_le_pow_right₀ hqone (Nat.sub_le j 1)
  have hfirst : (q : ℝ) ^ (j - 1) * ((1 + |t|) / N) ^ j ≤
      ((q : ℝ) * ((1 + U) / N)) ^ j := by
    rw [mul_pow]
    gcongr
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (q : ℝ) * (1 + U) / N)
    hratio j
  have hExp : (X ^ (-(η / 4))) ^ j = X ^ (-(j : ℝ) * η / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ((q : ℝ) * ((1 + U) / N)) ^ j := hfirst
    _ = ((q : ℝ) * (1 + U) / N) ^ j := by ring
    _ ≤ (X ^ (-(η / 4))) ^ j := hpow
    _ = X ^ (-(j : ℝ) * η / 4) := hExp

#print axioms smoothLongFactor_quadratureError_le_power

end FractionalPrimes.Literature.DirichletAdapter

end
