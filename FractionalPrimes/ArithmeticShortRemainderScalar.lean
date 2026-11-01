module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FractionalPrimes

/-- The power product produced by the boundary term after the `U_K log(2K)`
absorption. -/
theorem shortRemainderBoundaryPowerProduct {K η : ℝ}
    (hK : 0 < K) :
    K ^ (η / 4) * (2 * K) * K ^ (-η / 2) ≤
      2 * K ^ (1 - η / 4) := by
  calc
    _ = 2 * (K ^ (η / 4) * K * K ^ (-η / 2)) := by ring
    _ = 2 * (K ^ (η / 4 + 1) * K ^ (-η / 2)) := by
      rw [← Real.rpow_add_one hK.ne' (η / 4)]
    _ = 2 * K ^ (η / 4 + 1 + (-η / 2)) := by
      rw [← Real.rpow_add hK (η / 4 + 1) (-η / 2)]
    _ = 2 * K ^ (1 - η / 4) := by congr 2 <;> ring
    _ ≤ 2 * K ^ (1 - η / 4) := le_rfl

/-- The `K^-2` Taylor-remainder factor is absorbed by the spare `η/4`
power. -/
theorem shortRemainderTaylorPowerProduct {K η : ℝ}
    (hK : 1 ≤ K) (hη : η ≤ 1) :
    K ^ (η / 4) * K * K ^ (-2 : ℝ) ≤ K ^ (1 - η / 4) := by
  have hKpos : 0 < K := by linarith
  calc
    _ = K ^ (η / 4 + 1) * K ^ (-2 : ℝ) := by
      rw [← Real.rpow_add_one hKpos.ne' (η / 4)]
    _ = K ^ (η / 4 + 1 + (-2 : ℝ)) := by
      rw [← Real.rpow_add hKpos (η / 4 + 1) (-2 : ℝ)]
    _ = K ^ (-1 + η / 4) := by congr 1 <;> ring
    _ ≤ K ^ (1 - η / 4) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith)

end FractionalPrimes
