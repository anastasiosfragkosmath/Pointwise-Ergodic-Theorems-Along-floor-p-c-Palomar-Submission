module

public import FractionalPrimes.Literature.JSW.PositiveVectorExponentBridge

/-!
# Integrability of finite positive energies

This is the precise `L^(p/2)` prerequisite for the finite-family pairing in
`lj:positivity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A finite sum of squared `L^p` coordinates belongs to `L^(p/2)`.
The helper also applies outside the `p>2` range where the source uses it. -/
theorem finitePositiveEnergy_memLp
    {ι : Type*} [Fintype ι] {p : ℝ}
    (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume) :
    MemLp (fun x => ∑ i, ‖f i x‖ ^ 2)
      (ENNReal.ofReal (p / 2)) volume := by
  classical
  have hpow : ∀ i, MemLp (fun x => ‖f i x‖ ^ 2)
      (ENNReal.ofReal (p / 2)) volume := by
    intro i
    have h := (hf i).norm_rpow_div (2 : ℝ≥0∞)
    convert h using 1
    · ext x
      simp
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
      norm_num
  exact memLp_finsetSum Finset.univ (fun i _ => hpow i)

#print axioms finitePositiveEnergy_memLp

end

end FractionalPrimes.Literature.JSW

end
