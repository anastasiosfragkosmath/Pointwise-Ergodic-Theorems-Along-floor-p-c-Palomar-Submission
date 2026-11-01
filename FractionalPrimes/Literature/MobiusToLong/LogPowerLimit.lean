module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic

@[expose] public section

open Filter
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

/-- The logarithmic power appearing in the second Möbius tail tends to zero. -/
theorem log_rpow_one_sub_tendsto_zero {R : ℝ} (hR : 3 < R) :
    Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 - R)) atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun y : ℝ => y ^ (-(R - 1))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < R - 1)
  have hlog := hpow.comp Real.tendsto_log_atTop
  have hEq :
      (fun y : ℝ => y ^ (-(R - 1))) ∘ Real.log =ᶠ[atTop]
        (fun x : ℝ => Real.rpow (Real.log x) (1 - R)) := by
    exact Filter.Eventually.of_forall fun x => by
      simp only [Function.comp_apply, Real.rpow_eq_pow,
        show 1 - R = -(R - 1) by ring]
  exact Tendsto.congr' hEq hlog

end FractionalPrimes.Literature.MobiusToLong
