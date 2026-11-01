module

public import FractionalPrimes.Core
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section
namespace FractionalPrimes
open Filter

/-- Passing from n+1 to the original positive-integer scale filter loses
no convergence assertion. -/
theorem tendsto_scale_of_natSucc {Y : Type*} {l : Filter Y}
    (F : Scale → Y)
    (h : Tendsto (fun n : ℕ => F ⟨n + 1, by omega⟩) atTop l) :
    Tendsto F atTop l := by
  have hindex : Tendsto (fun N : Scale => N.val - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (⟨n + 1, by omega⟩ : Scale)] with N hN
    have hval : n + 1 ≤ N.val := hN
    omega
  have hcomp := h.comp hindex
  have heq : (fun N : Scale => F ⟨N.val - 1 + 1, by omega⟩) = F := by
    funext N
    apply congrArg F
    apply Subtype.ext
    change N.val - 1 + 1 = N.val
    omega
  change Tendsto (fun N : Scale => F ⟨N.val - 1 + 1, by omega⟩) atTop l at hcomp
  rw [heq] at hcomp
  exact hcomp

#print axioms tendsto_scale_of_natSucc
end FractionalPrimes
