module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open scoped BigOperators

namespace FractionalPrimes.Literature.LongArithmetic

/-- Remove a finite set of nonzero factors from a multipliable complex product.
The retained infinite product is written with the exact finite-set indicator. -/
theorem tprod_remove_finset
    {β : Type*} [DecidableEq β] (f : β → ℂ) (hf : Multipliable f)
    (S : Finset β) (hfnz : ∀ b ∈ S, f b ≠ 0) :
    (∏' b, if b ∈ S then 1 else f b) =
      (∏' b, f b) * ∏ b ∈ S, (f b)⁻¹ := by
  let g : β → ℂ := fun b => if b ∈ S then 1 else f b
  have h := hf.tsum_congr_cofinite₀ (g := g) hfnz (s := S) (by
    intro b hb
    simp [g, hb])
  have hprod :
      (∏ b ∈ S, if b ∈ S then (1 : ℂ) else f b) = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    simp [hb]
  calc
    (∏' b, if b ∈ S then 1 else f b) =
        (∏' b, f b) *
          ((∏ b ∈ S, if b ∈ S then 1 else f b) / ∏ b ∈ S, f b) := by
      simpa [g] using h
    _ = (∏' b, f b) * (∏ b ∈ S, f b)⁻¹ := by
      rw [hprod]
      simp
    _ = (∏' b, f b) * ∏ b ∈ S, (f b)⁻¹ := by
      rw [← Finset.prod_inv_distrib]

#print axioms tprod_remove_finset

end FractionalPrimes.Literature.LongArithmetic

end
