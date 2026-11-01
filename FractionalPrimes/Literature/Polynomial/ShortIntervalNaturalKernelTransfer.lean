module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalLargeValueKernel
public import FractionalPrimes.Literature.Polynomial.ShortIntervalDirichletMeanValue

/-! The scalar Gram-kernel estimate transferred to the natural-number
indexing used by the finite Dirichlet polynomial. This is a finite
reindexing prerequisite for `lgv:local-large-values`; it does not use the
separated-time estimate `lgv:sample-square`.

Blueprint: `expanded-blueprint.tex:5430-5462` (`lgv:kernel` and the indexing
in `lgv:data`). Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex:9-57`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LargeValues

open FractionalPrimes
open scoped BigOperators

private lemma dirichletIndices_mem_iff {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    n ∈ dirichletIndices N ↔ N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  rw [dirichletIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, hleft⟩
    have hfloor : n ≤ Nat.floor (2 * N) := by omega
    have hfloorR : (n : ℝ) ≤ Nat.floor (2 * N) := by exact_mod_cast hfloor
    exact ⟨hleft, le_trans hfloorR (Nat.floor_le (by positivity))⟩
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, hleft⟩
    have hfloor : n ≤ Nat.floor (2 * N) := Nat.le_floor hright
    omega

/-- The scalar Gram-kernel estimate in the natural-number interval used by
the short-interval Dirichlet polynomial. -/
theorem gramKernelBound_nat (N u : ℝ) (hN : 2 ≤ N) :
    ‖∑ n ∈ dirichletIndices N,
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖ ≤
      64 * (N / (1 + |u|) + Real.sqrt |u|) := by
  classical
  have hN0 : 0 ≤ N := by linarith
  have hsum :
      (∑ n ∈ dirichletIndices N,
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))) =
      ∑ z ∈ realIntegerInterval N N, scalarGramKernelPhase u z := by
    apply Finset.sum_bij
      (s := dirichletIndices N) (t := realIntegerInterval N N)
      (f := fun n : ℕ =>
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)))
      (g := fun z : ℤ => scalarGramKernelPhase u z)
      (fun n _ => (n : ℤ))
    · intro n hn
      have hn' := (dirichletIndices_mem_iff hN0 n).mp hn
      apply (mem_realIntegerInterval_iff N N (n : ℤ)).2
      constructor
      · exact_mod_cast hn'.1
      · have hnupper : (n : ℝ) ≤ N + N := by nlinarith [hn'.2]
        exact_mod_cast hnupper
    · intro n hn m hm hcast
      exact_mod_cast hcast
    · intro z hz
      have hz' := (mem_realIntegerInterval_iff N N z).mp hz
      have hzpos : 0 < (z : ℝ) := lt_trans (by linarith [hN]) hz'.1
      have hz0 : 0 ≤ z := by exact_mod_cast (le_of_lt hzpos)
      refine ⟨z.toNat, (dirichletIndices_mem_iff hN0 z.toNat).2 ?_, ?_⟩
      · constructor
        · have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
            exact_mod_cast (Int.toNat_of_nonneg hz0)
          rw [hcast]
          exact hz'.1
        · have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
            exact_mod_cast (Int.toNat_of_nonneg hz0)
          rw [hcast]
          nlinarith [hz'.2]
      · exact Int.toNat_of_nonneg hz0
    · intro n hn
      unfold scalarGramKernelPhase
      congr 1
      push_cast
      ring
  calc
    ‖∑ n ∈ dirichletIndices N,
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖ =
        ‖∑ z ∈ realIntegerInterval N N, scalarGramKernelPhase u z‖ := by
          rw [hsum]
    _ ≤ 64 * (N / (1 + |u|) + Real.sqrt |u|) := gramKernelBound N u hN

#print axioms gramKernelBound_nat

end FractionalPrimes.Literature.LargeValues
