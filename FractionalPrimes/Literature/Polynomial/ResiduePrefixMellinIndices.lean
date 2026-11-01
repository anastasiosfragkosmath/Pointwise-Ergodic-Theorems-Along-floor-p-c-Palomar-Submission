module
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope
public import FractionalPrimes.Literature.Polynomial.MellinWindowData
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.Polynomial
open scoped BigOperators

 theorem mellinWindowAverageIndices_natCast (X H : ℕ) :
    mellinWindowAverageIndices (X : ℝ) (H : ℝ) = Finset.Ioc X (X + H) := by
  ext n
  simp only [mellinWindowAverageIndices, mellinIntervalIndices,
    ← Nat.cast_add, Nat.ceil_natCast, Finset.mem_filter, Finset.mem_Icc,
    Nat.cast_lt, Nat.cast_le, Finset.mem_Ioc]
  omega

/-- The natural-index Mellin window and integer-index residue prefix have
identical endpoints and residue restriction. -/
theorem residuePrefixSum_eq_mellinWindowSum
    (X H q b : ℕ) (w : ℤ → ℂ) :
    residuePrefixSum X H q b w =
      ∑ n ∈ mellinWindowAverageIndices (X : ℝ) (H : ℝ),
        w (n : ℤ) * (if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0) := by
  classical
  rw [mellinWindowAverageIndices_natCast]
  unfold residuePrefixSum
  rw [Finset.sum_filter]
  have hsum :
      (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        if Int.ModEq (q : ℤ) n (b : ℤ) then w n else 0) =
      ∑ n ∈ Finset.Ioc X (X + H),
        if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then w (n : ℤ) else 0 := by
    symm
    apply Finset.sum_bij (fun (n : ℕ) hn => (n : ℤ))
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp only [realIntegerInterval, ← Nat.cast_add,
        Int.floor_natCast, Finset.mem_Ico]
      omega
    · intro n hn m hm hnm
      exact_mod_cast hnm
    · intro n hn
      have hn' : (X : ℤ) < n ∧ n ≤ (X : ℤ) + H := by
        simp only [realIntegerInterval, ← Nat.cast_add,
          Int.floor_natCast, Finset.mem_Ico] at hn
        omega
      refine ⟨n.toNat, ?_, ?_⟩
      · simp only [Finset.mem_Ioc]
        omega
      · omega
    · intro n hn
      rfl
  rw [hsum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

#print axioms mellinWindowAverageIndices_natCast
#print axioms residuePrefixSum_eq_mellinWindowSum
end FractionalPrimes.Literature.Polynomial
end
