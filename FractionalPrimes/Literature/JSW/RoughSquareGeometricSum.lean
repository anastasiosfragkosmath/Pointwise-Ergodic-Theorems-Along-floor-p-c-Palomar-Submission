module

public import FractionalPrimes.Literature.JSW.RoughSquareSourceInterpolation
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The exact two-sided decay sum in the approved rough-square constant. -/

@[expose] public section
namespace FractionalPrimes.Literature.JSW

theorem roughSquareGeometric_natAbs_hasSum
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℤ => q ^ j.natAbs) ((1+q)/(1-q)) := by
  have hnat : HasSum (fun n : ℕ => q^n) (1-q)⁻¹ :=
    hasSum_geometric_of_lt_one hq0 hq1
  have htail : HasSum (fun n : ℕ => q^(n+1)) (q * (1-q)⁻¹) := by
    simpa only [pow_succ, mul_comm] using hnat.mul_left q
  have hsum : HasSum (fun j : ℤ => q^j.natAbs)
      ((1-q)⁻¹ + q*(1-q)⁻¹) := by
    apply HasSum.of_nat_of_neg_add_one
    · simpa using hnat
    · have hn (n : ℕ) : (-((n : ℤ)+1)).natAbs = n+1 := by
        rw [Int.natAbs_neg]
        norm_cast
      simpa only [hn] using htail
  convert hsum using 1 <;> field_simp <;> ring

theorem roughSquareGeometric_decay_hasSum
    {b δ : ℝ} (hb : 1 < b) (hδ : 0 < δ) :
    HasSum (fun j : ℤ => b ^ (-(δ * |(j : ℝ)|)))
      ((1+b^(-δ))/(1-b^(-δ))) := by
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ b^(-δ) := Real.rpow_nonneg hb0.le _
  have hq1 : b^(-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  apply (roughSquareGeometric_natAbs_hasSum hq0 hq1).congr_fun
  intro j
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
  have habs : (j.natAbs : ℝ) = |(j : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  congr 1
  ring

theorem roughSquareGeometric_finite_sum_le
    {b δ : ℝ} (hb : 1 < b) (hδ : 0 < δ) (F : Finset ℤ) :
    ∑ j ∈ F, b ^ (-(δ * |(j : ℝ)|)) ≤ (1+b^(-δ))/(1-b^(-δ)) := by
  have h := roughSquareGeometric_decay_hasSum hb hδ
  rw [← h.tsum_eq]
  exact Summable.sum_le_tsum F
    (fun j _ => Real.rpow_nonneg (by linarith) _) h.summable

#print axioms roughSquareGeometric_finite_sum_le
#print axioms roughSquareGeometric_decay_hasSum
end FractionalPrimes.Literature.JSW
end
