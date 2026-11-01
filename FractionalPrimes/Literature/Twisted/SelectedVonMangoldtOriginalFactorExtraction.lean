module
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorOfMobiusGoal
public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtGroupTruncatedExtraction
@[expose] public section

noncomputable section
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators
namespace FractionalPrimes.Literature.Twisted

private theorem factorExtractionAllocationCoordinate_le {k r : ℕ}
    (d : divisorFactorTuples k r) (i : Fin k) :
    (d.1 i).1 ≤ r := by
  have hprod : (d.1 i).1 ≤ ∏ j : Fin k, (d.1 j).1 := by
    simpa using
      (Finset.single_le_prod
        (s := Finset.univ) (f := fun j : Fin k => (d.1 j).1)
        (fun j hj => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (d.1 j).2))
        (Finset.mem_univ i))
  rw [d.2] at hprod
  exact hprod

private theorem factorExtractionAllocationResidual_pos_le {k r : ℕ}
    (hr : 0 < r) (d : divisorFactorTuples k r) (i : Fin k) :
    0 < factorExtractionAllocationResidual d i ∧
      factorExtractionAllocationResidual d i ≤ r := by
  let P := ∏ j ∈ Finset.Iic i, (d.1 j).1
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun j hj => (d.1 j).2
  have hPle : P ≤ r := by
    calc
      P ≤ ∏ j ∈ Finset.univ, (d.1 j).1 := by
        apply Finset.prod_le_prod_of_subset_of_one_le
          (Finset.subset_univ _)
        intro j hj hjnot
        exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (d.1 j).2)
      _ = r := d.2
  constructor
  · exact Nat.div_pos hPle hPpos
  · exact Nat.div_le_self _ _

/-- Exact source factor extraction for the selected von Mangoldt group,
using the original long factor estimate on every divisor allocation.
The possible logarithmic factor retains its literal log(8X) loss. -/
theorem selectedVonMangoldtGroup_originalFactorExtraction
    {X z t x y : ℝ} (hX : 3 ≤ X)
    (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i₀ : Fin (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length)
    {r Q : ℕ} (hr : 1 ≤ r) (χ : BlueprintCharacter Q)
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hz : 0 ≤ z) {a : ℝ}
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (hQ : 1 ≤ Q) (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hfreqlo : (Real.log X) ^ (45 * a) ≤ |t|)
    (hfreqhi : |t| ≤ X ^ (a + 1))
    (hOrig : OriginalLongFactorAt X
      (dyadicFactorScale
        ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get i₀)) t a) :
    ‖(dyadicBinomialCoefficient ν.1 : ℂ) *
      ∑ n ∈ factorExtractionRealInterval x y,
        dyadicFactorComplexProduct z
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) (r * n) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) t n‖ ≤
      (2 : ℝ) ^ 10 *
        (3 : ℝ) ^
          ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length - 1) *
        (divisorFunction
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length
          ⟨r, lt_of_lt_of_le (by decide) hr⟩ : ℝ) *
        (Real.log X) ^ (-21 * a) * Real.sqrt
          (dyadicFactorScaleProduct
            (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) /
              (r : ℝ)) * Real.log (8 * X) := by
  classical
  let factors := selectedDyadicFactors (vonMangoldtLabelFactors ν) I
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  apply selectedVonMangoldtGroup_truncatedFactorExtraction hX ν I i₀ hr χ
    (Real.rpow_nonneg (Real.log_pos (by linarith [hX])).le _) hx hxy
  intro d u v hu hsub
  let rd : ℕ := (d.1 i₀).1
  let pd : ℕ := factorExtractionAllocationResidual d i₀
  have hrdpos : 0 < rd := (d.1 i₀).2
  have hrdle : rd ≤ r := factorExtractionAllocationCoordinate_le d i₀
  have hrdlog : (rd : ℝ) ≤ (Real.log X) ^ a := by
    exact (by exact_mod_cast hrdle : (rd : ℝ) ≤ (r : ℝ)).trans hrlog
  have hpd := factorExtractionAllocationResidual_pos_le hr0 d i₀
  have hpdlog : (pd : ℝ) ≤ (Real.log X) ^ a := by
    exact (by exact_mod_cast hpd.2 : (pd : ℝ) ≤ (r : ℝ)).trans hrlog
  have hsub' : Set.Ioc u v ⊆ Set.Ioc
      (dyadicFactorScale (factors.get i₀) / (rd : ℝ))
      (2 * (dyadicFactorScale (factors.get i₀) / (rd : ℝ))) := by
    simpa [factors, rd, mul_div_assoc] using hsub
  have hlocal := groupedDyadicFactorOriginalLocalEstimate hX hz
    (factors.get i₀) hOrig χ (Nat.succ_le_of_lt hrdpos) hrdlog
    (Nat.succ_le_of_lt hpd.1) hpdlog hQ hQlog hfreqlo hfreqhi hu hsub'
  have hsum :
      (∑ m ∈ factorExtractionRealInterval u v,
        factorExtractionAllocatedFactor
          (fun j n => dyadicFactorComplexFunction z (factors.get j) n)
          (fun j => (d.1 j).1)
          (fun j => factorExtractionAllocationResidual d j)
          (factorExtractionMellinWeight (fun m => evalInt χ (m : ℤ)) t) i₀ m) =
      ∑ m ∈ factorExtractionRealInterval u v,
        groupedFactorAllocationTerm z (factors.get i₀) rd pd
          (fun m => evalInt χ (m : ℤ)) t m := by
    apply Finset.sum_congr rfl
    intro m hm
    rfl
  rw [hsum]
  simpa [rd] using hlocal

#print axioms selectedVonMangoldtGroup_originalFactorExtraction
end FractionalPrimes.Literature.Twisted
