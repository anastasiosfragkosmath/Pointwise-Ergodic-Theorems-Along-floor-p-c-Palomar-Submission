module

public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition

/-!
# Coefficient bound for a selected von Mangoldt label group

The arithmetic dyadic von Mangoldt label has exactly one unnormalized
logarithmic factor. Its selected subgroups therefore retain at most the
single `log (8 * X)` mass appearing in the source type-II bookkeeping.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.Uniformity

private theorem selectedDyadicFactors_massWeight_eq_finset_prod
    {X : ℝ} (fs : List (DyadicArithmeticFactor X))
    (I : Finset (Fin fs.length)) :
    dyadicFactorsMassWeight (selectedDyadicFactors fs I) =
      ∏ i ∈ I, dyadicFactorMassWeight (fs.get i) := by
  simp [dyadicFactorsMassWeight, selectedDyadicFactors,
    List.map_map, Function.comp_def, Finset.prod_map_toList]

private theorem dyadicFactorsMassWeight_eq_fin_prod_get
    {X : ℝ} (fs : List (DyadicArithmeticFactor X)) :
    dyadicFactorsMassWeight fs =
      ∏ i : Fin fs.length, dyadicFactorMassWeight (fs.get i) := by
  simp [dyadicFactorsMassWeight, List.get_eq_getElem,
    ← Fin.prod_univ_fun_getElem]

private theorem vonMangoldtFactorMassWeight_ge_one
    {X : ℝ} (hX : 3 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (i : Fin (vonMangoldtLabelFactors ν).length) :
    1 ≤ dyadicFactorMassWeight ((vonMangoldtLabelFactors ν).get i) := by
  cases hfactor : (vonMangoldtLabelFactors ν).get i with
  | one j => simp [dyadicFactorMassWeight]
  | mobius j => simp [dyadicFactorMassWeight]
  | logarithm j =>
      dsimp [dyadicFactorMassWeight]
      exact (log_eightX_gt_one hX).le

private theorem log_eightX_le_four_logX {X : ℝ} (hX : 3 ≤ X) :
    Real.log (8 * X) ≤ 4 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hXcube : (8 : ℝ) ≤ X ^ 3 := by
    calc
      8 ≤ 3 ^ 3 := by norm_num
      _ ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
  have harg : 8 * X ≤ X ^ 4 := by
    calc
      8 * X ≤ X ^ 3 * X := mul_le_mul_of_nonneg_right hXcube hXpos.le
      _ = X ^ 4 := by ring
  have hlog := Real.log_le_log (by positivity : 0 < 8 * X) harg
  have hlogpow : Real.log (X ^ 4) = 4 * Real.log X := by
    rw [Real.log_pow X 4]
    ring
  rw [hlogpow] at hlog
  exact hlog

/-- The total mass weight of any selected von Mangoldt label group is no
larger than the unique logarithmic factor's full weight. -/
theorem selectedVonMangoldtGroup_massWeight_le
    {X : ℝ} (hX : 3 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length)) :
    dyadicFactorsMassWeight (selectedDyadicFactors
      (vonMangoldtLabelFactors ν) I) ≤ Real.log (8 * X) := by
  rw [selectedDyadicFactors_massWeight_eq_finset_prod]
  have hsubset : I ⊆ Finset.univ := Finset.subset_univ _
  have hprod :
      (∏ i ∈ I, dyadicFactorMassWeight
        ((vonMangoldtLabelFactors ν).get i)) ≤
      (∏ i : Fin (vonMangoldtLabelFactors ν).length,
        dyadicFactorMassWeight ((vonMangoldtLabelFactors ν).get i)) := by
    exact Finset.prod_le_prod_of_subset_of_one_le₀ hsubset
      (fun i _ => dyadicFactorMassWeight_nonneg hX
        ((vonMangoldtLabelFactors ν).get i))
      (fun i _ _ => vonMangoldtFactorMassWeight_ge_one hX ν i)
  rw [← dyadicFactorsMassWeight_eq_fin_prod_get,
    vonMangoldtLabelFactors_massWeight] at hprod
  exact hprod

/-- The scalar-weighted coefficient of a group selected from a von Mangoldt
Heath--Brown label has the exact single-logarithm envelope. The divisor
coefficient records the selected group's own number of factors. -/
theorem selectedVonMangoldtGroup_coefficient_norm_le
    {X z : ℝ} (hX : 3 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (n : PositiveInteger) :
    ‖groupedDyadicFactor z (dyadicBinomialCoefficient ν.1 : ℂ)
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) n‖ ≤
      (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length
          n.1 : ℝ) := by
  let fs := selectedDyadicFactors (vonMangoldtLabelFactors ν) I
  have hweight : dyadicFactorsMassWeight fs ≤ Real.log (8 * X) := by
    simpa [fs] using selectedVonMangoldtGroup_massWeight_le hX ν I
  have hweight0 : 0 ≤ dyadicFactorsMassWeight fs :=
    dyadicFactorsMassWeight_nonneg hX fs
  have hconv := dyadicConvolutionFactors_abs_le_massWeight hX z fs n
  have hscalar : |dyadicBinomialCoefficient ν.1| ≤ (2 : ℝ) ^ 10 :=
    dyadicBinomialCoefficient_abs_le ν.1
  have hdiv0 : 0 ≤ (divisorCoefficient fs.length n.1 : ℝ) :=
    Nat.cast_nonneg _
  change ‖(dyadicBinomialCoefficient ν.1 : ℂ) *
      ((dyadicConvolutionFactors z fs n.1 : ℝ) : ℂ)‖ ≤ _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |dyadicBinomialCoefficient ν.1| *
        |dyadicConvolutionFactors z fs n.1| ≤
      (2 : ℝ) ^ 10 *
        (dyadicFactorsMassWeight fs *
          (divisorCoefficient fs.length n.1 : ℝ)) := by
            exact mul_le_mul hscalar hconv (abs_nonneg _) (by positivity)
    _ ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient fs.length n.1 : ℝ) := by
          have hweightConv := mul_le_mul_of_nonneg_right hweight hdiv0
          have htwo0 : 0 ≤ (2 : ℝ) ^ 10 := by positivity
          calc
            (2 : ℝ) ^ 10 *
                (dyadicFactorsMassWeight fs *
                  (divisorCoefficient fs.length n.1 : ℝ)) ≤
              (2 : ℝ) ^ 10 *
                (Real.log (8 * X) *
                  (divisorCoefficient fs.length n.1 : ℝ)) :=
                    mul_le_mul_of_nonneg_left hweightConv htwo0
            _ = (2 : ℝ) ^ 10 * Real.log (8 * X) *
                (divisorCoefficient fs.length n.1 : ℝ) := by ring

/-- The exact logarithmic envelope above converts to the `4 log X`
normalization used in the source's later type-II absorption. -/
theorem selectedVonMangoldtGroup_coefficient_norm_le_four_logX
    {X z : ℝ} (hX : 3 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (n : PositiveInteger) :
    ‖groupedDyadicFactor z (dyadicBinomialCoefficient ν.1 : ℂ)
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) n‖ ≤
      (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (divisorCoefficient
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length
          n.1 : ℝ) := by
  have hmain := selectedVonMangoldtGroup_coefficient_norm_le
    (z := z) hX ν I n
  have hlog := log_eightX_le_four_logX hX
  have hdiv0 : 0 ≤ (divisorCoefficient
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length n.1 : ℝ) :=
    Nat.cast_nonneg _
  calc
    _ ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length
          n.1 : ℝ) := hmain
    _ ≤ (2 : ℝ) ^ 10 * (4 * Real.log X) *
        (divisorCoefficient
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length
          n.1 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hdiv0
          exact mul_le_mul_of_nonneg_left hlog (by positivity)

#print axioms selectedVonMangoldtGroup_massWeight_le
#print axioms selectedVonMangoldtGroup_coefficient_norm_le
#print axioms selectedVonMangoldtGroup_coefficient_norm_le_four_logX

end FractionalPrimes.Literature.Twisted

end
