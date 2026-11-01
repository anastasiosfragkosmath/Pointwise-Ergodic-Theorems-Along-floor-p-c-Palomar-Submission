module

public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Twisted.DivisorTwentyBound
public import FractionalPrimes.Literature.Twisted.SmallDivisorDomination
public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorTrilinearBridge
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtGroupCoefficientBound

/-! Exact shifted divisor envelopes for the three normalized PTW factor
polynomials. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.LargeValues
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- A scalar-weighted dyadic group with at most twenty factors has the
source coefficient envelope after a natural gcd shift. The divisor factor
at `r*m` is split exactly into the separate `r` and `m` envelopes. -/
theorem groupedDyadicFactor_shifted_divisorEnvelope
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (hweight : dyadicFactorsMassWeight fs ≤ Real.log (8 * X))
    (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    ‖groupedDyadicFactor z c fs ⟨r * m, Nat.mul_pos hr hm⟩‖ ≤
      (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 r : ℝ) ^ 20 *
          (divisorCoefficient 2 m : ℝ) ^ 20 := by
  have hlog : 0 < Real.log (8 * X) :=
    lt_trans zero_lt_one (log_eightX_gt_one hX)
  have hdivLength := divisorCoefficient_mono (Nat.mul_pos hr hm) hlen
  have hdivLengthR :
      (divisorCoefficient fs.length (r * m) : ℝ) ≤
        (divisorCoefficient 20 (r * m) : ℝ) := by
    exact_mod_cast hdivLength
  have hdiv20 := divisorCoefficient_twenty_le_two_pow (r * m)
    (Nat.mul_pos hr hm)
  have hdiv20R :
      (divisorCoefficient 20 (r * m) : ℝ) ≤
        (divisorCoefficient 2 (r * m) : ℝ) ^ 20 := by
    exact_mod_cast hdiv20
  have hdivMul := divisorCoefficient_two_mul_le r m hr hm
  have hdivMulR :
      (divisorCoefficient 2 (r * m) : ℝ) ≤
        (divisorCoefficient 2 r : ℝ) *
          (divisorCoefficient 2 m : ℝ) := by
    exact_mod_cast hdivMul
  have hconv := dyadicConvolutionFactors_abs_le_massWeight hX z fs
    ⟨r * m, Nat.mul_pos hr hm⟩
  have hconv' :
      |dyadicConvolutionFactors z fs (r * m)| ≤
        Real.log (8 * X) *
          ((divisorCoefficient 2 r : ℝ) ^ 20 *
            (divisorCoefficient 2 m : ℝ) ^ 20) := by
    calc
      |dyadicConvolutionFactors z fs (r * m)| ≤
          dyadicFactorsMassWeight fs *
            (divisorCoefficient fs.length (r * m) : ℝ) := hconv
      _ ≤ Real.log (8 * X) *
            (divisorCoefficient fs.length (r * m) : ℝ) :=
          mul_le_mul_of_nonneg_right hweight (Nat.cast_nonneg _)
      _ ≤ Real.log (8 * X) *
            (divisorCoefficient 20 (r * m) : ℝ) :=
          mul_le_mul_of_nonneg_left hdivLengthR hlog.le
      _ ≤ Real.log (8 * X) *
            (divisorCoefficient 2 (r * m) : ℝ) ^ 20 :=
          mul_le_mul_of_nonneg_left hdiv20R hlog.le
      _ ≤ Real.log (8 * X) *
            ((divisorCoefficient 2 r : ℝ) ^ 20 *
              (divisorCoefficient 2 m : ℝ) ^ 20) := by
          apply mul_le_mul_of_nonneg_left _ hlog.le
          have hpow :
              (divisorCoefficient 2 (r * m) : ℝ) ^ 20 ≤
                ((divisorCoefficient 2 r : ℝ) *
                  (divisorCoefficient 2 m : ℝ)) ^ 20 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hdivMulR 20
          simpa only [mul_pow] using hpow
  change ‖c * ((dyadicConvolutionFactors z fs (r * m) : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real]
  calc
    ‖c‖ * |dyadicConvolutionFactors z fs (r * m)| ≤
        (2 : ℝ) ^ 10 *
          (Real.log (8 * X) *
            ((divisorCoefficient 2 r : ℝ) ^ 20 *
              (divisorCoefficient 2 m : ℝ) ^ 20)) :=
      mul_le_mul hc hconv' (abs_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r : ℝ) ^ 20 *
          (divisorCoefficient 2 m : ℝ) ^ 20 := by ring

/-- The zero-scalar group used for the second and third factors in the
type-II decomposition obeys the same shifted divisor envelope. -/
theorem dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (hweight : dyadicFactorsMassWeight fs ≤ Real.log (8 * X))
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    ‖dyadicConvolutionPositiveComplex z fs ⟨r * m, Nat.mul_pos hr hm⟩‖ ≤
      (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 r : ℝ) ^ 20 *
          (divisorCoefficient 2 m : ℝ) ^ 20 := by
  have h := groupedDyadicFactor_shifted_divisorEnvelope
    (z := z) hX fs hlen hweight (1 : ℂ) (by norm_num) hr hm
  simpa [groupedDyadicFactor, dyadicConvolutionPositiveComplex] using h

private theorem selectedMobiusGroup_massWeight_eq_one {X : ℝ}
    (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length)) :
    dyadicFactorsMassWeight
      (selectedDyadicFactors (mobiusLabelFactors ν) I) = 1 := by
  have hselected :
      dyadicFactorsMassWeight (selectedDyadicFactors (mobiusLabelFactors ν) I) =
        ∏ i ∈ I, dyadicFactorMassWeight ((mobiusLabelFactors ν).get i) := by
    simp [dyadicFactorsMassWeight, selectedDyadicFactors,
      List.map_map, Function.comp_def, Finset.prod_map_toList]
  have hfactor : ∀ i : Fin (mobiusLabelFactors ν).length,
      dyadicFactorMassWeight ((mobiusLabelFactors ν).get i) = 1 := by
    intro i
    cases hkind : (mobiusLabelFactors ν).get i with
    | one j => simp [dyadicFactorMassWeight]
    | mobius j => simp [dyadicFactorMassWeight]
    | logarithm j =>
        have hmem : DyadicArithmeticFactor.logarithm j ∈
            mobiusLabelFactors ν := by
          rw [← hkind]
          exact List.get_mem (mobiusLabelFactors ν) i
        simp [mobiusLabelFactors] at hmem
  rw [hselected]
  exact Finset.prod_eq_one fun i hi => hfactor i

/-- The second and third positive convolution groups from a von Mangoldt
label have the exact shifted divisor envelope. The only logarithmic mass is
the source label's unique logarithmic factor, even after selecting a group. -/
theorem selectedVonMangoldtDyadicGroup_shifted_divisorEnvelope
    {X z : ℝ} (hX : 3 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    ‖dyadicConvolutionPositiveComplex z
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) I)
        ⟨r * m, Nat.mul_pos hr hm⟩‖ ≤
      (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 r : ℝ) ^ 20 *
          (divisorCoefficient 2 m : ℝ) ^ 20 := by
  have hlen :
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    calc
      I.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ I)
      _ = (vonMangoldtLabelFactors ν).length := by simp
      _ ≤ 20 := (vonMangoldtLabelFactorCount ν).2
  have hweight := selectedVonMangoldtGroup_massWeight_le hX ν I
  exact dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
    hX (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) hlen hweight hr hm

/-- The second and third positive convolution groups from a Möbius label
have the same shifted envelope, with no logarithmic mass loss. -/
theorem selectedMobiusDyadicGroup_shifted_divisorEnvelope
    {X z : ℝ} (hX : 3 ≤ X) (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    ‖dyadicConvolutionPositiveComplex z
        (selectedDyadicFactors (mobiusLabelFactors ν) I)
        ⟨r * m, Nat.mul_pos hr hm⟩‖ ≤
      (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 r : ℝ) ^ 20 *
          (divisorCoefficient 2 m : ℝ) ^ 20 := by
  have hlen :
      (selectedDyadicFactors (mobiusLabelFactors ν) I).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    calc
      I.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ I)
      _ = (mobiusLabelFactors ν).length := by simp
      _ ≤ 20 := (mobiusLabelFactorCount ν).2
  have hweight :
      dyadicFactorsMassWeight
          (selectedDyadicFactors (mobiusLabelFactors ν) I) ≤
        Real.log (8 * X) := by
    rw [selectedMobiusGroup_massWeight_eq_one]
    exact (log_eightX_gt_one hX).le
  exact dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
    hX (selectedDyadicFactors (mobiusLabelFactors ν) I) hlen hweight hr hm

/-- Normalizing any such shifted group by a constant at least its source
envelope gives the exact `C=20` coefficient hypothesis required by
`ldm:uncapped`. This specializes directly to the second and third PTW
factors, with their characters and archimedean twists included. -/
theorem selectedGroupTrilinearCoeff_factorCoefficientBound_of_groupedDyadicFactor
    {X z M B T : ℝ} (hX : 3 ≤ X) (hM : 0 < M)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (hweight : dyadicFactorsMassWeight fs ≤ Real.log (8 * X))
    (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    {r : ℕ} (hr : 1 ≤ r)
    (hB : (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 r : ℝ) ^ 20 ≤ B)
    (hBpos : 0 < B)
    (χ : ℕ → ℂ) (hχ : ∀ n, ‖χ n‖ ≤ 1) :
    factorCoefficientBound 20 M
      (selectedGroupTrilinearCoeff B r
        (fun n => toComplexArithmeticFunction
          (groupedDyadicFactor z c fs) n) χ T) := by
  let g : ℕ → ℂ := fun n => toComplexArithmeticFunction
    (groupedDyadicFactor z c fs) n
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hraw : ∀ n ∈ dirichletIndices M,
      ‖g (r * n)‖ ≤ B *
        (divisorCoefficient 2 n : ℝ) ^ 20 := by
    intro n hn
    have hmem' := Finset.mem_filter.mp hn
    have hnR : 0 < (n : ℝ) := lt_trans hM hmem'.2
    have hn0 : 0 < n := by exact_mod_cast hnR
    have hbound := groupedDyadicFactor_shifted_divisorEnvelope
      (z := z) hX fs hlen hweight c hc hr0 hn0
    have hsource : ‖g (r * n)‖ ≤
        (2 : ℝ) ^ 10 * Real.log (8 * X) *
          (divisorCoefficient 2 r : ℝ) ^ 20 *
            (divisorCoefficient 2 n : ℝ) ^ 20 := by
      change ‖toComplexArithmeticFunction (groupedDyadicFactor z c fs)
        (r * n)‖ ≤ _
      rw [toComplexArithmeticFunction_apply
        (groupedDyadicFactor z c fs) ⟨r * n, Nat.mul_pos hr0 hn0⟩]
      exact hbound
    calc
      ‖g (r * n)‖ ≤
          ((2 : ℝ) ^ 10 * Real.log (8 * X) *
            (divisorCoefficient 2 r : ℝ) ^ 20) *
              (divisorCoefficient 2 n : ℝ) ^ 20 := by ring_nf at hsource ⊢; exact hsource
      _ ≤ B * (divisorCoefficient 2 n : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hB (by positivity)
  exact selectedGroupTrilinearCoeff_factorCoefficientBound
    hBpos r g χ hχ hraw

#print axioms groupedDyadicFactor_shifted_divisorEnvelope
#print axioms dyadicConvolutionPositiveComplex_shifted_divisorEnvelope
#print axioms selectedVonMangoldtDyadicGroup_shifted_divisorEnvelope
#print axioms selectedMobiusDyadicGroup_shifted_divisorEnvelope
#print axioms selectedGroupTrilinearCoeff_factorCoefficientBound_of_groupedDyadicFactor

end FractionalPrimes.Literature.DirichletMean

end
