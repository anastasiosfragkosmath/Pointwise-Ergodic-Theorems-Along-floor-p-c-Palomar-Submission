module
public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtOriginalFactorExtraction
public import FractionalPrimes.Literature.Twisted.GroupedFactorLogarithmicAbsorption
@[expose] public section

noncomputable section
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators
namespace FractionalPrimes.Literature.Twisted

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

/-- The literal von Mangoldt grouped-factor bound after the source divisor
and logarithmic absorption, retaining the selected original-factor input. -/
theorem selectedVonMangoldtGroup_originalFactorExtractionAbsorbed
    {X z t N : ℝ} (hX : 3 ≤ X)
    (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i₀ : Fin (selectedDyadicFactors (vonMangoldtLabelFactors ν) I).length)
    {r Q : ℕ} (hr : 1 ≤ r) (χ : BlueprintCharacter Q)
    (hN : 0 < N)
    (hz : 0 ≤ z) {a : ℝ} (ha : 2 ≤ a)
    (hthreshold : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (hQ : 1 ≤ Q) (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hfreqlo : (Real.log X) ^ (45 * a) ≤ |t|)
    (hfreqhi : |t| ≤ X ^ (a + 1))
    (hOrig : OriginalLongFactorAt X
      (dyadicFactorScale
        ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get i₀)) t a)
    (hprod : dyadicFactorScaleProduct
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) ≤ 2 * N) :
    ‖(dyadicBinomialCoefficient ν.1 : ℂ) *
      ∑ n ∈ factorExtractionRealInterval (N / (r : ℝ)) (2 * N / (r : ℝ)),
        dyadicFactorComplexProduct z
          (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) (r * n) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) t n‖ ≤
      (Real.log X) ^ (-20 * a) * Real.sqrt (N / (r : ℝ)) := by
  classical
  let factors := selectedDyadicFactors (vonMangoldtLabelFactors ν) I
  let L := Real.log X
  let C := (2 : ℝ) ^ 10 * (3 : ℝ) ^ (factors.length - 1) *
    (divisorFunction factors.length ⟨r, lt_of_lt_of_le (by decide) hr⟩ : ℝ) *
      L ^ (-21 * a)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [hX])
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hr)
  have hx : 0 ≤ N / (r : ℝ) := (div_pos hN hrR).le
  have hxy : N / (r : ℝ) ≤ 2 * N / (r : ℝ) := by
    rw [show 2 * N / (r : ℝ) = 2 * (N / (r : ℝ)) by ring]
    linarith
  have hsmall := selectedVonMangoldtGroup_originalFactorExtraction hX ν I i₀
    hr χ hx hxy hz hrlog hQ hQlog hfreqlo hfreqhi hOrig
  have hkhi : factors.length ≤ 20 := by
    calc
      factors.length = I.card := by simp [factors]
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ I)
      _ = (vonMangoldtLabelFactors ν).length := by simp
      _ ≤ 20 := (vonMangoldtLabelFactorCount ν).2
  have habs := groupedFactorLogarithmicCoefficientAbsorption ha hthreshold
    hkhi hr hrlog
  have hroot : Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) ≤
      Real.sqrt 2 * Real.sqrt (N / (r : ℝ)) := by
    calc
      _ ≤ Real.sqrt (2 * (N / (r : ℝ))) := by
        apply Real.sqrt_le_sqrt
        calc
          _ ≤ (2 * N) / (r : ℝ) :=
            div_le_div_of_nonneg_right hprod hrR.le
          _ = _ := by ring
      _ = _ := Real.sqrt_mul (by norm_num) _
  have hlog : Real.log (8 * X) ≤ 4 * L := log_eightX_le_four_logX hX
  have hlogpos : 0 ≤ Real.log (8 * X) := Real.log_nonneg (by linarith [hX])
  calc
    _ ≤ C * Real.sqrt (dyadicFactorScaleProduct factors / (r : ℝ)) *
        Real.log (8 * X) := hsmall
    _ ≤ C * (Real.sqrt 2 * Real.sqrt (N / (r : ℝ))) * (4 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hroot hC) hlog hlogpos
        (mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    _ = (C * Real.sqrt 2 * (4 * L)) * Real.sqrt (N / (r : ℝ)) := by ring
    _ ≤ L ^ (-20 * a) * Real.sqrt (N / (r : ℝ)) :=
      mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg _)

#print axioms selectedVonMangoldtGroup_originalFactorExtractionAbsorbed
end FractionalPrimes.Literature.Twisted
