module
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorUniform
public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorTrilinearBridge
@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.Twisted

private theorem sourceBridge_toComplexArithmeticFunction_convolution
    (f g : ComplexPositiveIntegerFunction) :
    toComplexArithmeticFunction (complexPositiveDirichletConvolution f g) =
      toComplexArithmeticFunction f * toComplexArithmeticFunction g := by
  ext n
  cases n with
  | zero => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]
  | succ n => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]

private theorem sourceBridge_toComplexArithmeticFunction_dyadicProduct
    {X : ℝ} (z : ℝ) (fs : List (DyadicArithmeticFactor X)) :
    toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs) =
      dyadicFactorComplexProduct z fs := by
  induction fs with
  | nil =>
      ext n
      cases n with
      | zero => simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
          dyadicConvolutionFactors]
      | succ n =>
          by_cases hn : n = 0
          · subst n
            simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, dyadicFactorComplexProduct,
              ArithmeticFunction.one_apply]
          · simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, dyadicFactorComplexProduct, hn,
              ArithmeticFunction.one_apply]
  | cons f fs ih =>
      have hsingle :
          toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z [f]) =
            dyadicFactorComplexFunction z f := by
        ext n
        cases n with
        | zero => simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
            dyadicConvolutionFactors, dyadicFactorComplexFunction]
        | succ n =>
            simp [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
              dyadicConvolutionFactors, dyadicFactorComplexFunction]
      change toComplexArithmeticFunction
        (dyadicConvolutionPositiveComplex z ([f] ++ fs)) = _
      rw [← dyadicConvolutionPositiveComplex_append z [f] fs,
        sourceBridge_toComplexArithmeticFunction_convolution, hsingle, ih]
      simp [List.map_cons, List.prod_cons, dyadicFactorComplexProduct]

private theorem sourceBridge_dyadicProduct_apply_eq_ofReal
    {X z : ℝ} (fs : List (DyadicArithmeticFactor X))
    {n : ℕ} (hn : 0 < n) :
    dyadicFactorComplexProduct z fs n =
      ((dyadicConvolutionFactors z fs n : ℝ) : ℂ) := by
  have hproduct := sourceBridge_toComplexArithmeticFunction_dyadicProduct z fs
  have happly := congrArg (fun F : ArithmeticFunction ℂ => F n) hproduct
  simpa [toComplexArithmeticFunction, dyadicConvolutionPositiveComplex,
    dyadicFactorComplexProduct, hn] using happly.symm

/-- The grouped positive-integer source, extended by zero to an arithmetic
function, has exactly the component scalar times the ordered dyadic product
as its coefficient at every positive integer. -/
theorem groupedDyadicFactor_toComplexArithmeticFunction_product
    {X z : ℝ} (c : ℂ) (fs : List (DyadicArithmeticFactor X)) :
    toComplexArithmeticFunction (groupedDyadicFactor z c fs) =
      c • dyadicFactorComplexProduct z fs := by
  ext n
  cases n with
  | zero =>
      simp [toComplexArithmeticFunction, groupedDyadicFactor,
        dyadicFactorComplexProduct]
  | succ n =>
      have hcast := sourceBridge_dyadicProduct_apply_eq_ofReal (z := z) fs
        (Nat.succ_pos n)
      change c * ((dyadicConvolutionFactors z fs (n + 1) : ℝ) : ℂ) =
        c * dyadicFactorComplexProduct z fs (n + 1)
      rw [hcast]

/-- Exact finite source-sum identity on the factor-extraction interval. This
is the source-level bridge needed to use the fixed selected-block saving in a
Dirichlet-polynomial or PTW assembly. -/
theorem groupedDyadicFactor_factorExtraction_sum_eq
    {X z N₁ : ℝ} (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    {r Q : ℕ} (χ : BlueprintCharacter Q) (s : ℝ) :
    (∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
      toComplexArithmeticFunction (groupedDyadicFactor z c fs) (r * m) *
        factorExtractionMellinWeight
          (fun m => evalInt χ (m : ℤ)) s m) =
    c * ∑ m ∈ factorExtractionRealInterval
        (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
      dyadicFactorComplexProduct z fs (r * m) *
        factorExtractionMellinWeight
          (fun m => evalInt χ (m : ℤ)) s m := by
  classical
  have hgroup := groupedDyadicFactor_toComplexArithmeticFunction_product
    (z := z) c fs
  calc
    _ = ∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          (c * dyadicFactorComplexProduct z fs (r * m)) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hpoint := congrArg
          (fun F : ArithmeticFunction ℂ => F (r * m)) hgroup
        simpa [Pi.smul_apply, smul_eq_mul] using congrArg
          (fun w : ℂ => w * factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) s m) hpoint
    _ = c * ∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          dyadicFactorComplexProduct z fs (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring

/-- The fixed-witness selected small-factor theorem in the exact source-sum
form used by the PTW character decomposition. -/
theorem largeMobiusTypeIIGroupedSmallFactorSourceSum_uniform
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X N₁ : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    (hNoI : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hNoI2 : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hN₁ : 0 < N₁) {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ j, 0 ≤ α j) ∧
      (∑ j : Fin (mobiusLabelFactors ν).length, α j = 1) ∧
      (∀ j, α j < (3 / 8 : ℝ)) ∧
      ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
        ∃ i : Fin (mobiusLabelFactors ν).length,
        ∃ v : ComplexPositiveIntegerFunction,
          i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
          v = groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) I) ∧
          ∀ s : ℝ,
            (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
            ‖∑ m ∈ factorExtractionRealInterval
                (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
                toComplexArithmeticFunction v (r * m) *
                  factorExtractionMellinWeight
                    (fun m => evalInt χ (m : ℤ)) s m‖ ≤
              (Real.log X) ^ (-20 * a) *
                Real.sqrt (N₁ / (r : ℝ)) := by
  obtain ⟨α, hα, hsum, hNoIα, I, i, v, hiI, hiAlpha, hv, hbound⟩ :=
    largeMobiusTypeIIGroupedSmallFactor_uniform hMUF ha hXlarge hXorig
      hXabsorb ν hν hNoI hNoI2 hN₁ hr hrlog χ hQ hQlog
  refine ⟨α, hα, hsum, hNoIα, I, i, v, hiI, hiAlpha, hv, ?_⟩
  intro s hfreqlo hfreqhi
  have hsource := groupedDyadicFactor_factorExtraction_sum_eq
    (z := dyadicMobiusCutoff X)
    (N₁ := N₁) (r := r) (Q := Q)
    (c := (dyadicBinomialCoefficient ν.1 : ℂ))
    (fs := selectedDyadicFactors (mobiusLabelFactors ν) I)
    χ s
  have hsourceV :
      (∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
        toComplexArithmeticFunction v (r * m) *
          factorExtractionMellinWeight
            (fun m => evalInt χ (m : ℤ)) s m) =
      (dyadicBinomialCoefficient ν.1 : ℂ) *
        ∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          dyadicFactorComplexProduct (dyadicMobiusCutoff X)
            (selectedDyadicFactors (mobiusLabelFactors ν) I) (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m := by
    simpa only [hv] using hsource
  calc
    _ = ‖(dyadicBinomialCoefficient ν.1 : ℂ) *
          ∑ m ∈ factorExtractionRealInterval
            (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
            dyadicFactorComplexProduct (dyadicMobiusCutoff X)
              (selectedDyadicFactors (mobiusLabelFactors ν) I) (r * m) *
              factorExtractionMellinWeight
                (fun m => evalInt χ (m : ℤ)) s m‖ :=
            congrArg (fun w : ℂ => ‖w‖) hsourceV
    _ ≤ _ := hbound s hfreqlo hfreqhi

/-- The fixed source-sum saving gives the exact pointwise small-factor
hypothesis for the normalized trilinear polynomial throughout an arbitrary
measurable frequency set with the approved frequency window. -/
theorem largeMobiusTypeIIGroupedSmallFactor_factorPolynomial_uniform
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X N₁ : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    (hNoI : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hNoI2 : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hN₁ : 0 < N₁) {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    {B T : ℝ} (hB : 1 ≤ B) (E : Set ℝ)
    (hfreq : ∀ t ∈ E,
      (Real.log X) ^ (45 * a) ≤ |T - t| ∧
        |T - t| ≤ X ^ (a + 1)) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ j, 0 ≤ α j) ∧
      (∑ j : Fin (mobiusLabelFactors ν).length, α j = 1) ∧
      (∀ j, α j < (3 / 8 : ℝ)) ∧
      ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
        ∃ i : Fin (mobiusLabelFactors ν).length,
        ∃ v : ComplexPositiveIntegerFunction,
          i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
          v = groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) I) ∧
          ∀ t ∈ E,
            ‖FractionalPrimes.Literature.DirichletMean.factorPolynomial
                (N₁ / (r : ℝ))
                (FractionalPrimes.Literature.DirichletMean.selectedGroupTrilinearCoeff
                  B r (fun n => toComplexArithmeticFunction v n)
                    (fun n => evalInt χ (n : ℤ)) T) t‖ ≤
              (Real.log X) ^ (-20 * a) *
                Real.sqrt (N₁ / (r : ℝ)) := by
  obtain ⟨α, hα, hsum, hNoIα, I, i, v, hiI, hiAlpha, hv, hsource⟩ :=
    largeMobiusTypeIIGroupedSmallFactorSourceSum_uniform hMUF ha hXlarge
      hXorig hXabsorb ν hν hNoI hNoI2 hN₁ hr hrlog χ hQ hQlog
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hM : 0 < N₁ / (r : ℝ) := div_pos hN₁ hrR
  let g : ℕ → ℂ := fun n => toComplexArithmeticFunction v n
  let χnat : ℕ → ℂ := fun n => evalInt χ (n : ℤ)
  have hupp : 2 * (N₁ / (r : ℝ)) = 2 * N₁ / (r : ℝ) := by ring
  have hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * (N₁ / (r : ℝ))),
          g (r * n) * factorExtractionMellinWeight χnat s n‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
    intro s hlo hhi
    have hsumBound := hsource s hlo hhi
    simpa [g, χnat, hupp] using hsumBound
  have hpoly := FractionalPrimes.Literature.DirichletMean.selectedGroupSmallFactor_of_frequencyWindow
      (M := N₁ / (r : ℝ)) (B := B) (X := X) (a := a) (T := T)
      hM hB r g χnat E hfreq hblock
  exact ⟨α, hα, hsum, hNoIα, I, i, v, hiI, hiAlpha, hv, hpoly⟩

#print axioms groupedDyadicFactor_toComplexArithmeticFunction_product
#print axioms groupedDyadicFactor_factorExtraction_sum_eq
#print axioms largeMobiusTypeIIGroupedSmallFactorSourceSum_uniform
#print axioms largeMobiusTypeIIGroupedSmallFactor_factorPolynomial_uniform

end FractionalPrimes.Literature.Twisted

end
