module

public import FractionalPrimes.Literature.JSW.BoundedVectorInterpolation
public import FractionalPrimes.Literature.JSW.RoughSquareRawStrongEndpoints

/-! Interpolation of the actual finite raw square operator. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquareSourceRawVector_interpolation
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b s₀ p s₁ A₀ A₁ : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ)
    (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hStrong₀ : ∀ f : Variation.LayerCakeInput (volume : Measure ℝ),
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1) (ENNReal.ofReal s₀) volume ≤
        ENNReal.ofReal A₀ * eLpNorm f.1 (ENNReal.ofReal s₀) volume)
    (hStrong₁ : ∀ f : Variation.LayerCakeInput (volume : Measure ℝ),
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1) (ENNReal.ofReal s₁) volume ≤
        ENNReal.ofReal A₁ * eLpNorm f.1 (ENNReal.ofReal s₁) volume)
    (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (fun x => ‖roughSquareSourceRawVector (σ := σ) hb j F f.1 x‖)
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (weakTypeInterpolationConstant s₀ p s₁ *
        A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
        A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) *
          eLpNorm f.1 (ENNReal.ofReal p) volume := by
  let K : {k : ℤ // k ∈ F} → ℝ → ℂ := fun k =>
    littlewoodPaleyScaledKernel b (ne_of_gt (by linarith : 0 < b)) (k.1+j)
  let μ : {k : ℤ // k ∈ F} → ComplexMeasure ℝ := fun k =>
    initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) (b^k.1)
  have hK : ∀ k, Integrable (K k) volume := fun k =>
    littlewoodPaleyScaledKernel_integrable _ _
  have hKm : ∀ k, Measurable (K k) := fun k =>
    (littlewoodPaleyScaledKernel_smooth _ _).continuous.measurable
  have hμ : ∀ k, IsFiniteMeasure (μ k).variation := by
    intro k
    letI : IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation :=
      initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
    change IsFiniteMeasure
      ((initialSquareNuComplexMeasure σ).map (fun x : ℝ => b^k.1*x)).variation
    infer_instance
  have hT : ∀ g : Variation.LayerCakeInput (volume : Measure ℝ),
      AEStronglyMeasurable (roughSquareSourceRawVector (σ := σ) hb j F g.1) volume := by
    intro g
    apply Measurable.aestronglyMeasurable
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro k
    exact (localizedSquareRawNuAfterKernel_stronglyMeasurable
      (K k) (μ k) g.1 (hKm k) (hμ k) g.2.1).measurable
  apply boundedVector_strongEndpoint_interpolation
    (fun g => roughSquareSourceRawVector (σ := σ) hb j F g.1)
    (fun g => roughSquareRawVector_measurable_norm K μ hKm hμ g)
    (fun g h _ x => roughSquareRawVector_subadditive K μ hK hKm hμ g h x)
    (fun g c hc _ x => roughSquareRawVector_positive_homogeneous K μ g.1 x c hc)
    hs₀ h₀ h₁ hA₀ hA₁
    (fun g => ?_) (fun g => ?_) f
  · rw [eLpNorm_norm _ (hT g)]
    exact hStrong₀ g
  · rw [eLpNorm_norm _ (hT g)]
    exact hStrong₁ g

theorem roughSquareLittlewoodPaleyUpperConstant_nonneg
    {p b : ℝ} (hp : 2 < p) (hb : 1 < b) :
    0 ≤ littlewoodPaleyUpperConstant p b (ne_of_gt (by linarith : 0 < b)) := by
  have hd : 0 < p - 1 := by linarith
  have hr1 : 1 < p.conjExponent := by
    unfold Real.conjExponent
    apply (lt_div_iff₀ hd).2
    linarith
  have hr2 : p.conjExponent < 2 := by
    unfold Real.conjExponent
    apply (div_lt_iff₀ hd).2
    linarith
  have hr0 : 0 < p.conjExponent := by linarith
  have hden0 : 0 < p.conjExponent - 1 := by linarith
  have hden1 : 0 < 2 - p.conjExponent := by linarith
  have hI : 0 ≤ weakTypeInterpolationConstant 1 p.conjExponent 2 := by
    unfold weakTypeInterpolationConstant
    positivity
  have hB := littlewoodPaleyBb_nonneg hb (ne_of_gt (by linarith : 0 < b))
  unfold littlewoodPaleyUpperConstant weakTypeFromOffSupportStrongConstant
  rw [if_neg (not_lt.mpr hp.le), if_neg (ne_of_gt hp)]
  unfold littlewoodPaleyCp
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)))
  apply mul_nonneg
  · exact mul_nonneg hI (Real.rpow_nonneg (by positivity) _)
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem roughSquareLittlewoodPaleyUpperConstant_nonneg_below
    {p b : ℝ} (hp : 1 < p) (hp2 : p < 2) (hb : 1 < b) :
    0 ≤ littlewoodPaleyUpperConstant p b (ne_of_gt (by linarith : 0 < b)) := by
  have hp0 : 0 < p := by linarith
  have hd0 : 0 < p - 1 := by linarith
  have hd1 : 0 < 2 - p := by linarith
  have hI : 0 ≤ weakTypeInterpolationConstant 1 p 2 := by
    unfold weakTypeInterpolationConstant
    positivity
  have hB := littlewoodPaleyBb_nonneg hb (ne_of_gt (by linarith : 0 < b))
  unfold littlewoodPaleyUpperConstant weakTypeFromOffSupportStrongConstant
  rw [if_pos hp2]
  unfold littlewoodPaleyCp
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)))
  exact mul_nonneg (mul_nonneg hI (Real.rpow_nonneg (by positivity) _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem roughSquareSourceRawVector_interpolation_above_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 2 < p) (hpu : p < u)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      eLpNorm (fun x => ‖roughSquareSourceRawVector (σ := σ) hb j F f.1 x‖)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (weakTypeInterpolationConstant 2 p u *
        ((2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
          Real.sqrt (littlewoodPaleyNb b) * Real.rpow b (-(min 1 β * |(j : ℝ)|))) ^
            weakTypeInterpolationTheta0 2 p u *
        (C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))) ^
          weakTypeInterpolationTheta1 2 p u) * eLpNorm f.1 (ENNReal.ofReal p) volume := by
  have hu : 1 < u := by linarith
  obtain ⟨C, hC, hstrong⟩ := roughSquareSourceRawVector_strong_of_maximal
    hSupp hσ hb hq₀ hMax hu hregion
  refine ⟨C, hC, ?_⟩
  intro j F f
  apply roughSquareSourceRawVector_interpolation hSupp hb j F (by norm_num) hp hpu
    (A₀ := (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
      Real.sqrt (littlewoodPaleyNb b) * Real.rpow b (-(min 1 β * |(j : ℝ)|)))
    (A₁ := C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b)))
    (mul_nonneg (mul_nonneg (mul_nonneg
      (by nlinarith [Real.pi_pos, abs_nonneg D])
      (le_trans (by norm_num) (le_max_left 2 _))) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (by linarith) _))
    (mul_nonneg hC.le (roughSquareLittlewoodPaleyUpperConstant_nonneg (by linarith) hb))
    (fun g => roughSquareSourceRawVector_strong_two hSupp hσ hb hβ j F g)
    (hstrong j F) f

theorem roughSquareSourceRawVector_interpolation_below_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hu : 1 < u) (hup : u < p) (hp : p < 2)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      eLpNorm (fun x => ‖roughSquareSourceRawVector (σ := σ) hb j F f.1 x‖)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (weakTypeInterpolationConstant u p 2 *
        (C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))) ^
          weakTypeInterpolationTheta0 u p 2 *
        ((2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
          Real.sqrt (littlewoodPaleyNb b) * Real.rpow b (-(min 1 β * |(j : ℝ)|))) ^
            weakTypeInterpolationTheta1 u p 2) * eLpNorm f.1 (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hstrong⟩ := roughSquareSourceRawVector_strong_of_maximal
    hSupp hσ hb hq₀ hMax hu hregion
  refine ⟨C, hC, ?_⟩
  intro j F f
  apply roughSquareSourceRawVector_interpolation hSupp hb j F hu.le hup hp
    (A₀ := C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b)))
    (A₁ := (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
      Real.sqrt (littlewoodPaleyNb b) * Real.rpow b (-(min 1 β * |(j : ℝ)|)))
    (mul_nonneg hC.le (roughSquareLittlewoodPaleyUpperConstant_nonneg_below hu (by linarith) hb))
    (mul_nonneg (mul_nonneg (mul_nonneg
      (by nlinarith [Real.pi_pos, abs_nonneg D])
      (le_trans (by norm_num) (le_max_left 2 _))) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (by linarith) _))
    (hstrong j F)
    (fun g => roughSquareSourceRawVector_strong_two hSupp hσ hb hβ j F g) f

theorem roughSquareLocalizedDecay_rpow
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (ε θ t : ℝ) :
    (A * b ^ (-(ε * |t|))) ^ θ = A ^ θ * b ^ (-(ε * θ * |t|)) := by
  rw [Real.mul_rpow hA (Real.rpow_nonneg hb.le _), ← Real.rpow_mul hb.le]
  congr 1
  ring

theorem roughSquareInterpolationWeights_pos
    {s₀ p s₁ : ℝ} (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁) :
    0 < weakTypeInterpolationTheta0 s₀ p s₁ ∧
      0 < weakTypeInterpolationTheta1 s₀ p s₁ := by
  have hs₀pos : 0 < s₀ := by linarith
  have hp : 0 < p := by linarith
  have hs₁pos : 0 < s₁ := by linarith
  have hd : 0 < s₁ - s₀ := by linarith
  have hd0 : 0 < p - s₀ := by linarith
  have hd1 : 0 < s₁ - p := by linarith
  constructor <;> simp only [weakTypeInterpolationTheta0, weakTypeInterpolationTheta1] <;> positivity

#print axioms roughSquareLocalizedDecay_rpow
#print axioms roughSquareInterpolationWeights_pos
#print axioms roughSquareSourceRawVector_interpolation_below_two
#print axioms roughSquareSourceRawVector_interpolation_above_two
#print axioms roughSquareSourceRawVector_interpolation
end
end FractionalPrimes.Literature.JSW
end
