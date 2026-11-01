module

public import FractionalPrimes.Literature.JSW.InitialSquareAndMaximal
public import FractionalPrimes.Literature.JSW.SublinearDenseExtension

/-!
# Finite positive maximal operators on `L^p`

This module begins the finite-scale `L^p` realization of the positive
maximal operator in `lj:initial-square`, using the existing vector-measure
convolution and its Young bound.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Convolution by a finite complex measure, as a real-linear map on finite
`L^p`. -/
def lpComplexMeasureConvolutionRLinearMap
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Lp ℂ p (volume : Measure ℝ) →ₗ[ℝ] Lp ℂ p (volume : Measure ℝ) where
  toFun := lpComplexMeasureConvolution p μ
  map_add' F G := by
    unfold lpComplexMeasureConvolution
    have hF := integrable_lpRightTranslate hp μ F
    have hG := integrable_lpRightTranslate hp μ G
    calc
      ∫ᵛ y, lpRightTranslate p y (F + G) ∂[lpComplexSmulBilinear p; μ] =
          ∫ᵛ y, lpRightTranslate p y F + lpRightTranslate p y G
            ∂[lpComplexSmulBilinear p; μ] := by
              apply VectorMeasure.integral_congr_ae
              exact ae_of_all μ.variation fun y => by simp [lpRightTranslate]
      _ = ∫ᵛ y, lpRightTranslate p y F ∂[lpComplexSmulBilinear p; μ] +
            ∫ᵛ y, lpRightTranslate p y G ∂[lpComplexSmulBilinear p; μ] :=
          VectorMeasure.integral_add hF hG
  map_smul' c F := by
    unfold lpComplexMeasureConvolution
    have hF := integrable_lpRightTranslate hp μ F
    calc
      ∫ᵛ y, lpRightTranslate p y (c • F) ∂[lpComplexSmulBilinear p; μ] =
          ∫ᵛ y, c • lpRightTranslate p y F ∂[lpComplexSmulBilinear p; μ] := by
            apply VectorMeasure.integral_congr_ae
            apply ae_of_all
            intro y
            apply Lp.ext
            have hshift : (fun x : ℝ => (c • F) (x - y)) =ᵐ[volume]
                (fun x => c • F (x - y)) :=
              (measurePreserving_sub_right (volume : Measure ℝ) y).quasiMeasurePreserving.ae
                (Lp.coeFn_smul c F)
            filter_upwards [coeFn_lpRightTranslate p y (c • F), hshift,
              coeFn_lpRightTranslate p y F,
              Lp.coeFn_smul c (lpRightTranslate p y F)] with x h₁ h₂ h₃ h₄
            rw [h₁, h₂, ← h₃, h₄]
            rfl
      _ = c • ∫ᵛ y, lpRightTranslate p y F ∂[lpComplexSmulBilinear p; μ] := by
            exact VectorMeasure.integral_smul
              (f := fun y => lpRightTranslate p y F) (μ := μ)
              (B := lpComplexSmulBilinear p) c

/-- Young's inequality gives the exact operator-norm bound for the
real-linear convolution map. -/
theorem norm_lpComplexMeasureConvolutionRLinearMap_apply_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ p (volume : Measure ℝ)) :
    ‖lpComplexMeasureConvolutionRLinearMap p hp μ F‖ ≤
      μ.variation.real Set.univ * ‖F‖ := by
  exact norm_lpComplexMeasureConvolution_le hp μ F

/-- The bounded convolution map, using the operator bound from Young's
inequality. -/
def lpComplexMeasureConvolutionCLM
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Lp ℂ p (volume : Measure ℝ) →L[ℝ] Lp ℂ p (volume : Measure ℝ) :=
  (lpComplexMeasureConvolutionRLinearMap p hp μ).mkContinuous
    (μ.variation.real Set.univ)
    (norm_lpComplexMeasureConvolutionRLinearMap_apply_le p hp μ)

/-- The complex modulus is Lipschitz as a real-valued function. -/
theorem lipschitz_complex_norm :
    LipschitzWith 1 (fun z : ℂ => ‖z‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_norm_sub_norm_le z w

/-- Pointwise modulus as a continuous map from complex to real `L^p`. -/
def lpComplexPointwiseNorm
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℂ p (volume : Measure ℝ) → Lp ℝ p (volume : Measure ℝ) :=
  lipschitz_complex_norm.compLp (by simp)

theorem continuous_lpComplexPointwiseNorm
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Continuous (lpComplexPointwiseNorm p :
      Lp ℂ p (volume : Measure ℝ) → Lp ℝ p (volume : Measure ℝ)) :=
  (LipschitzWith.lipschitzWith_compLp lipschitz_complex_norm (by simp)).continuous

theorem continuous_lpComplexMeasureConvolutionCLM
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Continuous (lpComplexMeasureConvolutionCLM p hp μ) :=
  (lpComplexMeasureConvolutionCLM p hp μ).continuous

/-- The scalewise positive-convolution map on `L^p`: take the input modulus,
convolve its real complexification, and take the real part. -/
def lpPositiveConvolutionMap
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Lp ℂ p (volume : Measure ℝ) → Lp ℝ p (volume : Measure ℝ) :=
  fun F =>
    (Complex.reCLM.compLpL p volume)
      (lpComplexMeasureConvolutionCLM p hp μ
        ((Complex.ofRealCLM.compLpL p volume) (lpComplexPointwiseNorm p F)))

theorem continuous_lpPositiveConvolutionMap
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Continuous (lpPositiveConvolutionMap p hp μ) := by
  exact (Complex.reCLM.compLpL p volume).continuous.comp
    ((lpComplexMeasureConvolutionCLM p hp μ).continuous.comp
      ((Complex.ofRealCLM.compLpL p volume).continuous.comp
        (continuous_lpComplexPointwiseNorm p)))

/-- The scalewise map has the exact Young constant: total variation mass of
the measure. -/
theorem norm_lpPositiveConvolutionMap_sub_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F G : Lp ℂ p (volume : Measure ℝ)) :
    ‖lpPositiveConvolutionMap p hp μ F - lpPositiveConvolutionMap p hp μ G‖ ≤
      μ.variation.real Set.univ * ‖F - G‖ := by
  let N := lpComplexPointwiseNorm p
  let O := Complex.ofRealCLM.compLpL p (volume : Measure ℝ)
  let T := lpComplexMeasureConvolutionCLM p hp μ
  let R := Complex.reCLM.compLpL p (volume : Measure ℝ)
  have hN : ‖N F - N G‖ ≤ ‖F - G‖ := by
    have h := (LipschitzWith.lipschitzWith_compLp
      lipschitz_complex_norm (by simp)).dist_le_mul F G
    simpa [N, lpComplexPointwiseNorm, dist_eq_norm] using h
  have hO : ‖O‖ ≤ 1 := by
    calc
      ‖O‖ ≤ ‖Complex.ofRealCLM‖ := by
        simpa [O] using
          (ContinuousLinearMap.norm_compLpL_le
            (μ := (volume : Measure ℝ)) (p := p) Complex.ofRealCLM)
      _ = 1 := RCLike.ofRealCLM_norm
  have hR : ‖R‖ ≤ 1 := by
    calc
      ‖R‖ ≤ ‖Complex.reCLM‖ := by
        simpa [R] using
          (ContinuousLinearMap.norm_compLpL_le
            (μ := (volume : Measure ℝ)) (p := p) Complex.reCLM)
      _ = 1 := RCLike.reCLM_norm
  have hmass : 0 ≤ μ.variation.real Set.univ := ENNReal.toReal_nonneg
  have hT : ‖T‖ ≤ μ.variation.real Set.univ := by
    dsimp [T, lpComplexMeasureConvolutionCLM]
    exact LinearMap.mkContinuous_norm_le _ hmass
      (norm_lpComplexMeasureConvolutionRLinearMap_apply_le p hp μ)
  change ‖R (T (O (N F))) - R (T (O (N G)))‖ ≤ _
  rw [← R.map_sub, ← T.map_sub, ← O.map_sub]
  calc
    ‖R (T (O (N F - N G)))‖ ≤ ‖R‖ * ‖T (O (N F - N G))‖ := R.le_opNorm _
    _ ≤ 1 * ‖T (O (N F - N G))‖ := by gcongr
    _ ≤ 1 * (μ.variation.real Set.univ * ‖O (N F - N G)‖) := by
      gcongr
      exact T.le_of_opNorm_le hT _
    _ ≤ 1 * (μ.variation.real Set.univ * (1 * ‖N F - N G‖)) := by
      gcongr
      exact O.le_of_opNorm_le hO _
    _ ≤ μ.variation.real Set.univ * ‖F - G‖ := by
      simpa [one_mul] using mul_le_mul_of_nonneg_left hN hmass

/-- A finite supremum of scalewise positive-convolution maps, represented as
a real-valued `L^p` element. -/
def lpFinitePositiveConvolutionSup
    {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (s : Finset ι) (hne : s.Nonempty)
    (μ : ι → ComplexMeasure ℝ)
    (hμ : ∀ i, IsFiniteMeasure (μ i).variation) :
    Lp ℂ p (volume : Measure ℝ) → Lp ℝ p (volume : Measure ℝ) :=
  fun F => s.sup' hne (fun i => by
    letI : IsFiniteMeasure (μ i).variation := hμ i
    exact lpPositiveConvolutionMap p hp (μ i) F)

theorem continuous_lpFinitePositiveConvolutionSup
    {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (s : Finset ι) (hne : s.Nonempty)
    (μ : ι → ComplexMeasure ℝ)
    (hμ : ∀ i, IsFiniteMeasure (μ i).variation) :
    Continuous (lpFinitePositiveConvolutionSup p hp s hne μ hμ) := by
  change Continuous (fun F => s.sup' hne (fun i =>
    lpPositiveConvolutionMap p hp (μ i) F))
  exact Continuous.finset_sup'_apply hne fun i _hi =>
    continuous_lpPositiveConvolutionMap p hp (μ i)

/-- The complexification of the positive measure used by the source
positive maximal operator. -/
def initialSquareSigmaComplexifiedMeasure (σ : Measure ℝ) [IsFiniteMeasure σ] :
    ComplexMeasure ℝ := σ.toSignedMeasure.toComplexMeasure 0

theorem initialSquareSigmaComplexifiedMeasure_variation_eq
    (σ : Measure ℝ) [IsFiniteMeasure σ] :
    (initialSquareSigmaComplexifiedMeasure σ).variation = σ := by
  let μ : SignedMeasure ℝ := σ.toSignedMeasure
  have hle : (μ.toComplexMeasure 0).variation ≤ μ.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    have hval : (μ.toComplexMeasure 0) E = (μ E : ℂ) := by
      rw [SignedMeasure.toComplexMeasure_apply]
      have hz : (0 : SignedMeasure ℝ) E = 0 := by simp
      rw [hz]
      rfl
    rw [hval]
    change ENNReal.ofNNReal ‖(μ E : ℂ)‖₊ ≤ μ.variation E
    rw [Complex.nnnorm_real]
    exact VectorMeasure.enorm_measure_le_variation μ E
  have hge : μ.variation ≤ (μ.toComplexMeasure 0).variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    have hval : (μ.toComplexMeasure 0) E = (μ E : ℂ) := by
      rw [SignedMeasure.toComplexMeasure_apply]
      have hz : (0 : SignedMeasure ℝ) E = 0 := by simp
      rw [hz]
      rfl
    have hbound := VectorMeasure.enorm_measure_le_variation
      (μ.toComplexMeasure 0) E
    rw [hval] at hbound
    have hnorm : ‖(μ E : ℂ)‖ₑ = ‖μ E‖ₑ := by
      change ENNReal.ofNNReal ‖(μ E : ℂ)‖₊ = ENNReal.ofNNReal ‖μ E‖₊
      rw [Complex.nnnorm_real]
    rw [hnorm] at hbound
    exact hbound
  calc
    (initialSquareSigmaComplexifiedMeasure σ).variation =
        (μ.toComplexMeasure 0).variation := by rfl
    _ = μ.variation := le_antisymm hle hge
    _ = σ := by
      dsimp [μ]
      rw [Measure.variation_toSignedMeasure]

/-- The complexified dilated probability measure at a geometric scale. -/
def initialSquareComplexifiedSigmaScale
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ) (k : ℤ) :
    ComplexMeasure ℝ :=
  initialSquareDilateComplexMeasure
    (initialSquareSigmaComplexifiedMeasure σ) (b ^ k)

theorem initialSquareComplexifiedSigmaScale_variation_eq
    (σ : Measure ℝ) [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (k : ℤ) :
    (initialSquareComplexifiedSigmaScale σ b k).variation =
      Measure.map (fun y : ℝ => b ^ k * y) σ := by
  have ht : b ^ k ≠ 0 := by positivity
  have hemb := measurableEmbedding_mulLeft₀ ht
  rw [initialSquareComplexifiedSigmaScale, initialSquareDilateComplexMeasure,
    hemb.variation_map, initialSquareSigmaComplexifiedMeasure_variation_eq]

theorem initialSquareComplexifiedSigmaScale_variation_real_univ
    (σ : Measure ℝ) [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (k : ℤ) :
    (initialSquareComplexifiedSigmaScale σ b k).variation.real Set.univ = 1 := by
  rw [initialSquareComplexifiedSigmaScale_variation_eq σ hb k]
  simp

theorem initialSquareComplexifiedSigmaScale_variation_isFinite
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ) (k : ℤ) :
    IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation := by
  have hbase : IsFiniteMeasure (initialSquareSigmaComplexifiedMeasure σ).variation := by
    rw [initialSquareSigmaComplexifiedMeasure_variation_eq]
    infer_instance
  change IsFiniteMeasure
    ((initialSquareSigmaComplexifiedMeasure σ).map (fun y : ℝ => b ^ k * y)).variation
  infer_instance

theorem norm_initialSquareSigmaPositiveConvolutionLp_scale_sub_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (σ : Measure ℝ) [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (k : ℤ)
    [IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation]
    (F G : Lp ℂ p (volume : Measure ℝ)) :
    ‖lpPositiveConvolutionMap p hp
        (initialSquareComplexifiedSigmaScale σ b k) F -
      lpPositiveConvolutionMap p hp
        (initialSquareComplexifiedSigmaScale σ b k) G‖ ≤ ‖F - G‖ := by
  have h := norm_lpPositiveConvolutionMap_sub_le p hp
    (initialSquareComplexifiedSigmaScale σ b k) F G
  rw [initialSquareComplexifiedSigmaScale_variation_real_univ σ hb k] at h
  simpa using h

/-- The finite q-Lp realization of the source positive convolution maximal
operator. -/
def initialSquareSigmaFinitePositiveMaximalLp
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (s : Finset ℤ) (hne : s.Nonempty) :
    Lp ℂ p (volume : Measure ℝ) → Lp ℝ p (volume : Measure ℝ) :=
  lpFinitePositiveConvolutionSup p hp s hne
    (initialSquareComplexifiedSigmaScale σ b)
    (initialSquareComplexifiedSigmaScale_variation_isFinite σ b)

theorem continuous_initialSquareSigmaFinitePositiveMaximalLp
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (s : Finset ℤ) (hne : s.Nonempty) :
    Continuous (initialSquareSigmaFinitePositiveMaximalLp p hp σ b s hne) := by
  exact continuous_lpFinitePositiveConvolutionSup p hp s hne
    (initialSquareComplexifiedSigmaScale σ b)
    (initialSquareComplexifiedSigmaScale_variation_isFinite σ b)

#print axioms norm_lpComplexMeasureConvolutionRLinearMap_apply_le
#print axioms continuous_lpComplexPointwiseNorm
#print axioms continuous_lpComplexMeasureConvolutionCLM
#print axioms continuous_lpPositiveConvolutionMap
#print axioms norm_lpPositiveConvolutionMap_sub_le
#print axioms continuous_lpFinitePositiveConvolutionSup
#print axioms initialSquareSigmaComplexifiedMeasure_variation_eq
#print axioms initialSquareComplexifiedSigmaScale_variation_real_univ
#print axioms continuous_initialSquareSigmaFinitePositiveMaximalLp
#print axioms norm_initialSquareSigmaPositiveConvolutionLp_scale_sub_le

end

end FractionalPrimes.Literature.JSW

end
