module

public import FractionalPrimes.Literature.JSW.PositiveMaximalPsiAdapters

/-!
# Vector bounds for the cancellation measure

This module combines the already checked positive maximal adapters for the
geometric measure and smooth-density families. The first theorem isolates
the triangle-inequality step for arbitrary probability families; the source
adapter below then identifies their difference with the cancellation
measure at each geometric scale.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The diagonal vector convolution by the difference of two probability
families is bounded by the sum of the two positive-family constants. The
maximal inputs remain conditional, as in `lj:positivity`. -/
theorem finiteProbabilityDifference_lp_bound
    {ι : Type*} [Fintype ι] {p q : ℝ} (hp : 2 < p)
    (hrq : (p / 2).HolderConjugate q)
    (μσ μψ : ι → Measure ℝ)
    (hμσ : ∀ i, IsProbabilityMeasure (μσ i))
    (hμψ : ∀ i, IsProbabilityMeasure (μψ i))
    (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i))
    (Uσ Uψ : ℝ → EuclideanSpace ℂ ι)
    (hUσ : MemLp Uσ (ENNReal.ofReal p) volume)
    (hUψ : MemLp Uψ (ENNReal.ofReal p) volume)
    (hUσraw : ∀ i, (fun x => Uσ x i) =ᵐ[volume]
      (fun x => jswConvolution (μσ i) (f i) x))
    (hUψraw : ∀ i, (fun x => Uψ x i) =ᵐ[volume]
      (fun x => jswConvolution (μψ i) (f i) x))
    (Bσ Bψ : ℝ) (hBσ : 0 ≤ Bσ) (hBψ : 0 ≤ Bψ)
    (hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μσ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal q) volume)
    (hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μψ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal q) volume) :
    lpNorm (Uσ - Uψ) (ENNReal.ofReal p) volume ≤
      (Real.sqrt Bσ + Real.sqrt Bψ) *
        lpNorm (fun x => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  have hσ := finiteProbabilityConvolution_lp_bound hp hrq μσ hμσ
    f hf hstrong Uσ hUσ hUσraw Bσ hBσ hMaxσ
  have hψ := finiteProbabilityConvolution_lp_bound hp hrq μψ hμψ
    f hf hstrong Uψ hUψ hUψraw Bψ hBψ hMaxψ
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  calc
    lpNorm (Uσ - Uψ) (ENNReal.ofReal p) volume ≤
        lpNorm Uσ (ENNReal.ofReal p) volume +
          lpNorm Uψ (ENNReal.ofReal p) volume :=
      lpNorm_sub_le hUσ hp1
    _ ≤ Real.sqrt Bσ *
          lpNorm (fun x => WithLp.toLp 2 (fun i => f i x))
            (ENNReal.ofReal p) volume +
        Real.sqrt Bψ *
          lpNorm (fun x => WithLp.toLp 2 (fun i => f i x))
            (ENNReal.ofReal p) volume := add_le_add hσ hψ
    _ = (Real.sqrt Bσ + Real.sqrt Bψ) *
          lpNorm (fun x => WithLp.toLp 2 (fun i => f i x))
            (ENNReal.ofReal p) volume := by ring

/-- Complexification commutes with pushforward by a real dilation. -/
theorem initialSquareSigmaComplexMeasure_map_eq_dilate
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    initialSquareSigmaComplexMeasure (Measure.map (fun y : ℝ => t * y) μ) =
      initialSquareDilateComplexMeasure (initialSquareSigmaComplexMeasure μ) t := by
  ext E hE
  change ((Measure.map (fun y : ℝ => t * y) μ).toSignedMeasure.toComplexMeasure 0) E =
    ((μ.toSignedMeasure.toComplexMeasure 0).map (fun y : ℝ => t * y)) E
  rw [VectorMeasure.map_apply
    (v := μ.toSignedMeasure.toComplexMeasure 0)
    (f := fun y : ℝ => t * y) (by fun_prop) hE]
  rw [SignedMeasure.toComplexMeasure_apply, SignedMeasure.toComplexMeasure_apply,
    Measure.toSignedMeasure_apply_measurable hE,
    Measure.toSignedMeasure_apply_measurable
      (measurableSet_preimage (by fun_prop) hE)]
  rw [map_measureReal_apply (by fun_prop) hE]
  simp

#print axioms initialSquareSigmaComplexMeasure_map_eq_dilate

/-- The positive smooth-density complex measure is the complexification of
the probability measure with density `measureSplittingPsi`. -/
theorem initialSquarePsiComplexMeasure_eq_sigmaComplexMeasure
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hfinite : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ)) :
    initialSquarePsiComplexMeasure σ =
      @initialSquareSigmaComplexMeasure
        (initialSquarePsiProbabilityMeasure σ) hfinite := by
  letI : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ) := hfinite
  have hSigned : volume.withDensityᵥ (measureSplittingPsi σ) =
      (initialSquarePsiProbabilityMeasure σ).toSignedMeasure := by
    simpa [initialSquarePsiProbabilityMeasure] using
      initialSquarePsiMeasure_eq_toSignedMeasure_withDensity hSupp
  change SignedMeasure.toComplexMeasure
      (volume.withDensityᵥ (measureSplittingPsi σ)) 0 = _
  exact congrArg (fun μ : SignedMeasure ℝ => μ.toComplexMeasure 0) hSigned

#print axioms initialSquarePsiComplexMeasure_eq_sigmaComplexMeasure

/-- The dilated smooth complex measure is the complexification of the
corresponding pushforward probability measure. -/
theorem initialSquarePsiComplexMeasure_map_eq_dilate
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (t : ℝ)
    (hfinite : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ))
    (hmapfinite : IsFiniteMeasure (Measure.map (fun y : ℝ => t * y)
      (initialSquarePsiProbabilityMeasure σ))) :
    @initialSquareSigmaComplexMeasure
        (Measure.map (fun y : ℝ => t * y)
          (initialSquarePsiProbabilityMeasure σ)) hmapfinite =
      initialSquareDilateComplexMeasure
        (initialSquarePsiComplexMeasure σ) t := by
  letI : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ) := hfinite
  letI : IsFiniteMeasure (Measure.map (fun y : ℝ => t * y)
      (initialSquarePsiProbabilityMeasure σ)) := hmapfinite
  calc
    initialSquareSigmaComplexMeasure
        (Measure.map (fun y : ℝ => t * y)
          (initialSquarePsiProbabilityMeasure σ)) =
        initialSquareDilateComplexMeasure
          (initialSquareSigmaComplexMeasure (initialSquarePsiProbabilityMeasure σ)) t :=
      initialSquareSigmaComplexMeasure_map_eq_dilate
        (initialSquarePsiProbabilityMeasure σ) t
    _ = initialSquareDilateComplexMeasure
          (initialSquarePsiComplexMeasure σ) t := by
      rw [← initialSquarePsiComplexMeasure_eq_sigmaComplexMeasure hSupp hfinite]

#print axioms initialSquarePsiComplexMeasure_map_eq_dilate

/-- At every real dilation, the source cancellation measure is the difference
of the two complexified positive probability measures used in the maximal
adapters. -/
theorem initialSquareNuDilateComplexMeasure_eq_sigma_sub_psi
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (t : ℝ)
    (hfinitePsi : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ))
    (hfiniteSigmaMap : IsFiniteMeasure (Measure.map (fun y : ℝ => t * y) σ))
    (hfinitePsiMap : IsFiniteMeasure (Measure.map (fun y : ℝ => t * y)
      (initialSquarePsiProbabilityMeasure σ))) :
    initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) t =
      @initialSquareSigmaComplexMeasure
        (Measure.map (fun y : ℝ => t * y) σ) hfiniteSigmaMap -
      @initialSquareSigmaComplexMeasure
        (Measure.map (fun y : ℝ => t * y)
          (initialSquarePsiProbabilityMeasure σ)) hfinitePsiMap := by
  letI : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ) := hfinitePsi
  letI : IsFiniteMeasure (Measure.map (fun y : ℝ => t * y) σ) := hfiniteSigmaMap
  letI : IsFiniteMeasure (Measure.map (fun y : ℝ => t * y)
      (initialSquarePsiProbabilityMeasure σ)) := hfinitePsiMap
  calc
    initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) t =
        initialSquareDilateComplexMeasure
          (initialSquareSigmaComplexMeasure σ - initialSquarePsiComplexMeasure σ) t := by
          rw [initialSquareNuComplexMeasure_sub_split]
    _ = initialSquareDilateComplexMeasure
          (initialSquareSigmaComplexMeasure σ) t -
        initialSquareDilateComplexMeasure
          (initialSquarePsiComplexMeasure σ) t :=
      initialSquareDilateComplexMeasure_sub _ _ t
    _ = initialSquareSigmaComplexMeasure
          (Measure.map (fun y : ℝ => t * y) σ) -
        initialSquareSigmaComplexMeasure
          (Measure.map (fun y : ℝ => t * y)
            (initialSquarePsiProbabilityMeasure σ)) := by
      rw [← initialSquareSigmaComplexMeasure_map_eq_dilate σ t,
        ← initialSquarePsiComplexMeasure_map_eq_dilate hSupp t
          hfinitePsi hfinitePsiMap]

#print axioms initialSquareNuDilateComplexMeasure_eq_sigma_sub_psi

/-- At every finite exponent greater than one, the `Lᵖ` convolution by the
complexification of a finite positive measure agrees with the ordinary
probability-measure convolution of the chosen measurable representative. -/
theorem lpComplexSigmaConvolution_ae_eq_jswConvolution
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) volume)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f) :
    (lpComplexMeasureConvolution (ENNReal.ofReal q)
      (initialSquareSigmaComplexMeasure μ) F : ℝ → ℂ) =ᵐ[volume]
        jswConvolution μ f := by
  let μc : ComplexMeasure ℝ := initialSquareSigmaComplexMeasure μ
  have hμcVar : IsFiniteMeasure μc.variation := by
    have hvariation : μc.variation = μ := by
      dsimp [μc, initialSquareSigmaComplexMeasure,
        initialSquareSigmaComplexifiedMeasure]
      exact initialSquareSigmaComplexifiedMeasure_variation_eq μ
    rw [hvariation]
    infer_instance
  letI : IsFiniteMeasure μc.variation := hμcVar
  have hfAES : AEStronglyMeasurable f volume := hf.stronglyMeasurable.aestronglyMeasurable
  have hLpRaw := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp
    hq μc F f hf hfm hF
  have hfStrong : StronglyMeasurable f := hf.stronglyMeasurable
  have hmkStrong : StronglyMeasurable (hfAES.mk f) := hfAES.stronglyMeasurable_mk
  have hmk := rawComplexMeasureConvolution_ae_congr μc
    (hfAES.mk f) f hmkStrong hfStrong hfAES.ae_eq_mk.symm
  have hcomplex :
      (fun x : ℝ => complexMeasureConvolution μc f hfAES x) =ᵐ[volume]
        jswConvolution μ f := by
    filter_upwards [hmk] with x hxMk
    have hvec :
        (∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μc]) =
          ∫ y, f (x-y) ∂μ := by
      dsimp [μc, initialSquareSigmaComplexMeasure]
      rw [initialSquareNuComplexMeasure_integral_eq μ.toSignedMeasure,
        VectorMeasure.integral_toSignedMeasure]
    calc
      complexMeasureConvolution μc f hfAES x =
          ∫ᵛ y, hfAES.mk f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μc] := rfl
      _ = ∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μc] := hxMk
      _ = ∫ y, f (x-y) ∂μ := hvec
  exact hLpRaw.trans hcomplex

#print axioms lpComplexSigmaConvolution_ae_eq_jswConvolution

/-- Convolution on `Lᵖ` is additive in a difference of finite complex
measures. -/
theorem lpComplexMeasureConvolution_sub
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ ν : ComplexMeasure ℝ)
    [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    [IsFiniteMeasure (μ - ν).variation]
    (F : Lp ℂ p (volume : Measure ℝ)) :
    lpComplexMeasureConvolution p (μ - ν) F =
      lpComplexMeasureConvolution p μ F - lpComplexMeasureConvolution p ν F := by
  have hμ : μ.Integrable (fun y : ℝ => lpRightTranslate p y F) :=
    integrable_lpRightTranslate hp μ F
  have hν : ν.Integrable (fun y : ℝ => lpRightTranslate p y F) :=
    integrable_lpRightTranslate hp ν F
  unfold lpComplexMeasureConvolution
  exact VectorMeasure.integral_sub_vectorMeasure hμ hν

#print axioms lpComplexMeasureConvolution_sub

/-- The complexification of a finite positive measure has exactly that
measure as its total variation. -/
theorem initialSquareSigmaComplexMeasure_variation_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (initialSquareSigmaComplexMeasure μ).variation = μ := by
  simpa [initialSquareSigmaComplexMeasure, initialSquareSigmaComplexifiedMeasure]
    using initialSquareSigmaComplexifiedMeasure_variation_eq μ

#print axioms initialSquareSigmaComplexMeasure_variation_eq

/-- The smooth positive part has finite total variation because its density
is integrable. -/
private theorem initialSquarePsiComplexMeasure_variation_isFinite
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    IsFiniteMeasure (initialSquarePsiComplexMeasure σ).variation := by
  have hψint : Integrable (measureSplittingPsi σ) volume :=
    measureSplittingPsi_integrable σ hSupp
  have hfiniteDensity : IsFiniteMeasure
      (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    have hden : (fun x : ℝ => ‖measureSplittingPsi σ x‖ₑ) =
        fun x => ENNReal.ofReal (measureSplittingPsi σ x) := by
      funext x
      exact Real.enorm_eq_ofReal (measureSplittingPsi_nonneg σ x)
    rw [Measure.variation_withDensityᵥ hψint, hden]
    exact isFiniteMeasure_withDensity_ofReal hψint.2
  have hpsiFinite : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ) := by
    have hprob := initialSquarePsiProbabilityMeasure_isProbability hSupp
    letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) := hprob
    infer_instance
  have hpsiMapEq := initialSquarePsiComplexMeasure_eq_sigmaComplexMeasure
    hSupp hpsiFinite
  letI : IsFiniteMeasure (initialSquarePsiProbabilityMeasure σ) := hpsiFinite
  have hvariation : (initialSquarePsiComplexMeasure σ).variation =
      initialSquarePsiProbabilityMeasure σ := by
    rw [hpsiMapEq]
    exact initialSquareSigmaComplexifiedMeasure_variation_eq _
  rw [hvariation]
  infer_instance

/-- The complexified cancellation measure has finite total variation under
the source support assumption. -/
theorem initialSquareNuComplexMeasure_variation_isFinite_of_support
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation := by
  have hψint : Integrable (measureSplittingPsi σ) volume :=
    measureSplittingPsi_integrable σ hSupp
  have hden : (fun x : ℝ => ‖measureSplittingPsi σ x‖ₑ) =
      fun x => ENNReal.ofReal (measureSplittingPsi σ x) := by
    funext x
    exact Real.enorm_eq_ofReal (measureSplittingPsi_nonneg σ x)
  have hpsiVar : IsFiniteMeasure
      (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    rw [Measure.variation_withDensityᵥ hψint, hden]
    exact isFiniteMeasure_withDensity_ofReal hψint.2
  have hnuVar : IsFiniteMeasure (measureSplittingNu σ).variation := by
    have hvar : (measureSplittingNu σ).variation ≤
        σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
      simpa [measureSplittingNu, Measure.variation_toSignedMeasure] using
        (VectorMeasure.variation_sub_le (μ := σ.toSignedMeasure)
          (ν := volume.withDensityᵥ (measureSplittingPsi σ)))
    exact isFiniteMeasure_of_le
      (σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation) hvar
  have hvarComplex : (initialSquareNuComplexMeasure σ).variation ≤
      (measureSplittingNu σ).variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    rw [initialSquareNuComplexMeasure, SignedMeasure.toComplexMeasure_apply]
    have him : (0 : SignedMeasure ℝ) E = (0 : ℝ) := by simp
    rw [him]
    have hzero : ({ re := measureSplittingNu σ E, im := (0 : ℝ) } : ℂ) =
        (measureSplittingNu σ E : ℂ) := rfl
    rw [hzero]
    change ENNReal.ofNNReal ‖(measureSplittingNu σ E : ℂ)‖₊ ≤
      (measureSplittingNu σ).variation E
    rw [Complex.nnnorm_real]
    exact VectorMeasure.enorm_measure_le_variation (measureSplittingNu σ) E
  exact isFiniteMeasure_of_le (measureSplittingNu σ).variation hvarComplex

#print axioms initialSquareNuComplexMeasure_variation_isFinite_of_support

/-- The exact geometric `p>2` clause of `lj:positivity` for the
cancellation measure. The two source maximal adapters supply the positive
families, and their square-root strong bounds add by the triangle inequality. -/
theorem finiteGeometricNuVector_lp_bound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D b p q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 2 < p) (hq : 2 < q)
    (hrq : (p / 2).HolderConjugate q)
    (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p)⟩
    lpNorm
      (fun x : ℝ => WithLp.toLp 2 (fun i =>
        (lpComplexMeasureConvolution (ENNReal.ofReal p)
          (initialSquareDilateComplexMeasure
            (initialSquareNuComplexMeasure σ) (b ^ κ i))
          ((hf i).toLp (f i))) x))
      (ENNReal.ofReal p) volume ≤
      (Real.sqrt (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b)) +
        Real.sqrt ((4 * lpNorm φ ∞ volume) *
          ((6 * q * 2 ^ (q - 1) / (q - 1)) ^ (1 / q)))) *
        lpNorm (fun x => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hp1 : (1 : ℝ≥0∞) ≤ P := by
    dsimp [P]
    exact ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p)
  letI : Fact (1 ≤ P) := ⟨hp1⟩
  let ψbase : Measure ℝ := initialSquarePsiProbabilityMeasure σ
  have hψbaseProb : IsProbabilityMeasure ψbase :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  letI : IsProbabilityMeasure ψbase := hψbaseProb
  let μσ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) σ
  let μψ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) ψbase
  have hμσ : ∀ i, IsProbabilityMeasure (μσ i) := by
    intro i
    apply (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2
    infer_instance
  have hμψ : ∀ i, IsProbabilityMeasure (μψ i) := by
    intro i
    apply (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2
    infer_instance
  let μν : ι → ComplexMeasure ℝ := fun i =>
    initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ)
      (b ^ κ i)
  have hνbaseVar : IsFiniteMeasure
      (initialSquareNuComplexMeasure σ).variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation := hνbaseVar
  have hνVar : ∀ i, IsFiniteMeasure (μν i).variation := by
    intro i
    dsimp [μν, initialSquareDilateComplexMeasure]
    infer_instance
  let Tσ : ι → Lp ℂ P volume := fun i => by
    letI : IsProbabilityMeasure (μσ i) := hμσ i
    have hvar : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μσ i)).variation := by
      rw [initialSquareSigmaComplexMeasure_variation_eq]
      infer_instance
    letI : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μσ i)).variation := hvar
    exact lpComplexMeasureConvolution P
      (initialSquareSigmaComplexMeasure (μσ i)) ((hf i).toLp (f i))
  let Tψ : ι → Lp ℂ P volume := fun i => by
    letI : IsProbabilityMeasure (μψ i) := hμψ i
    have hvar : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μψ i)).variation := by
      rw [initialSquareSigmaComplexMeasure_variation_eq]
      infer_instance
    letI : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μψ i)).variation := hvar
    exact lpComplexMeasureConvolution P
      (initialSquareSigmaComplexMeasure (μψ i)) ((hf i).toLp (f i))
  let Tν : ι → Lp ℂ P volume := fun i => by
    letI : IsFiniteMeasure (μν i).variation := hνVar i
    exact lpComplexMeasureConvolution P (μν i) ((hf i).toLp (f i))
  let Uσ : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => (Tσ i) x)
  let Uψ : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => (Tψ i) x)
  let Vν : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => (Tν i) x)
  have hUσ : MemLp Uσ P volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (Tσ i)
  have hUψ : MemLp Uψ P volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (Tψ i)
  have hUσraw : ∀ i, (fun x => Uσ x i) =ᵐ[volume]
      (fun x => jswConvolution (μσ i) (f i) x) := by
    intro i
    letI : IsProbabilityMeasure (μσ i) := hμσ i
    change (fun x => (Tσ i) x) =ᵐ[volume] _
    dsimp [Tσ]
    exact lpComplexSigmaConvolution_ae_eq_jswConvolution (by linarith : 1 < p) (μσ i)
      ((hf i).toLp (f i)) (f i) (hstrong i).measurable (hf i)
      (MemLp.coeFn_toLp (hf i))
  have hUψraw : ∀ i, (fun x => Uψ x i) =ᵐ[volume]
      (fun x => jswConvolution (μψ i) (f i) x) := by
    intro i
    letI : IsProbabilityMeasure (μψ i) := hμψ i
    change (fun x => (Tψ i) x) =ᵐ[volume] _
    dsimp [Tψ]
    exact lpComplexSigmaConvolution_ae_eq_jswConvolution (by linarith : 1 < p) (μψ i)
      ((hf i).toLp (f i)) (f i) (hstrong i).measurable (hf i)
      (MemLp.coeFn_toLp (hf i))

  let Bσ : ℝ := weakTypeInterpolationStrongTwoInfinityConstant q
    (initialSquareSigmaPositiveMaximalB2 β D b)
  let Bψ : ℝ := (4 * lpNorm φ ∞ volume) *
    ((6 * q * 2 ^ (q - 1) / (q - 1)) ^ (1 / q))
  have hBσ : 0 ≤ Bσ := by
    dsimp [Bσ, weakTypeInterpolationStrongTwoInfinityConstant]
    have hbase : 0 ≤ q / (q - 2) := by
      apply div_nonneg
      · linarith
      · linarith
    have hA : 0 ≤ initialSquareSigmaPositiveMaximalB2 β D b :=
      initialSquareSigmaPositiveMaximalB2_nonneg hb hβ
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase _))
      (Real.rpow_nonneg hA _)
  have hBψ : 0 ≤ Bψ := by
    dsimp [Bψ]
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) lpNorm_nonneg
    · apply Real.rpow_nonneg
      apply div_nonneg
      · positivity
      · linarith
  have hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μσ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal q) volume := by
    intro g hg
    simpa [μσ, Bσ] using
      (finiteGeometricSigmaPositiveMaximalBound hSupp hdecay hb hβ hq κ g hg)
  have hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μψ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal q) volume := by
    intro g hg
    simpa [μψ, ψbase, Bψ] using
      (finiteGeometricPsiPositiveMaximalBound hSupp hb (by linarith : 1 < q)
        κ g hg)
  have hDiff := finiteProbabilityDifference_lp_bound hp hrq μσ μψ
    hμσ hμψ f hf hstrong Uσ Uψ hUσ hUψ hUσraw hUψraw
    Bσ Bψ hBσ hBψ hMaxσ hMaxψ
  have hVeq : Vν =ᵐ[volume] Uσ - Uψ := by
    have hcoord (i : ι) : (fun x => (Tν i) x) =ᵐ[volume]
        (fun x => (Tσ i) x - (Tψ i) x) := by
      letI : IsProbabilityMeasure (μσ i) := hμσ i
      letI : IsProbabilityMeasure (μψ i) := hμψ i
      have hσcVar : IsFiniteMeasure
          (initialSquareSigmaComplexMeasure (μσ i)).variation := by
        rw [initialSquareSigmaComplexMeasure_variation_eq]
        infer_instance
      have hψcVar : IsFiniteMeasure
          (initialSquareSigmaComplexMeasure (μψ i)).variation := by
        rw [initialSquareSigmaComplexMeasure_variation_eq]
        infer_instance
      letI : IsFiniteMeasure
          (initialSquareSigmaComplexMeasure (μσ i)).variation := hσcVar
      letI : IsFiniteMeasure
          (initialSquareSigmaComplexMeasure (μψ i)).variation := hψcVar
      have hψfinite : IsFiniteMeasure ψbase := inferInstance
      have hσmapFinite : IsFiniteMeasure (μσ i) := inferInstance
      have hψmapFinite : IsFiniteMeasure (μψ i) := inferInstance
      have hmeasure : μν i =
          initialSquareSigmaComplexMeasure (μσ i) -
            initialSquareSigmaComplexMeasure (μψ i) := by
        simpa [μν, μσ, μψ, ψbase] using
          (initialSquareNuDilateComplexMeasure_eq_sigma_sub_psi
            hSupp (b ^ κ i) hψfinite hσmapFinite hψmapFinite)
      have hsubFinite : IsFiniteMeasure
          ((initialSquareSigmaComplexMeasure (μσ i) -
            initialSquareSigmaComplexMeasure (μψ i)).variation) := by
        rw [← hmeasure]
        exact hνVar i
      letI : IsFiniteMeasure
          ((initialSquareSigmaComplexMeasure (μσ i) -
            initialSquareSigmaComplexMeasure (μψ i)).variation) := hsubFinite
      have hLpEq : Tν i = Tσ i - Tψ i := by
        dsimp [Tν, Tσ, Tψ]
        rw [hmeasure]
        exact lpComplexMeasureConvolution_sub ENNReal.ofReal_ne_top
          (initialSquareSigmaComplexMeasure (μσ i))
          (initialSquareSigmaComplexMeasure (μψ i))
          ((hf i).toLp (f i))
      rw [hLpEq]
      exact Lp.coeFn_sub (Tσ i) (Tψ i)
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    ext i
    exact hx i
  have hVNorm : lpNorm Vν P volume = lpNorm (Uσ - Uψ) P volume := by
    unfold lpNorm
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hVeq)
  change lpNorm Vν P volume ≤
      (Real.sqrt Bσ + Real.sqrt Bψ) *
        lpNorm (fun x => WithLp.toLp 2 (fun i => f i x)) P volume
  rw [hVNorm]
  simpa [Bσ, Bψ] using hDiff

#print axioms finiteGeometricNuVector_lp_bound

#print axioms finiteProbabilityDifference_lp_bound

end

end FractionalPrimes.Literature.JSW

end
