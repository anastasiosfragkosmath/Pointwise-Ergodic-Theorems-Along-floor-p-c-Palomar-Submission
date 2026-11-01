module

public import FractionalPrimes.Literature.Harmonic.EndpointBounds
public import FractionalPrimes.CompactMeasureSchwartz
public import FractionalPrimes.Literature.Multiplier.FiniteSupportDensity
public import FractionalPrimes.Literature.JSW.Conventions
public import FractionalPrimes.VariationMeasurability

/-!
# Dyadic variation limit bridge for the continuous model

This file records the exact dyadic family of endpoint operators and the
coordinatewise convergence/Fatou step in `ha:model-var`.  The estimate on
finite-support inputs remains conditional on the JSW variation estimate; this
file does not assert that external analytic input.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal
open scoped NNReal
open scoped Topology
open scoped FourierTransform
open scoped Convolution

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

/-- The paper's dyadic parameter `2^k`, reindexed by all positive integer
scales so it can be used by the project's variation functional. -/
def continuousModelDyadicParameter (s : FractionalPrimes.Scale) : ℝ :=
  (2 : ℝ) ^ (s.1 - 1)

theorem continuousModelDyadicParameter_pos (s : FractionalPrimes.Scale) :
    0 < continuousModelDyadicParameter s := by
  simp only [continuousModelDyadicParameter]
  positivity

theorem continuousModelDyadicParameter_succ (k : ℕ) :
    continuousModelDyadicParameter ⟨k + 1, by omega⟩ = (2 : ℝ) ^ k := by
  simp [continuousModelDyadicParameter]

/-- The endpoint operator at the dyadic parameter represented by a positive
scale. -/
noncomputable def continuousModelDyadicEndpointOperator {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (c : ℝ) (hc : 1 < c) (s : FractionalPrimes.Scale) :
    Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ p (Measure.count : Measure ℤ) :=
  continuousModelEndpointOperator (p := p) c
    (continuousModelDyadicParameter s) hc
    (continuousModelDyadicParameter_pos s)

/-- The dyadic continuous-model family as an actual counting-measure `Lᵖ`
output, with its canonical pointwise representative. -/
noncomputable def continuousModelDyadicFamily {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (c : ℝ) (hc : 1 < c)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    FractionalPrimes.Scale → ℤ → ℂ := fun s =>
      (continuousModelDyadicEndpointOperator (p := p) c hc s f :
        ℤ → ℂ)

/-- The dyadic family agrees with the paper's parameter `2^k` at scale
`⟨k+1, _⟩`; this keeps the source's `k ≥ 0` endpoint convention explicit. -/
theorem continuousModelDyadicFamily_succ {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : ℝ) (hc : 1 < c)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (k : ℕ) :
    continuousModelDyadicFamily c hc f ⟨k + 1, by omega⟩ =
      (continuousModelEndpointOperator (p := p) c ((2 : ℝ) ^ k) hc
        (by positivity) f : ℤ → ℂ) := by
  funext x
  simp [continuousModelDyadicFamily, continuousModelDyadicEndpointOperator,
    continuousModelDyadicParameter_succ]

/-- The finite Schwartz extension `E_ψ f`, retained as an actual Schwartz
map so the compact-measure convolution bridge applies without changing its
pointwise representative. -/
noncomputable def continuousModelSchwartzExtension (f : ℤ →₀ ℂ) :
    SchwartzMap ℝ ℂ :=
  ∑ n ∈ f.support, f n •
    continuousModelPsiSchwartz.compSubConstCLM ℂ (n : ℝ)

theorem continuousModelSchwartzExtension_apply (f : ℤ →₀ ℂ) (x : ℝ) :
    continuousModelSchwartzExtension f x =
      schwartzExtension continuousModelPsiSchwartz f x := by
  simp [continuousModelSchwartzExtension, schwartzExtension,
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul]

private theorem continuousModelFourier_eq_fourierIntegral (g : ℝ → ℂ)
    (ξ : ℝ) :
    𝓕 g ξ = Fourier.fourierIntegral Real.fourierChar volume g ξ := by
  rw [Real.fourier_eq, Fourier.fourierIntegral_def]
  congr 1
  funext x
  simp [mul_comm]

private theorem continuousModelFourier_translate (F : SchwartzMap ℝ ℂ)
    (a ξ : ℝ) :
    𝓕 (F.compSubConstCLM ℂ a) ξ =
      Real.fourierChar (-a * ξ) • 𝓕 F ξ := by
  rw [SchwartzMap.fourier_coe,
    continuousModelFourier_eq_fourierIntegral,
    SchwartzMap.fourier_coe,
    continuousModelFourier_eq_fourierIntegral]
  have hshift := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume
      (F : ℝ → ℂ) (-a)) ξ
  have htrans : (F.compSubConstCLM ℂ a : ℝ → ℂ) =
      (F : ℝ → ℂ) ∘ (fun x : ℝ => x + -a) := by
    funext x
    simp [SchwartzMap.compSubConstCLM_apply, sub_eq_add_neg]
  rw [htrans]
  exact hshift

private theorem continuousModelPsiFourier_eq_eta :
    𝓕 (continuousModelPsiSchwartz : ℝ → ℂ) =
      (continuousModelEtaComplexSchwartz : ℝ → ℂ) := by
  funext ξ
  change (𝓕 (𝓕⁻ continuousModelEtaComplexSchwartz)) ξ = _
  exact congrFun
    (congrArg (fun H : SchwartzMap ℝ ℂ => (H : ℝ → ℂ))
      (FourierInvPair.fourier_fourierInv_eq continuousModelEtaComplexSchwartz)) ξ

/-- A wider Fourier cutoff, equal to one on the exact support interval of the
fixed model cutoff.  The factor `1/2` keeps its support inside `(-1/2,1/2)`
and uses the model cutoff's checked plateau `[-1/8,1/8]`. -/
noncomputable def continuousModelReproducingFrequencyCutoff :
    SchwartzMap ℝ ℂ := by
  have hgrowth : Function.HasTemperateGrowth (fun x : ℝ => x / 2) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (show Function.HasTemperateGrowth (fun x : ℝ => (2 : ℝ)⁻¹ * x) by
        fun_prop)
  have hantiMul : AntilipschitzWith (2 : ℝ≥0)
      (fun x : ℝ => (2 : ℝ)⁻¹ * x) := by
    have hmul : AntilipschitzWith (‖(2 : ℝ)⁻¹‖₊⁻¹) ((2 : ℝ)⁻¹ * ·) :=
      antilipschitzWith_mul_left (a := (2 : ℝ)⁻¹) (by norm_num)
    simpa using hmul
  have hanti : AntilipschitzWith (2 : ℝ≥0) (fun x : ℝ => x / 2) := by
    convert hantiMul using 1
    funext x
    ring
  exact SchwartzMap.compCLMOfAntilipschitz ℂ hgrowth hanti
    continuousModelEtaComplexSchwartz

theorem continuousModelReproducingFrequencyCutoff_apply_eq_one
    {ξ : ℝ} (hξ : |ξ| ≤ 1 / 4) :
    continuousModelReproducingFrequencyCutoff ξ = 1 := by
  rw [continuousModelReproducingFrequencyCutoff,
    SchwartzMap.compCLMOfAntilipschitz_apply]
  have hξ' : |ξ / 2| ≤ 1 / 8 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  simpa [continuousModelEtaComplexSchwartz_apply, continuousModelEta] using
    (FractionalPrimes.Literature.Multiplier.ψ_eq_one_of_abs_le (ξ / 2) hξ')

/-- The physical-space reproducer whose Fourier transform is the wider cutoff. -/
noncomputable def continuousModelReproducingSchwartz : SchwartzMap ℝ ℂ :=
  𝓕⁻ continuousModelReproducingFrequencyCutoff

theorem continuousModelReproducingSchwartz_fourier_eq
    (ξ : ℝ) :
    𝓕 (continuousModelReproducingSchwartz : ℝ → ℂ) ξ =
      continuousModelReproducingFrequencyCutoff ξ := by
  change (𝓕 (𝓕⁻ continuousModelReproducingFrequencyCutoff)) ξ = _
  exact congrFun
    (congrArg (fun H : SchwartzMap ℝ ℂ => (H : ℝ → ℂ))
      (FourierInvPair.fourier_fourierInv_eq
        continuousModelReproducingFrequencyCutoff)) ξ

private theorem continuousModelSchwartzExtension_fourier_zero_of_eta_zero
    (f : ℤ →₀ ℂ) (ξ : ℝ)
    (hη : continuousModelEtaComplexSchwartz ξ = 0) :
    𝓕 (continuousModelSchwartzExtension f : ℝ → ℂ) ξ = 0 := by
  change (SchwartzMap.fourierTransformCLM ℂ
    (continuousModelSchwartzExtension f)) ξ = 0
  rw [continuousModelSchwartzExtension]
  change (SchwartzMap.fourierTransformCLM ℂ
      (∑ n ∈ f.support, f n •
        continuousModelPsiSchwartz.compSubConstCLM ℂ (n : ℝ))) ξ = 0
  rw [map_sum]
  simp only [map_smul]
  rw [sum_apply]
  simp only [smul_apply]
  apply Finset.sum_eq_zero
  intro n hn
  simp only [SchwartzMap.fourierTransformCLM_apply]
  rw [continuousModelFourier_translate]
  have hψ := congrFun continuousModelPsiFourier_eq_eta ξ
  have hψ' : (𝓕 continuousModelPsiSchwartz) ξ =
      continuousModelEtaComplexSchwartz ξ := by
    simpa only [SchwartzMap.fourier_coe] using hψ
  rw [hψ']
  simp [hη]

/-- The finite Schwartz extension is band-limited to the support of the
fixed cutoff.  Consequently the compact-measure Fourier cutoff reproduces
each of its compact-measure convolutions. -/
theorem continuousModelSchwartzExtension_fourierSupport_cutoff
    (f : ℤ →₀ ℂ) (ξ : ℝ)
    (hξ : ξ ∈ Function.support
      (𝓕 (continuousModelSchwartzExtension f : ℝ → ℂ))) :
    𝓕 (continuousModelReproducingSchwartz : ℝ → ℂ) ξ = 1 := by
  rw [continuousModelReproducingSchwartz_fourier_eq]
  have hη : continuousModelEtaComplexSchwartz ξ ≠ 0 := by
    intro hzero
    apply hξ
    have hzeroFourier :=
      continuousModelSchwartzExtension_fourier_zero_of_eta_zero f ξ hzero
    simpa [Function.mem_support] using hzeroFourier
  have hηreal : continuousModelEta ξ ≠ 0 := by
    intro hz
    apply hη
    simp [continuousModelEtaComplexSchwartz_apply, hz]
  have hts : ξ ∈ tsupport continuousModelEta :=
    subset_tsupport continuousModelEta hηreal
  have hinterval := continuousModelEta_tsupport_subset hts
  have habs : |ξ| < 1 / 4 := abs_lt.mpr ⟨by linarith [hinterval.1], hinterval.2⟩
  exact continuousModelReproducingFrequencyCutoff_apply_eq_one habs.le

/-- The exact dilation in `ha:model-var` at an integer scale `k`, namely
`2^(kc)`, written as the `c`th power of the positive dyadic scale. -/
def continuousModelDilation (c : ℝ) (k : ℤ) : ℝ := ((2 : ℝ) ^ k) ^ c

theorem continuousModelDilation_pos (c : ℝ) (_hc : 1 < c) (k : ℤ) :
    0 < continuousModelDilation c k := by
  unfold continuousModelDilation
  exact Real.rpow_pos_of_pos (zpow_pos (by norm_num) k) c

/-- The compactly supported pushforward measure for the `k`th JSW dilation,
realized directly from the unit-interval model measure. -/
noncomputable def continuousModelDyadicPushforward (c : ℝ) (k : ℤ) : Measure ℝ :=
  Measure.map (fun u : ℝ => continuousModelDilation c k * u ^ c)
    (volume.restrict (Set.Icc (0 : ℝ) 1))

theorem continuousModelDyadicPushforward_support_subset (c : ℝ)
    (hc : 1 < c) (k : ℤ) :
    (continuousModelDyadicPushforward c k).support ⊆
      Set.Icc (-(continuousModelDilation c k)) (continuousModelDilation c k) := by
  let t := continuousModelDilation c k
  have ht : 0 ≤ t := (continuousModelDilation_pos c hc k).le
  have hc0 : 0 ≤ c := by linarith
  apply (continuousModelDyadicPushforward c k).support_subset_of_isClosed isClosed_Icc
  change ∀ᵐ y ∂continuousModelDyadicPushforward c k,
    -(continuousModelDilation c k) ≤ y ∧ y ≤ continuousModelDilation c k
  rw [continuousModelDyadicPushforward,
    MeasureTheory.ae_map_iff (by fun_prop)
      (p := fun y : ℝ => -(continuousModelDilation c k) ≤ y ∧
        y ≤ continuousModelDilation c k) (by
          change MeasurableSet
            (Set.Ici (-(continuousModelDilation c k)) ∩
              Set.Iic (continuousModelDilation c k))
          exact measurableSet_Ici.inter measurableSet_Iic)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rcases Set.mem_Icc.mp hu with ⟨hu0, hu1⟩
  have hpow0 : 0 ≤ u ^ c := Real.rpow_nonneg hu0 c
  have hpow1 : u ^ c ≤ 1 := Real.rpow_le_one hu0 hu1 hc0
  change -t ≤ t * u ^ c ∧ t * u ^ c ≤ t
  constructor
  · nlinarith
  · calc
      t * u ^ c ≤ t * 1 := mul_le_mul_of_nonneg_left hpow1 ht
      _ = t := by ring

/-- The Schwartz convolution representing the continuous model at the exact
integer dilation `k∈ℤ`. -/
noncomputable def continuousModelDyadicConvolutionSchwartz (c : ℝ)
    (hc : 1 < c) (k : ℤ) (f : ℤ →₀ ℂ) : SchwartzMap ℝ ℂ := by
  let μ := continuousModelDyadicPushforward c k
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, continuousModelDyadicPushforward]
    exact (volume.restrict (Set.Icc (0 : ℝ) 1)).isFiniteMeasure_map _
  exact FractionalPrimes.measureSchwartzConvolutionSchwartz
    (continuousModelDilation_pos c hc k).le
    (continuousModelDyadicPushforward_support_subset c hc k)
    (continuousModelSchwartzExtension f)

/-- The continuous convolution family used by the conditional JSW estimate. -/
noncomputable def continuousModelAllDyadicConvolutionFamily (c : ℝ)
    (hc : 1 < c) (f : ℤ →₀ ℂ) : ℤ → ℝ → ℂ := fun k x =>
  continuousModelDyadicConvolutionSchwartz c hc k f x

theorem continuousModelAllDyadicConvolutionFamily_continuous (c : ℝ)
    (hc : 1 < c) (f : ℤ →₀ ℂ) (k : ℤ) :
    Continuous (continuousModelAllDyadicConvolutionFamily c hc f k) :=
  (continuousModelDyadicConvolutionSchwartz c hc k f).continuous

/-- The fixed cutoff identity required by the sampling lemma, obtained from
the checked compact-measure Fourier bridge for each dyadic pushforward. -/
theorem continuousModelAllDyadicConvolutionFamily_fixedPoint (c : ℝ)
    (hc : 1 < c) (f : ℤ →₀ ℂ) :
    IsSchwartzConvolutionFixedPoint continuousModelReproducingSchwartz
      (continuousModelAllDyadicConvolutionFamily c hc f) := by
  intro k z
  let μ := continuousModelDyadicPushforward c k
  let F := continuousModelSchwartzExtension f
  let G := continuousModelDyadicConvolutionSchwartz c hc k f
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, continuousModelDyadicPushforward]
    exact (volume.restrict (Set.Icc (0 : ℝ) 1)).isFiniteMeasure_map _
  have hχ : ∀ ξ, ξ ∈ Function.support (𝓕 (F : ℝ → ℂ)) →
      𝓕 (continuousModelReproducingSchwartz : ℝ → ℂ) ξ = 1 := by
    intro ξ hξ
    exact continuousModelSchwartzExtension_fourierSupport_cutoff f ξ hξ
  have hfix := FractionalPrimes.cutoff_measureSchwartzConvolution_apply
    (continuousModelDilation_pos c hc k).le
    (continuousModelDyadicPushforward_support_subset c hc k) F
    continuousModelReproducingSchwartz hχ z
  constructor
  · let M := SchwartzMap.seminorm ℝ 0 0 continuousModelReproducingSchwartz
    have hGint : Integrable (fun y : ℝ => (G y : ℂ)) (volume : Measure ℝ) :=
      G.integrable
    have hχmeas : AEStronglyMeasurable
        (fun y : ℝ => continuousModelReproducingSchwartz (z - y))
        (volume : Measure ℝ) :=
      (continuousModelReproducingSchwartz.continuous.comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    have hχbound : ∀ᵐ y ∂(volume : Measure ℝ),
        ‖continuousModelReproducingSchwartz (z - y)‖ ≤ M := by
      filter_upwards [] with y
      exact SchwartzMap.norm_le_seminorm ℝ continuousModelReproducingSchwartz (z - y)
    exact hGint.bdd_mul hχmeas hχbound
  · change G z = ∫ y : ℝ,
      continuousModelReproducingSchwartz (z - y) *
        continuousModelAllDyadicConvolutionFamily c hc f k y
    calc
      G z = FractionalPrimes.measureSchwartzConvolution μ F z := rfl
      _ = (continuousModelReproducingSchwartz ⋆[ContinuousLinearMap.mul ℂ ℂ]
            (G : ℝ → ℂ)) z := by
        simpa [F, G, μ, continuousModelDyadicConvolutionSchwartz,
          FractionalPrimes.measureSchwartzConvolution] using hfix.symm
      _ = ∫ y : ℝ,
          continuousModelReproducingSchwartz (z - y) * G y := by
        rw [convolution_eq_swap]
        simp only [ContinuousLinearMap.mul_apply']

private theorem continuousModel_unitInterval_restrict_integral
    (g : ℝ → ℂ) :
    (∫ u : ℝ, g u ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
      ∫ u in (0 : ℝ)..1, g u := by
  rw [integral_Icc_eq_integral_Ioc]
  symm
  exact intervalIntegral.integral_of_le (μ := volume) (by norm_num)

/-- Integrating one translated model cutoff against the exact dilation measure
gives the endpoint kernel coefficient used to define `C_{2^k}`. -/
private theorem continuousModelDyadicConvolution_term_eq_endpointKernel
    (c : ℝ) (hc : 1 < c) (k : ℕ) (m n : ℤ) :
    (∫ y : ℝ, continuousModelPsiSchwartz ((m - n : ℤ) - y) ∂
        continuousModelDyadicPushforward c (k : ℤ)) =
      (continuousModelEndpointKernel c ((2 : ℝ) ^ k) hc).coeff (m - n) := by
  let μ := continuousModelDyadicPushforward c (k : ℤ)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, continuousModelDyadicPushforward]
    exact (volume.restrict (Set.Icc (0 : ℝ) 1)).isFiniteMeasure_map _
  have hscale : continuousModelDilation c (k : ℤ) = ((2 : ℝ) ^ k) ^ c := by
    simp [continuousModelDilation]
  calc
    _ = ∫ u : ℝ, continuousModelPsiSchwartz
        ((m - n : ℤ) - continuousModelDilation c (k : ℤ) * u ^ c)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      dsimp [μ, continuousModelDyadicPushforward]
      rw [MeasureTheory.integral_map (by fun_prop)
        (integrable_schwartz_translate (μ := μ) continuousModelPsiSchwartz
          ((m - n : ℤ) : ℝ)).aestronglyMeasurable]
    _ = ∫ u in (0 : ℝ)..1, continuousModelPsiSchwartz
        ((m - n : ℤ) - ((2 : ℝ) ^ k) ^ c * u ^ c) := by
      rw [hscale]
      exact continuousModel_unitInterval_restrict_integral _
    _ = (continuousModelEndpointKernel c ((2 : ℝ) ^ k) hc).coeff (m - n) := by
      symm
      exact continuousModelEndpointKernel_coeff c ((2 : ℝ) ^ k) hc (m - n)

private theorem continuousModel_integerKernelConvolution_finsupp_sum
    (K : FractionalPrimes.IntegerL1Kernel) (f : ℤ →₀ ℂ) (x : ℤ) :
    FractionalPrimes.integerKernelConvolution K (f : ℤ → ℂ) x =
      ∑ n ∈ f.support, f n * K.coeff (x - n) := by
  classical
  let s := f.support.image (fun n : ℤ => x - n)
  have hzero (m : ℤ) (hm : m ∉ s) : K.coeff m * f (x - m) = 0 := by
    have hnot : x - m ∉ f.support := by
      intro hmem
      apply hm
      exact Finset.mem_image.mpr ⟨x - m, hmem, by simp⟩
    have hfzero : f (x - m) = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hfzero]
  have hexists := FractionalPrimes.integerKernelConvolutionExistsAt_of_finiteInputSupport
    K (f : ℤ → ℂ) x f.support (by
      intro j hj
      exact Finsupp.notMem_support_iff.mp hj)
  rw [FractionalPrimes.integerKernelConvolution_eq_tsum K (f : ℤ → ℂ) x hexists]
  rw [tsum_eq_sum (s := s) hzero]
  symm
  apply Finset.sum_bij (fun n _ => x - n)
  · intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    omega
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · intro n hn
    rw [show x - (x - n) = n by omega, mul_comm]

/-- On every finite input, the measure convolution at nonnegative dyadic
scales is exactly the source multiplier model `C_{2^k}` at each integer. -/
theorem continuousModelAllDyadicConvolutionFamily_apply_eq_continuousModelC
    (c : ℝ) (hc : 1 < c) (f : ℤ →₀ ℂ) (k : ℕ) (x : ℤ) :
    continuousModelAllDyadicConvolutionFamily c hc f (k : ℤ) x =
      continuousModelC c hc ((2 : ℝ) ^ k) (by positivity) f x := by
  let μ := continuousModelDyadicPushforward c (k : ℤ)
  let F := continuousModelSchwartzExtension f
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, continuousModelDyadicPushforward]
    exact (volume.restrict (Set.Icc (0 : ℝ) 1)).isFiniteMeasure_map _
  calc
    continuousModelAllDyadicConvolutionFamily c hc f (k : ℤ) x =
        ∫ y : ℝ, F ((x : ℝ) - y) ∂μ := rfl
    _ = ∫ y : ℝ, ∑ n ∈ f.support,
          f n * continuousModelPsiSchwartz (((x : ℝ) - (n : ℝ)) - y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [continuousModelSchwartzExtension_apply, schwartzExtension]
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      ring
    _ = ∑ n ∈ f.support, f n *
          ∫ y : ℝ, continuousModelPsiSchwartz
            (((x : ℝ) - (n : ℝ)) - y) ∂μ := by
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [integral_const_mul]
      · intro n hn
        exact (integrable_schwartz_translate (μ := μ)
          continuousModelPsiSchwartz ((x : ℝ) - (n : ℝ))).const_mul (f n)
    _ = ∑ n ∈ f.support, f n *
          (continuousModelEndpointKernel c ((2 : ℝ) ^ k) hc).coeff (x - n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Int.cast_sub]
      rw [continuousModelDyadicConvolution_term_eq_endpointKernel c hc k x n]
    _ = FractionalPrimes.integerKernelConvolution
          (continuousModelEndpointKernel c ((2 : ℝ) ^ k) hc) (f : ℤ → ℂ) x :=
      (continuousModel_integerKernelConvolution_finsupp_sum _ f x).symm
    _ = continuousModelC c hc ((2 : ℝ) ^ k) (by positivity) f x := by
      symm
      exact continuousModelC_apply_eq_integerKernelConvolution hc (by positivity) f x

/-- The source family `C_{2^k} f`, with `Scale = {N ≥ 1}` encoding exactly
the paper's finite starting index `k ≥ 0` through `N=k+1`. -/
noncomputable def continuousModelFiniteSupportDyadicFamily (c : ℝ)
    (hc : 1 < c) (f : ℤ →₀ ℂ) : FractionalPrimes.Scale → ℤ → ℂ :=
  fun s x => continuousModelC c hc (continuousModelDyadicParameter s)
    (continuousModelDyadicParameter_pos s) f x

/-- The order-preserving embedding of source scales `N≥1` into integer
dyadic indices `k=N-1`. -/
def continuousModelScaleIntegerIndex (s : FractionalPrimes.Scale) : ℤ :=
  ((s.1 - 1 : ℕ) : ℤ)

theorem continuousModelScaleIntegerIndex_strictMono :
    StrictMono continuousModelScaleIntegerIndex := by
  intro s t hst
  change s.1 < t.1 at hst
  have hnat : (s.1 - 1 : ℕ) < (t.1 - 1 : ℕ) := by omega
  change ((s.1 - 1 : ℕ) : ℤ) < ((t.1 - 1 : ℕ) : ℤ)
  exact_mod_cast hnat

private theorem continuousModel_scaleVariation_le_all (r : ℝ)
    (u : ℤ → ℂ) :
    FractionalPrimes.rVariation r
        (fun s : FractionalPrimes.Scale => u (continuousModelScaleIntegerIndex s)) ≤
      FractionalPrimes.Literature.Variation.orderedRVariation r u := by
  classical
  unfold FractionalPrimes.rVariation
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  let chain' : FractionalPrimes.Literature.Variation.StrictOrderedChain ℤ length :=
    { point := fun i => continuousModelScaleIntegerIndex (chain.index i)
      strictMono := continuousModelScaleIntegerIndex_strictMono.comp chain.strictMono }
  have heq :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (continuousModelScaleIntegerIndex
          (chain.index i.succ)) - u (continuousModelScaleIntegerIndex
          (chain.index i.castSucc))‖).rpow r).rpow r⁻¹ =
        FractionalPrimes.Literature.Variation.finiteChainVariation r u chain' := rfl
  rw [heq]
  exact FractionalPrimes.Literature.Variation.finiteChainVariation_le_orderedRVariation
    r u chain'

theorem continuousModelFiniteSupportDyadicFamily_eq_convolutionFamily
    (c : ℝ) (hc : 1 < c) (f : ℤ →₀ ℂ)
    (s : FractionalPrimes.Scale) (x : ℤ) :
    continuousModelFiniteSupportDyadicFamily c hc f s x =
      continuousModelAllDyadicConvolutionFamily c hc f
        (continuousModelScaleIntegerIndex s) x := by
  change continuousModelC c hc (continuousModelDyadicParameter s)
      (continuousModelDyadicParameter_pos s) f x = _
  have hparam : continuousModelDyadicParameter s =
      (2 : ℝ) ^ (s.1 - 1 : ℕ) := rfl
  cases hparam
  exact (continuousModelAllDyadicConvolutionFamily_apply_eq_continuousModelC
    c hc f (s.1 - 1) x).symm

/-- On a finite input, the operator extension on its canonical counting-`Lp`
representative is exactly the source finite-support model at every dyadic
scale. -/
theorem continuousModelDyadicFamily_apply_finsupp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (c : ℝ) (hc : 1 < c) (f : ℤ →₀ ℂ)
    (s : FractionalPrimes.Scale) (x : ℤ) :
    continuousModelDyadicFamily c hc
        (continuousModelFinsuppCountLp (Fact.out : 1 ≤ p) f) s x =
      continuousModelFiniteSupportDyadicFamily c hc f s x := by
  change ((continuousModelEndpointOperator (p := p) c
      (continuousModelDyadicParameter s) hc
      (continuousModelDyadicParameter_pos s)
      (continuousModelFinsuppCountLp (Fact.out : 1 ≤ p) f) :
        ℤ → ℂ) x) =
    continuousModelC c hc (continuousModelDyadicParameter s)
      (continuousModelDyadicParameter_pos s) f x
  exact continuousModelEndpointOperator_apply_finsupp hc
    (continuousModelDyadicParameter_pos s) f x

/-- Conditional finite-support `ha:model-var` transfer.  Its sole unproved
analytic input is the exact all-integer JSW variation estimate `hjsw` for
this measure-convolution family.  The sampling and extension factors are the
source constants `Lχ^(1−1/p)Sχ^(1/p)` and `Sψ^(1−1/p)Lψ^(1/p)`, respectively. -/
theorem continuousModelFiniteSupportDyadicVariation_eLpNorm_le_of_jsw
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : ℝ) (hc : 1 < c)
    (f : ℤ →₀ ℂ) (Cjsw : ℝ≥0∞)
    (hjsw : MeasureTheory.eLpNorm
        (fun y : ℝ =>
          FractionalPrimes.Literature.Variation.orderedRVariation r
            (fun k : ℤ => continuousModelAllDyadicConvolutionFamily c hc f k y))
        (ENNReal.ofReal p) (volume : Measure ℝ) ≤
      Cjsw * MeasureTheory.eLpNorm
        (continuousModelSchwartzExtension f : ℝ → ℂ)
        (ENNReal.ofReal p) (volume : Measure ℝ)) :
    MeasureTheory.eLpNorm
        (FractionalPrimes.rVariationFun r
          (continuousModelFiniteSupportDyadicFamily c hc f))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal
          (schwartzExtensionL continuousModelReproducingSchwartz ^ (1 - p⁻¹) *
            schwartzExtensionS continuousModelReproducingSchwartz ^ p⁻¹) *
        Cjsw *
        ENNReal.ofReal
          (schwartzExtensionS continuousModelPsiSchwartz ^ (1 - p⁻¹) *
            schwartzExtensionL continuousModelPsiSchwartz ^ p⁻¹) *
        ENNReal.ofReal
          (MeasureTheory.lpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
            (Measure.count : Measure ℤ)) := by
  let G := continuousModelAllDyadicConvolutionFamily c hc f
  let χ := continuousModelReproducingSchwartz
  let ψ := continuousModelPsiSchwartz
  let Cχ : ℝ := schwartzExtensionL χ ^ (1 - p⁻¹) *
    schwartzExtensionS χ ^ p⁻¹
  let Cψ : ℝ := schwartzExtensionS ψ ^ (1 - p⁻¹) *
    schwartzExtensionL ψ ^ p⁻¹
  have hp' : 1 ≤ p := le_of_lt hp
  have hr' : 1 ≤ r := by linarith
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hInv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hOneMinus : 0 ≤ 1 - p⁻¹ := by
    have hinv : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp'
    linarith
  have hCψ : 0 ≤ Cψ :=
    mul_nonneg
      (Real.rpow_nonneg (schwartzExtensionS_nonneg ψ) (1 - p⁻¹))
      (Real.rpow_nonneg (schwartzExtensionL_nonneg ψ) p⁻¹)
  have hψmem : MeasureTheory.MemLp
      (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
      (ENNReal.ofReal p) (volume : Measure ℝ) :=
    schwartzExtension_memLp hp' ψ f
  have hψnorm : MeasureTheory.eLpNorm
      (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
      (ENNReal.ofReal p) (volume : Measure ℝ) =
        ENNReal.ofReal (MeasureTheory.lpNorm
          (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
          (ENNReal.ofReal p) (volume : Measure ℝ)) := by
    symm
    exact MeasureTheory.ofReal_lpNorm hψmem
  have hψbound : MeasureTheory.eLpNorm
      (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
      (ENNReal.ofReal p) (volume : Measure ℝ) ≤
        ENNReal.ofReal Cψ * ENNReal.ofReal
          (MeasureTheory.lpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
            (Measure.count : Measure ℤ)) := by
    rw [hψnorm]
    have hreal := schwartzExtension_lpNorm_le hp' ψ f
    calc
      ENNReal.ofReal (MeasureTheory.lpNorm
          (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
          (ENNReal.ofReal p) (volume : Measure ℝ)) ≤
          ENNReal.ofReal (Cψ * MeasureTheory.lpNorm (f : ℤ → ℂ)
            (ENNReal.ofReal p) (Measure.count : Measure ℤ)) :=
        ENNReal.ofReal_le_ofReal (by simpa [Cψ, ψ] using hreal)
      _ = ENNReal.ofReal Cψ * ENNReal.ofReal
          (MeasureTheory.lpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
            (Measure.count : Measure ℤ)) := by
        rw [ENNReal.ofReal_mul hCψ]
  have hcont : ∀ k : ℤ, Continuous (G k) := by
    intro k
    exact continuousModelAllDyadicConvolutionFamily_continuous c hc f k
  have hfixed : IsSchwartzConvolutionFixedPoint χ G := by
    exact continuousModelAllDyadicConvolutionFamily_fixedPoint c hc f
  have hsample := schwartzVariationSampling_eLpNorm_le hp' hr' χ G hcont hfixed
  have hsample' : MeasureTheory.eLpNorm
      (fun n : ℤ => FractionalPrimes.Literature.Variation.orderedRVariation r
        (fun k : ℤ => G k n)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal Cχ * MeasureTheory.eLpNorm
        (fun y : ℝ => FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun k : ℤ => G k y)) (ENNReal.ofReal p) (volume : Measure ℝ) := by
    simpa [Cχ, χ, G] using hsample
  have hFψ : (continuousModelSchwartzExtension f : ℝ → ℂ) =
      FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f := by
    funext x
    exact continuousModelSchwartzExtension_apply f x
  have hjsw' : MeasureTheory.eLpNorm
      (fun y : ℝ => FractionalPrimes.Literature.Variation.orderedRVariation r
        (fun k : ℤ => G k y)) (ENNReal.ofReal p) (volume : Measure ℝ) ≤
      Cjsw * MeasureTheory.eLpNorm
        (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
        (ENNReal.ofReal p) (volume : Measure ℝ) := by
    simpa [G, hFψ] using hjsw
  have hvariation : MeasureTheory.eLpNorm
      (FractionalPrimes.rVariationFun r
        (continuousModelFiniteSupportDyadicFamily c hc f))
      (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      MeasureTheory.eLpNorm
        (fun n : ℤ => FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun k : ℤ => G k n)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    apply MeasureTheory.eLpNorm_mono_enorm_ae AEStronglyMeasurable.of_discrete
    filter_upwards [] with n
    have hseq : (fun s : FractionalPrimes.Scale =>
        continuousModelFiniteSupportDyadicFamily c hc f s n) =
        (fun s : FractionalPrimes.Scale =>
          G (continuousModelScaleIntegerIndex s) n) := by
      funext s
      exact continuousModelFiniteSupportDyadicFamily_eq_convolutionFamily
        c hc f s n
    rw [FractionalPrimes.rVariationFun_apply, hseq]
    exact continuousModel_scaleVariation_le_all r (fun k => G k n)
  calc
    _ ≤ MeasureTheory.eLpNorm
          (fun n : ℤ => FractionalPrimes.Literature.Variation.orderedRVariation r
            (fun k : ℤ => G k n)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      hvariation
    _ ≤ ENNReal.ofReal Cχ *
          MeasureTheory.eLpNorm
            (fun y : ℝ => FractionalPrimes.Literature.Variation.orderedRVariation r
              (fun k : ℤ => G k y)) (ENNReal.ofReal p) (volume : Measure ℝ) :=
      hsample'
    _ ≤ ENNReal.ofReal Cχ * (Cjsw *
          MeasureTheory.eLpNorm
            (FractionalPrimes.Literature.Harmonic.schwartzExtension ψ f)
            (ENNReal.ofReal p) (volume : Measure ℝ)) :=
      mul_le_mul_of_nonneg_left hjsw' (by positivity)
    _ ≤ ENNReal.ofReal Cχ * (Cjsw *
          (ENNReal.ofReal Cψ * ENNReal.ofReal
            (MeasureTheory.lpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
              (Measure.count : Measure ℤ)))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hψbound (by positivity)
      · positivity
    _ = _ := by simp [Cχ, Cψ, χ, ψ, mul_assoc]

/-- Conditional form of the `ha:model-var` density/Fatou step.  If a sequence
of inputs converges in `Lᵖ` and its dyadic model variations have a uniform
powered-integral bound, the same bound holds for the limit.  The finite-input
variation estimate needed to instantiate `hbound` comes from `ha:jsw` and is
not asserted here. -/
theorem continuousModelDyadicVariation_lintegral_le_of_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {r q : ℝ}
    (hr : 1 ≤ r) (hq : 1 ≤ q) (c : ℝ) (hc : 1 < c)
    (f : Lp ℂ p (Measure.count : Measure ℤ))
    (approx : ℕ → Lp ℂ p (Measure.count : Measure ℤ))
    (hlim : Tendsto approx atTop (𝓝 f)) (C : ℝ≥0∞)
    (hbound : ∀ m, ∫⁻ n : ℤ,
      (FractionalPrimes.rVariationFun r
        (continuousModelDyadicFamily c hc (approx m)) n) ^ q
        ∂(Measure.count : Measure ℤ) ≤ C) :
    ∫⁻ n : ℤ,
      (FractionalPrimes.rVariationFun r
        (continuousModelDyadicFamily c hc f) n) ^ q
        ∂(Measure.count : Measure ℤ) ≤ C := by
  let F : FractionalPrimes.Scale → ℤ → ℂ :=
    continuousModelDyadicFamily c hc f
  let G : ℕ → FractionalPrimes.Scale → ℤ → ℂ := fun m =>
    continuousModelDyadicFamily c hc (approx m)
  have hF : ∀ N, Measurable (F N) := by
    intro N
    exact measurable_of_countable _
  have hG : ∀ m N, Measurable (G m N) := by
    intro m N
    exact measurable_of_countable _
  have hconv : ∀ N, ∀ᵐ n ∂(Measure.count : Measure ℤ),
      Tendsto (fun m => G m N n) atTop (𝓝 (F N n)) := by
    intro N
    have hT : Tendsto
        (fun m => continuousModelDyadicEndpointOperator (p := p) c hc N
          (approx m)) atTop
        (𝓝 (continuousModelDyadicEndpointOperator (p := p) c hc N f)) :=
      (continuousModelDyadicEndpointOperator (p := p) c hc N).continuous.tendsto f |>.comp hlim
    have hpoint : ∀ n : ℤ, Tendsto (fun m => G m N n) atTop (𝓝 (F N n)) := by
      intro n
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [Metric.tendsto_nhds.mp hT ε hε] with m hm
      have hsubAE := ae_count_int_iff_forall.mp
          (Lp.coeFn_sub
            (continuousModelDyadicEndpointOperator (p := p) c hc N
              (approx m))
            (continuousModelDyadicEndpointOperator (p := p) c hc N f))
      have hsub :
          ((continuousModelDyadicEndpointOperator (p := p) c hc N
              (approx m) -
            continuousModelDyadicEndpointOperator (p := p) c hc N f :
              Lp ℂ p (Measure.count : Measure ℤ)) : ℤ → ℂ) n =
            (continuousModelDyadicEndpointOperator (p := p) c hc N
                (approx m) : ℤ → ℂ) n -
              (continuousModelDyadicEndpointOperator (p := p) c hc N f :
                ℤ → ℂ) n :=
        hsubAE n
      calc
        dist (G m N n) (F N n) =
            ‖((continuousModelDyadicEndpointOperator (p := p) c hc N
                (approx m) -
              continuousModelDyadicEndpointOperator (p := p) c hc N f :
                Lp ℂ p (Measure.count : Measure ℤ)) : ℤ → ℂ) n‖ := by
          rw [dist_eq_norm]
          rw [hsub]
          rfl
        _ ≤ ‖continuousModelDyadicEndpointOperator (p := p) c hc N
              (approx m) -
            continuousModelDyadicEndpointOperator (p := p) c hc N f‖ :=
          FractionalPrimes.integerLp_norm_apply_le_norm (Fact.out : 1 ≤ p)
            _ n
        _ = dist
            (continuousModelDyadicEndpointOperator (p := p) c hc N
              (approx m))
            (continuousModelDyadicEndpointOperator (p := p) c hc N f) :=
          (dist_eq_norm _ _).symm
        _ < ε := hm
    exact ae_of_all (Measure.count : Measure ℤ) hpoint
  have hfatou := FractionalPrimes.countableVariationFatou
    (Measure.count : Measure ℤ) r q hr hq F G hF hG hconv
  rcases hfatou with ⟨_, _, huniform, _⟩
  apply huniform C
  simpa [F, G] using hbound

/-- The symmetric finite truncations in counting-measure `Lᵖ`, expressed via
the checked isometric bridge to the sequence `lp` space. -/
private noncomputable def continuousModelDyadicLpTruncation
    {P : ℝ≥0∞} (hP0 : P ≠ 0) (hPtop : P ≠ ∞)
    [Fact (1 ≤ P)] (f : Lp ℂ P (Measure.count : Measure ℤ)) (m : ℕ) :
    Lp ℂ P (Measure.count : Measure ℤ) :=
  FractionalPrimes.generalLpToCountLp hP0 hPtop
    (FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
      (P := P) (Finset.Icc (-(m : ℤ)) (m : ℤ))
      (FractionalPrimes.countLpToGeneralLp hP0 hPtop f))

/-- The finite-support sequence representing the same truncation. -/
private noncomputable def continuousModelDyadicFinsuppTruncation
    (f : ℤ → ℂ) (m : ℕ) : ℤ →₀ ℂ :=
  Finsupp.onFinset (Finset.Icc (-(m : ℤ)) (m : ℤ))
    (fun n => if n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) then f n else 0)
    (by
      intro n hn
      by_contra hnot
      simp [hnot] at hn)

private theorem continuousModelDyadicFinsuppTruncation_apply
    (f : ℤ → ℂ) (m : ℕ) (n : ℤ) :
    continuousModelDyadicFinsuppTruncation f m n =
      if n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) then f n else 0 := by
  classical
  simp [continuousModelDyadicFinsuppTruncation]

private theorem continuousModelDyadicLpTruncation_apply
    {P : ℝ≥0∞} (hP0 : P ≠ 0) (hPtop : P ≠ ∞)
    [Fact (1 ≤ P)] (f : Lp ℂ P (Measure.count : Measure ℤ))
    (m : ℕ) (n : ℤ) :
    (continuousModelDyadicLpTruncation hP0 hPtop f m : ℤ → ℂ) n =
      if n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) then f n else 0 := by
  simp [continuousModelDyadicLpTruncation,
    FractionalPrimes.generalLpToCountLp_apply,
    FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation_apply,
    FractionalPrimes.countLpToGeneralLp_apply]

private theorem continuousModelDyadicLpTruncation_eq_finsupp
    {P : ℝ≥0∞} (hP0 : P ≠ 0) (hPtop : P ≠ ∞)
    [Fact (1 ≤ P)] (f : Lp ℂ P (Measure.count : Measure ℤ))
    (m : ℕ) :
    continuousModelDyadicLpTruncation hP0 hPtop f m =
      continuousModelFinsuppCountLp (Fact.out : 1 ≤ P)
        (continuousModelDyadicFinsuppTruncation (f : ℤ → ℂ) m) := by
  apply Lp.ext
  apply ae_count_int_iff_forall.mpr
  intro n
  rw [continuousModelDyadicLpTruncation_apply,
    continuousModelFinsuppCountLp_apply,
    continuousModelDyadicFinsuppTruncation_apply]

private theorem continuousModelDyadicLpTruncation_tendsto
    {P : ℝ≥0∞} (hP0 : P ≠ 0) (hPtop : P ≠ ∞)
    [Fact (1 ≤ P)] (f : Lp ℂ P (Measure.count : Measure ℤ)) :
    Tendsto (fun m => continuousModelDyadicLpTruncation hP0 hPtop f m)
      atTop (𝓝 f) := by
  let fSeq := FractionalPrimes.countLpToGeneralLp hP0 hPtop f
  have hseq :=
    FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation_Icc_tendsto
      (P := P) hPtop fSeq
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hseq ε hε] with m hm
  have hdist :
      dist (continuousModelDyadicLpTruncation hP0 hPtop f m) f =
        dist (FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
          (P := P) (Finset.Icc (-(m : ℤ)) (m : ℤ)) fSeq) fSeq := by
    rw [dist_eq_norm, dist_eq_norm]
    change ‖FractionalPrimes.generalLpToCountLp hP0 hPtop
        (FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
          (P := P) (Finset.Icc (-(m : ℤ)) (m : ℤ)) fSeq) - f‖ = _
    have hmap :
        FractionalPrimes.generalLpToCountLp hP0 hPtop
            (FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
              (P := P)
              (Finset.Icc (-(m : ℤ)) (m : ℤ)) fSeq - fSeq) =
          FractionalPrimes.generalLpToCountLp hP0 hPtop
              (FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
                (P := P) (Finset.Icc (-(m : ℤ)) (m : ℤ)) fSeq) - f := by
      rw [map_sub,
        FractionalPrimes.generalLpToCountLp_countLpToGeneralLp hP0 hPtop f]
    calc
      _ = ‖FractionalPrimes.generalLpToCountLp hP0 hPtop
            (FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
              (P := P) (Finset.Icc (-(m : ℤ)) (m : ℤ)) fSeq - fSeq)‖ := by
          rw [← hmap]
      _ = ‖FractionalPrimes.Literature.Multiplier.finiteSupportLpTruncation
            (P := P) (Finset.Icc (-(m : ℤ)) (m : ℤ)) fSeq - fSeq‖ :=
          FractionalPrimes.generalLpToCountLp_norm hP0 hPtop _
  rw [hdist]
  exact hm

private theorem continuousModel_eLpNorm_ennreal_rpow
    (p : ℝ) (hp : 0 < p) (F : ℤ → ℝ≥0∞)
    (hF : Measurable F) :
    MeasureTheory.eLpNorm F (ENNReal.ofReal p)
        (Measure.count : Measure ℤ) ^ p =
      ∫⁻ n : ℤ, F n ^ p ∂(Measure.count : Measure ℤ) := by
  have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0
    ENNReal.ofReal_ne_top hF.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- Conditional full `ha:model-var` statement.  The hypothesis is the
all-integer JSW variation bound for every finite-support Schwartz extension;
the proof transfers the finite estimate through symmetric finite-support
truncations and the checked countable-chain Fatou bridge. -/
theorem continuousModelDyadicVariation_eLpNorm_le_of_jsw
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : ℝ) (hc : 1 < c)
    (Cjsw : ℝ≥0)
    (hjsw : ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm
        (fun y : ℝ =>
          FractionalPrimes.Literature.Variation.orderedRVariation r
            (fun k : ℤ => continuousModelAllDyadicConvolutionFamily c hc g k y))
        (ENNReal.ofReal p) (volume : Measure ℝ) ≤
      (Cjsw : ℝ≥0∞) * MeasureTheory.eLpNorm
        (continuousModelSchwartzExtension g : ℝ → ℂ)
        (ENNReal.ofReal p) (volume : Measure ℝ))
    (f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
    MeasureTheory.eLpNorm
      (FractionalPrimes.rVariationFun r (continuousModelDyadicFamily c hc f))
      (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
    ENNReal.ofReal
        (schwartzExtensionL continuousModelReproducingSchwartz ^ (1 - p⁻¹) *
          schwartzExtensionS continuousModelReproducingSchwartz ^ p⁻¹) *
      (Cjsw : ℝ≥0∞) *
      ENNReal.ofReal
        (schwartzExtensionS continuousModelPsiSchwartz ^ (1 - p⁻¹) *
          schwartzExtensionL continuousModelPsiSchwartz ^ p⁻¹) *
      MeasureTheory.eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ) := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne'
  have hPtop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  letI : Fact (1 ≤ P) := ⟨by
    dsimp [P]
    simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  let approx : ℕ → Lp ℂ P (Measure.count : Measure ℤ) := fun m =>
    continuousModelDyadicLpTruncation hP0 hPtop f m
  let Cχ : ℝ :=
    schwartzExtensionL continuousModelReproducingSchwartz ^ (1 - p⁻¹) *
      schwartzExtensionS continuousModelReproducingSchwartz ^ p⁻¹
  let Cψ : ℝ :=
    schwartzExtensionS continuousModelPsiSchwartz ^ (1 - p⁻¹) *
      schwartzExtensionL continuousModelPsiSchwartz ^ p⁻¹
  let K : ℝ≥0∞ :=
    ENNReal.ofReal Cχ * (Cjsw : ℝ≥0∞) * ENNReal.ofReal Cψ
  have hlim : Tendsto approx atTop (𝓝 f) := by
    exact continuousModelDyadicLpTruncation_tendsto hP0 hPtop f
  have happroxPoint (m : ℕ) (n : ℤ) :
      (approx m : ℤ → ℂ) n =
        if n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) then f n else 0 := by
    exact continuousModelDyadicLpTruncation_apply hP0 hPtop f m n
  have happroxFinsupp (m : ℕ) :
      approx m = continuousModelFinsuppCountLp (Fact.out : 1 ≤ P)
        (continuousModelDyadicFinsuppTruncation (f : ℤ → ℂ) m) := by
    exact continuousModelDyadicLpTruncation_eq_finsupp hP0 hPtop f m
  have happroxNorm (m : ℕ) :
      MeasureTheory.eLpNorm (approx m : ℤ → ℂ) P
          (Measure.count : Measure ℤ) ≤
        MeasureTheory.eLpNorm (f : ℤ → ℂ) P
          (Measure.count : Measure ℤ) := by
    apply MeasureTheory.eLpNorm_mono_enorm_ae
      AEStronglyMeasurable.of_discrete
    filter_upwards [] with n
    rw [happroxPoint]
    by_cases hn : n ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · simp [hn]
    · simp [hn]
  have hfiniteBound (m : ℕ) :
      MeasureTheory.eLpNorm
          (FractionalPrimes.rVariationFun r
            (continuousModelDyadicFamily c hc (approx m))) P
          (Measure.count : Measure ℤ) ≤
        K * MeasureTheory.eLpNorm (f : ℤ → ℂ) P
          (Measure.count : Measure ℤ) := by
    let g := continuousModelDyadicFinsuppTruncation (f : ℤ → ℂ) m
    have hfamily :
        continuousModelDyadicFamily c hc (approx m) =
          continuousModelFiniteSupportDyadicFamily c hc g := by
      rw [happroxFinsupp m]
      funext s
      funext n
      exact continuousModelDyadicFamily_apply_finsupp c hc g s n
    have hvariation :
        FractionalPrimes.rVariationFun r
            (continuousModelDyadicFamily c hc (approx m)) =
          FractionalPrimes.rVariationFun r
            (continuousModelFiniteSupportDyadicFamily c hc g) := by
      funext n
      change FractionalPrimes.rVariation r
          (fun s => continuousModelDyadicFamily c hc (approx m) s n) =
        FractionalPrimes.rVariation r
          (fun s => continuousModelFiniteSupportDyadicFamily c hc g s n)
      congr 1
      funext s
      exact congrFun (congrFun hfamily s) n
    have hinputNorm :
        ENNReal.ofReal (MeasureTheory.lpNorm (g : ℤ → ℂ) P
          (Measure.count : Measure ℤ)) =
        MeasureTheory.eLpNorm (approx m : ℤ → ℂ) P
          (Measure.count : Measure ℤ) := by
      calc
        _ = MeasureTheory.eLpNorm
            (continuousModelFinsuppCountLp (Fact.out : 1 ≤ P) g : ℤ → ℂ)
            P (Measure.count : Measure ℤ) :=
          (MeasureTheory.ofReal_lpNorm
            (continuousModelFinsupp_memLp (Fact.out : 1 ≤ P) g)).trans
            (MeasureTheory.eLpNorm_congr_ae
              (Filter.Eventually.of_forall fun n =>
                continuousModelFinsuppCountLp_apply
                  (Fact.out : 1 ≤ P) g n)).symm
        _ = _ := by rw [← happroxFinsupp m]
    have hfinite :=
      continuousModelFiniteSupportDyadicVariation_eLpNorm_le_of_jsw
        (p := p) (r := r) hp hr c hc g (Cjsw : ℝ≥0∞) (hjsw g)
    rw [← hvariation] at hfinite
    rw [hinputNorm] at hfinite
    have hfiniteApprox :
        MeasureTheory.eLpNorm
            (FractionalPrimes.rVariationFun r
              (continuousModelDyadicFamily c hc (approx m))) P
            (Measure.count : Measure ℤ) ≤
          K * MeasureTheory.eLpNorm (approx m : ℤ → ℂ) P
            (Measure.count : Measure ℤ) := by
      simpa [K, Cχ, Cψ, mul_assoc, mul_left_comm, mul_comm] using hfinite
    exact hfiniteApprox.trans
      (mul_le_mul_of_nonneg_left (happroxNorm m) (by positivity))
  have hbound : ∀ m, ∫⁻ n : ℤ,
      (FractionalPrimes.rVariationFun r
        (continuousModelDyadicFamily c hc (approx m)) n) ^ p
        ∂(Measure.count : Measure ℤ) ≤
      (K * MeasureTheory.eLpNorm (f : ℤ → ℂ) P
        (Measure.count : Measure ℤ)) ^ p := by
    intro m
    have hVmeas : Measurable
        (FractionalPrimes.rVariationFun r
          (continuousModelDyadicFamily c hc (approx m))) :=
      FractionalPrimes.measurable_rVariationFun r _ (by
        intro s
        exact measurable_of_countable _)
    rw [← continuousModel_eLpNorm_ennreal_rpow p (by linarith : 0 < p)
      _ hVmeas]
    exact ENNReal.rpow_le_rpow (hfiniteBound m) (by linarith)
  have hfatou := continuousModelDyadicVariation_lintegral_le_of_tendsto
    (r := r) (q := p) (by linarith : 1 ≤ r) (by linarith : 1 ≤ p)
    c hc f approx hlim
    ((K * MeasureTheory.eLpNorm (f : ℤ → ℂ) P
      (Measure.count : Measure ℤ)) ^ p) hbound
  have hVmeas : Measurable
      (FractionalPrimes.rVariationFun r (continuousModelDyadicFamily c hc f)) :=
    FractionalPrimes.measurable_rVariationFun r _ (by
      intro s
      exact measurable_of_countable _)
  have hpow := continuousModel_eLpNorm_ennreal_rpow p
    (by linarith : 0 < p)
    (FractionalPrimes.rVariationFun r (continuousModelDyadicFamily c hc f))
    hVmeas
  apply (ENNReal.rpow_le_rpow_iff (by linarith : 0 < p)).mp
  calc
    MeasureTheory.eLpNorm
        (FractionalPrimes.rVariationFun r (continuousModelDyadicFamily c hc f))
        P (Measure.count : Measure ℤ) ^ p =
      ∫⁻ n : ℤ,
        (FractionalPrimes.rVariationFun r
          (continuousModelDyadicFamily c hc f) n) ^ p
        ∂(Measure.count : Measure ℤ) := hpow
    _ ≤ (K * MeasureTheory.eLpNorm (f : ℤ → ℂ) P
        (Measure.count : Measure ℤ)) ^ p := hfatou

end

end FractionalPrimes.Literature.Harmonic
