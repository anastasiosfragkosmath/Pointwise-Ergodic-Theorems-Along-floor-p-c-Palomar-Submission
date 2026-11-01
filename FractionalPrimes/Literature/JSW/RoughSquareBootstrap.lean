module

public import FractionalPrimes.Literature.JSW.LocalizedSquareDecay
public import FractionalPrimes.Literature.JSW.WeakTypeInterpolation
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Finite interpolation step for the rough square bootstrap

This module isolates the first finite-dimensional interpolation step in
`lj:rough-square`. The endpoint estimates can be supplied by the checked
localized-square `L²` estimate and its conditional diagonal-operator bound.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem roughSquare_complexLpMoment_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : ℝ}
    (hs : 0 < s) (f : X → ℂ) (hf : Measurable f) :
    Variation.complexLpMoment s μ f =
      eLpNorm f (ENNReal.ofReal s) μ ^ s := by
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hsTop : ENNReal.ofReal s ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal s).toReal = s := ENNReal.toReal_ofReal hs.le
  calc
    Variation.complexLpMoment s μ f = ∫⁻ x, ‖f x‖ₑ ^ s ∂μ := by
      unfold Variation.complexLpMoment
      apply lintegral_congr_ae
      filter_upwards [] with x
      simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm f (ENNReal.ofReal s) μ ^ s := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hsTop
        hf.aestronglyMeasurable, htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one]

theorem roughSquare_strongEndpoint_weak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s A : ℝ} (hs : 0 < s) (_hA : 0 ≤ A)
    (T : Variation.LayerCakeInput (volume : Measure ℝ) → ℝ → E)
    (hStrong : ∀ f : Variation.LayerCakeInput (volume : Measure ℝ),
      eLpNorm (fun x => ‖T f x‖) (ENNReal.ofReal s) volume ≤
        ENNReal.ofReal A * eLpNorm f.1 (ENNReal.ofReal s) volume)
    (f : Variation.LayerCakeInput (volume : Measure ℝ)) (t : ℝ) (ht : 0 < t) :
    volume {x | t < ‖T f x‖} ≤
      (ENNReal.ofReal A).rpow s * (ENNReal.ofReal t).rpow (-s) *
        Variation.complexLpMoment s volume f.1 := by
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hsTop : ENNReal.ofReal s ≠ ∞ := ENNReal.ofReal_ne_top
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  have hset : {x | t < ‖T f x‖} ⊆
      {x | ENNReal.ofReal t ≤ ‖(‖T f x‖ : ℝ)‖ₑ} := by
    intro x hx
    change t < ‖T f x‖ at hx
    change ENNReal.ofReal t ≤ ‖(‖T f x‖ : ℝ)‖ₑ
    rw [Real.enorm_of_nonneg (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hx.le
  have hcheb := MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm
    (μ := volume) (p := ENNReal.ofReal s) hs0 hsTop
    (f := fun x => (‖T f x‖ : ℝ)) ht0 (by simp)
  have hstrong := hStrong f
  have hpowStrong :
      eLpNorm (fun x => ‖T f x‖) (ENNReal.ofReal s) volume ^ s ≤
        (ENNReal.ofReal A * eLpNorm f.1 (ENNReal.ofReal s) volume) ^ s :=
    ENNReal.rpow_le_rpow hstrong (by linarith)
  have hmoment := roughSquare_complexLpMoment_eq_eLpNorm_rpow
    volume hs f.1 f.2.1
  have htoReal : (ENNReal.ofReal s).toReal = s := ENNReal.toReal_ofReal hs.le
  calc
    volume {x | t < ‖T f x‖} ≤
        volume {x | ENNReal.ofReal t ≤ ‖(‖T f x‖ : ℝ)‖ₑ} := measure_mono hset
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ s *
        eLpNorm (fun x => ‖T f x‖) (ENNReal.ofReal s) volume ^ s := by
          simpa [htoReal, Real.enorm_of_nonneg (norm_nonneg _)] using hcheb
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ s *
        (ENNReal.ofReal A * eLpNorm f.1 (ENNReal.ofReal s) volume) ^ s :=
          mul_le_mul_of_nonneg_left hpowStrong (by positivity)
    _ = (ENNReal.ofReal A).rpow s * (ENNReal.ofReal t).rpow (-s) *
        Variation.complexLpMoment s volume f.1 := by
          rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal A)
            (eLpNorm f.1 (ENNReal.ofReal s) volume) (by linarith), hmoment,
            ENNReal.inv_rpow, ← ENNReal.rpow_neg]
          ac_rfl

/-- Finite-dimensional strong endpoint estimates interpolate with the exact
constant `I(s₀,p,s₁)` from `lj:interpolation`. This is the finite step used
to interpolate each fixed `(j,F)` localized-square operator. -/
theorem finiteVector_strongEndpoint_interpolation
    {ι : Type*} [Fintype ι]
    {s₀ p s₁ A₀ A₁ : ℝ}
    (T : (ℝ → ℂ) →ₗ[ℂ] ℝ → EuclideanSpace ℂ ι)
    (hmeas : ∀ f : Variation.LayerCakeInput (volume : Measure ℝ),
      Measurable (fun x => ‖T f.1 x‖))
    (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hStrong₀ : ∀ f : Variation.LayerCakeInput (volume : Measure ℝ),
      eLpNorm (fun x => ‖T f.1 x‖) (ENNReal.ofReal s₀) volume ≤
        ENNReal.ofReal A₀ * eLpNorm f.1 (ENNReal.ofReal s₀) volume)
    (hStrong₁ : ∀ f : Variation.LayerCakeInput (volume : Measure ℝ),
      eLpNorm (fun x => ‖T f.1 x‖) (ENNReal.ofReal s₁) volume ≤
        ENNReal.ofReal A₁ * eLpNorm f.1 (ENNReal.ofReal s₁) volume)
    (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (fun x => ‖T f.1 x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal
        (weakTypeInterpolationConstant s₀ p s₁ *
          A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
          A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) *
        eLpNorm f.1 (ENNReal.ofReal p) volume := by
  have hweak₀ : ∀ (f : Variation.LayerCakeInput (volume : Measure ℝ))
      (t : ℝ), 0 < t →
      volume {x | t < ‖T f.1 x‖} ≤
        (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
          Variation.complexLpMoment s₀ volume f.1 := by
    intro f t ht
    exact roughSquare_strongEndpoint_weak (by linarith) hA₀ (fun g => T g.1) hStrong₀ f t ht
  have hweak₁ : ∀ (f : Variation.LayerCakeInput (volume : Measure ℝ))
      (t : ℝ), 0 < t →
      volume {x | t < ‖T f.1 x‖} ≤
        (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
          Variation.complexLpMoment s₁ volume f.1 := by
    intro f t ht
    exact roughSquare_strongEndpoint_weak (by linarith) hA₁ (fun g => T g.1) hStrong₁ f t ht
  exact weakTypeInterpolation_finiteVector T hmeas hweak₀ hweak₁
    hs₀ h₀ h₁ hA₀ hA₁ f

/-- The finite-exponent cancellation convolution in `LocalizedSquareDecay`
has the ordinary raw complex-measure convolution as its representative. This
lets the `L²` and conditional `Lᵘ` constructions be compared on a common
input representative. -/
theorem localizedSquareNuLpConvolution_ae_eq_complexMeasureConvolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {q b : ℝ} (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hq : 1 < q) (k : ℤ)
    (G : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    (localizedSquareNuLpConvolution hSupp q b hq k G : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution
        (initialSquareDilateComplexMeasure
          (initialSquareNuComplexMeasure σ) (b ^ k))
        (fun x : ℝ => (Lp.aestronglyMeasurable G).mk G x)
        ((Lp.aestronglyMeasurable G).stronglyMeasurable_mk.aestronglyMeasurable) := by
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμ : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure μ.variation := hμ
  let μk : ComplexMeasure ℝ := initialSquareDilateComplexMeasure μ (b ^ k)
  have hμk : IsFiniteMeasure μk.variation := by
    dsimp [μk, μ, initialSquareDilateComplexMeasure]
    infer_instance
  letI : IsFiniteMeasure μk.variation := hμk
  let hG : AEStronglyMeasurable (fun x : ℝ => (G : ℝ → ℂ) x) volume :=
    Lp.aestronglyMeasurable G
  let f : ℝ → ℂ := hG.mk (fun x => (G : ℝ → ℂ) x)
  have hfStrong : StronglyMeasurable f := by
    dsimp [f]
    exact hG.stronglyMeasurable_mk
  have hfMem : MemLp f (ENNReal.ofReal q) volume := by
    apply (Lp.memLp G).congr_norm hfStrong.aestronglyMeasurable
    filter_upwards [hG.ae_eq_mk] with x hx
    simp [f, hx]
  have hF : (fun x : ℝ => (G : ℝ → ℂ) x) =ᵐ[volume] f := by
    exact hG.ae_eq_mk
  have hraw := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp
    hq μk G f hfStrong.measurable hfMem hF
  simpa [localizedSquareNuLpConvolution, μk, μ] using hraw

/-- Raw pointwise composition of one Schwartz-kernel convolution with one
finite complex-measure convolution. The integrals are deliberately left in
raw form so linearity holds pointwise on the bounded input class. -/
noncomputable def localizedSquareRawNuAfterKernel
    (K : ℝ → ℂ) (μ : ComplexMeasure ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ᵛ z, (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ))
    ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- The inner kernel integral is integrable for bounded measurable inputs. -/
theorem localizedSquareRawNuAfterKernel_inner_integrable
    (K f : ℝ → ℂ) (hK : Integrable K (volume : Measure ℝ))
    (hf : Measurable f) (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∀ x z, Integrable
      (fun y : ℝ => K y * f (x - z - y)) (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := hfbdd
  intro x z
  have hshift : Measurable (fun y : ℝ => f (x - z - y)) :=
    hf.comp (measurable_const.sub measurable_id)
  have hbounded : ∀ᵐ y ∂(volume : Measure ℝ),
      ‖f (x - z - y)‖ ≤ max 0 C := by
    filter_upwards [] with y
    exact (hC _).trans (le_max_right 0 C)
  have hmul := hK.bdd_mul hshift.aestronglyMeasurable (c := max 0 C) hbounded
  simpa only [mul_comm] using hmul

/-- The outer finite-measure integral is also integrable for a bounded
measurable input. -/
theorem localizedSquareRawNuAfterKernel_outer_integrable
    (K : ℝ → ℂ) (μ : ComplexMeasure ℝ) (f : ℝ → ℂ)
    (hK : Integrable K (volume : Measure ℝ)) (hKm : Measurable K)
    (hμ : IsFiniteMeasure μ.variation) (hf : Measurable f)
    (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∀ x, μ.Integrable
      (fun z : ℝ => ∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ)) := by
  letI : IsFiniteMeasure μ.variation := hμ
  obtain ⟨C, hC⟩ := hfbdd
  intro x
  have hinner := localizedSquareRawNuAfterKernel_inner_integrable K f hK hf ⟨C, hC⟩ x
  have hKnorm : Integrable (fun y : ℝ => ‖K y‖) (volume : Measure ℝ) := hK.norm
  have hmajorIntegrable : Integrable
      (fun y : ℝ => max 0 C * ‖K y‖) (volume : Measure ℝ) := by
    simpa only [mul_comm] using hKnorm.const_mul (max 0 C)
  have hjoint : Measurable (fun q : ℝ × ℝ => K q.2 * f (x - q.1 - q.2)) := by
    exact (hKm.comp measurable_snd).mul
      (hf.comp (measurable_const.sub measurable_fst |>.sub measurable_snd))
  have houter : StronglyMeasurable
      (fun z : ℝ => ∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ)) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  have hpoint (z : ℝ) :
      ‖∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ)‖ ≤
        max 0 C * ∫ y, ‖K y‖ ∂(volume : Measure ℝ) := by
    calc
      _ ≤ ∫ y, ‖K y * f (x - z - y)‖ ∂(volume : Measure ℝ) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y, max 0 C * ‖K y‖ ∂(volume : Measure ℝ) :=
        integral_mono (hinner z).norm hmajorIntegrable (by
          intro y
          calc
            ‖K y * f (x - z - y)‖ = ‖K y‖ * ‖f (x - z - y)‖ := norm_mul _ _
            _ ≤ ‖K y‖ * max 0 C := mul_le_mul_of_nonneg_left
              ((hC (x - z - y)).trans (le_max_right 0 C)) (norm_nonneg _)
            _ = max 0 C * ‖K y‖ := by ring)
      _ = max 0 C * ∫ y, ‖K y‖ ∂(volume : Measure ℝ) := by
        rw [integral_const_mul]
  change Integrable _ μ.variation
  exact Integrable.of_bound houter.aestronglyMeasurable
    (max 0 C * ∫ y, ‖K y‖ ∂(volume : Measure ℝ)) (ae_of_all _ hpoint)

/-- The raw finite-measure/kernel composition is strongly measurable in its
output variable. -/
theorem localizedSquareRawNuAfterKernel_stronglyMeasurable
    (K : ℝ → ℂ) (μ : ComplexMeasure ℝ) (f : ℝ → ℂ)
    (hKm : Measurable K) (hμ : IsFiniteMeasure μ.variation)
    (hf : Measurable f) :
    StronglyMeasurable (fun x : ℝ => localizedSquareRawNuAfterKernel K μ f x) := by
  letI : IsFiniteMeasure μ.variation := hμ
  letI : SFinite μ.variation := inferInstance
  have htriple : Measurable
      (fun q : (ℝ × ℝ) × ℝ => K q.2 * f (q.1.1 - q.1.2 - q.2)) := by
    exact (hKm.comp measurable_snd).mul
      (hf.comp (((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst)).sub measurable_snd))
  have hinner : StronglyMeasurable (fun q : ℝ × ℝ =>
      ∫ y, K y * f (q.1 - q.2 - y) ∂(volume : Measure ℝ)) := by
    exact htriple.stronglyMeasurable.integral_prod_right'
  change StronglyMeasurable (fun x : ℝ =>
    ∫ᵛ z, (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ))
      ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
  exact hinner.integral_vectorMeasure_prod_right'

/-- Pointwise additivity of the raw finite-scale convolution composition,
assuming the two component integrals are integrable. -/
theorem localizedSquareRawNuAfterKernel_add
    (K : ℝ → ℂ) (μ : ComplexMeasure ℝ) (f g : ℝ → ℂ) (x : ℝ)
    (hf : ∀ x z, Integrable
      (fun y : ℝ => K y * f (x - z - y)) (volume : Measure ℝ))
    (hg : ∀ x z, Integrable
      (fun y : ℝ => K y * g (x - z - y)) (volume : Measure ℝ))
    (hfOuter : ∀ x, μ.Integrable
      (fun z : ℝ => ∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ)))
    (hgOuter : ∀ x, μ.Integrable
      (fun z : ℝ => ∫ y, K y * g (x - z - y) ∂(volume : Measure ℝ))) :
    localizedSquareRawNuAfterKernel K μ (f + g) x =
      localizedSquareRawNuAfterKernel K μ f x +
        localizedSquareRawNuAfterKernel K μ g x := by
  unfold localizedSquareRawNuAfterKernel
  have hinner (z : ℝ) :
      (∫ y, K y * (f + g) (x - z - y) ∂(volume : Measure ℝ)) =
        (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ)) +
          (∫ y, K y * g (x - z - y) ∂(volume : Measure ℝ)) := by
    calc
      _ = ∫ y, K y * f (x - z - y) + K y * g (x - z - y)
          ∂(volume : Measure ℝ) := by
            apply integral_congr_ae
            filter_upwards [] with y
            simp [Pi.add_apply, mul_add]
      _ = _ := integral_add (hf x z) (hg x z)
  calc
    _ = ∫ᵛ z, (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ)) +
          (∫ y, K y * g (x - z - y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
            apply VectorMeasure.integral_congr_ae
            exact ae_of_all μ.variation hinner
    _ = _ := VectorMeasure.integral_add (hfOuter x) (hgOuter x)

/-- Positive homogeneity of the raw pointwise convolution composition. The
statement is for real scalars, as required by the layer-cake interpolation
operator. -/
theorem localizedSquareRawNuAfterKernel_smul_real
    (K : ℝ → ℂ) (μ : ComplexMeasure ℝ) (f : ℝ → ℂ) (x c : ℝ) :
    localizedSquareRawNuAfterKernel K μ (fun y => (c : ℂ) * f y) x =
      (c : ℂ) * localizedSquareRawNuAfterKernel K μ f x := by
  unfold localizedSquareRawNuAfterKernel
  have hinner (z : ℝ) :
      (∫ y, K y * ((c : ℂ) * f (x - z - y)) ∂(volume : Measure ℝ)) =
        (c : ℂ) * ∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ) := by
    calc
      _ = ∫ y, (c : ℂ) * (K y * f (x - z - y)) ∂(volume : Measure ℝ) := by
            apply integral_congr_ae
            filter_upwards [] with y
            ring
      _ = _ := integral_const_mul _ _
  calc
    _ = ∫ᵛ z, (c : ℝ) •
          (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
            apply VectorMeasure.integral_congr_ae
            filter_upwards [] with z
            simpa only [Complex.real_smul] using hinner z
    _ = (c : ℝ) •
          ∫ᵛ z, (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ))
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] :=
          VectorMeasure.integral_smul
            (f := fun z : ℝ => ∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ))
            (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) c
    _ = (c : ℂ) *
          ∫ᵛ z, (∫ y, K y * f (x - z - y) ∂(volume : Measure ℝ))
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
          simp [Complex.real_smul]

/-- On a common `L² ∩ Lᵖ` input, the `L²` and finite-`Lᵖ` realizations of
one localized cancellation output agree almost everywhere. -/
theorem localizedSquareNuProjectionConvolution_ae_eq_lp_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (j k : ℤ) (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 volume)
    (hfp : MemLp f (ENNReal.ofReal p) volume) :
    (localizedSquareNuProjectionConvolution hSupp hσ hb j k
      (hf₂.toLp f) : ℝ → ℂ) =ᵐ[volume]
      (localizedSquareNuLpConvolution hSupp p b hp k
        (littlewoodPaleyProjectionLp hb hp (k + j)
          (hfp.toLp f)) : ℝ → ℂ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let G₂ : Lp ℂ 2 (volume : Measure ℝ) := hf₂.toLp f
  let Gp : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    hfp.toLp f
  have hGp_f : (fun x : ℝ => (Gp : ℝ → ℂ) x) =ᵐ[volume] f :=
    hfp.coeFn_toLp
  have hG₂_f : (fun x : ℝ => (G₂ : ℝ → ℂ) x) =ᵐ[volume] f :=
    hf₂.coeFn_toLp
  have hGp₂ : MemLp (fun x : ℝ => (Gp : ℝ → ℂ) x) 2 volume :=
    (memLp_congr_ae hGp_f).mpr hf₂
  have htoLp : hGp₂.toLp (fun x : ℝ => (Gp : ℝ → ℂ) x) = G₂ := by
    apply Lp.ext
    filter_upwards [hGp₂.coeFn_toLp, hGp_f, hG₂_f] with x hto hpf h₂f
    exact hto.trans (hpf.trans h₂f.symm)
  let Pp : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    littlewoodPaleyProjectionLp hb hp (k + j) Gp
  let P₂ : Lp ℂ 2 (volume : Measure ℝ) :=
    localizedSquareProjectionL2 hb (k + j) G₂
  have hprojection : (Pp : ℝ → ℂ) =ᵐ[volume] (P₂ : ℝ → ℂ) := by
    have h := littlewoodPaleyProjectionLp_ae_eq_localizedSquareProjectionL2
      hb hp (k + j) Gp hGp₂
    simpa [Pp, P₂, G₂, htoLp] using h
  let hP : AEStronglyMeasurable (fun x : ℝ => (Pp : ℝ → ℂ) x) volume :=
    Lp.aestronglyMeasurable Pp
  let fp : ℝ → ℂ := hP.mk (fun x => (Pp : ℝ → ℂ) x)
  let hP' : AEStronglyMeasurable fp volume :=
    hP.stronglyMeasurable_mk.aestronglyMeasurable
  let rp : ℝ → ℂ := hP'.mk fp
  let h₂ : AEStronglyMeasurable (fun x : ℝ => (P₂ : ℝ → ℂ) x) volume :=
    Lp.aestronglyMeasurable P₂
  let r₂ : ℝ → ℂ := h₂.mk (fun x => (P₂ : ℝ → ℂ) x)
  have hrpStrong : StronglyMeasurable rp := by
    dsimp [rp]
    exact hP'.stronglyMeasurable_mk
  have hr₂Strong : StronglyMeasurable r₂ := by
    dsimp [r₂]
    exact h₂.stronglyMeasurable_mk
  have hrp : rp =ᵐ[volume] r₂ := by
    filter_upwards [hP'.ae_eq_mk, hP.ae_eq_mk, hprojection, h₂.ae_eq_mk]
      with x hrp' hfp hproj h₂'
    exact hrp'.symm.trans (hfp.symm.trans (hproj.trans h₂'))
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμ : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure μ.variation := hμ
  let μk : ComplexMeasure ℝ := initialSquareDilateComplexMeasure μ (b ^ k)
  have hμk : IsFiniteMeasure μk.variation := by
    dsimp [μk, μ, initialSquareDilateComplexMeasure]
    infer_instance
  letI : IsFiniteMeasure μk.variation := hμk
  have hraw :
      (fun x : ℝ => complexMeasureConvolution μk fp hP' x) =ᵐ[volume]
        (fun x : ℝ => complexMeasureConvolution μk
          (fun x : ℝ => (P₂ : ℝ → ℂ) x) h₂ x) := by
    change (fun x : ℝ => ∫ᵛ y, rp (x - y)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μk]) =ᵐ[volume]
      (fun x : ℝ => ∫ᵛ y, r₂ (x - y)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μk])
    exact rawComplexMeasureConvolution_ae_congr μk rp r₂ hrpStrong hr₂Strong hrp
  have hLp := localizedSquareNuLpConvolution_ae_eq_complexMeasureConvolution
    (b := b) hSupp hp k Pp
  have hL₂ := initialSquareNuConvolution_ae_eq_complexMeasureConvolution
    hSupp hσ b k P₂
  have hLp' :
      (localizedSquareNuLpConvolution hSupp p b hp k Pp : ℝ → ℂ) =ᵐ[volume]
        complexMeasureConvolution μk fp hP' := by
    exact hLp
  have hL₂' :
      (initialSquareNuConvolution hSupp hσ b k P₂ : ℝ → ℂ) =ᵐ[volume]
        complexMeasureConvolution μk (fun x : ℝ => (P₂ : ℝ → ℂ) x) h₂ := by
    simpa [μk, μ, h₂] using hL₂
  have hOutput := hL₂'.trans (hraw.symm.trans hLp'.symm)
  simpa [localizedSquareNuProjectionConvolution, P₂, G₂, Pp, Gp] using hOutput

/-- Finite-vector form of the common `L² ∩ Lᵖ` representative identity. -/
theorem localizedSquareFiniteNuProjectionConvolution_ae_eq_lp_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (j : ℤ) (F : Finset ℤ) (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 volume)
    (hfp : MemLp f (ENNReal.ofReal p) volume) :
    (fun x : ℝ => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
      (localizedSquareNuProjectionConvolution hSupp hσ hb j k.1
        (hf₂.toLp f) : ℝ → ℂ) x)) =ᵐ[volume]
    (fun x : ℝ => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
      (localizedSquareNuLpConvolution hSupp p b hp k.1
        (littlewoodPaleyProjectionLp hb hp (k.1 + j)
          (hfp.toLp f)) : ℝ → ℂ) x)) := by
  have hcoord : ∀ k : {k : ℤ // k ∈ F},
      (localizedSquareNuProjectionConvolution hSupp hσ hb j k.1
        (hf₂.toLp f) : ℝ → ℂ) =ᵐ[volume]
      (localizedSquareNuLpConvolution hSupp p b hp k.1
        (littlewoodPaleyProjectionLp hb hp (k.1 + j)
          (hfp.toLp f)) : ℝ → ℂ) := by
    intro k
    exact localizedSquareNuProjectionConvolution_ae_eq_lp_of_memLp
      hSupp hσ hb hp j k.1 f hf₂ hfp
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext k
  exact hx k

/-- Transfer almost-everywhere equality of two endpoint realizations from a
common dense sequence to their limiting inputs. Convergence in each endpoint
Lp norm gives convergence in measure; uniqueness of that limit identifies
the output representatives. -/
theorem ae_eq_of_common_sequence_lp_continuousLinearMaps
    {p₂ p : ℝ≥0∞} [Fact (1 ≤ p₂)] [Fact (1 ≤ p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T₂ : Lp ℂ p₂ (volume : Measure ℝ) →L[ℂ]
      Lp E p₂ (volume : Measure ℝ))
    (Tp : Lp ℂ p (volume : Measure ℝ) →L[ℂ]
      Lp E p (volume : Measure ℝ))
    (g₂ : ℕ → Lp ℂ p₂ (volume : Measure ℝ))
    (gp : ℕ → Lp ℂ p (volume : Measure ℝ))
    (F₂ : Lp ℂ p₂ (volume : Measure ℝ))
    (Fp : Lp ℂ p (volume : Measure ℝ))
    (h₂ : Tendsto g₂ atTop (𝓝 F₂)) (hp : Tendsto gp atTop (𝓝 Fp))
    (hcommon : ∀ n, (T₂ (g₂ n) : ℝ → E) =ᵐ[volume] (Tp (gp n) : ℝ → E)) :
    (T₂ F₂ : ℝ → E) =ᵐ[volume] (Tp Fp : ℝ → E) := by
  have h₂measure : TendstoInMeasure volume
      (fun n => (T₂ (g₂ n) : ℝ → E)) atTop (T₂ F₂ : ℝ → E) := by
    exact tendstoInMeasure_of_tendsto_Lp
      ((T₂.continuous.tendsto F₂).comp h₂)
  have hpmeasure : TendstoInMeasure volume
      (fun n => (Tp (gp n) : ℝ → E)) atTop (Tp Fp : ℝ → E) := by
    exact tendstoInMeasure_of_tendsto_Lp
      ((Tp.continuous.tendsto Fp).comp hp)
  exact tendstoInMeasure_ae_unique (h₂measure.congr_left hcommon) hpmeasure

#print axioms finiteVector_strongEndpoint_interpolation
#print axioms localizedSquareRawNuAfterKernel_inner_integrable
#print axioms localizedSquareRawNuAfterKernel_outer_integrable
#print axioms localizedSquareRawNuAfterKernel_stronglyMeasurable
#print axioms localizedSquareRawNuAfterKernel_add
#print axioms localizedSquareRawNuAfterKernel_smul_real
#print axioms localizedSquareNuLpConvolution_ae_eq_complexMeasureConvolution
#print axioms localizedSquareNuProjectionConvolution_ae_eq_lp_of_memLp
#print axioms localizedSquareFiniteNuProjectionConvolution_ae_eq_lp_of_memLp
#print axioms ae_eq_of_common_sequence_lp_continuousLinearMaps

end
end FractionalPrimes.Literature.JSW
