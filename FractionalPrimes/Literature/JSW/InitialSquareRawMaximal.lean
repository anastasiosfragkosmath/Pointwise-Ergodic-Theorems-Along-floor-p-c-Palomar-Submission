module

public import FractionalPrimes.Literature.JSW.FiniteDenseMaximalInterpolation

/-!
# Raw-input completion for the initial-square maximal bounds

This module transfers the checked quotient-space positive maximal operator
to its source-average representative for arbitrary finite-exponent inputs.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The full positive geometric-scale maximal operator on `L^q` agrees almost
everywhere with the raw source supremum for every `L^q` representative when
`q>1`. The proof takes the common exceptional set across the countable scale
family using the arbitrary-input per-scale convolution bridge. -/
theorem initialSquareSigmaPositiveMaximalLp_ae_eq_raw_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b q : ℝ}
    (hb : 1 < b) (hq : 1 < q)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) volume)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f) :
    (@initialSquareSigmaPositiveMaximalLp q
      (⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩ :
        Fact (1 ≤ ENNReal.ofReal q)) σ ‹IsProbabilityMeasure σ› b F) =ᵐ[volume]
      initialSquareSigmaRawPositiveMaximal σ b f := by
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let scale : ℤ → Lp ℝ (ENNReal.ofReal q) volume := fun k =>
    initialSquareSigmaPositiveConvolutionScaleLp q σ b k F
  have hterm (k : ℤ) :
      (fun x : ℝ => ENNReal.ofReal (scale k x)) =ᵐ[volume]
        fun x => ENNReal.ofReal
          (initialSquareSigmaRawPositiveScale σ b k f x) := by
    letI : IsFiniteMeasure
        (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    have hscale := initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale_of_memLp
      (q := q) (by linarith : 1 < q) (σ := σ) (b := b) hb k f hf hfm F hF
    have hscale' : (scale k : ℝ → ℝ) =ᵐ[volume]
        initialSquareSigmaRawPositiveScale σ b k f := by
      simpa [scale, initialSquareSigmaPositiveConvolutionScaleLp] using hscale
    filter_upwards [hscale'] with x hx
    exact congrArg ENNReal.ofReal hx
  have htermAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ,
      ENNReal.ofReal (scale k x) = ENNReal.ofReal
        (initialSquareSigmaRawPositiveScale σ b k f x) :=
    ae_all_iff.mpr hterm
  have hsup :
      (fun x : ℝ => ⨆ k : ℤ, ENNReal.ofReal (scale k x)) =ᵐ[volume]
        fun x => ⨆ k : ℤ, ENNReal.ofReal
          (initialSquareSigmaRawPositiveScale σ b k f x) := by
    filter_upwards [htermAll] with x hx
    exact iSup_congr hx
  filter_upwards [hsup] with x hx
  change (⨆ k : ℤ, ENNReal.ofReal (scale k x)).toReal = _
  exact congrArg ENNReal.toReal hx

#print axioms initialSquareSigmaPositiveMaximalLp_ae_eq_raw_of_memLp

/-- The exact `q>2` source maximal bound for both the probability measure and
its reflection. The quotient-space interpolation theorem is transferred to
the raw source averages by the countable-scale representative bridge above. -/
theorem initialSquareSigmaRawPositiveMaximalLp_bound_both_reflections
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hq : 2 < q)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) volume) :
    eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm f (ENNReal.ofReal q) volume ∧
    eLpNorm (initialSquareSigmaRawPositiveMaximal
        (Measure.map Neg.neg σ) b f)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm f (ENNReal.ofReal q) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let P : ℝ≥0∞ := ENNReal.ofReal q
  let F : Lp ℂ P volume := hfm.toLp f
  have hF : (F : ℝ → ℂ) =ᵐ[volume] f := MemLp.coeFn_toLp hfm
  have hraw : initialSquareSigmaPositiveMaximalLp q σ b F =ᵐ[volume]
      initialSquareSigmaRawPositiveMaximal σ b f :=
    initialSquareSigmaPositiveMaximalLp_ae_eq_raw_of_memLp
      hb (by linarith : 1 < q) F f hf hfm hF
  haveI : IsProbabilityMeasure (Measure.map Neg.neg σ) := inferInstance
  have hrawRef : initialSquareSigmaPositiveMaximalLp q
      (Measure.map Neg.neg σ) b F =ᵐ[volume]
        initialSquareSigmaRawPositiveMaximal (Measure.map Neg.neg σ) b f :=
    initialSquareSigmaPositiveMaximalLp_ae_eq_raw_of_memLp
      hb (by linarith : 1 < q) F f hf hfm hF
  have hLp := initialSquareSigmaPositiveMaximalLp_bound_both_reflections
    hSupp hdecay hb hβ hq F
  rcases hLp with ⟨hLp, hLpRef⟩
  have hmain :
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f) P volume ≤
        ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b)) *
          eLpNorm f P volume := by
    calc
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f) P volume =
          eLpNorm (initialSquareSigmaPositiveMaximalLp q σ b F) P volume :=
        eLpNorm_congr_ae hraw.symm
      _ ≤ ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
            (initialSquareSigmaPositiveMaximalB2 β D b)) *
          eLpNorm (F : ℝ → ℂ) P volume := hLp
      _ = _ := by rw [eLpNorm_congr_ae hF]
  have href :
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) b f) P volume ≤
        ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b)) *
          eLpNorm f P volume := by
    calc
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) b f) P volume =
          eLpNorm (initialSquareSigmaPositiveMaximalLp q
            (Measure.map Neg.neg σ) b F) P volume :=
        eLpNorm_congr_ae hrawRef.symm
      _ ≤ ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
            (initialSquareSigmaPositiveMaximalB2 β D b)) *
          eLpNorm (F : ℝ → ℂ) P volume := hLpRef
      _ = _ := by rw [eLpNorm_congr_ae hF]
  exact ⟨by simpa [P] using hmain, by simpa [P] using href⟩

#print axioms initialSquareSigmaRawPositiveMaximalLp_bound_both_reflections

/-- Almost-everywhere congruent inputs have the same full raw positive
maximal function. The countable intersection is taken over all integer
scales. -/
theorem initialSquareSigmaRawPositiveMaximal_ae_congr
    {σ : Measure ℝ} [SFinite σ] (b : ℝ)
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[volume] g) :
    initialSquareSigmaRawPositiveMaximal σ b f =ᵐ[volume]
      initialSquareSigmaRawPositiveMaximal σ b g := by
  have hterm (k : ℤ) :
      (fun x : ℝ => ENNReal.ofReal
        (initialSquareSigmaRawPositiveScale σ b k f x)) =ᵐ[volume]
      fun x => ENNReal.ofReal
        (initialSquareSigmaRawPositiveScale σ b k g x) := by
    have hscale := initialSquareSigmaRawPositiveScale_ae_congr
      (σ := σ) (b ^ k) hf hg hfg
    filter_upwards [hscale] with x hx
    exact congrArg ENNReal.ofReal hx
  have htermAll : ∀ᵐ x ∂volume, ∀ k : ℤ,
      ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f x) =
        ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g x) :=
    ae_all_iff.mpr hterm
  have hsup :
      (fun x : ℝ => ⨆ k : ℤ, ENNReal.ofReal
        (initialSquareSigmaRawPositiveScale σ b k f x)) =ᵐ[volume]
      fun x => ⨆ k : ℤ, ENNReal.ofReal
        (initialSquareSigmaRawPositiveScale σ b k g x) := by
    filter_upwards [htermAll] with x hx
    exact iSup_congr hx
  filter_upwards [hsup] with x hx
  exact congrArg ENNReal.toReal hx

/-- The source `L²` positive maximal operator, expressed by integrating the
chosen `Lp` representative at the original measure scale, is the raw source
maximal function almost everywhere. -/
theorem initialSquareSigmaPositiveConvolutionMaximalReal_ae_eq_raw
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    initialSquareSigmaPositiveConvolutionMaximalReal σ b F =ᵐ[volume]
      initialSquareSigmaRawPositiveMaximal σ b (fun y => F y) := by
  filter_upwards [] with x
  change (⨆ k : ℤ, ENNReal.ofReal
      (∫ y, ‖F (x-y)‖ ∂Measure.map (fun y : ℝ => b ^ k * y) σ)).toReal = _
  change _ = (⨆ k : ℤ, ENNReal.ofReal
      (initialSquareSigmaRawPositiveScale σ b k (fun y => F y) x)).toReal
  congr 1
  apply iSup_congr
  intro k
  congr 1
  exact integral_map_of_stronglyMeasurable (by fun_prop)
    (((Lp.stronglyMeasurable F).comp_measurable (by fun_prop)).norm)

/-- The exact `q=2` source maximal bound for the probability measure and its
reflection, for arbitrary measurable `L²` inputs. -/
theorem initialSquareSigmaRawPositiveMaximalL2_bound_both_reflections
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal 2) volume) :
    eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f)
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
        eLpNorm f (ENNReal.ofReal 2) volume ∧
    eLpNorm (initialSquareSigmaRawPositiveMaximal
        (Measure.map Neg.neg σ) b f)
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
        eLpNorm f (ENNReal.ofReal 2) volume := by
  have hsplit := measureSplitting σ hSupp β hβ D hdecay
  have hfm₂ : MemLp f (2 : ℝ≥0∞) volume := by
    simpa [ENNReal.ofReal_ofNat] using hfm
  let F : Lp ℂ 2 volume := hfm₂.toLp f
  have hF : (F : ℝ → ℂ) =ᵐ[volume] f := MemLp.coeFn_toLp hfm₂
  have hrawF := initialSquareSigmaRawPositiveMaximal_ae_congr
    (σ := σ) b (Lp.stronglyMeasurable F).measurable hf hF
  have hrawBase := initialSquareSigmaPositiveConvolutionMaximalReal_ae_eq_raw
    (σ := σ) (b := b) F
  have hmainEq := hrawBase.trans hrawF
  have hmain := initialSquare_sigma_positive_convolution_maximal_L2_bound
    hSupp hsplit.1 hb hβ F
  have hmain' :
      eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal σ b F)
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
          eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal 2) volume := by
    simpa [initialSquareSigmaPositiveMaximalB2] using hmain
  have hmainNorm : eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal 2) volume =
      eLpNorm f (ENNReal.ofReal 2) volume := eLpNorm_congr_ae hF
  haveI : IsProbabilityMeasure (Measure.map Neg.neg σ) := inferInstance
  have hrawFRef := initialSquareSigmaRawPositiveMaximal_ae_congr
    (σ := Measure.map Neg.neg σ) b
    (Lp.stronglyMeasurable F).measurable hf hF
  have hrawBaseRef := initialSquareSigmaPositiveConvolutionMaximalReal_ae_eq_raw
    (σ := Measure.map Neg.neg σ) (b := b) F
  have hrefEq := hrawBaseRef.trans hrawFRef
  have href := initialSquare_sigma_reflected_positive_convolution_maximal_L2_bound
    hSupp hdecay hb hβ F
  have href' :
      eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal
          (Measure.map Neg.neg σ) b F) (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
          eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal 2) volume := by
    simpa [initialSquareSigmaPositiveMaximalB2] using href
  constructor
  · calc
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f)
          (ENNReal.ofReal 2) volume =
        eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal σ b F)
          (ENNReal.ofReal 2) volume := eLpNorm_congr_ae hmainEq.symm
      _ ≤ _ := hmain'
      _ = _ := by rw [hmainNorm]
  · calc
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) b f) (ENNReal.ofReal 2) volume =
        eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal
          (Measure.map Neg.neg σ) b F) (ENNReal.ofReal 2) volume :=
            eLpNorm_congr_ae hrefEq.symm
      _ ≤ _ := href'
      _ = _ := by rw [hmainNorm]

#print axioms initialSquareSigmaRawPositiveMaximalL2_bound_both_reflections

/-- The `q=2` source bound stated directly for the `L²` equivalence-class
input, using its strongly measurable representative. -/
theorem initialSquareSigmaRawPositiveMaximalL2_bound_both_reflections_of_Lp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (initialSquareSigmaRawPositiveMaximal σ b (fun y => F y))
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
        eLpNorm (fun y => F y) (ENNReal.ofReal 2) volume ∧
    eLpNorm (initialSquareSigmaRawPositiveMaximal
        (Measure.map Neg.neg σ) b (fun y => F y))
        (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
        eLpNorm (fun y => F y) (ENNReal.ofReal 2) volume := by
  have hfm : MemLp (fun y : ℝ => F y) (ENNReal.ofReal 2) volume := by
    simpa [ENNReal.ofReal_ofNat] using (Lp.memLp F)
  exact initialSquareSigmaRawPositiveMaximalL2_bound_both_reflections
    hSupp hdecay hb hβ (fun y => F y)
    (Lp.stronglyMeasurable F).measurable hfm

/-- The `q>2` source bound stated directly for the `L^q` equivalence-class
input, using its strongly measurable representative. -/
theorem initialSquareSigmaRawPositiveMaximalLp_bound_both_reflections_of_Lp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hq : 2 < q)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) :
    eLpNorm (initialSquareSigmaRawPositiveMaximal σ b (fun y => F y))
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (fun y => F y) (ENNReal.ofReal q) volume ∧
    eLpNorm (initialSquareSigmaRawPositiveMaximal
        (Measure.map Neg.neg σ) b (fun y => F y))
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (fun y => F y) (ENNReal.ofReal q) volume := by
  exact initialSquareSigmaRawPositiveMaximalLp_bound_both_reflections
    hSupp hdecay hb hβ hq (fun y => F y)
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)

/-- The full smooth-part convolution maximal function at the geometric
scales. Its terms are the complex-measure representatives of
`ψ_{b^k} * |F|`. -/
def initialSquarePsiConvolutionMaximal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ENNReal.ofReal ‖complexMeasureConvolution
    (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ)
      (b ^ k))
    (fun y : ℝ => F y) (Lp.aestronglyMeasurable F) x‖

/-- The source maximal comparison for the smooth density, with its exact
`4 * ‖φ‖∞` factor. -/
theorem initialSquarePsiConvolutionMaximal_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hb : 1 < b)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) :
    initialSquarePsiConvolutionMaximal σ b F x ≤
      ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
        lineMaximal (fun y : ℝ => F y) x := by
  apply iSup_le
  intro k
  have htk : 0 < b ^ k := by positivity
  exact initialSquarePsiConvolution_maximal_bound hSupp
    (fun y : ℝ => F y) (Lp.memLp F) (b ^ k) htk x

/-- The complete `lj:initial-square` package: the full square-function
estimate, smooth-part maximal comparison, `q=2` bounds, and the exact
interpolated `q>2` bounds for both the probability measure and its
reflection. -/
private theorem initialSquareAndMaximal_of_b
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) :
    (∀ G : Lp ℂ 2 (volume : Measure ℝ),
      eLpNorm (initialSquareConvolutionSquareFunction hSupp
          (measureSplitting σ hSupp β hβ D hdecay).1 b G)
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal ((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
            1 / (1 - Real.rpow b (-2 * β))) * ‖G‖)) ∧
    (∀ G : Lp ℂ 2 (volume : Measure ℝ), ∀ x : ℝ,
      initialSquarePsiConvolutionMaximal σ b G x ≤
        ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
          lineMaximal (fun y : ℝ => G y) x) ∧
    (∀ F : Lp ℂ 2 (volume : Measure ℝ),
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ b (fun y => F y))
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
          eLpNorm (fun y => F y) (ENNReal.ofReal 2) volume ∧
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) b (fun y => F y))
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
          eLpNorm (fun y => F y) (ENNReal.ofReal 2) volume) ∧
    (∀ q : ℝ, 2 < q →
      ∀ F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ),
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ b (fun y => F y))
          (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b)) *
          eLpNorm (fun y => F y) (ENNReal.ofReal q) volume ∧
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) b (fun y => F y))
          (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b)) *
          eLpNorm (fun y => F y) (ENNReal.ofReal q) volume) := by
  have hsplit := measureSplitting σ hSupp β hβ D hdecay
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G
    exact initialSquare_square_function_L2_bound hSupp hsplit.1 hb hβ G
  · intro G x
    exact initialSquarePsiConvolutionMaximal_bound hSupp hb G x
  · intro F
    exact initialSquareSigmaRawPositiveMaximalL2_bound_both_reflections_of_Lp
      hSupp hdecay hb hβ F
  · intro q hq F
    exact initialSquareSigmaRawPositiveMaximalLp_bound_both_reflections_of_Lp
      hSupp hdecay hb hβ hq F

/-- The paper-facing initial-square package, with the scale ratio fixed by
the standing convention `b = 2^a` for `a>0`. -/
theorem initialSquareAndMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (ha : 0 < a) (hβ : 0 < β) :
    (∀ G : Lp ℂ 2 (volume : Measure ℝ),
      eLpNorm (initialSquareConvolutionSquareFunction hSupp
          (measureSplitting σ hSupp β hβ D hdecay).1 (Real.rpow 2 a) G)
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal ((2 * Real.pi + 2 * |D|) *
          Real.sqrt (1 / (1 - (Real.rpow 2 a)⁻¹ ^ 2) +
            1 / (1 - Real.rpow (Real.rpow 2 a) (-2 * β))) * ‖G‖)) ∧
    (∀ G : Lp ℂ 2 (volume : Measure ℝ), ∀ x : ℝ,
      initialSquarePsiConvolutionMaximal σ (Real.rpow 2 a) G x ≤
        ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
          lineMaximal (fun y : ℝ => G y) x) ∧
    (∀ F : Lp ℂ 2 (volume : Measure ℝ),
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ (Real.rpow 2 a)
          (fun y => F y)) (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D
          (Real.rpow 2 a)) *
          eLpNorm (fun y => F y) (ENNReal.ofReal 2) volume ∧
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) (Real.rpow 2 a) (fun y => F y))
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D
          (Real.rpow 2 a)) *
          eLpNorm (fun y => F y) (ENNReal.ofReal 2) volume) ∧
    (∀ q : ℝ, 2 < q →
      ∀ F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ),
      eLpNorm (initialSquareSigmaRawPositiveMaximal σ (Real.rpow 2 a)
          (fun y => F y)) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D (Real.rpow 2 a))) *
          eLpNorm (fun y => F y) (ENNReal.ofReal q) volume ∧
      eLpNorm (initialSquareSigmaRawPositiveMaximal
          (Measure.map Neg.neg σ) (Real.rpow 2 a) (fun y => F y))
          (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D (Real.rpow 2 a))) *
          eLpNorm (fun y => F y) (ENNReal.ofReal q) volume) := by
  have hb : 1 < Real.rpow 2 a := by
    simpa using
      (Real.rpow_lt_rpow_of_exponent_lt
        (by norm_num : 1 < (2 : ℝ)) ha)
  exact initialSquareAndMaximal_of_b (b := Real.rpow 2 a)
    hSupp hdecay hb hβ

#print axioms initialSquareAndMaximal

end

end FractionalPrimes.Literature.JSW

end
