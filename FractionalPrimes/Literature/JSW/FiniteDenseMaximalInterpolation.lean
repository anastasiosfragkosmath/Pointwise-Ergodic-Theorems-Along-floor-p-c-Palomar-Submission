module

public import FractionalPrimes.Literature.JSW.LpConvolutionDenseConsistency

/-!
# Finite positive maximal interpolation on the dense input class

This file identifies finite-exponent positive convolution with the exact
source average on bounded finite-support inputs.  The scale comparison keeps
the source probability normalization and geometric cutoff unchanged.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The source `B₂ = Aν + 4 ‖φ‖∞ H₂` coefficient, with the approved
frequency and maximal-function constants. -/
def initialSquareSigmaPositiveMaximalB2 (β D b : ℝ) : ℝ :=
  (2 * Real.pi + 2 * |D|) *
      Real.sqrt (1 / (1 - b⁻¹ ^ 2) +
        1 / (1 - Real.rpow b (-2 * β))) +
    (4 * lpNorm φ ∞ volume) *
      (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
        ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ))

theorem initialSquareSigmaPositiveMaximalB2_nonneg
    {β D b : ℝ} (hb : 1 < b) (hβ : 0 < β) :
    0 ≤ initialSquareSigmaPositiveMaximalB2 β D b := by
  have hbpos : 0 < b := by linarith
  have hinvlt : b⁻¹ < 1 := (inv_lt_one₀ hbpos).2 hb
  have hinvnonneg : 0 ≤ b⁻¹ := inv_nonneg.mpr hbpos.le
  have hden1 : 0 < 1 - b⁻¹ ^ 2 := by nlinarith
  have hpowlt : Real.rpow b (-2 * β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  have hden2 : 0 < 1 - Real.rpow b (-2 * β) := by linarith
  have hphi : 0 ≤ lpNorm φ ∞ volume := lpNorm_nonneg
  dsimp [initialSquareSigmaPositiveMaximalB2]
  have hconst1 : 0 ≤ 2 * Real.pi + 2 * |D| := by positivity
  have hconst2 : 0 ≤ 4 * lpNorm φ ∞ volume := by positivity
  have hconst3 :
      0 ≤ (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
        ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  exact add_nonneg
    (mul_nonneg hconst1 (Real.sqrt_nonneg _))
    (mul_nonneg hconst2 hconst3)

private def initialSquareSigmaRawPositiveMaximalENNReal
    (σ : Measure ℝ) (b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f x)

private theorem initialSquareSigmaRawPositiveScale_integrable
    {σ : Measure ℝ} [IsFiniteMeasure σ] {b : ℝ}
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) (k : ℤ) (x : ℝ) :
    Integrable (fun y : ℝ => ‖g.1 (x - b ^ k * y)‖) σ := by
  rcases g.2.2.1 with ⟨C, hC⟩
  let C' : ℝ := max C 0
  have hsm : StronglyMeasurable (fun y : ℝ => g.1 (x - b ^ k * y)) :=
    g.2.1.stronglyMeasurable.comp_measurable (by fun_prop)
  have hbound (y : ℝ) : ‖‖g.1 (x-b^k*y)‖‖ ≤ C' := by
    calc
      _ = ‖g.1 (x-b^k*y)‖ := by simp
      _ ≤ C := hC _
      _ ≤ C' := by dsimp [C']; exact le_max_left _ _
  apply Integrable.of_bound hsm.norm.aestronglyMeasurable C'
  filter_upwards [] with y
  exact hbound y

private theorem initialSquareSigmaRawPositiveScale_le_of_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (f : ℝ → ℂ) (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C) (k : ℤ) (x : ℝ) :
    initialSquareSigmaRawPositiveScale σ b k f x ≤ C := by
  have hsm : StronglyMeasurable (fun y : ℝ => f (x - b ^ k * y)) :=
    hf.stronglyMeasurable.comp_measurable (by fun_prop)
  have hI : Integrable (fun y : ℝ => ‖f (x - b ^ k * y)‖) σ := by
    apply Integrable.of_bound hsm.norm.aestronglyMeasurable C
    filter_upwards [] with y
    have hbound : ‖‖f (x-b^k*y)‖‖ ≤ C := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC _
    exact hbound
  have hconst : Integrable (fun _ : ℝ => C) σ := integrable_const C
  change (∫ y, ‖f (x - b ^ k * y)‖ ∂σ) ≤ C
  calc
    _ ≤ ∫ y, C ∂σ := by
      apply integral_mono_ae hI hconst
      exact ae_of_all _ fun y => hC _
    _ = C := by
      rw [integral_const]
      simp [IsProbabilityMeasure.measure_univ]

private theorem initialSquareSigmaRawPositiveMaximalENNReal_le_of_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (f : ℝ → ℂ) (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    initialSquareSigmaRawPositiveMaximalENNReal σ b f x ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro k
  exact ENNReal.ofReal_le_ofReal
    (initialSquareSigmaRawPositiveScale_le_of_bound f hf hC0 hC k x)

theorem initialSquareSigmaRawPositiveMaximal_le_of_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (f : ℝ → ℂ) (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    initialSquareSigmaRawPositiveMaximal σ b f x ≤ C := by
  have hsup := initialSquareSigmaRawPositiveMaximalENNReal_le_of_bound
    (σ := σ) (b := b) f hf hC0 hC x
  have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
  simpa [initialSquareSigmaRawPositiveMaximal,
    initialSquareSigmaRawPositiveMaximalENNReal,
    ENNReal.toReal_ofReal hC0] using hmono

theorem initialSquareSigmaRawPositiveScale_le_rawMax
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) (k : ℤ) (x : ℝ) :
    initialSquareSigmaRawPositiveScale σ b k g.1 x ≤
      initialSquareSigmaRawPositiveMaximal σ b g.1 x := by
  rcases g.2.2.1 with ⟨C, hC⟩
  let C' : ℝ := max C 0
  have hC'nonneg : 0 ≤ C' := le_max_right _ _
  have hC'bound : ∀ y, ‖g.1 y‖ ≤ C' :=
    fun y => (hC y).trans (le_max_left _ _)
  have hsupBound := initialSquareSigmaRawPositiveMaximalENNReal_le_of_bound
    (σ := σ) (b := b) g.1 g.2.1 hC'nonneg hC'bound x
  have hsupNe :
      initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hsupBound ENNReal.ofReal_lt_top
  have hscale0 : 0 ≤ initialSquareSigmaRawPositiveScale σ b k g.1 x :=
    integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
  calc
    initialSquareSigmaRawPositiveScale σ b k g.1 x =
        (ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g.1 x)).toReal :=
      (ENNReal.toReal_ofReal hscale0).symm
    _ ≤ (initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x).toReal :=
      ENNReal.toReal_mono hsupNe
        (le_iSup (fun j : ℤ =>
          ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b j g.1 x)) k)
    _ = initialSquareSigmaRawPositiveMaximal σ b g.1 x := rfl

private theorem initialSquareSigmaRawPositiveMaximalENNReal_subadditive
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (f g : Variation.LayerCakeInput (volume : Measure ℝ))
    (hsum : Variation.LayerCakeAdmissible (volume : Measure ℝ) (f.1 + g.1))
    (x : ℝ) :
    initialSquareSigmaRawPositiveMaximalENNReal σ b (f.1 + g.1) x ≤
      initialSquareSigmaRawPositiveMaximalENNReal σ b f.1 x +
        initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x := by
  apply iSup_le
  intro k
  have hIf := initialSquareSigmaRawPositiveScale_integrable (σ := σ) (b := b) f k x
  have hIg := initialSquareSigmaRawPositiveScale_integrable (σ := σ) (b := b) g k x
  let sumInput : Variation.LayerCakeInput (volume : Measure ℝ) := ⟨f.1 + g.1, hsum⟩
  have hIsum := initialSquareSigmaRawPositiveScale_integrable
    (σ := σ) (b := b) sumInput k x
  have hscale :
      initialSquareSigmaRawPositiveScale σ b k (f.1 + g.1) x ≤
        initialSquareSigmaRawPositiveScale σ b k f.1 x +
          initialSquareSigmaRawPositiveScale σ b k g.1 x := by
    calc
      _ ≤ ∫ y, ‖f.1 (x-b^k*y)‖ + ‖g.1 (x-b^k*y)‖ ∂σ := by
        apply integral_mono_ae hIsum (hIf.add hIg)
        exact ae_of_all _ fun y => by
          change ‖f.1 (x-b^k*y) + g.1 (x-b^k*y)‖ ≤ _
          exact norm_add_le _ _
      _ = _ := by
        change (∫ y, ‖f.1 (x-b^k*y)‖ + ‖g.1 (x-b^k*y)‖ ∂σ) = _
        rw [integral_add hIf hIg]
        rfl
  have hnonnegf :
      0 ≤ initialSquareSigmaRawPositiveScale σ b k f.1 x :=
    integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
  have hnonnegg :
      0 ≤ initialSquareSigmaRawPositiveScale σ b k g.1 x :=
    integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
  calc
    ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k (f.1+g.1) x) ≤
        ENNReal.ofReal
          (initialSquareSigmaRawPositiveScale σ b k f.1 x +
            initialSquareSigmaRawPositiveScale σ b k g.1 x) :=
      ENNReal.ofReal_le_ofReal hscale
    _ = ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f.1 x) +
          ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g.1 x) :=
      (ENNReal.ofReal_add hnonnegf hnonnegg)
    _ ≤ initialSquareSigmaRawPositiveMaximalENNReal σ b f.1 x +
          initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x :=
      add_le_add (le_iSup (fun j : ℤ =>
        ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b j f.1 x)) k)
        (le_iSup (fun j : ℤ =>
          ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b j g.1 x)) k)

theorem initialSquareSigmaRawPositiveMaximal_le_add
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (f g : Variation.LayerCakeInput (volume : Measure ℝ))
    (hsum : Variation.LayerCakeAdmissible (volume : Measure ℝ) (f.1 + g.1))
    (x : ℝ) :
    initialSquareSigmaRawPositiveMaximal σ b (f.1 + g.1) x ≤
      initialSquareSigmaRawPositiveMaximal σ b f.1 x +
        initialSquareSigmaRawPositiveMaximal σ b g.1 x := by
  have hsup := initialSquareSigmaRawPositiveMaximalENNReal_subadditive
    (σ := σ) (b := b) f g hsum x
  rcases f.2.2.1 with ⟨Cf, hCf⟩
  rcases g.2.2.1 with ⟨Cg, hCg⟩
  let Cf' : ℝ := max Cf 0
  let Cg' : ℝ := max Cg 0
  have hCf0 : 0 ≤ Cf' := le_max_right _ _
  have hCg0 : 0 ≤ Cg' := le_max_right _ _
  have hCfBound : ∀ y, ‖f.1 y‖ ≤ Cf' := fun y => (hCf y).trans (le_max_left _ _)
  have hCgBound : ∀ y, ‖g.1 y‖ ≤ Cg' := fun y => (hCg y).trans (le_max_left _ _)
  have hftop :
      initialSquareSigmaRawPositiveMaximalENNReal σ b f.1 x ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ENNReal.ofReal Cf' :=
        initialSquareSigmaRawPositiveMaximalENNReal_le_of_bound
          f.1 f.2.1 hCf0 hCfBound x
      _ < ∞ := ENNReal.ofReal_lt_top
  have hgtop :
      initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ENNReal.ofReal Cg' :=
        initialSquareSigmaRawPositiveMaximalENNReal_le_of_bound
          g.1 g.2.1 hCg0 hCgBound x
      _ < ∞ := ENNReal.ofReal_lt_top
  calc
    initialSquareSigmaRawPositiveMaximal σ b (f.1+g.1) x =
        (initialSquareSigmaRawPositiveMaximalENNReal σ b (f.1+g.1) x).toReal := rfl
    _ ≤ (initialSquareSigmaRawPositiveMaximalENNReal σ b f.1 x +
          initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hftop, hgtop⟩) hsup
    _ = (initialSquareSigmaRawPositiveMaximalENNReal σ b f.1 x).toReal +
          (initialSquareSigmaRawPositiveMaximalENNReal σ b g.1 x).toReal :=
      ENNReal.toReal_add hftop hgtop
    _ = _ := rfl

private theorem initialSquare_realSquareMoment_eq_eLpNorm_rpow
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(volume : Measure ℝ)) =
      eLpNorm f (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
  have hp0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have hpTop : ENNReal.ofReal (2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  calc
    (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(volume : Measure ℝ)) =
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
          apply lintegral_congr_ae
          filter_upwards with x
          rw [ENNReal.ofReal_pow (hf0 x) 2]
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
          exact (ENNReal.rpow_natCast (ENNReal.ofReal (f x)) 2).symm
    _ = eLpNorm f (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
        hf.aestronglyMeasurable, htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
        ENNReal.rpow_one]

private theorem initialSquare_complexLpMoment_two_eq_eLpNorm_rpow
    (f : ℝ → ℂ) (hf : Measurable f) :
    Variation.complexLpMoment 2 volume f =
      eLpNorm f (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
  have hp : 0 < (2 : ℝ) := by norm_num
  have hp0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal (2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  calc
    Variation.complexLpMoment 2 volume f =
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
          unfold Variation.complexLpMoment
          apply lintegral_congr_ae
          filter_upwards with x
          simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm f (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
        hf.aestronglyMeasurable, htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
        ENNReal.rpow_one]

/-- The raw positive maximal function on bounded finite-support inputs has
the exact strong `L²` and `L∞` bounds required by the source interpolation
lemma. -/
def initialSquareSigmaRawPositiveMaximalOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) :
    WeakTypeInterpolationStrongTwoInfinityOperator (volume : Measure ℝ)
      (initialSquareSigmaPositiveMaximalB2 β D b) where
  apply f := initialSquareSigmaRawPositiveMaximal σ b f.1
  measurable_apply f :=
    measurable_initialSquareSigmaRawPositiveMaximal σ b f.1 f.2.1
  nonneg_apply f x := ENNReal.toReal_nonneg
  subadditive f g hfg x :=
    initialSquareSigmaRawPositiveMaximal_le_add (σ := σ) (b := b) f g hfg x
  strongL2 f := by
    have hG' : MemLp f.1 (2 : ℝ≥0∞) volume := by
      simpa using initialSquare_layerCakeInput_memLp_two f
    let hG : MemLp f.1 2 volume := hG'
    let F₂ : Lp ℂ 2 volume := hG.toLp f.1
    have hF₂ : (F₂ : ℝ → ℂ) =ᵐ[volume] f.1 := MemLp.coeFn_toLp hG
    have hbridge := initialSquareSigmaRawPositiveMaximalReal_ae_eq_source
      (σ := σ) (b := b) f F₂ hF₂
    have hsource := initialSquare_sigma_positive_convolution_maximal_L2_bound
      hSupp hσ hb hβ F₂
    have houtput :
        eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f.1)
            (ENNReal.ofReal 2) volume =
          eLpNorm (initialSquareSigmaPositiveConvolutionMaximalReal σ b F₂)
            (ENNReal.ofReal 2) volume :=
      eLpNorm_congr_ae hbridge
    have hinput :
        eLpNorm (fun x : ℝ => F₂ x) (ENNReal.ofReal 2) volume =
          eLpNorm f.1 (ENNReal.ofReal 2) volume :=
      eLpNorm_congr_ae hF₂
    have hbpos : 0 < b := by linarith
    have hinvlt : b⁻¹ < 1 := (inv_lt_one₀ hbpos).2 hb
    have hinvnonneg : 0 ≤ b⁻¹ := inv_nonneg.mpr hbpos.le
    have hden1 : 0 < 1 - b⁻¹ ^ 2 := by nlinarith
    have hpowlt : Real.rpow b (-2 * β) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
    have hden2 : 0 < 1 - Real.rpow b (-2 * β) := by linarith
    have hphi : 0 ≤ lpNorm φ ∞ volume := lpNorm_nonneg
    have hA : 0 ≤ initialSquareSigmaPositiveMaximalB2 β D b := by
      dsimp [initialSquareSigmaPositiveMaximalB2]
      have hconst1 : 0 ≤ 2 * Real.pi + 2 * |D| := by positivity
      have hconst2 : 0 ≤ 4 * lpNorm φ ∞ volume := by positivity
      have hconst3 :
          0 ≤ (6 * (2 : ℝ) * (2 : ℝ) ^ ((2 : ℝ) - 1) /
            ((2 : ℝ) - 1)) ^ (1 / (2 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      exact add_nonneg
        (mul_nonneg hconst1 (Real.sqrt_nonneg _))
        (mul_nonneg hconst2 hconst3)
    have hnormBound :
        eLpNorm (initialSquareSigmaRawPositiveMaximal σ b f.1)
            (ENNReal.ofReal 2) volume ≤
          ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
            eLpNorm f.1 (ENNReal.ofReal 2) volume := by
      rw [houtput]
      have hsource' := hsource
      rw [hinput] at hsource'
      simpa [initialSquareSigmaPositiveMaximalB2] using hsource'
    have hmoment := initialSquare_realSquareMoment_eq_eLpNorm_rpow
      (measurable_initialSquareSigmaRawPositiveMaximal σ b f.1 f.2.1)
      (fun x => ENNReal.toReal_nonneg)
    have hinputMoment := initialSquare_complexLpMoment_two_eq_eLpNorm_rpow
      f.1 f.2.1
    have hpow := ENNReal.rpow_le_rpow hnormBound (by norm_num : 0 ≤ (2 : ℝ))
    have hpow' := hpow
    rw [← hmoment] at hpow'
    have hcoeff :
        (ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
          eLpNorm f.1 (ENNReal.ofReal 2) volume) ^ (2 : ℝ) =
        (ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b)).rpow 2 *
          Variation.complexLpMoment 2 volume f.1 := by
      calc
        _ = (ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b)).rpow 2 *
            (eLpNorm f.1 (ENNReal.ofReal 2) volume) ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))
        _ = _ := by rw [← hinputMoment]
    calc
      (∫⁻ x, ENNReal.ofReal
          (initialSquareSigmaRawPositiveMaximal σ b f.1 x ^ 2) ∂volume) ≤
        (ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b) *
          eLpNorm f.1 (ENNReal.ofReal 2) volume) ^ (2 : ℝ) := hpow'
      _ = (ENNReal.ofReal (initialSquareSigmaPositiveMaximalB2 β D b)).rpow 2 *
          Variation.complexLpMoment 2 volume f.1 := hcoeff
  strongLInf f C hC hbound x := by
    exact initialSquareSigmaRawPositiveMaximal_le_of_bound
      f.1 f.2.1 hC hbound x

private theorem complexMeasureConvolution_ae_congr
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f g : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ))
    (hg : AEStronglyMeasurable g (volume : Measure ℝ))
    (hfg : f =ᵐ[volume] g) :
    (fun x => complexMeasureConvolution μ f hf x) =ᵐ[volume]
      fun x => complexMeasureConvolution μ g hg x := by
  have hfg' : hf.mk f =ᵐ[volume] hg.mk g :=
    hf.ae_eq_mk.symm.trans (hfg.trans hg.ae_eq_mk)
  simpa [complexMeasureConvolution] using
    rawComplexMeasureConvolution_ae_congr μ (hf.mk f) (hg.mk g)
      hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk hfg'

/-- At each geometric scale, the finite-exponent positive convolution map on
a `LayerCakeInput` agrees almost everywhere with the source real average. -/
theorem initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale
    {q : ℝ} (hq : 1 < q)
    [Fact (1 ≤ ENNReal.ofReal q)]
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (k : ℤ)
    [IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation]
    (g : Variation.LayerCakeInput (volume : Measure ℝ))
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (hF : (F : ℝ → ℂ) =ᵐ[volume] g.1) :
    (lpPositiveConvolutionMap (ENNReal.ofReal q) ENNReal.ofReal_ne_top
        (initialSquareComplexifiedSigmaScale σ b k) F : ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ y, ‖g.1 (x - b ^ k * y)‖ ∂σ := by
  let p : ℝ≥0∞ := ENNReal.ofReal q
  let μ : ComplexMeasure ℝ := initialSquareComplexifiedSigmaScale σ b k
  let fAbs : ℝ → ℂ := fun x => (‖g.1 x‖ : ℂ)
  let FAbs : Lp ℂ p (volume : Measure ℝ) :=
    (Complex.ofRealCLM.compLpL p volume) (lpComplexPointwiseNorm p F)
  have hμfinite : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
  letI : IsFiniteMeasure μ.variation := hμfinite
  have hfAbs : Measurable fAbs := by
    dsimp [fAbs]
    exact Complex.continuous_ofReal.measurable.comp g.2.1.norm
  have hbounded : ∃ C : ℝ, ∀ x, ‖fAbs x‖ ≤ C := by
    rcases g.2.2.1 with ⟨C, hC⟩
    refine ⟨max C 0, ?_⟩
    intro x
    have hnorm : ‖fAbs x‖ = ‖g.1 x‖ := by
      simp [fAbs, Complex.norm_real, abs_of_nonneg (norm_nonneg _)]
    rw [hnorm]
    exact (hC x).trans (le_max_left _ _)
  have hnormF : (lpComplexPointwiseNorm p F : ℝ → ℝ) =ᵐ[volume]
      fun x => ‖g.1 x‖ := by
    have h := lipschitz_complex_norm.coeFn_compLp (by simp) F
    filter_upwards [h, hF] with x hx₁ hx₂
    simpa [lpComplexPointwiseNorm] using hx₁.trans (congrArg norm hx₂)
  have hFAbs : (FAbs : ℝ → ℂ) =ᵐ[volume] fAbs := by
    have h := Complex.ofRealCLM.coeFn_compLpL
      (lpComplexPointwiseNorm p F)
    filter_upwards [h, hnormF] with x hx₁ hx₂
    simpa [FAbs, fAbs] using hx₁.trans (congrArg Complex.ofReal hx₂)
  have hqconv := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_bounded
    (q := q) hq (μ := μ) FAbs fAbs hfAbs hbounded hFAbs
  have hqconv' : (lpComplexMeasureConvolution p μ FAbs : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution μ fAbs (hfAbs.stronglyMeasurable.aestronglyMeasurable) := by
    simpa [p, μ] using hqconv
  have hG₂ : MemLp g.1 (2 : ℝ≥0∞) (volume : Measure ℝ) := by
    simpa [ENNReal.ofReal_ofNat] using initialSquare_layerCakeInput_memLp_two g
  let F₂ : Lp ℂ 2 (volume : Measure ℝ) := hG₂.toLp g.1
  let F₂Abs : Lp ℂ 2 (volume : Measure ℝ) :=
    initialSquareAbsL2Representative F₂
  have hF₂ : (F₂ : ℝ → ℂ) =ᵐ[volume] g.1 :=
    MemLp.coeFn_toLp hG₂
  have hF₂Abs : (F₂Abs : ℝ → ℂ) =ᵐ[volume] fAbs := by
    have hnorm : (fun x : ℝ => (‖F₂ x‖ : ℂ)) =ᵐ[volume] fAbs := by
      filter_upwards [hF₂] with x hx
      simp [fAbs, hx]
    exact (initialSquareAbsL2Representative_ae_bridge F₂).trans hnorm
  have hconv : (lpComplexMeasureConvolution p μ FAbs : ℝ → ℂ) =ᵐ[volume]
      (fun x => complexMeasureConvolution
        (initialSquareDilateComplexMeasure
          (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
        (fun y => F₂Abs y) (Lp.aestronglyMeasurable F₂Abs) x) := by
    have hcongr := complexMeasureConvolution_ae_congr μ fAbs
      (fun x => F₂Abs x) hfAbs.aestronglyMeasurable
      (Lp.aestronglyMeasurable F₂Abs) hF₂Abs.symm
    have hsame := hqconv'.trans hcongr
    simpa [μ, initialSquareComplexifiedSigmaScale,
      initialSquareSigmaComplexifiedMeasure] using hsame
  have hsource := initialSquare_sigma_positive_convolution_scale_ae_bridge
    (σ := σ) (b := b) hb F₂ k
  have hsource' :
      (fun x => complexMeasureConvolution
        (initialSquareDilateComplexMeasure
          (σ.toSignedMeasure.toComplexMeasure 0) (b ^ k))
        (fun y => F₂Abs y) (Lp.aestronglyMeasurable F₂Abs) x) =ᵐ[volume]
      (fun x => ((∫ y, ‖F₂ (x - b ^ k * y)‖ ∂σ : ℝ) : ℂ)) := by
    simpa [F₂Abs] using hsource
  have havg : (fun x : ℝ => ∫ y, ‖F₂ (x-b^k*y)‖ ∂σ) =ᵐ[volume]
      fun x => ∫ y, ‖g.1 (x-b^k*y)‖ ∂σ := by
    simpa [initialSquareSigmaRawPositiveScale] using
      initialSquareSigmaRawPositiveScale_ae_congr (σ := σ) (b ^ k)
        (Lp.stronglyMeasurable F₂).measurable g.2.1 hF₂
  have hreal : (fun x : ℝ =>
      Complex.re ((lpComplexMeasureConvolution p μ FAbs : ℝ → ℂ) x)) =ᵐ[volume]
      fun x => ∫ y, ‖g.1 (x-b^k*y)‖ ∂σ := by
    filter_upwards [hconv, hsource', havg] with x hx hsourceX havgX
    have hval := hx.trans hsourceX
    have hrealpart : Complex.re ((lpComplexMeasureConvolution p μ FAbs) x) =
        ∫ y, ‖F₂ (x-b^k*y)‖ ∂σ := by
      rw [hval]
      simp
    rw [hrealpart, havgX]
  have hRe := Complex.reCLM.coeFn_compLpL
    (lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs)
  have hCLM :
      (lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs :
          ℝ → ℂ) =ᵐ[volume]
        (lpComplexMeasureConvolution p μ FAbs : ℝ → ℂ) := by
    rfl
  change (Complex.reCLM.compLpL p volume
      (lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs) :
        ℝ → ℝ) =ᵐ[volume] _
  filter_upwards [hRe, hCLM, hreal] with x h₁ h₂ h₃
  calc
    _ = Complex.re ((lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs) x) := h₁
    _ = Complex.re ((lpComplexMeasureConvolution p μ FAbs) x) := by
      exact congrArg Complex.re h₂
    _ = _ := h₃

/-- Each finite-exponent positive scale map is positive on all `L^q`
inputs.  Positivity follows by continuity from the bounded finite-support
dense class, where the map is the source average of a modulus. -/
theorem initialSquare_lpPositiveConvolutionMap_nonneg
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (hq : 2 < q) [Fact (1 ≤ ENNReal.ofReal q)] (k : ℤ)
    [IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) :
    0 ≤ lpPositiveConvolutionMap (ENNReal.ofReal q) ENNReal.ofReal_ne_top
      (initialSquareComplexifiedSigmaScale σ b k) F := by
  let P : ℝ≥0∞ := ENNReal.ofReal q
  let hp : P ≠ ∞ := ENNReal.ofReal_ne_top
  let μ : ComplexMeasure ℝ := initialSquareComplexifiedSigmaScale σ b k
  have hμ' : IsFiniteMeasure
      (initialSquareComplexifiedSigmaScale σ b k).variation :=
    initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
  letI : IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation := hμ'
  have hμ : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
  letI : IsFiniteMeasure μ.variation := hμ
  have hp0 : 0 < q := by linarith
  obtain ⟨g, _inputNs, hgMem, _hinputNs, hgnorm, _hinputAE⟩ :=
    Variation.exists_layerCakeInput_approximation volume hp0 (F : ℝ → ℂ)
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)
  let Fseq : ℕ → Lp ℂ P volume := fun n => (hgMem n).toLp (g n).1
  have hFseq : Tendsto Fseq atTop (𝓝 F) := by
    simpa only [P, Fseq, Lp.toLp_coeFn] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (g n).1) hgMem (F : ℝ → ℂ) (Lp.memLp F)).mpr hgnorm
  have hlimit : Tendsto
      (fun n => lpPositiveConvolutionMap P hp μ (Fseq n)) atTop
        (𝓝 (lpPositiveConvolutionMap P hp μ F)) :=
    (continuous_lpPositiveConvolutionMap P hp μ).continuousAt.tendsto.comp hFseq
  have hnonneg (n : ℕ) : 0 ≤ lpPositiveConvolutionMap P hp μ (Fseq n) := by
    have hFrep : (Fseq n : ℝ → ℂ) =ᵐ[volume] (g n).1 :=
      MemLp.coeFn_toLp (hgMem n)
    have hscale := initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale
      (q := q) (σ := σ) (b := b) (by linarith : 1 < q) hb k
      (g n) (Fseq n) hFrep
    have hscaleNonneg : ∀ᵐ x ∂volume,
        0 ≤ (lpPositiveConvolutionMap P hp μ (Fseq n) : ℝ → ℝ) x := by
      filter_upwards [hscale] with x hx
      rw [hx]
      exact integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
    exact (Lp.coeFn_nonneg _).1 hscaleNonneg
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit hnonneg

private theorem lp_coeFn_finset_sup'_ae
    {ι : Type*} [DecidableEq ι] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → Lp ℝ p (volume : Measure ℝ)) :
    ((s.sup' hs f : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
      fun x => s.sup' hs (fun i => fun y => f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsn : s.Nonempty
      · have hcoe := Lp.coeFn_sup (f a) (s.sup' hsn f)
        have htail := ih hsn
        have hstep :
            ((f a ⊔ s.sup' hsn f : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume]
              fun x => f a x ⊔ s.sup' hsn (fun i => fun y => f i y) x := by
          filter_upwards [hcoe, htail] with x hx₁ hx₂
          rw [hx₁]
          calc
            (((f a : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ) ⊔
                ((s.sup' hsn f : Lp ℝ p (volume : Measure ℝ)) : ℝ → ℝ)) x =
                max (f a x) ((s.sup' hsn f : Lp ℝ p (volume : Measure ℝ)) x) := rfl
            _ = max (f a x) (s.sup' hsn (fun i => fun y => f i y) x) := by
              rw [hx₂]
        have hsEq : hs = Finset.insert_nonempty a s := Subsingleton.elim _ _
        subst hs
        rw [Finset.sup'_insert]
        rw [Finset.sup'_insert]
        exact hstep
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        have hsEq : hs = Finset.insert_nonempty a ∅ := Subsingleton.elim _ _
        subst hs
        simpa using (EventuallyEq.rfl :
          (fun x : ℝ => f a x) =ᵐ[volume] fun x => f a x)

/-- The source positive maximal operator satisfies the exact interpolated
`L^q` estimate on the bounded finite-support dense class. -/
theorem initialSquareSigmaRawPositiveMaximalLq_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (hq : 2 < q) (g : Variation.LayerCakeInput (volume : Measure ℝ))
    : eLpNorm (initialSquareSigmaRawPositiveMaximal σ b g.1)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm g.1 (ENNReal.ofReal q) volume := by
  have hB2 := initialSquareSigmaPositiveMaximalB2_nonneg
    (β := β) (D := D) (b := b) hb hβ
  simpa [initialSquareSigmaRawPositiveMaximalOperator] using
    weakTypeInterpolationStrongTwoInfinity
      (initialSquareSigmaRawPositiveMaximalOperator hSupp hσ hb hβ)
      hq hB2 g

/-- The finite positive maximal truncation has the same exact `L^q` bound on
all bounded finite-support inputs as the full source maximal function. -/
theorem initialSquareSigmaFinitePositiveMaximalLp_dense_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (hq : 2 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (s : Finset ℤ) (hne : s.Nonempty)
    (g : Variation.LayerCakeInput (volume : Measure ℝ))
    (hg : MemLp g.1 (ENNReal.ofReal q) volume) :
    eLpNorm
        (initialSquareSigmaFinitePositiveMaximalLp (ENNReal.ofReal q)
          ENNReal.ofReal_ne_top σ b s hne (hg.toLp g.1) : ℝ → ℝ)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm g.1 (ENNReal.ofReal q) volume := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal q
  let hp : P ≠ ∞ := ENNReal.ofReal_ne_top
  let F : Lp ℂ P volume := hg.toLp g.1
  have hF : (F : ℝ → ℂ) =ᵐ[volume] g.1 := MemLp.coeFn_toLp hg
  have hrawBound := initialSquareSigmaRawPositiveMaximalLq_bound
    hSupp hσ hb hβ hq g
  let rawFn : ℝ → ℝ := initialSquareSigmaRawPositiveMaximal σ b g.1
  have hrawMem : MemLp rawFn P volume := by
    calc
      eLpNorm rawFn P volume ≤
          ENNReal.ofReal
            (weakTypeInterpolationStrongTwoInfinityConstant q
              (initialSquareSigmaPositiveMaximalB2 β D b)) *
            eLpNorm g.1 (ENNReal.ofReal q) volume := by
              simpa [rawFn, P] using hrawBound
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top
  let rawLp : Lp ℝ P volume := hrawMem.toLp rawFn
  have hrawRep : (rawLp : ℝ → ℝ) =ᵐ[volume] rawFn :=
    MemLp.coeFn_toLp hrawMem
  let scaleMap : ℤ → Lp ℝ P volume := fun k => by
    letI : IsFiniteMeasure
        (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    exact lpPositiveConvolutionMap P hp
      (initialSquareComplexifiedSigmaScale σ b k) F
  let hne' : s.Nonempty := hne
  let finiteLp : Lp ℝ P volume :=
    initialSquareSigmaFinitePositiveMaximalLp P hp σ b s hne' F
  have horder : finiteLp ≤ rawLp := by
    change s.sup' hne' scaleMap ≤ rawLp
    apply Finset.sup'_le
    intro k hk
    letI : IsFiniteMeasure
        (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    have hscaleAE := initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale
      (q := q) (σ := σ) (b := b)
      (lt_trans (by norm_num : (1 : ℝ) < 2) hq) hb k g F hF
    have hleAE :
        (scaleMap k) ≤ᵐ[volume]
          (rawLp : ℝ → ℝ) := by
      filter_upwards [hscaleAE, hrawRep] with x hx hrep
      calc
        scaleMap k x =
            initialSquareSigmaRawPositiveScale σ b k g.1 x := by
              simpa [initialSquareSigmaRawPositiveScale] using hx
        _ ≤ rawFn x := by
          exact initialSquareSigmaRawPositiveScale_le_rawMax g k x
        _ = (rawLp : ℝ → ℝ) x := hrep.symm
    exact (Lp.coeFn_le _ _).1 hleAE
  rcases hne with ⟨k₀, hk₀⟩
  letI : IsFiniteMeasure
      (initialSquareComplexifiedSigmaScale σ b k₀).variation :=
    initialSquareComplexifiedSigmaScale_variation_isFinite σ b k₀
  have hscaleAE := initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale
    (q := q) (σ := σ) (b := b)
    (lt_trans (by norm_num : (1 : ℝ) < 2) hq) hb k₀ g F hF
  have hscaleNonnegAE :
      0 ≤ᵐ[volume] (lpPositiveConvolutionMap P hp
        (initialSquareComplexifiedSigmaScale σ b k₀) F) := by
    filter_upwards [hscaleAE] with x hx
    rw [hx]
    exact integral_nonneg_of_ae (ae_of_all _ fun y => norm_nonneg _)
  have hscaleNonneg :
      (0 : Lp ℝ P volume) ≤ lpPositiveConvolutionMap P hp
        (initialSquareComplexifiedSigmaScale σ b k₀) F :=
    (Lp.coeFn_nonneg _).1 hscaleNonnegAE
  have hfiniteNonneg : (0 : Lp ℝ P volume) ≤ finiteLp := by
    change 0 ≤ s.sup' hne' scaleMap
    exact hscaleNonneg.trans (Finset.le_sup' scaleMap hk₀)
  have hfiniteNonnegAE : 0 ≤ᵐ[volume] (finiteLp : ℝ → ℝ) :=
    (Lp.coeFn_nonneg finiteLp).2 hfiniteNonneg
  have hfiniteLeAE :
      (finiteLp : ℝ → ℝ) ≤ᵐ[volume] (rawLp : ℝ → ℝ) :=
    (Lp.coeFn_le finiteLp rawLp).2 horder
  have hnormLe : ∀ᵐ x ∂volume,
      ‖(finiteLp : ℝ → ℝ) x‖ ≤ rawFn x := by
    filter_upwards [hfiniteNonnegAE, hfiniteLeAE, hrawRep] with x hnonneg hle hrep
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      (finiteLp : ℝ → ℝ) x ≤ (rawLp : ℝ → ℝ) x := hle
      _ = rawFn x := hrep
  have hmono := eLpNorm_mono_ae_real (p := P)
    (Lp.aestronglyMeasurable finiteLp) hnormLe
  calc
    eLpNorm
        (initialSquareSigmaFinitePositiveMaximalLp P hp σ b s hne' F : ℝ → ℝ)
        P volume = eLpNorm (finiteLp : ℝ → ℝ) P volume := rfl
    _ ≤ eLpNorm rawFn P volume := hmono
    _ ≤ ENNReal.ofReal
          (weakTypeInterpolationStrongTwoInfinityConstant q
            (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm g.1 (ENNReal.ofReal q) volume := by
          simpa [rawFn, P] using hrawBound

/-- The finite positive maximal truncation has the source `L^q` estimate for
arbitrary `L^q` inputs, by the checked nonlinear dense extension. -/
theorem initialSquareSigmaFinitePositiveMaximalLp_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (hq : 2 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (s : Finset ℤ) (hne : s.Nonempty)
    (F : Lp ℂ (ENNReal.ofReal q) volume) :
    eLpNorm
        (initialSquareSigmaFinitePositiveMaximalLp (ENNReal.ofReal q)
          ENNReal.ofReal_ne_top σ b s hne F : ℝ → ℝ)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal q) volume := by
  let S : Lp ℂ (ENNReal.ofReal q) volume →
    Lp ℝ (ENNReal.ofReal q) volume :=
      initialSquareSigmaFinitePositiveMaximalLp (ENNReal.ofReal q)
        ENNReal.ofReal_ne_top σ b s hne
  have hS : Continuous S :=
    continuous_initialSquareSigmaFinitePositiveMaximalLp
      (ENNReal.ofReal q) ENNReal.ofReal_ne_top σ b s hne
  have hA : 0 ≤ initialSquareSigmaPositiveMaximalB2 β D b :=
    initialSquareSigmaPositiveMaximalB2_nonneg
      (β := β) (D := D) (b := b) hb hβ
  have hC : 0 ≤ weakTypeInterpolationStrongTwoInfinityConstant q
      (initialSquareSigmaPositiveMaximalB2 β D b) := by
    dsimp [weakTypeInterpolationStrongTwoInfinityConstant]
    positivity
  have hbound := weakTypeInterpolation_extend_dense_continuous
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (p := q)
    (show 1 ≤ q by linarith) S hS
    (weakTypeInterpolationStrongTwoInfinityConstant q
      (initialSquareSigmaPositiveMaximalB2 β D b)) hC
    (by
      intro g hg
      simpa [S] using initialSquareSigmaFinitePositiveMaximalLp_dense_bound
        hSupp hσ hb hβ hq s hne g hg)
    F
  simpa [S] using hbound

theorem eLpNorm_toReal_iSup_ofReal_mono
    {q : ℝ} (hq : 0 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Measurable (f n))
    (hnonneg : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f n x)
    (hmono : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), f n x ≤ f n.succ x)
    {C : ℝ≥0∞}
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) volume ≤ C) :
    eLpNorm (fun x : ℝ => (⨆ n, ENNReal.ofReal (f n x)).toReal)
      (ENNReal.ofReal q) volume ≤ C := by
  by_cases hCtop : C = ∞
  · simp [hCtop]
  · let P : ℝ≥0∞ := ENNReal.ofReal q
    have hP0 : P ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
    have hPtop : P ≠ ∞ := ENNReal.ofReal_ne_top
    have hPtoReal : P.toReal = q := by simp [P, hq.le]
    let U : ℝ → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (f n x)
    let W : ℕ → ℝ → ℝ≥0∞ := fun n x => ENNReal.ofReal (f n x) ^ q
    have hUmeas : Measurable U := by
      dsimp [U]
      exact Measurable.iSup fun n => ENNReal.continuous_ofReal.measurable.comp (hf n)
    have hWmeas : ∀ n, Measurable (W n) := by
      intro n
      dsimp [W]
      exact (ENNReal.continuous_rpow_const (y := q)).measurable.comp
        (ENNReal.continuous_ofReal.measurable.comp (hf n))
    have hWmono : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), W n x ≤ W n.succ x := by
      intro n
      filter_upwards [hmono n] with x hx
      dsimp [W]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hx) hq.le
    have hWsup : ∀ᵐ x ∂(volume : Measure ℝ), (⨆ n, W n x) = U x ^ q := by
      filter_upwards [ae_all_iff.mpr hmono] with x hx
      have hvmono : Monotone (fun n => ENNReal.ofReal (f n x)) := by
        intro n m hnm
        induction hnm with
        | refl => exact le_rfl
        | @step m hnm ih =>
            exact ih.trans (ENNReal.ofReal_le_ofReal (hx m))
      let v : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (f n x)
      have hv : Tendsto v atTop (𝓝 (⨆ n, v n)) :=
        tendsto_atTop_iSup (by simpa [v] using hvmono)
      have hvpow : Tendsto (fun n => v n ^ q) atTop
          (𝓝 ((⨆ n, v n) ^ q)) :=
        (ENNReal.continuous_rpow_const (y := q)).continuousAt.tendsto.comp hv
      have hvpowMono : Monotone (fun n => v n ^ q) := by
        intro n m hnm
        exact ENNReal.rpow_le_rpow (hvmono hnm) hq.le
      have hvpowSup : Tendsto (fun n => v n ^ q) atTop
          (𝓝 (⨆ n, v n ^ q)) := tendsto_atTop_iSup hvpowMono
      have hEq := tendsto_nhds_unique hvpowSup hvpow
      simpa [U, W, v] using hEq
    have hWint_eq :
        (∫⁻ x, U x ^ q ∂(volume : Measure ℝ)) =
          ⨆ n, ∫⁻ x, W n x ∂(volume : Measure ℝ) := by
      calc
        _ = ∫⁻ x, ⨆ n, W n x ∂(volume : Measure ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [hWsup] with x hx
          exact hx.symm
        _ = _ := lintegral_iSup_ae hWmeas hWmono
    have hWbound (n : ℕ) :
        ∫⁻ x, W n x ∂(volume : Measure ℝ) ≤ C ^ q := by
      have hnormIntegral :
          eLpNorm (f n) P volume ^ q = ∫⁻ x, W n x ∂(volume : Measure ℝ) := by
        calc
          _ = (∫⁻ x, ‖f n x‖ₑ ^ q ∂(volume : Measure ℝ)) := by
            rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop
              (hf n).aestronglyMeasurable, hPtoReal]
            rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
          _ = _ := by
            apply lintegral_congr_ae
            filter_upwards [hnonneg n] with x hx
            simp [W, Real.enorm_eq_ofReal_abs, abs_of_nonneg hx]
      rw [← hnormIntegral]
      exact ENNReal.rpow_le_rpow (hbound n) hq.le
    have hWintBound :
        (∫⁻ x, U x ^ q ∂(volume : Measure ℝ)) ≤ C ^ q := by
      rw [hWint_eq]
      exact iSup_le hWbound
    have hCpow : C ^ q ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq.le hCtop
    have hUqfinite : ∀ᵐ x ∂(volume : Measure ℝ), U x ^ q < ∞ :=
      ae_lt_top ((ENNReal.continuous_rpow_const (y := q)).measurable.comp hUmeas)
        (ne_top_of_le_ne_top hCpow hWintBound)
    have hUfinite : ∀ᵐ x ∂(volume : Measure ℝ), U x < ∞ := by
      filter_upwards [hUqfinite] with x hx
      exact (ENNReal.rpow_lt_top_iff_of_pos hq).mp hx
    have hnonnegAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, 0 ≤ f n x :=
      ae_all_iff.mpr hnonneg
    have hmonoAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, f n x ≤ f n.succ x :=
      ae_all_iff.mpr hmono
    have hlim : ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n => f n x) atTop (𝓝 (U x).toReal) := by
      filter_upwards [hnonnegAll, hmonoAll, hUfinite] with x hxnonneg hxmono hxU
      have hvmono : Monotone (fun n => ENNReal.ofReal (f n x)) := by
        intro n m hnm
        induction hnm with
        | refl => exact le_rfl
        | @step m hnm ih =>
            exact ih.trans (ENNReal.ofReal_le_ofReal (hxmono m))
      have hv := tendsto_atTop_iSup hvmono
      have htoReal := (ENNReal.tendsto_toReal hxU.ne).comp hv
      have hEq : (fun n => f n x) =ᶠ[atTop]
          fun n => (ENNReal.ofReal (f n x)).toReal :=
        Filter.Eventually.of_forall fun n =>
          (ENNReal.toReal_ofReal (hxnonneg n)).symm
      exact (Filter.tendsto_congr' hEq).mpr htoReal
    have hGmeas : Measurable (fun x : ℝ => (U x).toReal) :=
      ENNReal.measurable_toReal.comp hUmeas
    apply Lp.eLpNorm_le_of_ae_tendsto
      (u := (Filter.atTop : Filter ℕ)) (p := P) (μ := volume)
      (C := C)
    · exact Filter.Eventually.of_forall hbound
    · exact fun n => (hf n).aestronglyMeasurable
    · exact hGmeas.aestronglyMeasurable
    · exact hlim

/-- A single scale of the positive maximal operator on finite-exponent `L^q`. -/
def initialSquareSigmaPositiveConvolutionScaleLp
    (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)]
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ) (k : ℤ)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) :
    Lp ℝ (ENNReal.ofReal q) (volume : Measure ℝ) := by
  letI : IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation :=
    initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
  exact lpPositiveConvolutionMap (ENNReal.ofReal q) ENNReal.ofReal_ne_top
    (initialSquareComplexifiedSigmaScale σ b k) F

/-- The full geometric-scale positive maximal operator on `L^q`, represented
as the supremum of the checked positive convolution maps at each scale. -/
def initialSquareSigmaPositiveMaximalLp
    (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)]
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) : ℝ → ℝ :=
  fun x => (⨆ k : ℤ, ENNReal.ofReal
    ((initialSquareSigmaPositiveConvolutionScaleLp q σ b k F : ℝ → ℝ) x)).toReal

/-- The full positive geometric maximal operator obeys the exact interpolated
`L^q` bound.  The proof exhausts the integer scales by finite symmetric
windows and applies the monotone Fatou lemma to the finite truncations. -/
theorem initialSquareSigmaPositiveMaximalLp_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (hq : 2 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) :
    eLpNorm (initialSquareSigmaPositiveMaximalLp q σ b F)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal q) volume := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal q
  let hp : P ≠ ∞ := ENNReal.ofReal_ne_top
  let C : ℝ≥0∞ := ENNReal.ofReal
      (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
      eLpNorm (F : ℝ → ℂ) P volume
  let s : ℕ → Finset ℤ := fun n => Finset.Icc (-(n : ℤ)) (n : ℤ)
  have hne (n : ℕ) : (s n).Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  let S : ℕ → Lp ℝ P volume := fun n =>
    initialSquareSigmaFinitePositiveMaximalLp P hp σ b (s n) (hne n) F
  let f : ℕ → ℝ → ℝ := fun n x => (S n : ℝ → ℝ) x
  let scale : ℤ → Lp ℝ P volume := fun k =>
    initialSquareSigmaPositiveConvolutionScaleLp q σ b k F
  have hscaleNonneg (k : ℤ) : 0 ≤ scale k := by
    dsimp [scale, initialSquareSigmaPositiveConvolutionScaleLp]
    letI : IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    exact initialSquare_lpPositiveConvolutionMap_nonneg
      hSupp hσ hb hq k F
  have hsSubset {n m : ℕ} (hnm : n ≤ m) : s n ⊆ s m := by
    intro k hk
    simp only [s, Finset.mem_Icc] at hk ⊢
    omega
  have hSmono : Monotone S := by
    intro n m hnm
    change (s n).sup' (hne n) (fun k => scale k) ≤
      (s m).sup' (hne m) (fun k => scale k)
    exact Finset.sup'_mono (f := fun k => scale k)
      (hsSubset hnm) (hne n)
  have hSnonneg (n : ℕ) : 0 ≤ S n := by
    change (0 : Lp ℝ P volume) ≤
      (s n).sup' (hne n) (fun k => scale k)
    rcases hne n with ⟨k₀, hk₀⟩
    exact (hscaleNonneg k₀).trans (Finset.le_sup' scale hk₀)
  have hfmeas (n : ℕ) : Measurable (f n) := by
    exact (Lp.stronglyMeasurable (S n)).measurable
  have hfnonneg (n : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f n x := by
    change 0 ≤ᵐ[volume] (S n : ℝ → ℝ)
    exact (Lp.coeFn_nonneg (S n)).2 (hSnonneg n)
  have hfmono (n : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ), f n x ≤ f n.succ x := by
    have hstep : S n ≤ S n.succ := hSmono (Nat.le_succ n)
    change (S n : ℝ → ℝ) ≤ᵐ[volume] (S n.succ : ℝ → ℝ)
    exact (Lp.coeFn_le (S n) (S n.succ)).2 hstep
  have hfbound (n : ℕ) : eLpNorm (f n) P volume ≤ C := by
    have h := initialSquareSigmaFinitePositiveMaximalLp_bound
      hSupp hσ hb hβ hq (s n) (hne n) F
    simpa [f, S, C, P] using h
  have hFatou := eLpNorm_toReal_iSup_ofReal_mono
    (q := q) (by linarith : 0 < q) f hfmeas hfnonneg hfmono hfbound
  have hfiniteRep (n : ℕ) :
      (S n : ℝ → ℝ) =ᵐ[volume]
        fun x => (s n).sup' (hne n) (fun k => scale k x) := by
    simpa [S, s, initialSquareSigmaFinitePositiveMaximalLp,
      lpFinitePositiveConvolutionSup, scale,
      initialSquareSigmaPositiveConvolutionScaleLp] using
      (lp_coeFn_finset_sup'_ae (s n) (hne n) scale)
  have hmapSup (n : ℕ) (x : ℝ) :
      ENNReal.ofReal ((s n).sup' (hne n) (fun k => scale k x)) =
        (s n).sup' (hne n) (fun k => ENNReal.ofReal (scale k x)) := by
    exact Finset.apply_sup'_eq_sup'_comp (hne n) ENNReal.ofReal
      (by intro u v; simp [ENNReal.ofReal_max])
  have hfiniteOfReal (n : ℕ) :
      (fun x => ENNReal.ofReal (f n x)) =ᵐ[volume]
        fun x => (s n).sup' (hne n) (fun k => ENNReal.ofReal (scale k x)) := by
    filter_upwards [hfiniteRep n] with x hx
    change ENNReal.ofReal ((S n : ℝ → ℝ) x) = _
    rw [hx]
    exact hmapSup n x
  have hscaleSup : ∀ᵐ x ∂(volume : Measure ℝ),
      (⨆ n, ENNReal.ofReal (f n x)) =
        ⨆ k : ℤ, ENNReal.ofReal (scale k x) := by
    filter_upwards [ae_all_iff.mpr hfiniteOfReal] with x hx
    apply le_antisymm
    · apply iSup_le
      intro n
      rw [hx n]
      apply Finset.sup'_le
      intro k hk
      exact le_iSup_of_le k le_rfl
    · apply iSup_le
      intro k
      have hk : k ∈ s k.natAbs := by
        cases k with
        | ofNat n => simp [s]
        | negSucc n => simp [s] <;> omega
      calc
        ENNReal.ofReal (scale k x) ≤
            (s k.natAbs).sup' (hne k.natAbs)
              (fun j => ENNReal.ofReal (scale j x)) :=
          Finset.le_sup' (fun j => ENNReal.ofReal (scale j x)) hk
        _ = ENNReal.ofReal (f k.natAbs x) := (hx k.natAbs).symm
        _ ≤ ⨆ n, ENNReal.ofReal (f n x) :=
          le_iSup_of_le k.natAbs le_rfl
  have hfullEq :
      initialSquareSigmaPositiveMaximalLp q σ b F =ᵐ[volume]
        fun x => (⨆ n, ENNReal.ofReal (f n x)).toReal := by
    filter_upwards [hscaleSup] with x hx
    change (⨆ k : ℤ, ENNReal.ofReal (scale k x)).toReal = _
    rw [hx]
  calc
    eLpNorm (initialSquareSigmaPositiveMaximalLp q σ b F) P volume =
        eLpNorm (fun x => (⨆ n, ENNReal.ofReal (f n x)).toReal) P volume :=
      eLpNorm_congr_ae hfullEq
    _ ≤ C := hFatou
    _ = ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal q) volume := rfl

/-- On the bounded finite-support dense class, the full Lp representative is
the exact source supremum of averages of the input modulus. -/
theorem initialSquareSigmaPositiveMaximalLp_ae_eq_raw
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (hq : 2 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (g : Variation.LayerCakeInput (volume : Measure ℝ))
    (hg : MemLp g.1 (ENNReal.ofReal q) volume) :
    initialSquareSigmaPositiveMaximalLp q σ b (hg.toLp g.1) =ᵐ[volume]
      initialSquareSigmaRawPositiveMaximal σ b g.1 := by
  let F : Lp ℂ (ENNReal.ofReal q) volume := hg.toLp g.1
  let scale : ℤ → Lp ℝ (ENNReal.ofReal q) volume := fun k =>
    initialSquareSigmaPositiveConvolutionScaleLp q σ b k F
  have hFrep : (F : ℝ → ℂ) =ᵐ[volume] g.1 := MemLp.coeFn_toLp hg
  have hterm (k : ℤ) :
      (fun x => ENNReal.ofReal (scale k x)) =ᵐ[volume]
        fun x => ENNReal.ofReal
          (initialSquareSigmaRawPositiveScale σ b k g.1 x) := by
    letI : IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation :=
      initialSquareComplexifiedSigmaScale_variation_isFinite σ b k
    have hscale := initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale
      (q := q) (σ := σ) (b := b) (by linarith : 1 < q) hb k g F hFrep
    filter_upwards [hscale] with x hx
    exact congrArg ENNReal.ofReal hx
  have htermAll : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ,
      ENNReal.ofReal (scale k x) = ENNReal.ofReal
        (initialSquareSigmaRawPositiveScale σ b k g.1 x) :=
    ae_all_iff.mpr hterm
  change (fun x => (⨆ k : ℤ, ENNReal.ofReal (scale k x)).toReal) =ᵐ[volume]
    fun x => (⨆ k : ℤ,
      ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g.1 x)).toReal
  filter_upwards [htermAll] with x hx
  congr 1
  exact iSup_congr hx

private theorem initialSquare_measure_map_neg_support
    (σ : Measure ℝ)
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    (Measure.map Neg.neg σ).support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
  intro x hx
  have hxopen : ∀ U, x ∈ U → IsOpen U → 0 < (Measure.map Neg.neg σ) U := by
    rw [Measure.support_eq_forall_isOpen] at hx
    exact hx
  have hxpre : -x ∈ σ.support := by
    rw [Measure.support_eq_forall_isOpen]
    intro U hU hUopen
    have hpreopen : IsOpen (Neg.neg ⁻¹' U) := hUopen.preimage continuous_neg
    have hxpre : x ∈ Neg.neg ⁻¹' U := by simpa using hU
    have hpos := hxopen (Neg.neg ⁻¹' U) hxpre hpreopen
    rw [Measure.map_apply (by fun_prop) hpreopen.measurableSet] at hpos
    simpa using hpos
  have hbound := hSupp hxpre
  rcases Set.mem_Icc.mp hbound with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The source `L^q` maximal bound holds for the positive measure and its
reflection with the same interpolation constant. The reflected splitting
data are supplied by the checked measure-splitting theorem. -/
theorem initialSquareSigmaPositiveMaximalLp_bound_both_reflections
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hq : 2 < q)
    [Fact (1 ≤ ENNReal.ofReal q)]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) :
    eLpNorm (initialSquareSigmaPositiveMaximalLp q σ b F)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal q) volume ∧
    eLpNorm (initialSquareSigmaPositiveMaximalLp q
        (Measure.map Neg.neg σ) b F)
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal q) volume := by
  let σref : Measure ℝ := Measure.map Neg.neg σ
  have hsplit := measureSplitting σ hSupp β hβ D hdecay
  have hσ : MeasureSplittingBounds σ β D := hsplit.1
  have hσref : MeasureSplittingBounds σref β D := by
    simpa [σref] using hsplit.2
  have hSuppRef : σref.support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
    dsimp [σref]
    exact initialSquare_measure_map_neg_support σ hSupp
  have hmain := initialSquareSigmaPositiveMaximalLp_bound
    hSupp hσ hb hβ hq F
  haveI : IsProbabilityMeasure σref := inferInstance
  have href := initialSquareSigmaPositiveMaximalLp_bound
    hSuppRef hσref hb hβ hq F
  exact ⟨hmain, by simpa [σref] using href⟩

#print axioms initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale
#print axioms initialSquare_lpPositiveConvolutionMap_nonneg
#print axioms initialSquareSigmaRawPositiveMaximalLq_bound
#print axioms initialSquareSigmaFinitePositiveMaximalLp_dense_bound
#print axioms initialSquareSigmaFinitePositiveMaximalLp_bound
#print axioms initialSquareSigmaPositiveMaximalLp_bound
#print axioms initialSquareSigmaPositiveMaximalLp_ae_eq_raw
#print axioms initialSquareSigmaPositiveMaximalLp_bound_both_reflections

end

end FractionalPrimes.Literature.JSW

end
