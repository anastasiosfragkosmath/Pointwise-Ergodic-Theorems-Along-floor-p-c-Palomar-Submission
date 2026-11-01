module

public import FractionalPrimes.Literature.Ergodic.MobiusBoundedLTwo
public import FractionalPrimes.Literature.Ergodic.UnweightedErgodicMaximal
public import FractionalPrimes.Literature.Variation.LayerCakeInputDensity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section
namespace FractionalPrimes
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section

/-- A bounded measurable finite-measure-support layer-cake input belongs to
both `L²` and `L∞`. -/
theorem layerCakeInput_memLp_two_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : Literature.Variation.LayerCakeInput μ) :
    MemLp g.1 (2 : ℝ≥0∞) μ ∧ MemLp g.1 ∞ μ := by
  rcases g.2 with ⟨hmeas, ⟨C, hC⟩, hsupport⟩
  have htop : MemLp g.1 ∞ μ :=
    memLp_top_of_bound hmeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have htwo : MemLp g.1 (2 : ℝ≥0∞) μ :=
    htop.mono_exponent_of_measure_support_ne_top
      (s := {x | g.1 x ≠ 0})
      (by
        intro x hx
        exact not_ne_iff.mp hx)
      (ne_of_lt hsupport)
      (by norm_num)
  exact ⟨htwo, htop⟩

/-- The bounded finite-support approximants can be chosen with an arbitrarily
small prescribed Lp error. -/
theorem exists_layerCakeInput_approximation_lt
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (f : X → ℂ) (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p) μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : Literature.Variation.LayerCakeInput μ,
      eLpNorm (g.1 - f) (ENNReal.ofReal p) μ < ε ∧
      MemLp g.1 (ENNReal.ofReal p) μ ∧
      MemLp g.1 (2 : ℝ≥0∞) μ ∧ MemLp g.1 ∞ μ := by
  obtain ⟨g, ns, hmem, hstrict, hnorm, hae⟩ :=
    Literature.Variation.exists_layerCakeInput_approximation μ hp f hf hfp
  have hsmall := hnorm.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hsmall.exists
  obtain ⟨h2, htop⟩ := layerCakeInput_memLp_two_top μ (g n)
  exact ⟨g n, hn, hmem n, h2, htop⟩

#print axioms layerCakeInput_memLp_two_top
#print axioms exists_layerCakeInput_approximation_lt

/-- Finite Möbius averages respect subtraction of their input functions. -/
theorem mobiusAverage_sub_apply
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f g : X → ℂ) (N : Scale) (x : X) :
    mobiusAverage S c (f - g) N x =
      mobiusAverage S c f N x - mobiusAverage S c g N x := by
  simp [mobiusAverage, weightedAverage, Finset.sum_sub_distrib, mul_sub]

/-- Changing a representative on a null set changes each finite Möbius
average only on a null set. -/
theorem mobiusAverage_ae_eq_of_ae_eq
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) {f g : X → ℂ} (hfg : f =ᵐ[S.μ] g) (N : Scale) :
    mobiusAverage S c f N =ᵐ[S.μ] mobiusAverage S c g N := by
  have hiterate (n : ℕ) : ∀ᵐ x ∂S.μ,
      f (S.iterate (floorPower c n) x) = g (S.iterate (floorPower c n) x) :=
    (S.measurePreserving_integerIterate (floorPower c n)).quasiMeasurePreserving.ae hfg
  have hall : ∀ᵐ x ∂S.μ, ∀ n : ℕ,
      f (S.iterate (floorPower c n) x) = g (S.iterate (floorPower c n) x) :=
    ae_all_iff.mpr hiterate
  filter_upwards [hall] with x hx
  unfold mobiusAverage weightedAverage
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hx n]

#print axioms mobiusAverage_sub_apply
#print axioms mobiusAverage_ae_eq_of_ae_eq

/-- The scalar Chebyshev loss is summable when the approximation error is
quadratic in the geometric threshold. -/
theorem mobius_geometric_markov_bound
    {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ENNReal.ofReal δ)⁻¹ ^ p *
        (ENNReal.ofReal (δ ^ 2)) ^ p ≤ ENNReal.ofReal δ := by
  let e : ℝ≥0∞ := ENNReal.ofReal δ
  have hepos : 0 < e := by simp [e, hδ]
  have hetop : e ≠ ∞ := by simp [e]
  have hep0 : e ^ p ≠ 0 := (ENNReal.rpow_pos hepos hetop).ne'
  have heptop : e ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (le_trans zero_le_one hp.le) hetop
  have hpowmul : ENNReal.ofReal (δ ^ 2) = e * e := by
    dsimp [e]
    rw [pow_two, ← ENNReal.ofReal_mul hδ.le]
  calc
    _ = e⁻¹ ^ p * (e * e) ^ p := by rw [hpowmul]
    _ = e⁻¹ ^ p * (e ^ p * e ^ p) := by
      rw [ENNReal.mul_rpow_of_ne_top hetop hetop]
    _ = (e ^ p)⁻¹ * (e ^ p * e ^ p) := by rw [ENNReal.inv_rpow]
    _ = e ^ p := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hep0 heptop, one_mul]
    _ ≤ e := by
      have hele1 : e ≤ 1 := by
        dsimp [e]
        exact ENNReal.ofReal_le_one.mpr hδ1
      simpa using ENNReal.rpow_le_rpow_of_exponent_ge hele1 hp.le
    _ = ENNReal.ofReal δ := rfl
#print axioms mobius_geometric_markov_bound

private def mobiusDenseThreshold (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (k + 1)

/-- The source all-scale Möbius conclusion on a measurable representative of
an arbitrary Lp input, conditional only on the checked D=4 discrete L²
operator-decay estimate. -/
theorem mobiusAverage_ae_tendsto_zero_of_discreteOperatorDecay_of_measurable
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) {p : ℝ} (hp : 1 < p) (f : X → ℂ)
    (hfmeas : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p) S.μ)
    (hoperatorD4 :
      letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : Scale, 3 ≤ N.1 →
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (primeComparisonIntegerKernel c.value N)‖ +
            ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (mobiusIntegerKernel c.value N)‖ ≤
                B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) :
    ∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x) atTop (𝓝 0) := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hp0 : 0 < p := by linarith
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  obtain ⟨K, hmaximal⟩ := unweightedErgodicMaximalBound hp c
  let Kreal : ℝ := K
  have hKreal : 0 ≤ Kreal := by simp [Kreal]
  have hdenom : 0 < Kreal + 1 := by linarith
  let δ : ℕ → ℝ := mobiusDenseThreshold
  have hδpos (k : ℕ) : 0 < δ k := by
    dsimp [δ, mobiusDenseThreshold]
    exact pow_pos (by norm_num) _
  have hδle (k : ℕ) : δ k ≤ 1 := by
    dsimp [δ, mobiusDenseThreshold]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hδsummable : Summable δ := by
    have h := hgeom.mul_left (1 / 2 : ℝ)
    refine h.congr fun k => ?_
    dsimp [δ, mobiusDenseThreshold]
    rw [pow_succ]
    ring
  have hδtendsto : Tendsto δ atTop (𝓝 0) := hδsummable.tendsto_atTop_zero
  let η : ℕ → ℝ := fun k => (δ k) ^ 2 / (Kreal + 1)
  have hηpos (k : ℕ) : 0 < η k :=
    div_pos (sq_pos_of_pos (hδpos k)) hdenom
  have happroxExists (k : ℕ) :
      ∃ g : Literature.Variation.LayerCakeInput S.μ,
        eLpNorm (g.1 - f) P S.μ < ENNReal.ofReal (η k) ∧
        MemLp g.1 P S.μ ∧
        MemLp g.1 (2 : ℝ≥0∞) S.μ ∧ MemLp g.1 ∞ S.μ := by
    simpa [P] using exists_layerCakeInput_approximation_lt S.μ hp0 f hfmeas hfp
      (ENNReal.ofReal_pos.mpr (hηpos k))
  choose g hg using happroxExists
  let err : ℕ → X → ℂ := fun k => (g k).1 - f
  let errNorm : ℕ → X → ℂ := fun k x => (‖err k x‖ : ℂ)
  let badMax : ℕ → X → ℝ≥0∞ := fun k =>
    unweightedErgodicMaximal S c.value (errNorm k)
  have hbounded (k : ℕ) :
      ∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => mobiusAverage S c.value (g k).1 N x)
        atTop (𝓝 0) := by
    rcases hg k with ⟨happrox, hmemP, hmem2, hmemTop⟩
    exact mobiusAverage_ae_tendsto_zero_of_bounded_ltwo_of_discreteOperatorDecay
      S c.value (g k).1 hmem2 hmemTop hoperatorD4
  have herrMem (k : ℕ) : MemLp (err k) P S.μ := by
    rcases hg k with ⟨happrox, hmemP, hmem2, hmemTop⟩
    exact hmemP.sub hfp
  have herrNormMem (k : ℕ) : MemLp (errNorm k) P S.μ := by
    have h : MemLp (fun x => ((‖err k x‖ : ℝ) : ℂ)) P S.μ :=
      (herrMem k).norm.ofReal
    simpa [errNorm] using h
  have herrNormEq (k : ℕ) :
      eLpNorm (errNorm k) P S.μ = eLpNorm (err k) P S.μ := by
    have hsame :
        (fun x => ‖errNorm k x‖ₑ) =ᵐ[S.μ] (fun x => ‖err k x‖ₑ) :=
      Filter.Eventually.of_forall fun x => by
        simp [errNorm, enorm_eq_nnnorm, Complex.nnnorm_real]
    calc
      _ = eLpNorm (fun x => ‖errNorm k x‖ₑ) P S.μ :=
        (eLpNorm_enorm _ (herrNormMem k).aestronglyMeasurable).symm
      _ = eLpNorm (fun x => ‖err k x‖ₑ) P S.μ := eLpNorm_congr_ae hsame
      _ = _ := eLpNorm_enorm _ (herrMem k).aestronglyMeasurable
  have hbad_measure (k : ℕ) :
      S.μ {x | ENNReal.ofReal (δ k) ≤ badMax k x} ≤ ENNReal.ofReal (δ k) := by
    rcases hg k with ⟨happrox, hmemP, hmem2, hmemTop⟩
    have hmax := hmaximal S (errNorm k) (herrNormMem k)
    have hKmul :
        eLpNorm (badMax k) P S.μ ≤
          ENNReal.ofReal ((δ k) ^ 2) := by
      have herror : eLpNorm (err k) P S.μ ≤
          ENNReal.ofReal ((δ k) ^ 2 / (Kreal + 1)) :=
        le_of_lt (by simpa [P, err] using happrox)
      have hbase : eLpNorm (badMax k) P S.μ ≤
          ENNReal.ofNNReal K * eLpNorm (errNorm k) P S.μ :=
        hmax.1
      have hmul :
          ENNReal.ofNNReal K * eLpNorm (errNorm k) P S.μ ≤
            ENNReal.ofNNReal K * ENNReal.ofReal ((δ k) ^ 2 / (Kreal + 1)) := by
        rw [herrNormEq k]
        gcongr
      have hKnn : 0 ≤ Kreal := hKreal
      have hKcoerce : ENNReal.ofNNReal K = ENNReal.ofReal Kreal := by
        simp [Kreal]
      have hscalar : Kreal * ((δ k) ^ 2 / (Kreal + 1)) ≤ (δ k) ^ 2 := by
        have hratio : Kreal / (Kreal + 1) ≤ 1 :=
          (div_le_iff₀ hdenom).2 (by nlinarith)
        calc
          _ = (δ k) ^ 2 * (Kreal / (Kreal + 1) ) := by ring
          _ ≤ _ := by
            simpa using mul_le_mul_of_nonneg_left hratio (sq_nonneg (δ k))
      calc
        _ ≤ ENNReal.ofNNReal K * eLpNorm (errNorm k) P S.μ := hbase
        _ ≤ ENNReal.ofNNReal K * ENNReal.ofReal ((δ k) ^ 2 / (Kreal + 1)) :=
          by simpa [herrNormEq k] using hmul
        _ = ENNReal.ofReal (Kreal * ((δ k) ^ 2 / (Kreal + 1)) ) := by
          rw [hKcoerce, ← ENNReal.ofReal_mul hKnn]
        _ ≤ ENNReal.ofReal ((δ k) ^ 2) := ENNReal.ofReal_le_ofReal hscalar
    have hmark := meas_ge_le_mul_pow_eLpNorm_enorm
      (μ := S.μ) (p := P) (f := badMax k) hP0 hPtop
      (ENNReal.ofReal_pos.mpr (hδpos k)).ne'
      (by intro h; exact (ENNReal.ofReal_ne_top).elim h)
    have hmark' :
        S.μ {x | ENNReal.ofReal (δ k) ≤ badMax k x} ≤
          (ENNReal.ofReal (δ k))⁻¹ ^ p *
            (eLpNorm (badMax k) P S.μ) ^ p := by
      simpa [badMax, enorm_eq_self, P, ENNReal.toReal_ofReal hp0.le] using hmark
    calc
      _ ≤ (ENNReal.ofReal (δ k))⁻¹ ^ p *
          (ENNReal.ofReal ((δ k) ^ 2)) ^ p := by
        refine hmark'.trans ?_
        gcongr
      _ ≤ ENNReal.ofReal (δ k) :=
        mobius_geometric_markov_bound hp (hδpos k) (hδle k)
  let bad : ℕ → Set X := fun k => {x | ENNReal.ofReal (δ k) ≤ badMax k x}
  have hsum_bad : (∑' k : ℕ, S.μ (bad k)) ≠ ∞ := by
    have hterm : ∀ k : ℕ, S.μ (bad k) ≤ ENNReal.ofReal (δ k) := by
      intro k
      exact hbad_measure k
    have hsumle :
        (∑' k : ℕ, S.μ (bad k)) ≤ ∑' k : ℕ, ENNReal.ofReal (δ k) :=
      ENNReal.tsum_le_tsum hterm
    have hsumreal : (∑' k : ℕ, ENNReal.ofReal (δ k)) =
        ENNReal.ofReal (∑' k : ℕ, δ k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => le_of_lt (hδpos k)) hδsummable]
    have hfinite : (∑' k : ℕ, ENNReal.ofReal (δ k)) ≠ ∞ := by
      rw [hsumreal]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfinite hsumle
  have hnotbad : ∀ᵐ x ∂S.μ, ∀ᶠ k in atTop, x ∉ bad k :=
    ae_eventually_notMem hsum_bad
  have hgood : ∀ᵐ x ∂S.μ, ∀ k : ℕ,
      Tendsto (fun N : Scale => mobiusAverage S c.value (g k).1 N x)
        atTop (𝓝 0) :=
    ae_all_iff.mpr hbounded
  have hf'ae : ∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x) atTop (𝓝 0) := by
    filter_upwards [hgood, hnotbad] with x hxgood hxnotbad
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hsmallδ : ∀ᶠ k in atTop, δ k < ε / 2 :=
      hδtendsto.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨k, hkδ, hknot⟩ := (hsmallδ.and hxnotbad).exists
    have hbadlt : badMax k x < ENNReal.ofReal (δ k) := by
      have hnot : x ∉ bad k := hknot
      exact lt_of_not_ge (by simpa [bad] using hnot)
    have hconv : Tendsto
        (fun N : Scale => mobiusAverage S c.value (g k).1 N x)
        atTop (𝓝 0) := hxgood k
    have hnormconv := tendsto_zero_iff_norm_tendsto_zero.mp hconv
    have hNsmall : ∀ᶠ N : Scale in atTop,
        ‖mobiusAverage S c.value (g k).1 N x‖ < ε / 2 :=
      hnormconv.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hNsmall] with N hNsmall
    have herror : ‖mobiusAverage S c.value (err k) N x‖ < δ k := by
      have hdom : scaleFamilyMaximal
          (fun N : Scale => mobiusAverage S c.value (err k) N) x ≤ badMax k x :=
        (hmaximal S (err k) (herrMem k)).2 x
      have hcoord : ENNReal.ofReal
          ‖mobiusAverage S c.value (err k) N x‖ ≤ badMax k x := by
        change (⨆ M : Scale, ENNReal.ofReal
          ‖mobiusAverage S c.value (err k) M x‖) ≤ badMax k x at hdom
        exact (le_iSup (fun M : Scale => ENNReal.ofReal
          ‖mobiusAverage S c.value (err k) M x‖) N).trans hdom
      have hlt : ENNReal.ofReal
          ‖mobiusAverage S c.value (err k) N x‖ < ENNReal.ofReal (δ k) :=
        hcoord.trans_lt hbadlt
      exact (ENNReal.ofReal_lt_ofReal_iff (hδpos k)).mp hlt
    have hdecomp : mobiusAverage S c.value f N x =
        mobiusAverage S c.value (g k).1 N x -
          mobiusAverage S c.value (err k) N x := by
      have hsub : mobiusAverage S c.value (err k) N x =
          mobiusAverage S c.value (g k).1 N x -
            mobiusAverage S c.value f N x := by
        simpa [err] using mobiusAverage_sub_apply S c.value (g k).1 f N x
      calc
        mobiusAverage S c.value f N x =
            mobiusAverage S c.value (g k).1 N x -
              (mobiusAverage S c.value (g k).1 N x -
                mobiusAverage S c.value f N x) := by abel
        _ = _ := by rw [hsub]
    have hfinal :
        ‖mobiusAverage S c.value f N x‖ < ε := by
      calc
        ‖mobiusAverage S c.value f N x‖ ≤
            ‖mobiusAverage S c.value (g k).1 N x‖ +
              ‖mobiusAverage S c.value (err k) N x‖ := by
          rw [hdecomp]
          exact norm_sub_le _ _
        _ < ε := by linarith
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hfinal
  filter_upwards [hf'ae] with x hx
  exact hx

/-- Dominated convergence turns the almost-everywhere conclusion into
convergence in Lp for a measurable representative. -/
theorem mobiusAverage_eLpNorm_tendsto_zero_of_discreteOperatorDecay_of_measurable
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) {p : ℝ} (hp : 1 < p) (f : X → ℂ)
    (hfmeas : Measurable f)
    (hf : MemLp f (ENNReal.ofReal p) S.μ)
    (hoperatorD4 :
      letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : Scale, 3 ≤ N.1 →
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (primeComparisonIntegerKernel c.value N)‖ +
            ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (mobiusIntegerKernel c.value N)‖ ≤
                B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) :
    Tendsto (fun N : Scale =>
      eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
      atTop (𝓝 0) := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hp0 : 0 < p := by linarith
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  obtain ⟨K, hmaximal⟩ := unweightedErgodicMaximalBound hp c
  let fAbs : X → ℂ := fun x => (‖f x‖ : ℂ)
  have hfAbs : MemLp fAbs P S.μ := by
    have h : MemLp (fun x => ((‖f x‖ : ℝ) : ℂ)) P S.μ := hf.norm.ofReal
    simpa [fAbs] using h
  have hfAbsNorm : eLpNorm fAbs P S.μ = eLpNorm f P S.μ := by
    have hsame : (fun x => ‖fAbs x‖ₑ) =ᵐ[S.μ] (fun x => ‖f x‖ₑ) :=
      Filter.Eventually.of_forall fun x => by
        simp [fAbs, enorm_eq_nnnorm, Complex.nnnorm_real]
    calc
      _ = eLpNorm (fun x => ‖fAbs x‖ₑ) P S.μ :=
        (eLpNorm_enorm _ hfAbs.aestronglyMeasurable).symm
      _ = eLpNorm (fun x => ‖f x‖ₑ) P S.μ := eLpNorm_congr_ae hsame
      _ = _ := eLpNorm_enorm _ hf.aestronglyMeasurable
  let B : X → ℝ≥0∞ := unweightedErgodicMaximal S c.value fAbs
  have hmaxAbs := hmaximal S fAbs hfAbs
  have hBfinite : eLpNorm B P S.μ < ∞ := by
    have hprod : ENNReal.ofNNReal K * eLpNorm fAbs P S.μ < ∞ :=
      ENNReal.mul_lt_top (by simp) hfAbs.eLpNorm_lt_top
    exact hmaxAbs.1.trans_lt hprod
  have hBmem : MemLp B P S.μ := memLp_iff.mpr hBfinite
  have hae : ∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x) atTop (𝓝 0) :=
    mobiusAverage_ae_tendsto_zero_of_discreteOperatorDecay_of_measurable
      S c hp f hfmeas hf hoperatorD4
  let F : Scale → X → ℝ≥0∞ := fun N x =>
    ‖mobiusAverage S c.value f N x‖ₑ ^ p
  let bound : X → ℝ≥0∞ := fun x => B x ^ p
  have hFmeas (N : Scale) : AEMeasurable (F N) S.μ := by
    have havg : AEStronglyMeasurable (mobiusAverage S c.value f N) S.μ := by
      simpa [mobiusAverage] using
        aestronglyMeasurable_weightedAverage S c.value
          (fun n => (mobiusWeight n : ℂ)) f N hfmeas.aestronglyMeasurable
    change AEMeasurable
      ((fun a : ℝ≥0∞ => a ^ p) ∘
        (fun x => ‖mobiusAverage S c.value f N x‖ₑ)) S.μ
    exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable
      havg.enorm
  have hFbound (N : Scale) (x : X) : F N x ≤ bound x := by
    have hdom := (hmaximal S f hf).2 x
    have hcoord : ENNReal.ofReal
        ‖mobiusAverage S c.value f N x‖ ≤ B x := by
      change (⨆ M : Scale, ENNReal.ofReal
        ‖mobiusAverage S c.value f M x‖) ≤ B x at hdom
      exact (le_iSup (fun M : Scale => ENNReal.ofReal
        ‖mobiusAverage S c.value f M x‖) N).trans hdom
    have hcoord' : ‖mobiusAverage S c.value f N x‖ₑ ≤ B x := by
      simpa only [← ofReal_norm] using hcoord
    exact ENNReal.rpow_le_rpow hcoord' hp0.le
  have hBpowFinite : (∫⁻ x, bound x ∂S.μ) ≠ ∞ := by
    have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      hP0 hPtop hBmem.eLpNorm_lt_top
    have hlt' : (∫⁻ x, ‖B x‖ₑ ^ p ∂S.μ) < ∞ := by
      simpa [P, ENNReal.toReal_ofReal hp0.le] using hlt
    simpa [bound, enorm_eq_self] using hlt'.ne
  have hFlim : ∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => F N x) atTop (𝓝 0) := by
    filter_upwards [hae] with x hx
    have henorm := continuous_enorm.continuousAt.tendsto.comp hx
    have hpow' :=
      (ENNReal.continuous_rpow_const (y := p)).continuousAt.tendsto.comp henorm
    have heq :
        ((fun a : ℝ≥0∞ => a ^ p) ∘ (fun a => ‖a‖ₑ) ∘
          (fun N : Scale => mobiusAverage S c.value f N x)) =ᶠ[atTop]
        (fun N : Scale => ‖mobiusAverage S c.value f N x‖ₑ ^ p) :=
      Filter.Eventually.of_forall fun N => rfl
    have hpow : Tendsto (fun N : Scale =>
        ‖mobiusAverage S c.value f N x‖ₑ ^ p) atTop (𝓝 (0 ^ p)) := by
      simpa using hpow'.congr' heq
    simpa [F, ENNReal.zero_rpow_of_pos hp0] using hpow
  have hIntegral : Tendsto
      (fun N : Scale => ∫⁻ x, F N x ∂S.μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := S.μ) (F := F) (f := fun _ : X => 0) bound
      (Filter.Eventually.of_forall hFmeas)
      (Filter.Eventually.of_forall fun N => Filter.Eventually.of_forall (hFbound N))
      hBpowFinite hFlim
    simpa using h
  have hformula (N : Scale) :
      eLpNorm (mobiusAverage S c.value f N) P S.μ =
        (∫⁻ x, F N x ∂S.μ) ^ (1 / p) := by
    have havg : AEStronglyMeasurable (mobiusAverage S c.value f N) S.μ := by
      simpa [mobiusAverage] using
        aestronglyMeasurable_weightedAverage S c.value
          (fun n => (mobiusWeight n : ℂ)) f N hfmeas.aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop havg]
    simp [F, P, ENNReal.toReal_ofReal hp0.le]
  have hroot : Tendsto
      (fun N : Scale => (∫⁻ x, F N x ∂S.μ) ^ (1 / p))
      atTop (𝓝 0) := by
    have hroot' :=
      (ENNReal.continuous_rpow_const (y := 1 / p)).continuousAt.tendsto.comp hIntegral
    have hroot'' : Tendsto
        (fun N : Scale => (∫⁻ x, F N x ∂S.μ) ^ (1 / p))
        atTop (𝓝 (0 ^ (1 / p))) := by
      apply hroot'.congr'
      exact Filter.Eventually.of_forall fun N => rfl
    have hzero : (0 : ℝ≥0∞) ^ (1 / p) = 0 :=
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)
    simpa only [hzero] using hroot''
  apply hroot.congr'
  exact Filter.Eventually.of_forall fun N => (hformula N).symm

/-- The source Möbius-zero conclusion for an arbitrary Lp class, with the
bounded-L² cancellation supplied by the exact discrete D=4 operator-decay
input. The representative is made measurable only for the proof; the
conclusion is invariant under changes on a null set. -/
theorem mobiusAverage_tendsto_zero_of_discreteOperatorDecay
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) {p : ℝ} (hp : 1 < p) (f : X → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) S.μ)
    (hoperatorD4 :
      letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : Scale, 3 ≤ N.1 →
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (primeComparisonIntegerKernel c.value N)‖ +
            ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (mobiusIntegerKernel c.value N)‖ ≤
                B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) :
    (∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x) atTop (𝓝 0)) ∧
    Tendsto (fun N : Scale =>
      eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
      atTop (𝓝 0) := by
  let fm : X → ℂ := hf.aestronglyMeasurable.mk f
  have hfm : MemLp fm (ENNReal.ofReal p) S.μ :=
    hf.ae_eq hf.aestronglyMeasurable.ae_eq_mk
  have hfmmeas : Measurable fm :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hrepr : f =ᵐ[S.μ] fm := hf.aestronglyMeasurable.ae_eq_mk
  have haeFm :=
    mobiusAverage_ae_tendsto_zero_of_discreteOperatorDecay_of_measurable
      S c hp fm hfmmeas hfm hoperatorD4
  have hlpFm :=
    mobiusAverage_eLpNorm_tendsto_zero_of_discreteOperatorDecay_of_measurable
      S c hp fm hfmmeas hfm hoperatorD4
  have hreprAll : ∀ᵐ x ∂S.μ, ∀ N : Scale,
      mobiusAverage S c.value f N x = mobiusAverage S c.value fm N x :=
    ae_all_iff.mpr fun N =>
      (mobiusAverage_ae_eq_of_ae_eq S c.value hrepr N)
  have hae : ∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x) atTop (𝓝 0) := by
    filter_upwards [haeFm, hreprAll] with x hx hxeq
    apply hx.congr'
    exact Filter.Eventually.of_forall fun N => (hxeq N).symm
  have hlp : Tendsto (fun N : Scale =>
      eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
      atTop (𝓝 0) := by
    apply hlpFm.congr'
    exact Filter.Eventually.of_forall fun N => by
      apply eLpNorm_congr_ae
      exact (mobiusAverage_ae_eq_of_ae_eq S c.value hrepr N).symm
  exact ⟨hae, hlp⟩

#print axioms mobiusAverage_ae_tendsto_zero_of_discreteOperatorDecay_of_measurable
#print axioms mobiusAverage_eLpNorm_tendsto_zero_of_discreteOperatorDecay_of_measurable
#print axioms mobiusAverage_tendsto_zero_of_discreteOperatorDecay
end
end FractionalPrimes
