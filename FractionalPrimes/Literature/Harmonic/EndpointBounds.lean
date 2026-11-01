module

public import FractionalPrimes.Literature.Harmonic.Sampling
public import FractionalPrimes.Operators
public import FractionalPrimes.LpConvolutionCLM
public import FractionalPrimes.FiniteSupportLpGeneral
public import FractionalPrimes.Literature.Multiplier.Data
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Endpoint bounds for the sampled continuous model

This file formalizes `ha:endpoints`: the inverse-Fourier kernel of the
continuous-model multiplier is an average of translates of the fixed
Schwartz cutoff, its `ℓ¹` mass is bounded by the sampling constant, and the
resulting convolution has the full `1 ≤ p ≤ ∞` Young bound.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open scoped FourierTransform

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

open FractionalPrimes.Literature.Multiplier
open FractionalPrimes

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : IsProbabilityMeasure torusHaar := torusHaar_isProbability
local instance : IsFiniteMeasure torusHaar := ⟨by simp⟩

/-- The coefficient kernel prescribed by the Fourier-inversion formula in
`ha:endpoints`. -/
def continuousModelKernelCoefficient (c N : ℝ) (m : ℤ) : ℂ :=
  ∫ u in (0 : ℝ)..1,
    continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)

/-- A finite portion of a shifted Schwartz periodization is bounded by its
uniform lattice-sum constant `S_ω`. -/
private theorem schwartz_periodization_finite_le (ω : SchwartzMap ℝ ℂ)
    (s : Finset ℤ) (y : ℝ) :
    (∑ m ∈ s, ‖ω ((m : ℝ) - y)‖) ≤ schwartzExtensionS ω := by
  classical
  let t := s.map (Equiv.neg ℤ).toEmbedding
  let f : ℤ →₀ ℂ := Finsupp.onFinset t
    (fun n => if n ∈ t then (1 : ℂ) else 0) (by
      intro n hn
      by_contra hnt
      simp [hnt] at hn)
  have hsupport : f.support = t := by
    dsimp [f]
    rw [Finsupp.support_onFinset]
    ext n
    simp
  have hweight :
      (∑ n ∈ t, ‖ω ((-y) - (n : ℝ))‖) ≤ schwartzExtensionS ω := by
    simpa [hsupport] using schwartzExtension_weight_sum_le ω f (-y)
  have hsum :
      (∑ m ∈ s, ‖ω ((m : ℝ) - y)‖) =
        ∑ n ∈ t, ‖ω ((-y) - (n : ℝ))‖ := by
    apply Finset.sum_bij (fun m _ => -m)
    · intro m hm
      exact Finset.mem_map.mpr ⟨m, hm, by simp⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      exact neg_injective heq
    · intro n hn
      have hn' := Finset.mem_map.mp hn
      rcases hn' with ⟨m, hm, hmn⟩
      have hmn' : -m = n := by simpa using hmn
      exact ⟨m, hm, hmn'⟩
    · intro m hm
      congr 2
      push_cast
      ring
  rw [hsum]
  exact hweight

/-- Finite sums of the kernel coefficients have the exact uniform bound
`S_ψ`. -/
theorem continuousModelKernelCoefficient_sum_norm_le {c N : ℝ}
    (hc : 1 < c)
    (s : Finset ℤ) :
    (∑ m ∈ s, ‖continuousModelKernelCoefficient c N m‖) ≤
      schwartzExtensionS continuousModelPsiSchwartz := by
  classical
  have hcontinuous (m : ℤ) : Continuous (fun u : ℝ =>
      continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)) := by
    have hc0 : 0 ≤ c := by linarith
    exact continuousModelPsiSchwartz.continuous.comp
      (continuous_const.sub (continuous_const.mul (Real.continuous_rpow_const hc0)))
  have hcontinuousNorm (m : ℤ) : Continuous (fun u : ℝ =>
      ‖continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)‖) :=
    (hcontinuous m).norm
  have hfinite (m : ℤ) : IntervalIntegrable
      (fun u : ℝ => continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c))
      volume 0 1 := (hcontinuous m).intervalIntegrable _ _
  have hfiniteNorm (m : ℤ) : IntervalIntegrable
      (fun u : ℝ => ‖continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)‖)
      volume 0 1 := (hcontinuousNorm m).intervalIntegrable _ _
  have hcontinuousSum : Continuous (fun u : ℝ =>
      ∑ m ∈ s,
        ‖continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)‖) := by
    fun_prop
  have hsumIntegrable : IntervalIntegrable
      (fun u : ℝ => ∑ m ∈ s,
        ‖continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)‖)
      volume 0 1 := hcontinuousSum.intervalIntegrable _ _
  have hconstantIntegrable : IntervalIntegrable
      (fun _ : ℝ => schwartzExtensionS continuousModelPsiSchwartz)
      volume 0 1 := continuous_const.intervalIntegrable _ _
  calc
    (∑ m ∈ s, ‖continuousModelKernelCoefficient c N m‖) ≤
        ∑ m ∈ s, ∫ u in (0 : ℝ)..1,
          ‖continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ u in (0 : ℝ)..1, ∑ m ∈ s,
          ‖continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)‖ := by
      symm
      exact intervalIntegral.integral_finsetSum (s := s) (fun m hm => hfiniteNorm m)
    _ ≤ ∫ u in (0 : ℝ)..1, schwartzExtensionS continuousModelPsiSchwartz := by
      apply intervalIntegral.integral_mono_on (by norm_num) hsumIntegrable
        hconstantIntegrable
      intro u hu
      exact schwartz_periodization_finite_le continuousModelPsiSchwartz s
        (N ^ c * u ^ c)
    _ = schwartzExtensionS continuousModelPsiSchwartz := by
      simp

/-- The kernel coefficients in `ha:endpoints` are absolutely summable, and
their mass is bounded by `S_ψ`. -/
theorem continuousModelKernelCoefficient_summable {c N : ℝ}
    (hc : 1 < c) :
    Summable (fun m : ℤ => ‖continuousModelKernelCoefficient c N m‖) := by
  exact summable_of_sum_le (f := fun m : ℤ =>
    ‖continuousModelKernelCoefficient c N m‖)
    (c := schwartzExtensionS continuousModelPsiSchwartz)
    (fun m => norm_nonneg _)
    (continuousModelKernelCoefficient_sum_norm_le hc)

theorem continuousModelKernelCoefficient_tsum_norm_le {c N : ℝ}
    (hc : 1 < c) :
    (∑' m : ℤ, ‖continuousModelKernelCoefficient c N m‖) ≤
      schwartzExtensionS continuousModelPsiSchwartz := by
  exact Real.tsum_le_of_sum_le (fun m => norm_nonneg _)
    (continuousModelKernelCoefficient_sum_norm_le hc)

/-- Fourier inversion for the already fixed Schwartz cutoff, in the paper's
`e(t)=exp(2πit)` convention. -/
private theorem continuousModelPsiSchwartz_apply_integral (x : ℝ) :
    continuousModelPsiSchwartz x =
      ∫ ξ : ℝ, continuousModelEtaComplexSchwartz ξ *
        unitFrequencyPhase (x * ξ) := by
  change (𝓕⁻ continuousModelEtaComplexSchwartz) x = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp [unitFrequencyPhase, smul_eq_mul, inner, mul_comm, mul_left_comm, mul_assoc]

private theorem continuousModelEta_eq_zero_of_abs_ge_quarter {x : ℝ}
    (hx : 1 / 4 ≤ |x|) : continuousModelEta x = 0 := by
  have hnot : x ∉ tsupport continuousModelEta := by
    intro hts
    have hts' := continuousModelEta_tsupport_subset hts
    have habs : |x| < (1 / 4 : ℝ) := by
      rw [abs_lt]
      exact ⟨by linarith [hts'.1], hts'.2⟩
    exact (not_lt_of_ge hx) habs
  have hzero : ¬ continuousModelEta x ≠ 0 := by
    intro hne
    have hsupp : x ∈ Function.support continuousModelEta := by
      change continuousModelEta x ≠ 0
      exact hne
    exact hnot (subset_tsupport continuousModelEta hsupp)
  exact not_ne_iff.mp hzero

/-- The cutoff support lies strictly inside the unit-frequency interval, so
its inverse Fourier integral can be taken over one period. -/
private theorem continuousModelEtaPhase_interval_eq (x : ℝ) :
    (∫ ξ in (-(1 / 2 : ℝ))..(1 / 2),
      continuousModelEtaComplexSchwartz ξ * unitFrequencyPhase (x * ξ)) =
      continuousModelPsiSchwartz x := by
  have hsupport : Function.support (fun ξ : ℝ =>
      continuousModelEtaComplexSchwartz ξ * unitFrequencyPhase (x * ξ)) ⊆
      Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro ξ hξ
    change continuousModelEtaComplexSchwartz ξ *
        unitFrequencyPhase (x * ξ) ≠ 0 at hξ
    by_contra hnot
    have hlt : |ξ| < (1 / 4 : ℝ) := by
      by_contra hlarge
      have habs : (1 / 4 : ℝ) ≤ |ξ| := le_of_not_gt hlarge
      have hzero := continuousModelEta_eq_zero_of_abs_ge_quarter habs
      apply hξ
      simp [continuousModelEtaComplexSchwartz_apply, hzero]
    have hinterval : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      rw [Set.mem_Ioc]
      have hlt' := abs_lt.mp hlt
      constructor <;> linarith
    exact hnot hinterval
  calc
    _ = ∫ ξ : ℝ,
        continuousModelEtaComplexSchwartz ξ * unitFrequencyPhase (x * ξ) :=
      intervalIntegral.integral_eq_integral_of_support_subset hsupport
    _ = continuousModelPsiSchwartz x :=
      (continuousModelPsiSchwartz_apply_integral x).symm

/-- The Fourier coefficient of the torus symbol is exactly the averaged
translate of `ψ` stated in `ha:endpoints`. -/
theorem continuousModelKernelCoefficient_eq_fourierCoefficient
    {c N : ℝ} (hc : 1 < c) (m : ℤ) :
    continuousModelKernelCoefficient c N m =
      kernelCoefficient (continuousModelTorusSymbol c N) m := by
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  have hab : a + 1 = b := by norm_num [a, b]
  have hphase (ξ : ℝ) :
      fourier (T := (1 : ℝ)) m (ξ : Torus) =
        unitFrequencyPhase ((m : ℝ) * ξ) := by
    rw [fourier_coe_apply]
    simp [unitFrequencyPhase]
    congr 1
    ring
  have hcoeff :
      kernelCoefficient (continuousModelTorusSymbol c N) m =
        ∫ ξ in a..b,
          (continuousModelEta ξ : ℂ) * continuousModelV c N ξ *
            unitFrequencyPhase ((m : ℝ) * ξ) := by
    rw [kernelCoefficient, fourierCoeff_eq_intervalIntegral
      (f := continuousModelTorusSymbol c N) (n := -m) (a := a)]
    simp only [hab, neg_neg, one_div, inv_one, one_smul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 / 2 : ℝ)] with ξ hξne
    intro hξ
    have hξ' : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa [a, b, Set.uIoc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] using hξ
    have hupper : ξ < (1 / 2 : ℝ) := lt_of_le_of_ne hξ'.2 hξne
    have hξco : ξ ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
      exact ⟨le_of_lt hξ'.1, hupper⟩
    rw [continuousModelTorusSymbol_apply_coe c N hξco, hphase]
    ring
  let F : ℝ → ℝ → ℂ := fun ξ u =>
    (continuousModelEta ξ : ℂ) *
      unitFrequencyPhase (-ξ * N ^ c * u ^ c) *
      unitFrequencyPhase ((m : ℝ) * ξ)
  have hcontinuousF : Continuous (Function.uncurry F) := by
    have hc0 : 0 ≤ c := by linarith
    have hpow : Continuous (fun u : ℝ => u ^ c) := Real.continuous_rpow_const hc0
    have harg : Continuous (fun p : ℝ × ℝ => -p.1 * N ^ c * p.2 ^ c) :=
      continuous_fst.neg.mul continuous_const |>.mul (hpow.comp continuous_snd)
    have hphase1 : Continuous (fun p : ℝ × ℝ =>
        unitFrequencyPhase (-p.1 * N ^ c * p.2 ^ c)) :=
      continuous_unitFrequencyPhase.comp harg
    have hphase2 : Continuous (fun p : ℝ × ℝ =>
        unitFrequencyPhase ((m : ℝ) * p.1)) :=
      continuous_unitFrequencyPhase.comp (continuous_const.mul continuous_fst)
    have heta : Continuous (fun p : ℝ × ℝ => (continuousModelEta p.1 : ℂ)) :=
      (Complex.continuous_ofReal.comp continuousModelEta_contDiff.continuous).comp
        continuous_fst
    change Continuous (fun p : ℝ × ℝ => _)
    dsimp [F]
    exact heta.mul hphase1 |>.mul hphase2
  have hcompact : IsCompact
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcontinuousOnF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := hcontinuousF.continuousOn
  have hintegrableClosed : IntegrableOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) :=
    hcontinuousOnF.integrableOn_compact hcompact
  have hxiSubset : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le (by norm_num [a, b])]
    exact Set.Ioc_subset_Icc_self
  have huSubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num)]
    exact Set.Ioc_subset_Icc_self
  have hrect : IntegrableOn (Function.uncurry F)
      (Set.uIoc a b ×ˢ Set.uIoc (0 : ℝ) 1) (volume.prod volume) :=
    hintegrableClosed.mono_set (Set.prod_mono hxiSubset huSubset)
  have hinnerFactor (ξ : ℝ) :
      (continuousModelEta ξ : ℂ) * continuousModelV c N ξ *
          unitFrequencyPhase ((m : ℝ) * ξ) =
        ∫ u in (0 : ℝ)..1, F ξ u := by
    rw [continuousModelV]
    calc
      _ = (continuousModelEta ξ : ℂ) *
          ((∫ u in (0 : ℝ)..1, unitFrequencyPhase (-ξ * N ^ c * u ^ c)) *
            unitFrequencyPhase ((m : ℝ) * ξ)) := by ring
      _ = (continuousModelEta ξ : ℂ) *
          (∫ u in (0 : ℝ)..1,
            unitFrequencyPhase (-ξ * N ^ c * u ^ c) *
              unitFrequencyPhase ((m : ℝ) * ξ)) := by
        rw [← intervalIntegral.integral_mul_const]
      _ = ∫ u in (0 : ℝ)..1,
          (continuousModelEta ξ : ℂ) *
            (unitFrequencyPhase (-ξ * N ^ c * u ^ c) *
              unitFrequencyPhase ((m : ℝ) * ξ)) := by
        rw [← intervalIntegral.integral_const_mul]
      _ = ∫ u in (0 : ℝ)..1, F ξ u := by
        congr 1
        funext u
        simp [F]
        ring
  have hinner (u : ℝ) :
      ∫ ξ in a..b, F ξ u =
        continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c) := by
    have hphaseProduct (ξ : ℝ) :
        unitFrequencyPhase (-ξ * N ^ c * u ^ c) *
          unitFrequencyPhase ((m : ℝ) * ξ) =
        unitFrequencyPhase (((m : ℝ) - N ^ c * u ^ c) * ξ) := by
      rw [← unitFrequencyPhase_add]
      congr 1
      ring
    have hcongr :
        (∫ ξ in a..b, F ξ u) =
          ∫ ξ in a..b,
            continuousModelEtaComplexSchwartz ξ *
              unitFrequencyPhase (((m : ℝ) - N ^ c * u ^ c) * ξ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with ξ hξ
      change (continuousModelEta ξ : ℂ) *
          unitFrequencyPhase (-ξ * N ^ c * u ^ c) *
            unitFrequencyPhase ((m : ℝ) * ξ) =
          (continuousModelEta ξ : ℂ) *
            unitFrequencyPhase (((m : ℝ) - N ^ c * u ^ c) * ξ)
      calc
        _ = (continuousModelEta ξ : ℂ) *
            (unitFrequencyPhase (-ξ * N ^ c * u ^ c) *
              unitFrequencyPhase ((m : ℝ) * ξ)) := by ring
        _ = (continuousModelEta ξ : ℂ) *
            unitFrequencyPhase (((m : ℝ) - N ^ c * u ^ c) * ξ) := by
          rw [hphaseProduct ξ]
        _ = continuousModelEtaComplexSchwartz ξ *
            unitFrequencyPhase (((m : ℝ) - N ^ c * u ^ c) * ξ) := by
          rw [continuousModelEtaComplexSchwartz_apply]
    rw [hcongr]
    convert continuousModelEtaPhase_interval_eq
      ((m : ℝ) - N ^ c * u ^ c) using 1
  calc
    continuousModelKernelCoefficient c N m =
        ∫ u in (0 : ℝ)..1, ∫ ξ in a..b, F ξ u := by
      rw [continuousModelKernelCoefficient]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with u hu
      exact (hinner u).symm
    _ = ∫ ξ in a..b, ∫ u in (0 : ℝ)..1, F ξ u :=
      (intervalIntegral_intervalIntegral_swap hrect).symm
    _ = ∫ ξ in a..b,
          (continuousModelEta ξ : ℂ) * continuousModelV c N ξ *
            unitFrequencyPhase ((m : ℝ) * ξ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with ξ hξ
      exact (hinnerFactor ξ).symm
    _ = kernelCoefficient (continuousModelTorusSymbol c N) m := hcoeff.symm

/-- The absolutely summable kernel attached to the continuous-model
multiplier. Its coefficients are exactly the finite-endpoint integrals in
`ha:endpoints`. -/
noncomputable def continuousModelEndpointKernel (c N : ℝ) (hc : 1 < c) :
    IntegerL1Kernel where
  coeff := continuousModelKernelCoefficient c N
  summable_norm := continuousModelKernelCoefficient_summable (c := c) (N := N) hc

theorem continuousModelEndpointKernel_coeff (c N : ℝ) (hc : 1 < c)
    (m : ℤ) :
    (continuousModelEndpointKernel c N hc).coeff m =
      ∫ u in (0 : ℝ)..1,
        continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c) := rfl

theorem continuousModelEndpointKernel_norm_sum_le (c N : ℝ) (hc : 1 < c) :
    (∑' m : ℤ, ‖(continuousModelEndpointKernel c N hc).coeff m‖) ≤
      schwartzExtensionS continuousModelPsiSchwartz :=
  continuousModelKernelCoefficient_tsum_norm_le (c := c) (N := N) hc

/-- The all-exponent `Lᵖ` realization of the continuous model.  On finite
inputs it agrees pointwise with `continuousModelC`; the definition uses the
same kernel for every `1 ≤ p ≤ ∞`. -/
noncomputable def continuousModelEndpointOperator {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (c N : ℝ) (hc : 1 < c) (_hN : 0 < N) :
    Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ p (Measure.count : Measure ℤ) :=
  integerKernelLpConvolutionCLM (p := p) (continuousModelEndpointKernel c N hc)

/-- The operator norm bound for the `Lᵖ` extension, including both endpoints. -/
theorem continuousModelEndpointOperator_norm_le {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {c N : ℝ} (hc : 1 < c) (hN : 0 < N) :
    ‖continuousModelEndpointOperator (p := p) c N hc hN‖ ≤
      schwartzExtensionS continuousModelPsiSchwartz := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (schwartzExtensionS_nonneg continuousModelPsiSchwartz)
  intro f
  change ‖integerKernelLpConvolutionCLM (p := p)
      (continuousModelEndpointKernel c N hc) f‖ ≤ _
  calc
    ‖integerKernelLpConvolutionCLM (p := p)
        (continuousModelEndpointKernel c N hc) f‖ ≤
        (∑' m : ℤ,
          ‖(continuousModelEndpointKernel c N hc).coeff m‖) * ‖f‖ :=
      integerKernelLpConvolutionCLM_norm_le _ f
    _ ≤ schwartzExtensionS continuousModelPsiSchwartz * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (continuousModelEndpointKernel_norm_sum_le c N hc) (norm_nonneg _)

/-- Every finitely supported sequence is in counting-measure `Lᵖ`, including
`p=∞`; this records the finite-input domain needed to identify the all-`p`
extension with `continuousModelC`. -/
theorem continuousModelFinsupp_memLp {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : ℤ →₀ ℂ) : MemLp (f : ℤ → ℂ) p (Measure.count : Measure ℤ) := by
  by_cases hpTop : p = ∞
  · let C : ℝ := ∑ k ∈ f.support, ‖f k‖
    have hmeas : AEStronglyMeasurable (f : ℤ → ℂ) Measure.count :=
      (measurable_of_countable (f : ℤ → ℂ)).aestronglyMeasurable
    have hbound : ∀ᵐ k ∂(Measure.count : Measure ℤ),
        ‖(f : ℤ → ℂ) k‖ ≤ C := by
      apply Filter.Eventually.of_forall
      intro k
      by_cases hk : k ∈ f.support
      · dsimp [C]
        exact Finset.single_le_sum (fun i hi => norm_nonneg (f i)) hk
      · have hkzero : f k = 0 := Finsupp.notMem_support_iff.mp hk
        rw [hkzero]
        dsimp [C]
        simpa using (Finset.sum_nonneg fun i hi => norm_nonneg (f i))
    rw [hpTop]
    exact memLp_top_of_bound hmeas C hbound
  · have hp0 : p ≠ 0 := by
      intro hpzero
      rw [hpzero] at hp
      norm_num at hp
    have htruncate : MemLp
        (fun k : ℤ => if k ∈ f.support then (f : ℤ → ℂ) k else 0)
        p (Measure.count : Measure ℤ) :=
      finiteSupportMemLpGeneral hp0 hpTop hp f.support (f : ℤ → ℂ)
    have hEq : (fun k : ℤ => if k ∈ f.support then (f : ℤ → ℂ) k else 0) =ᵐ[
        (Measure.count : Measure ℤ)] (f : ℤ → ℂ) := by
      apply Filter.Eventually.of_forall
      intro k
      by_cases hk : k ∈ f.support
      · simp [hk]
      · simp [hk, Finsupp.notMem_support_iff.mp hk]
    exact (memLp_congr_ae hEq).mp htruncate

/-- The counting-measure `Lᵖ` representative of a finite sequence. -/
noncomputable def continuousModelFinsuppCountLp {p : ℝ≥0∞}
    (hp : 1 ≤ p) (f : ℤ →₀ ℂ) : Lp ℂ p (Measure.count : Measure ℤ) :=
  (continuousModelFinsupp_memLp hp f).toLp (f : ℤ → ℂ)

theorem continuousModelFinsuppCountLp_apply {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : ℤ →₀ ℂ) (k : ℤ) :
    (continuousModelFinsuppCountLp hp f : ℤ → ℂ) k = f k := by
  exact ae_count_int_iff_forall.mp
    (MemLp.coeFn_toLp (continuousModelFinsupp_memLp hp f)) k

/-- The finite-input convolution formula for any absolutely summable
integer kernel, exposed for the source Fourier projection adapter. -/
theorem integerKernelConvolution_eq_finsupp_sum (K : IntegerL1Kernel)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    integerKernelConvolution K (f : ℤ → ℂ) x =
      ∑ n ∈ f.support, f n * K.coeff (x - n) := by
  classical
  let s := f.support.image (fun n : ℤ => x - n)
  have hzero (m : ℤ) (hm : m ∉ s) : K.coeff m * f (x - m) = 0 := by
    have hnot : x - m ∉ f.support := by
      intro hmem
      apply hm
      exact Finset.mem_image.mpr ⟨x - m, hmem, by simp⟩
    have hfzero : f (x - m) = 0 := by
      exact Finsupp.notMem_support_iff.mp hnot
    simp [hfzero]
  have hexists := integerKernelConvolutionExistsAt_of_finiteInputSupport
    K (f : ℤ → ℂ) x f.support (by
      intro j hj
      exact Finsupp.notMem_support_iff.mp hj)
  rw [integerKernelConvolution_eq_tsum K (f : ℤ → ℂ) x hexists]
  rw [tsum_eq_sum (s := s) hzero]
  symm
  apply Finset.sum_bij (fun n _ => x - n)
  · intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    omega
  · intro m hm
    have hm' := Finset.mem_image.mp hm
    rcases hm' with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · intro n hn
    rw [show x - (x - n) = n by omega, mul_comm]

/-- Fourier inversion identifies the defined `L²` multiplier with convolution
by the kernel in `ha:endpoints`, at every output coordinate. -/
theorem continuousModelC_apply_eq_integerKernelConvolution
    {c N : ℝ} (hc : 1 < c) (hN : 0 < N) (f : ℤ →₀ ℂ) (x : ℤ) :
    continuousModelC c hc N hN f x =
      integerKernelConvolution (continuousModelEndpointKernel c N hc)
        (f : ℤ → ℂ) x := by
  let g : Lp ℂ 2 torusHaar :=
    continuousModelSymbolLp c N hc •
      sequenceToCircleL2 (finiteSequenceL2 f)
  have hsymbol :
      (continuousModelSymbolLp c N hc : Torus → ℂ) =ᵐ[torusHaar]
        continuousModelTorusSymbol c N := by
    unfold continuousModelSymbolLp
    let hmem : MemLp (continuousModelTorusSymbol c N) ⊤ torusHaar := by
      have hmeas : AEStronglyMeasurable
          (continuousModelTorusSymbol c N) torusHaar :=
        (continuousModelTorusSymbol_continuous c N hc).measurable.aestronglyMeasurable
      have hbound : ∀ᵐ ξ ∂torusHaar,
          ‖continuousModelTorusSymbol c N ξ‖ ≤ 1 :=
        Filter.Eventually.of_forall (continuousModelTorusSymbol_norm_le_one c N)
      exact MemLp.of_bound hmeas 1 hbound
    change (hmem.toLp (continuousModelTorusSymbol c N) : Torus → ℂ) =ᵐ[torusHaar]
      continuousModelTorusSymbol c N
    exact MemLp.coeFn_toLp hmem
  have hseq :
      (sequenceToCircleL2 (finiteSequenceL2 f) : Torus → ℂ) =ᵐ[torusHaar]
        finiteFourierTransform f := by
    rw [sequenceToCircleL2_finiteSequence]
    exact finiteFourierTransformLp_coeFn f
  have hprod : (g : Torus → ℂ) =ᵐ[torusHaar]
      (fun ξ => continuousModelTorusSymbol c N ξ * finiteFourierTransform f ξ) := by
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (continuousModelSymbolLp c N hc) (sequenceToCircleL2 (finiteSequenceL2 f)),
      hsymbol, hseq] with ξ hmul hsymbolξ hseqξ
    calc
      g ξ = (continuousModelSymbolLp c N hc : Torus → ℂ) ξ *
          (sequenceToCircleL2 (finiteSequenceL2 f) : Torus → ℂ) ξ := by
        change (continuousModelSymbolLp c N hc •
          sequenceToCircleL2 (finiteSequenceL2 f)) ξ = _
        simpa only [Pi.smul_apply', smul_eq_mul] using hmul
      _ = continuousModelTorusSymbol c N ξ * finiteFourierTransform f ξ := by
        rw [hsymbolξ, hseqξ]
  have hterm (n : ℤ) : Integrable
      (fun ξ : Torus => f n *
        (continuousModelTorusSymbol c N ξ * fourier (T := (1 : ℝ)) (-n) ξ))
      torusHaar := by
    have hmeas : Measurable (fun ξ : Torus => f n *
        (continuousModelTorusSymbol c N ξ * fourier (T := (1 : ℝ)) (-n) ξ)) :=
      measurable_const.mul
        ((continuousModelTorusSymbol_continuous c N hc).measurable.mul
          (map_continuous (fourier (T := (1 : ℝ)) (-n))).measurable)
    apply Integrable.of_bound hmeas.aestronglyMeasurable ‖f n‖
    filter_upwards [] with ξ
    have hfourier : ‖fourier (T := (1 : ℝ)) (-n) ξ‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    calc
      ‖f n * (continuousModelTorusSymbol c N ξ *
          fourier (T := (1 : ℝ)) (-n) ξ)‖ =
          ‖f n‖ * (‖continuousModelTorusSymbol c N ξ‖ *
            ‖fourier (T := (1 : ℝ)) (-n) ξ‖) := by simp
      _ ≤ ‖f n‖ * (1 * 1) := by
        apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [hfourier]
        exact mul_le_mul_of_nonneg_right
          (continuousModelTorusSymbol_norm_le_one c N ξ) (by norm_num)
      _ = ‖f n‖ := by ring
  have hfun :
      (fun ξ : Torus => continuousModelTorusSymbol c N ξ *
        finiteFourierTransform f ξ) =
      ∑ n ∈ f.support, (fun ξ : Torus => f n *
        (continuousModelTorusSymbol c N ξ * fourier (T := (1 : ℝ)) (-n) ξ)) := by
    funext ξ
    simp only [finiteFourierTransform, Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hcoef :
      fourierCoeff (fun ξ : Torus => continuousModelTorusSymbol c N ξ *
        finiteFourierTransform f ξ) (-x) =
      ∑ n ∈ f.support, f n *
        kernelCoefficient (continuousModelTorusSymbol c N) (x - n) := by
    rw [hfun]
    have hsum := fourierCoeff.sum f.support
      (fun n ξ => f n *
        (continuousModelTorusSymbol c N ξ * fourier (T := (1 : ℝ)) (-n) ξ))
      (by intro n hn; exact hterm n)
    rw [hsum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [fourierCoeff.const_mul, fourierCoeff_mul_fourier_shift]
    rw [kernelCoefficient]
    congr 2
    omega
  have hrepr : continuousModelC c hc N hN f x = fourierCoeff g (-x) := by
    change sequenceToCircleL2.symm g x = _
    rw [sequenceToCircleL2_symm_apply]
    exact fourierBasis_repr g (-x)
  have hcoeff' : fourierCoeff g (-x) =
      fourierCoeff (fun ξ => continuousModelTorusSymbol c N ξ *
        finiteFourierTransform f ξ) (-x) :=
    congrFun (fourierCoeff_congr_ae hprod) (-x)
  rw [hrepr, hcoeff', hcoef, integerKernelConvolution_eq_finsupp_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [continuousModelEndpointKernel_coeff]
  rw [(continuousModelKernelCoefficient_eq_fourierCoefficient hc (x - n)).symm,
    continuousModelKernelCoefficient]

/-- On every finite input, the all-exponent convolution extension agrees at
each integer with the original Fourier-multiplier definition of `C_N`. -/
theorem continuousModelEndpointOperator_apply_finsupp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {c N : ℝ} (hc : 1 < c) (hN : 0 < N)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    ((continuousModelEndpointOperator (p := p) c N hc hN
        (continuousModelFinsuppCountLp (p := p) (Fact.out : 1 ≤ p) f) :
        Lp ℂ p (Measure.count : Measure ℤ)) : ℤ → ℂ) x =
      continuousModelC c hc N hN f x := by
  have hinput :
      (continuousModelFinsuppCountLp (p := p) (Fact.out : 1 ≤ p) f :
        ℤ → ℂ) = (f : ℤ → ℂ) := by
    funext k
    exact continuousModelFinsuppCountLp_apply (p := p) (Fact.out : 1 ≤ p) f k
  calc
    _ = integerKernelConvolution (continuousModelEndpointKernel c N hc)
        (continuousModelFinsuppCountLp (p := p) (Fact.out : 1 ≤ p) f :
          ℤ → ℂ) x := by
      change (integerKernelLpConvolutionCLM (p := p)
        (continuousModelEndpointKernel c N hc)
        (continuousModelFinsuppCountLp (p := p) (Fact.out : 1 ≤ p) f) :
          ℤ → ℂ) x = _
      rw [integerKernelLpConvolutionCLM_apply]
      exact integerKernelLpConvolution_apply_eq_integerKernelConvolution
        (continuousModelEndpointKernel c N hc)
        (continuousModelFinsuppCountLp (p := p) (Fact.out : 1 ≤ p) f) x
    _ = integerKernelConvolution (continuousModelEndpointKernel c N hc)
        (f : ℤ → ℂ) x := by rw [hinput]
    _ = continuousModelC c hc N hN f x :=
      (continuousModelC_apply_eq_integerKernelConvolution hc hN f x).symm

/-- `ha:endpoints`: the exact inverse-Fourier kernel formula, its uniform
`ℓ¹` bound, and the full `1 ≤ p ≤ ∞` operator estimate.  The convolution
identity is stated on the finitely supported domain of `continuousModelC`;
`continuousModelEndpointOperator` is its bounded `Lᵖ` extension. -/
theorem continuousModelEndpointBounds (c N : ℝ) (hc : 1 < c) (hN : 0 < N) :
    (∀ m : ℤ,
      (continuousModelEndpointKernel c N hc).coeff m =
        ∫ u in (0 : ℝ)..1,
          continuousModelPsiSchwartz ((m : ℝ) - N ^ c * u ^ c)) ∧
    (∑' m : ℤ, ‖(continuousModelEndpointKernel c N hc).coeff m‖) ≤
      schwartzExtensionS continuousModelPsiSchwartz ∧
    (∀ {p : ℝ≥0∞} [Fact (1 ≤ p)],
      ‖continuousModelEndpointOperator (p := p) c N hc hN‖ ≤
        schwartzExtensionS continuousModelPsiSchwartz) ∧
    (∀ (f : ℤ →₀ ℂ) (x : ℤ),
      continuousModelC c hc N hN f x =
        integerKernelConvolution (continuousModelEndpointKernel c N hc)
          (f : ℤ → ℂ) x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    exact continuousModelEndpointKernel_coeff c N hc m
  · exact continuousModelEndpointKernel_norm_sum_le c N hc
  · intro p hp
    exact continuousModelEndpointOperator_norm_le hc hN
  · intro f x
    exact continuousModelC_apply_eq_integerKernelConvolution hc hN f x

end

end FractionalPrimes.Literature.Harmonic
