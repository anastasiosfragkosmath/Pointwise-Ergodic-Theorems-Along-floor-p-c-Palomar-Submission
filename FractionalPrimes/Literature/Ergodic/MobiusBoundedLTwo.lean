module

public import FractionalPrimes.Literature.Ergodic.MobiusSlowScales
public import FractionalPrimes.Literature.Ergodic.MobiusSubsequenceCompletion
public import FractionalPrimes.Literature.Ergodic.ArithmeticSystemOperatorDecay
public import FractionalPrimes.ShortVariation
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section
namespace FractionalPrimes
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

private theorem mobiusSlowScale_log_rpow_bound {k : ℕ} (hk : 4 ≤ k) :
    (Real.log (mobiusSlowScale k : ℝ)) ^ (-4 : ℝ) ≤
      (Real.log 2 / 2) ^ (-4 : ℝ) * ((k : ℝ) ^ 2)⁻¹ := by
  let a : ℝ := Real.log 2 / 2
  have ha : 0 < a := by
    dsimp [a]
    exact half_pos (Real.log_pos (by norm_num))
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (by omega : 0 < k)
  have hsqrtpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hprodpos : 0 < a * Real.sqrt (k : ℝ) := mul_pos ha hsqrtpos
  have hlog := mobiusSlowScale_log_bounds hk
  have hmono := Real.rpow_le_rpow_of_nonpos hprodpos hlog.1
    (by norm_num : (-4 : ℝ) ≤ 0)
  have hpower : (a * Real.sqrt (k : ℝ)) ^ (-4 : ℝ) =
      a ^ (-4 : ℝ) * ((k : ℝ) ^ 2)⁻¹ := by
    have hleft : (a * Real.sqrt (k : ℝ)) ^ (-4 : ℝ) =
        ((a * Real.sqrt (k : ℝ)) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hprodpos)]
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    have hright : a ^ (-4 : ℝ) = (a ^ 4)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt ha)]
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    have hsquare : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
    have hsquare4 : (Real.sqrt (k : ℝ)) ^ 4 = (k : ℝ) ^ 2 := by
      calc
        (Real.sqrt (k : ℝ)) ^ 4 = ((Real.sqrt (k : ℝ)) ^ 2) ^ 2 := by ring
        _ = (k : ℝ) ^ 2 := by rw [hsquare]
    rw [hleft, hright, mul_pow, hsquare4]
    field_simp [ne_of_gt ha, ne_of_gt hkpos]
  simpa [a, hpower] using hmono

/-- Summability of the Möbius averages along the explicit slow scales follows
from the exact D=4 `L²` operator-decay output.  The constant in `hdecay` may
depend on the input function, as it does after transference. -/
theorem mobiusSlowScale_eLpNorm_summable_of_log_decay
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (g : X → ℂ) (hg2 : MemLp g (2 : ℝ≥0∞) S.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ N : Scale, 3 ≤ N.1 →
      eLpNorm (mobiusAverage S c g N) (2 : ℝ≥0∞) S.μ ≤
        ENNReal.ofReal (C * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ))) :
    ∑' k : ℕ,
      eLpNorm (mobiusAverage S c g ⟨mobiusSlowScale k, mobiusSlowScale_pos k⟩)
        (2 : ℝ≥0∞) S.μ ≠ ∞ := by
  let G : ℝ := (eLpNorm g (2 : ℝ≥0∞) S.μ).toReal
  let K : ℝ := C * (Real.log 2 / 2) ^ (-4 : ℝ)
  let majorant : ℕ → ℝ := fun k =>
    8 * G * (1 / 2 : ℝ) ^ k + K * ((k : ℝ) ^ 2)⁻¹
  have hGnonneg : 0 ≤ G := ENNReal.toReal_nonneg
  have hKnonneg : 0 ≤ K := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hG_eq : ENNReal.ofReal G = eLpNorm g (2 : ℝ≥0∞) S.μ :=
    ENNReal.ofReal_toReal hg2.eLpNorm_ne_top
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hpoly : Summable (fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hmajorant : Summable majorant := by
    have h₁ : Summable (fun k : ℕ => 8 * G * (1 / 2 : ℝ) ^ k) :=
      hgeom.mul_left (8 * G)
    have h₂ : Summable (fun k : ℕ => K * ((k : ℝ) ^ 2)⁻¹) :=
      hpoly.mul_left K
    exact h₁.add h₂ |>.congr fun k => by simp [majorant]
  have hmajorant_nonneg (k : ℕ) : 0 ≤ majorant k := by
    simp only [majorant]
    positivity
  have hterm_bound (k : ℕ) :
      eLpNorm
        (mobiusAverage S c g ⟨mobiusSlowScale k, mobiusSlowScale_pos k⟩)
        (2 : ℝ≥0∞) S.μ ≤ ENNReal.ofReal (majorant k) := by
    by_cases hk : 4 ≤ k
    · have hroot : 2 ≤ Real.sqrt (k : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        have hkreal : (4 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ Real.sqrt (k : ℝ) := by
        calc
          (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
          _ ≤ (2 : ℝ) ^ Real.sqrt (k : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hroot
      have hN : 3 ≤ mobiusSlowScale k := by
        dsimp [mobiusSlowScale]
        apply Nat.le_floor
        exact_mod_cast (show (3 : ℝ) ≤ (2 : ℝ) ^ Real.sqrt (k : ℝ) by linarith)
      have hdec := hdecay ⟨mobiusSlowScale k, mobiusSlowScale_pos k⟩ hN
      have hlogpow := mobiusSlowScale_log_rpow_bound hk
      have hreal : C * (Real.log (mobiusSlowScale k : ℝ)) ^ (-4 : ℝ) ≤
          majorant k := by
        have htail : C * (Real.log (mobiusSlowScale k : ℝ)) ^ (-4 : ℝ) ≤
            K * ((k : ℝ) ^ 2)⁻¹ := by
          calc
            _ ≤ C * ((Real.log 2 / 2) ^ (-4 : ℝ) * ((k : ℝ) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hlogpow hC
            _ = K * ((k : ℝ) ^ 2)⁻¹ := by simp [K, mul_assoc]
        have hgeomTerm : 0 ≤ 8 * G * (1 / 2 : ℝ) ^ k := by positivity
        dsimp [majorant]
        linarith [hGnonneg, htail, hgeomTerm]
      exact hdec.trans (ENNReal.ofReal_le_ofReal (by
        exact hreal))
    · have hN : mobiusSlowScale k > 0 := mobiusSlowScale_pos k
      have hcontract := eLpNorm_mobiusAverage_le_self S c g
        ⟨mobiusSlowScale k, hN⟩ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        hg2.aestronglyMeasurable
      have hk' : k < 4 := by omega
      have hsmall : 1 ≤ 8 * (1 / 2 : ℝ) ^ k := by
        interval_cases k <;> norm_num
      have hreal : G ≤ majorant k := by
        dsimp [majorant]
        have hterm : G ≤ 8 * G * (1 / 2 : ℝ) ^ k := by
          calc
            G = G * 1 := by ring
            _ ≤ G * (8 * (1 / 2 : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_left hsmall hGnonneg
            _ = 8 * G * (1 / 2 : ℝ) ^ k := by ring
        have htail : 0 ≤ K * ((k : ℝ) ^ 2)⁻¹ := by positivity
        linarith
      calc
        _ ≤ eLpNorm g (2 : ℝ≥0∞) S.μ := hcontract
        _ = ENNReal.ofReal G := hG_eq.symm
        _ ≤ ENNReal.ofReal (majorant k) := ENNReal.ofReal_le_ofReal hreal
  have htsum_le :
      (∑' k : ℕ,
        eLpNorm (mobiusAverage S c g ⟨mobiusSlowScale k, mobiusSlowScale_pos k⟩)
          (2 : ℝ≥0∞) S.μ) ≤
      ∑' k : ℕ, ENNReal.ofReal (majorant k) :=
    ENNReal.tsum_le_tsum hterm_bound
  have htsum_majorant :
      (∑' k : ℕ, ENNReal.ofReal (majorant k)) =
        ENNReal.ofReal (∑' k : ℕ, majorant k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hmajorant_nonneg hmajorant]
  have hmajorant_ne_top :
      (∑' k : ℕ, ENNReal.ofReal (majorant k)) ≠ ∞ := by
    rw [htsum_majorant]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hmajorant_ne_top htsum_le

/-- The D=4 source `L²` decay gives almost-everywhere cancellation on the
explicit slow subsequence. -/
theorem mobiusSlowScale_ae_tendsto_zero_of_log_decay
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (g : X → ℂ) (hg2 : MemLp g (2 : ℝ≥0∞) S.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ N : Scale, 3 ≤ N.1 →
      eLpNorm (mobiusAverage S c g N) (2 : ℝ≥0∞) S.μ ≤
        ENNReal.ofReal (C * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ))) :
    ∀ᵐ x ∂S.μ, Tendsto
      (fun k : ℕ => mobiusAverage S c g
        ⟨mobiusSlowScale k, mobiusSlowScale_pos k⟩ x) atTop (𝓝 0) := by
  have htsum := mobiusSlowScale_eLpNorm_summable_of_log_decay S c g hg2 C hC hdecay
  have hpoint := summable_norm_of_tsum_eLpNorm_ne_top
    (by norm_num : 1 ≤ (2 : ℝ≥0∞)) htsum
  filter_upwards [hpoint] with x hx
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa using hx.tendsto_atTop_zero

/-- Source `er:mobius-dense`: the L² decay hypothesis gives slow-subsequence
cancellation, and boundedness transfers it to all positive integer scales. -/
theorem mobiusAverage_ae_tendsto_zero_of_bounded_ltwo_log_decay
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (g : X → ℂ) (hg2 : MemLp g (2 : ℝ≥0∞) S.μ)
    (hgTop : MemLp g ∞ S.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ N : Scale, 3 ≤ N.1 →
      eLpNorm (mobiusAverage S c g N) (2 : ℝ≥0∞) S.μ ≤
        ENNReal.ofReal (C * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ))) :
    ∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => mobiusAverage S c g N x)
      atTop (𝓝 0) := by
  have hsub := mobiusSlowScale_ae_tendsto_zero_of_log_decay
    S c g hg2 C hC hdecay
  exact mobiusAverage_ae_tendsto_zero_of_bounded_subsequence S c g hgTop
    mobiusSlowScale mobiusSlowScale_pos mobiusSlowScale_monotone
    tendsto_mobiusSlowScale mobiusSlowScale_relativeGap_tendsto_zero hsub

/-- The transferred Möbius average is bounded by the discrete Möbius
convolution operator norm, as a consequence of the checked combined
arithmetic operator bound. -/
theorem mobiusAverage_eLpNorm_le_of_discreteOperatorBound
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (N : Scale) (B : ℝ)
    (hdisc : letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
          (primeComparisonIntegerKernel c N)‖ +
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
          (mobiusIntegerKernel c N)‖ ≤ B)
    (g : X → ℂ) (hg : MemLp g (2 : ℝ≥0∞) S.μ) :
    eLpNorm (mobiusAverage S c g N) (2 : ℝ≥0∞) S.μ ≤
      ENNReal.ofReal B * eLpNorm g (2 : ℝ≥0∞) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) S.μ := by simpa using hg
  have hsystem := arithmeticComparisonSystemNorm_le_of_discrete
    (S := S) (p := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) c N B hdisc g hg'
  have hsum :
      eLpNorm (vonMangoldtAverage S c g N - unweightedAverage S c g N)
          (2 : ℝ≥0∞) S.μ +
        eLpNorm (mobiusAverage S c g N) (2 : ℝ≥0∞) S.μ ≤
          ENNReal.ofReal B * eLpNorm g (2 : ℝ≥0∞) S.μ := by
    simpa using hsystem
  exact (le_add_of_nonneg_left (bot_le :
      (0 : ℝ≥0∞) ≤ eLpNorm
        (vonMangoldtAverage S c g N - unweightedAverage S c g N)
        (2 : ℝ≥0∞) S.μ)).trans hsum

/-- Full bounded-class source assembly for `er:mobius-dense`, conditional only
on the D=4 output of the approved arithmetic operator-decay node. -/
theorem mobiusAverage_ae_tendsto_zero_of_bounded_ltwo_of_discreteOperatorDecay
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (g : X → ℂ) (hg2 : MemLp g (2 : ℝ≥0∞) S.μ)
    (hgTop : MemLp g ∞ S.μ)
    (hoperatorD4 :
      letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : Scale, 3 ≤ N.1 →
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (primeComparisonIntegerKernel c N)‖ +
            ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (mobiusIntegerKernel c N)‖ ≤
                B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) :
    ∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => mobiusAverage S c g N x)
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hdisc⟩ := hoperatorD4
  let G : ℝ := (eLpNorm g (2 : ℝ≥0∞) S.μ).toReal
  have hGnonneg : 0 ≤ G := ENNReal.toReal_nonneg
  have hG_eq : ENNReal.ofReal G = eLpNorm g (2 : ℝ≥0∞) S.μ :=
    ENNReal.ofReal_toReal hg2.eLpNorm_ne_top
  have hdecay : ∀ N : Scale, 3 ≤ N.1 →
      eLpNorm (mobiusAverage S c g N) (2 : ℝ≥0∞) S.μ ≤
        ENNReal.ofReal ((B * G) * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) := by
    intro N hN
    have hlogpos : 0 < Real.log (N.1 : ℝ) := by
      apply Real.log_pos
      have hNreal : (3 : ℝ) ≤ N.1 := by exact_mod_cast hN
      exact lt_of_lt_of_le (by norm_num) hNreal
    have hlogpowpos : 0 < (Real.log (N.1 : ℝ)) ^ (-4 : ℝ) :=
      Real.rpow_pos_of_pos hlogpos _
    have hBnonneg : 0 ≤ B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ) :=
      mul_nonneg hB hlogpowpos.le
    have hsingle := mobiusAverage_eLpNorm_le_of_discreteOperatorBound
      S c N (B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) (hdisc N hN) g hg2
    calc
      _ ≤ ENNReal.ofReal (B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) *
          eLpNorm g (2 : ℝ≥0∞) S.μ := hsingle
      _ = ENNReal.ofReal
          ((B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) * G) := by
            rw [← hG_eq, ← ENNReal.ofReal_mul hBnonneg]
      _ = ENNReal.ofReal
          ((B * G) * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ)) := by
            congr 1
            ring
  exact mobiusAverage_ae_tendsto_zero_of_bounded_ltwo_log_decay
    S c g hg2 hgTop (B * G) (mul_nonneg hB hGnonneg) hdecay

#print axioms mobiusSlowScale_eLpNorm_summable_of_log_decay
#print axioms mobiusSlowScale_ae_tendsto_zero_of_log_decay
#print axioms mobiusAverage_ae_tendsto_zero_of_bounded_ltwo_log_decay
#print axioms mobiusAverage_eLpNorm_le_of_discreteOperatorBound
#print axioms mobiusAverage_ae_tendsto_zero_of_bounded_ltwo_of_discreteOperatorDecay
end
end FractionalPrimes
