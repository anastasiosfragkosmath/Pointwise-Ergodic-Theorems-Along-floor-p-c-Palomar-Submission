module

public import FractionalPrimes.Literature.Multiplier.BaseKernelL1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute convergence and reconstruction of the dyadic kernel

This module proves the final absolute-convergence and Fourier-coefficient
reconstruction clauses of `lp:dyadic-kernel` from the approved finite
telescoping identity and the checked dyadic pointwise bounds.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open Filter
open scoped FourierTransform Interval Topology

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : IsProbabilityMeasure torusHaar := torusHaar_isProbability

private theorem ψ_eq_zero_of_abs_ge_quarter {x : ℝ}
    (hx : 1 / 4 ≤ |x|) : ψ x = 0 := by
  have hnot : x ∉ tsupport ψ := by
    intro hts
    have hts' := tsupport_ψ_subset hts
    have habs : |x| < 1 / 4 := by
      rw [abs_lt]
      exact ⟨by linarith [hts'.1], hts'.2⟩
    exact (not_lt_of_ge hx) habs
  have hzero : ¬ ψ x ≠ 0 := by
    intro hne
    have hmem : x ∈ Function.support ψ := by
      change ψ x ≠ 0
      exact hne
    exact hnot (subset_tsupport ψ hmem)
  exact not_ne_iff.mp hzero

theorem fixedCutoffTorus_continuous : Continuous fixedCutoffTorus := by
  have hleft : ψ (-(1 / 2 : ℝ)) = 0 := by
    exact ψ_eq_zero_of_abs_ge_quarter (by norm_num)
  have hright : ψ (1 / 2 : ℝ) = 0 := by
    exact ψ_eq_zero_of_abs_ge_quarter (by norm_num)
  have hend : ψ (-(1 / 2 : ℝ)) = ψ (-(1 / 2 : ℝ) + 1) := by
    rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num, hleft, hright]
  simpa [fixedCutoffTorus] using
    (AddCircle.liftIoc_continuous (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
      hend (ψ_contDiff.continuous.continuousOn))

theorem fixedCutoffTorus_bounds (ξ : Torus) :
    0 ≤ fixedCutoffTorus ξ ∧ fixedCutoffTorus ξ ≤ 1 := by
  let y : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ
  have hy : (y : Torus) = ξ := AddCircle.coe_equivIoc
  have hvalue : fixedCutoffTorus ξ = ψ y := by
    rw [← hy]
    simp [fixedCutoffTorus, AddCircle.liftIoc, y]
  rw [hvalue]
  exact ⟨ψ_nonneg _, ψ_le_one _⟩

private theorem baseTorusMultiplierSymbol_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) : Integrable (baseTorusMultiplierSymbol h) torusHaar := by
  obtain ⟨C, hC⟩ := h.bounded
  have hC_nonneg : 0 ≤ C := (norm_nonneg (m 0)).trans (hC 0)
  have hcutMeas : Measurable
      (fun ξ : Torus => ((1 - fixedCutoffTorus ξ : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp
      (measurable_const.sub fixedCutoffTorus_continuous.measurable)
  have hmeas : AEStronglyMeasurable (baseTorusMultiplierSymbol h) torusHaar := by
    exact ((torusSymbol_measurable h).mul hcutMeas).aestronglyMeasurable
  have hbound : ∀ᵐ ξ ∂torusHaar, ‖baseTorusMultiplierSymbol h ξ‖ ≤ C := by
    filter_upwards with ξ
    have hcut := fixedCutoffTorus_bounds ξ
    have hcutnorm : ‖((1 - fixedCutoffTorus ξ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hcut.2], by linarith [hcut.1]⟩
    have hsymbol := torusSymbol_norm_le h C hC ξ
    change ‖torusSymbol h ξ * ((1 - fixedCutoffTorus ξ : ℝ) : ℂ)‖ ≤ C
    rw [norm_mul]
    calc
      ‖torusSymbol h ξ‖ * ‖((1 - fixedCutoffTorus ξ : ℝ) : ℂ)‖ ≤ C * 1 :=
        mul_le_mul hsymbol hcutnorm (norm_nonneg _) hC_nonneg
      _ = C := by ring
  exact Integrable.of_bound hmeas C hbound

private theorem dyadicSymbolPiece_zero_at_half {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) {x : ℝ} (hx : |x| = 1 / 2) :
    dyadicSymbolPiece h j x = 0 := by
  by_contra hne
  have hsupp : x ∈ Function.support (dyadicSymbolPiece h j) := by
    change dyadicSymbolPiece h j x ≠ 0
    exact hne
  have hIcc := dyadicSymbolPiece_support_Icc h j hsupp
  have habs : |x| ≤ dyadicScale j / 4 := abs_le.mpr hIcc
  have ht := dyadicScale_le_one j
  rw [hx] at habs
  norm_num at habs
  linarith

private theorem dyadicTorusSymbolPiece_continuous {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Continuous (dyadicTorusSymbolPiece h j) := by
  have hleft : dyadicSymbolPiece h j (-(1 / 2 : ℝ)) = 0 :=
    dyadicSymbolPiece_zero_at_half h j (by norm_num)
  have hright : dyadicSymbolPiece h j (1 / 2 : ℝ) = 0 :=
    dyadicSymbolPiece_zero_at_half h j (by norm_num)
  have hend : dyadicSymbolPiece h j (-(1 / 2 : ℝ)) =
      dyadicSymbolPiece h j (-(1 / 2 : ℝ) + 1) := by
    rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num, hleft, hright]
  simpa [dyadicTorusSymbolPiece] using
    (AddCircle.liftIoc_continuous (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
      hend (dyadicSymbolPiece_contDiff h j).continuous.continuousOn)

private theorem dyadicTorusSymbolPiece_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Integrable (dyadicTorusSymbolPiece h j) torusHaar := by
  have hmeas : AEStronglyMeasurable (dyadicTorusSymbolPiece h j) torusHaar :=
    (dyadicTorusSymbolPiece_continuous h j).measurable.aestronglyMeasurable
  have hbound : ∀ᵐ ξ ∂torusHaar, ‖dyadicTorusSymbolPiece h j ξ‖ ≤ D := by
    filter_upwards with ξ
    let y : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
      AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ
    have hy : (y : Torus) = ξ := AddCircle.coe_equivIoc
    have hvalue : dyadicTorusSymbolPiece h j ξ = dyadicSymbolPiece h j y := by
      rw [← hy]
      simp [dyadicTorusSymbolPiece, AddCircle.liftIoc, y]
    rw [hvalue]
    exact dyadicSymbolPiece_norm_le h j y
  exact Integrable.of_bound hmeas D hbound

/-- The finite residual symbol from the source's telescoping identity,
represented on the additive circle. -/
def dyadicPartialTorusSymbol {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (N : ℕ) : Torus → ℂ :=
  AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) (dyadicPartialSymbol h N)

theorem base_and_dyadicTorusPieces_eq_partialTorusSymbol
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (N : ℕ) :
    baseTorusMultiplierSymbol h +
        ∑ j ∈ Finset.range (N + 1), dyadicTorusSymbolPiece h j =
      dyadicPartialTorusSymbol h N := by
  apply AddCircle.Ioc_ext (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
  intro ξ hξ
  rw [baseTorusMultiplierSymbol_eq_lift h]
  simp only [Pi.add_apply, Finset.sum_apply, dyadicTorusSymbolPiece,
    dyadicPartialTorusSymbol, AddCircle.liftIoc_coe_apply hξ]
  exact base_and_dyadicPieces_eq_partialSymbol h N ξ

theorem kernelCoefficient_torusSymbol_eq_fourierCoeffOn
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (n : ℤ) :
    kernelCoefficient (torusSymbol h) n =
      fourierCoeffOn (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) m (-n) := by
  have hlift : torusSymbol h =
      AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) m := by
    apply AddCircle.Ioc_ext (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
    intro ξ hξ
    simp only [AddCircle.liftIoc_coe_apply hξ, torusSymbol_coe]
  rw [kernelCoefficient, hlift]
  simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using
    (fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := -(1 / 2 : ℝ)) m (-n))

theorem dyadicKernelPiece_integer_norm_summable
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (n : ℤ) :
    Summable (fun j : ℕ => ‖dyadicKernelPiece h j (n : ℝ)‖) := by
  have hAD : 0 ≤ A * D := by
    unfold A
    exact mul_nonneg (mul_nonneg (by positivity)
      (by unfold B; linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg])) h.D_nonneg
  have hmajor : Summable (fun j : ℕ => A * D * dyadicScale j) := by
    simpa [dyadicScale, mul_assoc] using summable_geometric_two.mul_left (A * D)
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) ?_ hmajor
  intro j
  have hpoint := dyadicKernelPiece_pointwise_bound h j (n : ℝ)
  have hden : 1 ≤ (1 + dyadicScale j * |(n : ℝ)|) ^ 2 := by
    have hterm : 0 ≤ dyadicScale j * |(n : ℝ)| :=
      mul_nonneg (dyadicScale_pos j).le (abs_nonneg _)
    nlinarith [sq_nonneg (dyadicScale j * |(n : ℝ)|)]
  have hnum : 0 ≤ A * D * dyadicScale j :=
    mul_nonneg hAD (dyadicScale_pos j).le
  exact hpoint.trans (div_le_self hnum hden)

private theorem dyadicPartialSymbol_fourierCoeffOn_tendsto
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (n : ℤ) :
    Tendsto
      (fun N : ℕ => fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
        (dyadicPartialSymbol h N) (-n))
      atTop
      (𝓝 (fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) m (-n))) := by
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  let F : ℕ → ℝ → ℂ := fun N ξ =>
    fourier (T := (1 : ℝ)) n (ξ : Torus) • dyadicPartialSymbol h N ξ
  let F_limit : ℝ → ℂ := fun ξ =>
    fourier (T := (1 : ℝ)) n (ξ : Torus) • m ξ
  have hab : a < b := by norm_num [a, b]
  have hlen : b - a = 1 := by norm_num [a, b]
  have hFmeas : ∀ N : ℕ,
      AEStronglyMeasurable (F N) (volume.restrict (Ι a b)) := by
    intro N
    have hphase : Measurable
        (fun ξ : ℝ => fourier (T := (1 : ℝ)) n (ξ : Torus)) :=
      (map_continuous (fourier (T := (1 : ℝ)) n)).measurable.comp
        (AddCircle.continuous_mk' (1 : ℝ)).measurable
    have hscale : Measurable (fun ξ : ℝ => ξ / dyadicScale (N + 1)) :=
      measurable_id.div_const _
    have hcut : Measurable
        (fun ξ : ℝ => ((1 - ψ (ξ / dyadicScale (N + 1)) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (measurable_const.sub (ψ_contDiff.continuous.measurable.comp hscale))
    have hpartial : Measurable (dyadicPartialSymbol h N) := by
      exact h.measurable.mul hcut
    have hmeas : Measurable (F N) := by
      dsimp [F]
      exact hphase.mul hpartial
    exact hmeas.aestronglyMeasurable.restrict
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ᵐ ξ ∂volume,
      ξ ∈ Ι a b → ‖F N ξ‖ ≤ D := by
    filter_upwards [] with N
    filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 / 2 : ℝ)] with ξ hξ0 hξhalf
    intro hξI
    have hξI' : ξ ∈ Set.Ioc a b := by
      simpa [a, b, Set.uIoc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ (1 / 2 : ℝ))] using hξI
    have hξpos : 0 < |ξ| := abs_pos.mpr hξ0
    have hξlt : |ξ| < 1 / 2 := by
      rw [abs_lt]
      constructor
      · have := hξI'.1
        dsimp [a] at this
        linarith
      · have := hξI'.2
        dsimp [b] at this
        exact lt_of_le_of_ne this hξhalf
    have hweight := h.weightedDerivativeBound ξ hξpos hξlt
    have hm : ‖m ξ‖ ≤ D := by
      have h1 : 0 ≤ ‖ξ * deriv m ξ‖ := norm_nonneg _
      have h2 : 0 ≤ ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ := norm_nonneg _
      linarith
    have hψ0 := ψ_nonneg (ξ / dyadicScale (N + 1))
    have hψ1 := ψ_le_one (ξ / dyadicScale (N + 1))
    have hcut : |1 - ψ (ξ / dyadicScale (N + 1))| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hphase : ‖fourier (T := (1 : ℝ)) n (ξ : Torus)‖ = 1 := by
      simp only [fourier_apply, Circle.norm_coe]
    have hpartial : ‖dyadicPartialSymbol h N ξ‖ ≤ D := by
      rw [dyadicPartialSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        ‖m ξ‖ * |1 - ψ (ξ / dyadicScale (N + 1))| ≤ D * 1 :=
          mul_le_mul hm hcut (abs_nonneg _) h.D_nonneg
        _ = D := by ring
    dsimp [F]
    rw [norm_mul]
    have hfirst : ‖(AddCircle.toCircle (n • (ξ : Torus)) : ℂ)‖ = 1 := by
      simpa only [fourier_apply] using hphase
    rw [hfirst, one_mul]
    exact hpartial
  have hboundIntegrable : IntervalIntegrable (fun _ : ℝ => D) volume a b :=
    intervalIntegrable_const
  have hlim : ∀ᵐ ξ ∂volume,
      ξ ∈ Ι a b → Tendsto (fun N : ℕ => F N ξ) atTop (𝓝 (F_limit ξ)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with ξ hξ0
    intro _
    have hscale : Tendsto (fun N : ℕ => dyadicScale (N + 1)) atTop (𝓝 (0 : ℝ)) := by
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
      have hpow' : Tendsto
          (fun N : ℕ => (1 / 2 : ℝ) ^ N / 2) atTop (𝓝 (0 : ℝ)) := by
        simpa using hpow.div_const 2
      convert hpow' using 1
      funext N
      rw [dyadicScale_succ]
      rfl
    have hψevent : ∀ᶠ N : ℕ in atTop,
        ψ (ξ / dyadicScale (N + 1)) = 0 := by
      have hsmall := hscale.eventually
        (Iio_mem_nhds (show (0 : ℝ) < 4 * |ξ| by positivity))
      filter_upwards [hsmall] with N hsmall
      have ht : 0 < dyadicScale (N + 1) := dyadicScale_pos _
      have hratio : (1 / 4 : ℝ) ≤ |ξ / dyadicScale (N + 1)| := by
        rw [abs_div, abs_of_pos ht]
        apply le_of_lt
        apply (lt_div_iff₀ ht).2
        nlinarith
      exact ψ_eq_zero_of_abs_ge_quarter hratio
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hψevent] with N hψ
    simp [F, F_limit, dyadicPartialSymbol, hψ]
  have hDCT : Tendsto
      (fun N : ℕ => ∫ ξ in a..b, F N ξ ∂volume) atTop
      (𝓝 (∫ ξ in a..b, F_limit ξ ∂volume)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := a) (b := b) (bound := fun _ : ℝ => D)
      (Filter.Eventually.of_forall hFmeas) hbound hboundIntegrable hlim
  have hcoeffOnIntegral (f : ℝ → ℂ) :
      fourierCoeffOn
          (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) f (-n) =
        ∫ ξ in a..b,
          fourier (T := (1 : ℝ)) n (ξ : Torus) • f ξ ∂volume := by
    rw [fourierCoeffOn_eq_integral]
    rw [hlen]
    simp [a, b]
  have hseq :
      (fun N : ℕ => fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
        (dyadicPartialSymbol h N) (-n)) =
      fun N : ℕ => ∫ ξ in a..b, F N ξ ∂volume := by
    funext N
    rw [hcoeffOnIntegral]
  have hlimit :
      fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) m (-n) =
      ∫ ξ in a..b, F_limit ξ ∂volume := by
    rw [hcoeffOnIntegral]
  rw [hseq, hlimit]
  exact hDCT

theorem kernelCoefficient_dyadicKernel_reconstruction
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (n : ℤ) :
    Summable (fun j : ℕ => ‖dyadicKernelPiece h j (n : ℝ)‖) ∧
      kernelCoefficient (torusSymbol h) n =
        baseKernelCoefficient h n +
          ∑' j : ℕ, dyadicKernelPiece h j (n : ℝ) := by
  have hsum := dyadicKernelPiece_integer_norm_summable h n
  let piece : ℕ → ℂ := fun j => dyadicKernelPiece h j (n : ℝ)
  have hpieceNormSummable : Summable (fun j : ℕ => ‖piece j‖) := by
    simpa [piece] using hsum
  have hpieceSummable : Summable piece := hpieceNormSummable.of_norm
  have hpartialTendsto : Tendsto
      (fun N : ℕ => fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
        (dyadicPartialSymbol h N) (-n))
      atTop
      (𝓝 (fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) m (-n))) :=
    dyadicPartialSymbol_fourierCoeffOn_tendsto h n
  have hbaseInt : Integrable (baseTorusMultiplierSymbol h) torusHaar :=
    baseTorusMultiplierSymbol_integrable h
  have hpieceInt : ∀ j : ℕ, Integrable (dyadicTorusSymbolPiece h j) torusHaar :=
    dyadicTorusSymbolPiece_integrable h
  have hpieceCoeff (j : ℕ) :
      fourierCoeff (dyadicTorusSymbolPiece h j) (-n) = piece j := by
    simpa [kernelCoefficient, piece] using
      kernelCoefficient_dyadicTorusSymbolPiece h j n
  have hfiniteCoeff (N : ℕ) :
      baseKernelCoefficient h n +
          ∑ j ∈ Finset.range (N + 1), piece j =
        fourierCoeffOn
          (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
          (dyadicPartialSymbol h N) (-n) := by
    have hfiniteSymbol := base_and_dyadicTorusPieces_eq_partialTorusSymbol h N
    have hsumInt : Integrable
        (fun ξ : Torus => ∑ j ∈ Finset.range (N + 1), dyadicTorusSymbolPiece h j ξ)
        torusHaar := by
      exact integrable_finsetSum (Finset.range (N + 1))
        (fun j hj => hpieceInt j)
    have hcoeff := congrFun
      (fourierCoeff.add hbaseInt hsumInt) (-n)
    have hcoeffSum := fourierCoeff.sum (Finset.range (N + 1))
      (fun j : ℕ => dyadicTorusSymbolPiece h j)
      (by intro j hj; exact hpieceInt j)
    have hsumFunction :
        (∑ j ∈ Finset.range (N + 1), dyadicTorusSymbolPiece h j) =
          (fun ξ : Torus => ∑ j ∈ Finset.range (N + 1),
            dyadicTorusSymbolPiece h j ξ) := by
      funext ξ
      simp only [Finset.sum_apply]
    have htorusCoeff :
        kernelCoefficient (dyadicPartialTorusSymbol h N) n =
          baseKernelCoefficient h n +
            ∑ j ∈ Finset.range (N + 1), piece j := by
      rw [kernelCoefficient, ← hfiniteSymbol]
      change fourierCoeff
          (baseTorusMultiplierSymbol h +
            ∑ j ∈ Finset.range (N + 1), dyadicTorusSymbolPiece h j) (-n) = _
      rw [hsumFunction]
      rw [hcoeff]
      have hpointwiseCoeff :
          fourierCoeff
              (fun ξ : Torus => ∑ j ∈ Finset.range (N + 1),
                dyadicTorusSymbolPiece h j ξ) (-n) =
            ∑ j ∈ Finset.range (N + 1),
              fourierCoeff (dyadicTorusSymbolPiece h j) (-n) := by
        rw [← hsumFunction]
        rw [congrFun hcoeffSum (-n)]
        simp only [Finset.sum_apply]
      simp only [Pi.add_apply]
      rw [hpointwiseCoeff]
      simp [baseKernelCoefficient, kernelCoefficient, piece, hpieceCoeff]
    have hbridge : kernelCoefficient (dyadicPartialTorusSymbol h N) n =
        fourierCoeffOn
          (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
          (dyadicPartialSymbol h N) (-n) := by
      rw [kernelCoefficient, dyadicPartialTorusSymbol, fourierCoeff_liftIoc_eq]
      simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num]
    exact htorusCoeff.symm.trans hbridge
  have hseriesTendsto : Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), piece j)
      atTop (𝓝 (∑' j : ℕ, piece j)) := by
    have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with N hN
      omega
    convert hpieceSummable.hasSum.tendsto_sum_nat.comp hshift using 1
    funext N
    rfl
  have hleft : Tendsto
      (fun N : ℕ => baseKernelCoefficient h n +
        ∑ j ∈ Finset.range (N + 1), piece j)
      atTop (𝓝 (baseKernelCoefficient h n + ∑' j : ℕ, piece j)) :=
    tendsto_const_nhds.add hseriesTendsto
  have hright : Tendsto
      (fun N : ℕ => fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
        (dyadicPartialSymbol h N) (-n))
      atTop
      (𝓝 (fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ)) m (-n))) :=
    hpartialTendsto
  have heq : (fun N : ℕ => baseKernelCoefficient h n +
      ∑ j ∈ Finset.range (N + 1), piece j) =ᶠ[atTop]
      (fun N : ℕ => fourierCoeffOn
        (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
        (dyadicPartialSymbol h N) (-n)) := by
    filter_upwards [] with N
    exact hfiniteCoeff N
  have hright' := Tendsto.congr' heq.symm hright
  have hlimit := tendsto_nhds_unique hleft hright'
  have hfull := kernelCoefficient_torusSymbol_eq_fourierCoeffOn h n
  refine ⟨hsum, ?_⟩
  simpa [piece] using hfull.trans hlimit.symm

end
end FractionalPrimes.Literature.Multiplier
