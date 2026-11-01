module

public import FractionalPrimes.Literature.Multiplier.DyadicKernelDecay
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Coefficient and reconstruction work for `lp:dyadic-kernel`

This module records the relation between the real inverse-transform kernels
and the Fourier coefficients on the unit circle.  The checked decay estimates
remain in `DyadicKernelDecay`; this file is kept separate while the parent
module is being aggregate-built.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open Filter
open scoped FourierTransform Topology

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The circle function represented by the real dyadic symbol piece on the
fundamental interval. -/
def dyadicTorusSymbolPiece {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) : Torus → ℂ :=
  AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) (dyadicSymbolPiece h j)

/-- The base symbol `m_* = m(1-ψ)` on the real fundamental interval. -/
def baseMultiplierSymbol {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (ξ : ℝ) : ℂ :=
  m ξ * ((1 - ψ ξ : ℝ) : ℂ)

theorem baseMultiplierSymbol_contDiffAt {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ContDiffAt ℝ 2 (baseMultiplierSymbol h) ξ := by
  by_cases hzero : ξ = 0
  · subst ξ
    have hlocal : baseMultiplierSymbol h =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 / 8 : ℝ))]
        with y hy
      have hy' : |y| ≤ 1 / 8 := by
        have hdist := Metric.mem_ball.mp hy
        rw [Real.dist_eq] at hdist
        simpa using hdist.le
      simp [baseMultiplierSymbol, ψ_eq_one_of_abs_le y hy']
    exact contDiff_const.contDiffAt.congr_of_eventuallyEq hlocal
  · have hpunct : ξ ∈ puncturedTorusLift := by
      change ξ ∉ Set.range (fun z : ℤ => (z : ℝ))
      rintro ⟨z, hz⟩
      have hlo : -(1 / 2 : ℝ) ≤ (z : ℝ) := by
        calc
          -(1 / 2 : ℝ) ≤ ξ := hξ.1
          _ = (z : ℝ) := hz.symm
      have hhi : (z : ℝ) ≤ 1 / 2 := by
        calc
          (z : ℝ) = ξ := hz
          _ ≤ 1 / 2 := hξ.2
      have hzloR : (-1 : ℝ) < (z : ℝ) := by
        linarith
      have hzhiR : (z : ℝ) < 1 := by
        linarith
      have hzlo : (-1 : ℤ) < z := by exact_mod_cast hzloR
      have hzhi : z < 1 := by exact_mod_cast hzhiR
      have hz0 : z = 0 := by omega
      have hξeq : ξ = 0 := by
        calc
          ξ = (z : ℝ) := hz.symm
          _ = 0 := by simp [hz0]
      exact hzero hξeq
    have hm : ContDiffAt ℝ 2 m ξ :=
      h.smoothOnPuncturedTorus.contDiffAt
        (Real.isOpen_compl_range_intCast.mem_nhds hpunct)
    have hψ : ContDiff ℝ 2 ψ := ψ_contDiff.of_le (by norm_num)
    have hcutReal : ContDiff ℝ 2 (fun y : ℝ => 1 - ψ y) :=
      contDiff_const.sub hψ
    have hcut : ContDiff ℝ 2
        (fun y : ℝ => ((1 - ψ y : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hcutReal
    change ContDiffAt ℝ 2 (fun y : ℝ => m y * ((1 - ψ y : ℝ) : ℂ)) ξ
    exact hm.mul hcut.contDiffAt

/-- The once-fixed cutoff represented on the unit circle. -/
def fixedCutoffTorus : Torus → ℝ :=
  AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) ψ

/-- The base multiplier symbol as an actual function on the torus. -/
def baseTorusMultiplierSymbol {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) : Torus → ℂ :=
  fun ξ => torusSymbol h ξ * ((1 - fixedCutoffTorus ξ : ℝ) : ℂ)

/-- `m_*` on the torus is the lift of its real representative on
`(-1/2,1/2]`. -/
theorem baseTorusMultiplierSymbol_eq_lift {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) :
    baseTorusMultiplierSymbol h =
      AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) (baseMultiplierSymbol h) := by
  apply AddCircle.Ioc_ext (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
  intro ξ hξ
  simp only [baseTorusMultiplierSymbol, fixedCutoffTorus, baseMultiplierSymbol,
    AddCircle.liftIoc_coe_apply hξ, torusSymbol_coe]

/-- The base torus kernel coefficient `K_*` in the approved lemma. -/
def baseKernelCoefficient {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (n : ℤ) : ℂ :=
  kernelCoefficient (baseTorusMultiplierSymbol h) n

/-- Express the base coefficient as an interval Fourier coefficient, retaining
the approved `[-1/2,1/2]` normalization. -/
theorem baseKernelCoefficient_eq_fourierCoeffOn {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (n : ℤ) :
    baseKernelCoefficient h n =
      fourierCoeffOn (by norm_num : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ))
        (baseMultiplierSymbol h) (-n) := by
  rw [baseKernelCoefficient, kernelCoefficient,
    baseTorusMultiplierSymbol_eq_lift]
  simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using
    (fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := -(1 / 2 : ℝ))
      (baseMultiplierSymbol h) (-n))

/-- The cutoff at dyadic scale `j`, written using the exact scale `t_j`. -/
def dyadicScaledCutoff (j : ℕ) (ξ : ℝ) : ℝ :=
  ψ (ξ / dyadicScale j)

theorem dyadicScale_succ (j : ℕ) :
    dyadicScale (j + 1) = dyadicScale j / 2 := by
  unfold dyadicScale
  rw [pow_succ]
  ring

/-- Real-valued complementary cutoff used in the base symbol. -/
def baseCutoffReal (ξ : ℝ) : ℝ := 1 - ψ ξ

theorem baseCutoffReal_contDiff : ContDiff ℝ 2 baseCutoffReal := by
  exact contDiff_const.sub (ψ_contDiff.of_le (by norm_num))

theorem deriv_baseCutoffReal (ξ : ℝ) :
    deriv baseCutoffReal ξ = -deriv ψ ξ := by
  have hψ : HasDerivAt ψ (deriv ψ ξ) ξ :=
    (ψ_contDiff.of_le (by norm_num)).contDiffAt.differentiableAt_one.hasDerivAt
  change deriv (fun y : ℝ => 1 - ψ y) ξ = _
  simpa using ((hasDerivAt_const ξ (1 : ℝ)).sub hψ).deriv

theorem iteratedDeriv_two_baseCutoffReal (ξ : ℝ) :
    iteratedDeriv 2 baseCutoffReal ξ = -iteratedDeriv 2 ψ ξ := by
  have hderivFun : deriv baseCutoffReal = fun y => -deriv ψ y := by
    funext y
    exact deriv_baseCutoffReal y
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderivFun]
  simp [iteratedDeriv_succ, iteratedDeriv_one, deriv_neg]

theorem deriv_baseCutoffComplex (ξ : ℝ) :
    deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ =
      Complex.ofReal (deriv baseCutoffReal ξ) := by
  have hcont : ContDiff ℝ 1 baseCutoffReal :=
    baseCutoffReal_contDiff.of_le (by norm_num)
  exact hcont.contDiffAt.differentiableAt_one.hasDerivAt.ofReal_comp.deriv

theorem iteratedDeriv_two_baseCutoffComplex (ξ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ =
      Complex.ofReal (iteratedDeriv 2 baseCutoffReal ξ) := by
  have hderivFun :
      deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) =
        fun y => Complex.ofReal (deriv baseCutoffReal y) := by
    funext y
    exact deriv_baseCutoffComplex y
  have hcont : ContDiff ℝ 1 (deriv baseCutoffReal) :=
    baseCutoffReal_contDiff.deriv'
  have hsecond : HasDerivAt (deriv baseCutoffReal)
      (iteratedDeriv 2 baseCutoffReal ξ) ξ := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      hcont.contDiffAt.differentiableAt_one.hasDerivAt
  have hcomplex := hsecond.ofReal_comp
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderivFun]
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using hcomplex.deriv

theorem norm_baseCutoffComplex_le (ξ : ℝ) :
    ‖((baseCutoffReal ξ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, baseCutoffReal]
  have hnonneg := ψ_nonneg ξ
  have hle := ψ_le_one ξ
  rw [abs_le]
  constructor <;> linarith

theorem norm_deriv_baseCutoffComplex_le (ξ : ℝ) :
    ‖deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤ B := by
  rw [deriv_baseCutoffComplex, deriv_baseCutoffReal]
  have hsup : ψDerivSup ≤ B := by
    unfold B
    linarith [ψSecondDerivSup_nonneg]
  simpa using (norm_deriv_ψ_le_sup ξ).trans hsup

theorem norm_iteratedDeriv_two_baseCutoffComplex_le (ξ : ℝ) :
    ‖iteratedDeriv 2 (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤ B := by
  rw [iteratedDeriv_two_baseCutoffComplex]
  have hsup : ψSecondDerivSup ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg]
  rw [iteratedDeriv_two_baseCutoffReal]
  simpa using (norm_iteratedDeriv_two_ψ_le_sup ξ).trans hsup

theorem dyadicCutoffFactor_eq_scaled_sub_succ (j : ℕ) (ξ : ℝ) :
    dyadicCutoffFactor j ξ =
      dyadicScaledCutoff j ξ - dyadicScaledCutoff (j + 1) ξ := by
  have ht := dyadicScale_pos j
  have hratio : (2 * ξ) / dyadicScale j = ξ / dyadicScale (j + 1) := by
    rw [dyadicScale_succ]
    field_simp [ne_of_gt ht]
  rw [dyadicCutoffFactor, dyadicScaledCutoff, dyadicScaledCutoff, hratio]

theorem sum_dyadicCutoffFactor (N : ℕ) (ξ : ℝ) :
    (∑ j ∈ Finset.range (N + 1), dyadicCutoffFactor j ξ) =
      ψ ξ - ψ (ξ / dyadicScale (N + 1)) := by
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range (N + 1),
        (dyadicScaledCutoff j ξ - dyadicScaledCutoff (j + 1) ξ)) =
        dyadicScaledCutoff 0 ξ - dyadicScaledCutoff (N + 1) ξ := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        abel
  calc
    _ = ∑ j ∈ Finset.range (N + 1),
        (dyadicScaledCutoff j ξ - dyadicScaledCutoff (j + 1) ξ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact dyadicCutoffFactor_eq_scaled_sub_succ j ξ
    _ = dyadicScaledCutoff 0 ξ - dyadicScaledCutoff (N + 1) ξ := htel N
    _ = ψ ξ - ψ (ξ / dyadicScale (N + 1)) := by
          simp [dyadicScaledCutoff, dyadicScale]

/-- The residual symbol after the first `N+1` dyadic annuli have been
removed. -/
def dyadicPartialSymbol {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (N : ℕ) (ξ : ℝ) : ℂ :=
  m ξ * ((1 - ψ (ξ / dyadicScale (N + 1)) : ℝ) : ℂ)

/-- The exact finite telescoping identity from the Astra proof notes. -/
theorem base_and_dyadicPieces_eq_partialSymbol {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (N : ℕ) (ξ : ℝ) :
    baseMultiplierSymbol h ξ +
      ∑ j ∈ Finset.range (N + 1), dyadicSymbolPiece h j ξ =
        dyadicPartialSymbol h N ξ := by
  rw [baseMultiplierSymbol, dyadicPartialSymbol]
  simp only [dyadicSymbolPiece]
  have hsum :
      (∑ j ∈ Finset.range (N + 1), (dyadicCutoffFactor j ξ : ℂ)) =
        ((ψ ξ - ψ (ξ / dyadicScale (N + 1)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    exact congrArg (fun x : ℝ => (x : ℂ)) (sum_dyadicCutoffFactor N ξ)
  rw [← Finset.mul_sum, hsum]
  push_cast
  ring

/-- The torus Fourier coefficient of a dyadic piece agrees with its real
inverse-transform kernel at integer arguments, with the approved positive
phase convention. -/
theorem kernelCoefficient_dyadicTorusSymbolPiece {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (n : ℤ) :
    kernelCoefficient (dyadicTorusSymbolPiece h j) n =
      dyadicKernelPiece h j (n : ℝ) := by
  have hab : (-(1 / 2 : ℝ)) < (-(1 / 2 : ℝ) + 1) := by norm_num
  have hphase (ξ : ℝ) :
      fourier (T := (1 : ℝ)) n (ξ : Torus) =
        dyadicInversePhase (n : ℝ) ξ := by
    rw [fourier_coe_apply]
    simp [dyadicInversePhase]
    congr 1
    push_cast
    ring
  have hsupp : Function.support (fun ξ : ℝ =>
      dyadicSymbolPiece h j ξ * dyadicInversePhase (n : ℝ) ξ) ⊆
        Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    apply (Function.support_mul_subset_left _ _).trans
    intro ξ hξ
    have hξ' : ξ ∈ Function.support (dyadicSymbolPiece h j) := hξ
    have hIcc := dyadicSymbolPiece_support_Icc h j hξ'
    have ht := dyadicScale_le_one j
    constructor <;> rcases hIcc with ⟨hl, hr⟩ <;> nlinarith
  rw [kernelCoefficient, dyadicTorusSymbolPiece, fourierCoeff_liftIoc_eq]
  rw [fourierCoeffOn_eq_integral _ _ hab]
  simp only [neg_neg]
  rw [show ((-(1 / 2 : ℝ) + 1) - (-(1 / 2 : ℝ))) = 1 by ring]
  simp only [one_div, one_smul]
  have h_integrand :
      (fun ξ : ℝ => fourier (T := (1 : ℝ)) n (ξ : Torus) •
        dyadicSymbolPiece h j ξ) =
      dyadicKernelIntegrand h j (n : ℝ) := by
    funext ξ
    rw [smul_eq_mul, hphase ξ]
    simp [dyadicKernelIntegrand, mul_comm]
  have hsupp' : Function.support (dyadicKernelIntegrand h j (n : ℝ)) ⊆
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    intro ξ hξ
    change ξ ∈ Function.support (fun y : ℝ =>
      dyadicSymbolPiece h j y * dyadicInversePhase (n : ℝ) y) at hξ
    exact hsupp hξ
  rw [h_integrand]
  have hIntegral :
      (∫ ξ in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ) + 1),
        dyadicKernelIntegrand h j (n : ℝ) ξ ∂volume) =
        ∫ ξ, dyadicKernelIntegrand h j (n : ℝ) ξ ∂volume :=
    intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsupp'
  calc
    _ = (1 : ℝ)⁻¹ • ∫ ξ, dyadicKernelIntegrand h j (n : ℝ) ξ ∂volume := by
      congr 1
      simpa only [one_div] using hIntegral
    _ = dyadicKernelPiece h j (n : ℝ) := by simp [dyadicKernelPiece]

end
end FractionalPrimes.Literature.Multiplier
