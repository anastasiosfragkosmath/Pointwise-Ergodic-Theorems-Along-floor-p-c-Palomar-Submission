module

public import FractionalPrimes.Literature.Multiplier.DyadicKernelReconstruction
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The base kernel in the periodic multiplier estimate

This module isolates the base-symbol derivative estimate needed for the
Fourier-coefficient `ℓ¹` bound in `lp:dyadic-kernel`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open Filter
open MeasureTheory
open scoped Topology

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem baseMultiplierSymbol_iteratedDeriv_two_norm_le
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖iteratedDeriv 2 (baseMultiplierSymbol h) ξ‖ ≤ 81 * B * D := by
  by_cases hsmall : |ξ| < 1 / 8
  · have hlocal : baseMultiplierSymbol h =ᶠ[𝓝 ξ]
        (fun _ : ℝ => (0 : ℂ)) := by
      have hr : 0 < (1 / 8 : ℝ) - |ξ| := by linarith
      filter_upwards [Metric.ball_mem_nhds ξ hr] with y hy
      have hdist : |y - ξ| < (1 / 8 : ℝ) - |ξ| := by
        rwa [Metric.mem_ball, Real.dist_eq] at hy
      have hyabs : |y| ≤ 1 / 8 := by
        calc
          |y| = |(y - ξ) + ξ| := by congr 1 <;> ring
          _ ≤ |y - ξ| + |ξ| := abs_add_le _ _
          _ ≤ 1 / 8 := by linarith
      simp [baseMultiplierSymbol, ψ_eq_one_of_abs_le y hyabs]
    have hsecond :
        deriv (deriv (baseMultiplierSymbol h)) ξ =
          deriv (deriv (fun _ : ℝ => (0 : ℂ))) ξ := hlocal.deriv.deriv_eq
    calc
      ‖iteratedDeriv 2 (baseMultiplierSymbol h) ξ‖ = 0 := by
        simp [iteratedDeriv_succ, iteratedDeriv_one, hsecond]
      _ ≤ 81 * B * D := by
        exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt B_pos)) h.D_nonneg
  · have hξ0 : ξ ≠ 0 := by
      intro h0
      subst ξ
      simp at hsmall
    have hξpunct : ξ ∈ puncturedTorusLift := by
      change ξ ∉ Set.range (fun z : ℤ => (z : ℝ))
      rintro ⟨z, hz⟩
      have hzloR : (-1 : ℝ) < (z : ℝ) := by
        calc
          (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num
          _ < ξ := hξ.1
          _ = (z : ℝ) := hz.symm
      have hzhiR : (z : ℝ) < 1 := by
        calc
          (z : ℝ) = ξ := hz
          _ < (1 / 2 : ℝ) := hξ.2
          _ < 1 := by norm_num
      have hzlo : (-1 : ℤ) < z := by exact_mod_cast hzloR
      have hzhi : z < 1 := by exact_mod_cast hzhiR
      have hz0 : z = 0 := by omega
      apply hξ0
      calc
        ξ = (z : ℝ) := hz.symm
        _ = 0 := by simp [hz0]
    have hm : ContDiffAt ℝ 2 m ξ :=
      h.smoothOnPuncturedTorus.contDiffAt
        (Real.isOpen_compl_range_intCast.mem_nhds hξpunct)
    have hcut : ContDiff ℝ 2
        (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp baseCutoffReal_contDiff
    have hformula :
        iteratedDeriv 2 (baseMultiplierSymbol h) ξ =
          iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ) +
            2 * deriv m ξ *
              deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ +
            m ξ * iteratedDeriv 2
              (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ := by
      have hmul := iteratedDeriv_mul (n := 2) hm hcut.contDiffAt
      change iteratedDeriv 2
          (fun y : ℝ => m y * ((baseCutoffReal y : ℝ) : ℂ)) ξ = _ at hmul
      have hmul' :
          iteratedDeriv 2
              (fun y : ℝ => m y * ((baseCutoffReal y : ℝ) : ℂ)) ξ =
            m ξ * iteratedDeriv 2
                (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ +
              2 * deriv m ξ *
                deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ +
              iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ) := by
        simpa [Finset.sum_range_succ, iteratedDeriv_one, iteratedDeriv_zero] using hmul
      calc
        iteratedDeriv 2 (baseMultiplierSymbol h) ξ = _ := hmul'
        _ = _ := by ring
    have hbound := h.weightedDerivativeBound ξ (abs_pos.mpr hξ0)
      (by rw [abs_lt]; exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
    have hfirstNonneg : 0 ≤ ‖ξ * deriv m ξ‖ := norm_nonneg _
    have hsecondNonneg :
        0 ≤ ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ := norm_nonneg _
    have hm0 : ‖m ξ‖ ≤ D := by nlinarith [hbound]
    have hfirstWeighted : ‖ξ * deriv m ξ‖ ≤ D := by
      nlinarith [hbound, norm_nonneg (m ξ)]
    have hfirstAbs : |ξ| * ‖deriv m ξ‖ ≤ D := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hfirstWeighted
      exact hfirstWeighted
    have hlow : (1 / 8 : ℝ) ≤ |ξ| := le_of_not_gt hsmall
    have hfirstSmall :=
      (mul_le_mul_of_nonneg_right hlow (norm_nonneg (deriv m ξ))).trans hfirstAbs
    have hm1 : ‖deriv m ξ‖ ≤ 8 * D := by nlinarith [hfirstSmall]
    have hsecondWeighted : ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ ≤ D := by
      nlinarith [hbound, norm_nonneg (m ξ), hfirstNonneg]
    have hsecondAbs : |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ D := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hsecondWeighted
      exact hsecondWeighted
    have hlowSq : (1 / 8 : ℝ) ^ 2 ≤ |ξ| ^ 2 := by
      nlinarith [hlow, abs_nonneg ξ]
    have hsecondSmall :=
      (mul_le_mul_of_nonneg_right hlowSq
        (norm_nonneg (iteratedDeriv 2 m ξ))).trans hsecondAbs
    have hm2 : ‖iteratedDeriv 2 m ξ‖ ≤ 64 * D := by
      nlinarith [hsecondSmall]
    have hq : ‖((baseCutoffReal ξ : ℝ) : ℂ)‖ ≤ 1 :=
      norm_baseCutoffComplex_le ξ
    have hq1 :
        ‖deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤ B :=
      norm_deriv_baseCutoffComplex_le ξ
    have hq2 :
        ‖iteratedDeriv 2 (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤ B :=
      norm_iteratedDeriv_two_baseCutoffComplex_le ξ
    have hB : 1 ≤ B := by
      unfold B
      linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
    have hBnonneg : 0 ≤ B := by linarith
    have hD : 0 ≤ D := h.D_nonneg
    have hterm1 :
        ‖iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ)‖ ≤ 64 * D := by
      rw [norm_mul]
      calc
        ‖iteratedDeriv 2 m ξ‖ * ‖((baseCutoffReal ξ : ℝ) : ℂ)‖ ≤
            (64 * D) * 1 := mul_le_mul hm2 hq (norm_nonneg _) (by positivity)
        _ = 64 * D := by ring
    have hterm2 :
        ‖(2 : ℂ) * deriv m ξ *
          deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤
            16 * D * B := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      calc
        2 * ‖deriv m ξ‖ *
            ‖deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤
          (2 * (8 * D)) * B := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hm1 (by norm_num)) hq1
              (by positivity) (by positivity)
        _ = 16 * D * B := by ring
    have hterm3 : ‖m ξ * iteratedDeriv 2
        (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤ D * B := by
      rw [norm_mul]
      exact mul_le_mul hm0 hq2 (norm_nonneg _) hD
    have hDB : D ≤ B * D := by
      calc
        D = 1 * D := by ring
        _ ≤ B * D := mul_le_mul_of_nonneg_right hB hD
    calc
      ‖iteratedDeriv 2 (baseMultiplierSymbol h) ξ‖ ≤
          ‖iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ)‖ +
            ‖(2 : ℂ) * deriv m ξ *
              deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ +
            ‖m ξ * iteratedDeriv 2
              (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ := by
        rw [hformula]
        calc
          ‖(iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ) +
              2 * deriv m ξ *
                deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ) +
              m ξ * iteratedDeriv 2
                (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ ≤
              ‖iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ) +
                2 * deriv m ξ *
                  deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ +
              ‖m ξ * iteratedDeriv 2
                (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ := norm_add_le _ _
          _ ≤ (‖iteratedDeriv 2 m ξ * ((baseCutoffReal ξ : ℝ) : ℂ)‖ +
              ‖2 * deriv m ξ *
                deriv (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖) +
              ‖m ξ * iteratedDeriv 2
                (fun y : ℝ => ((baseCutoffReal y : ℝ) : ℂ)) ξ‖ :=
                add_le_add_left (norm_add_le _ _) _
      _ ≤ 64 * D + 16 * D * B + D * B := add_le_add (add_le_add hterm1 hterm2) hterm3
      _ ≤ 81 * B * D := by nlinarith [hDB]

private theorem ψ_eq_zero_of_abs_ge_quarter {x : ℝ} (hx : 1 / 4 ≤ |x|) : ψ x = 0 := by
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

private theorem baseMultiplierSymbol_eq_m_eventually_of_abs_ge
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) {x : ℝ}
    (hx : 3 / 8 ≤ |x|) :
    baseMultiplierSymbol h =ᶠ[𝓝 x] m := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 8)] with y hy
  have hdist : |y - x| < 1 / 8 := by
    have hdist' := Metric.mem_ball.mp hy
    rw [Real.dist_eq] at hdist'
    simpa using hdist'
  have htriangle : |x| ≤ |x - y| + |y| := by
    calc
      |x| = |(x - y) + y| := by rw [sub_add_cancel]
      _ ≤ |x - y| + |y| := abs_add_le _ _
  have hxy : |x - y| = |y - x| := by rw [abs_sub_comm]
  have hylarge : 1 / 4 ≤ |y| := by nlinarith [htriangle]
  simp [baseMultiplierSymbol, ψ_eq_zero_of_abs_ge_quarter hylarge]

private theorem baseMultiplierSymbol_value_eq_m_at_half
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (x : ℝ)
    (hx : |x| = 1 / 2) : baseMultiplierSymbol h x = m x := by
  have hψ := ψ_eq_zero_of_abs_ge_quarter (by linarith : (1 / 4 : ℝ) ≤ |x|)
  simp [baseMultiplierSymbol, hψ]

private theorem baseMultiplierSymbol_deriv_eq_m_at_half
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (x : ℝ)
    (hx : |x| = 1 / 2) :
    deriv (baseMultiplierSymbol h) x = deriv m x := by
  have hevent : baseMultiplierSymbol h =ᶠ[𝓝 x] m :=
    baseMultiplierSymbol_eq_m_eventually_of_abs_ge h (by linarith : (3 / 8 : ℝ) ≤ |x|)
  exact hevent.deriv_eq

private theorem baseMultiplierSymbol_value_seam
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    baseMultiplierSymbol h (1 / 2) = baseMultiplierSymbol h (-(1 / 2 : ℝ)) := by
  rw [baseMultiplierSymbol_value_eq_m_at_half h _ (by norm_num),
    baseMultiplierSymbol_value_eq_m_at_half h _ (by norm_num), h.seamValue]

private theorem baseMultiplierSymbol_deriv_seam
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    deriv (baseMultiplierSymbol h) (1 / 2) =
      deriv (baseMultiplierSymbol h) (-(1 / 2 : ℝ)) := by
  rw [baseMultiplierSymbol_deriv_eq_m_at_half h _ (by norm_num),
    baseMultiplierSymbol_deriv_eq_m_at_half h _ (by norm_num), h.seamFirstDerivative]

theorem baseKernelCoefficient_nonzero_bound
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (n : ℤ) (hn : n ≠ 0) :
    ‖baseKernelCoefficient h n‖ ≤
      81 * B * D / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  let f : ℝ → ℂ := baseMultiplierSymbol h
  let k : ℤ := -n
  have hab : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ) := by norm_num
  have hlen : (1 / 2 : ℝ) - (-(1 / 2 : ℝ)) = 1 := by norm_num
  have hk : k ≠ 0 := by
    dsimp [k]
    exact neg_ne_zero.mpr hn
  have hcontAt (x : ℝ) (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
      ContDiffAt ℝ 2 f x := by
    simpa [f] using baseMultiplierSymbol_contDiffAt h hx
  have hfContOn :
      ContinuousOn f (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    intro x hx
    exact (hcontAt x hx).continuousAt.continuousWithinAt
  have hfDerivContOn :
      ContinuousOn (deriv f) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    intro x hx
    have hdf : ContDiffAt ℝ 0 (deriv f) x :=
      (hcontAt x hx).derivWithin (m := 0) (by norm_num)
    exact hdf.continuousAt.continuousWithinAt
  have hfSecondContOn :
      ContinuousOn (iteratedDeriv 2 f)
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    intro x hx
    have hdf : ContDiffAt ℝ 1 (deriv f) x :=
      (hcontAt x hx).derivWithin (m := 1) (by norm_num)
    have hddf : ContDiffAt ℝ 0 (deriv (deriv f)) x :=
      hdf.derivWithin (m := 0) (by norm_num)
    have hddfCont : ContinuousAt (iteratedDeriv 2 f) x := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hddf.continuousAt
    exact hddfCont.continuousWithinAt
  have hfInt : IntervalIntegrable f volume (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    hfContOn.intervalIntegrable_of_Icc hab.le
  have hfDerivInt :
      IntervalIntegrable (deriv f) volume (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    hfDerivContOn.intervalIntegrable_of_Icc hab.le
  have hfSecondInt :
      IntervalIntegrable (iteratedDeriv 2 f) volume (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    hfSecondContOn.intervalIntegrable_of_Icc hab.le
  have hfCont : ContinuousOn f (Set.uIcc (-(1 / 2 : ℝ)) (1 / 2)) := by
    simpa [Set.uIcc_of_le hab.le] using hfContOn
  have hfDerivCont :
      ContinuousOn (deriv f) (Set.uIcc (-(1 / 2 : ℝ)) (1 / 2)) := by
    simpa [Set.uIcc_of_le hab.le] using hfDerivContOn
  have hfDiff : ∀ x, x ∈ Set.Ioo (min (-(1 / 2 : ℝ)) (1 / 2))
      (max (-(1 / 2 : ℝ)) (1 / 2)) →
        HasDerivWithinAt f (deriv f x) (Set.Ioi x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa [min_eq_left hab.le, max_eq_right hab.le] using hx
    have hxIcc : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
    have hcontAtOne : ContDiffAt ℝ 1 f x :=
      (hcontAt x hxIcc).of_le (by norm_num)
    exact hcontAtOne.differentiableAt_one.hasDerivAt.hasDerivWithinAt
  have hfDerivDiff :
      ∀ x, x ∈ Set.Ioo (min (-(1 / 2 : ℝ)) (1 / 2))
        (max (-(1 / 2 : ℝ)) (1 / 2)) →
          HasDerivWithinAt (deriv f) (iteratedDeriv 2 f x) (Set.Ioi x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa [min_eq_left hab.le, max_eq_right hab.le] using hx
    have hxIcc : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
    have hdf : ContDiffAt ℝ 1 (deriv f) x :=
      (hcontAt x hxIcc).derivWithin (m := 1) (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      hdf.differentiableAt_one.hasDerivAt.hasDerivWithinAt
  have hseam0 : f (1 / 2) = f (-(1 / 2 : ℝ)) := by
    simpa [f] using baseMultiplierSymbol_value_seam h
  have hseam1 : deriv f (1 / 2) = deriv f (-(1 / 2 : ℝ)) := by
    simpa [f] using baseMultiplierSymbol_deriv_seam h
  have hIBP₁ := fourierCoeffOn_of_hasDeriv_right
    (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (f := f) (f' := deriv f)
    hab hk hfCont hfDiff hfDerivInt
  have hcoeff₁ : fourierCoeffOn hab f k =
      (1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) *
        fourierCoeffOn hab (deriv f) k := by
    rw [hIBP₁, hseam0, hlen]
    simp_all
    all_goals ring
  have hIBP₂ := fourierCoeffOn_of_hasDeriv_right
    (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (f := deriv f)
    (f' := iteratedDeriv 2 f) hab hk hfDerivCont hfDerivDiff hfSecondInt
  have hcoeff₂ : fourierCoeffOn hab (deriv f) k =
      (1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) *
        fourierCoeffOn hab (iteratedDeriv 2 f) k := by
    rw [hIBP₂, hseam1, hlen]
    simp_all
    all_goals ring
  have hcoeff : fourierCoeffOn hab f k =
      (1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) ^ 2 *
        fourierCoeffOn hab (iteratedDeriv 2 f) k := by
    calc
      fourierCoeffOn hab f k =
          (1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) *
            fourierCoeffOn hab (deriv f) k := hcoeff₁
      _ = _ := by rw [hcoeff₂]; ring
  have hboundAE : ∀ᵐ x, x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2) →
      ‖fourier (-k) (x : Torus) • iteratedDeriv 2 f x‖ ≤ 81 * B * D := by
    filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with x hxb
    intro hx
    have hxIoc : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa [Set.uIoc_of_le hab.le] using hx
    have hxIoo : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxb⟩
    have hbound := baseMultiplierSymbol_iteratedDeriv_two_norm_le h hxIoo
    have hfourier : ‖fourier (-k) (x : Torus)‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    rw [norm_smul, hfourier, one_mul]
    simpa [f] using hbound
  have hcoeffSecond :
      ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ ≤ 81 * B * D := by
    calc
      ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ =
          ‖∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
              fourier (-k) (x : Torus) • iteratedDeriv 2 f x ∂volume‖ := by
        rw [fourierCoeffOn_eq_integral]
        rw [hlen]
        simp
      _ ≤ (81 * B * D) * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const_ae hboundAE
      _ = 81 * B * D := by norm_num
  have hrealK : (k : ℝ) ^ 2 = (n : ℝ) ^ 2 := by simp [k]
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkAbs : 0 < |(k : ℝ)| := abs_pos.mpr hkReal
  have hdenomNorm :
      ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ)‖ =
        2 * Real.pi * |(k : ℝ)| := by
    simp [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hfactorNorm :
      ‖(1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ))‖ =
        1 / (2 * Real.pi * |(k : ℝ)|) := by
    rw [norm_div, norm_one, hdenomNorm]
  have hdenomPos : 0 < 2 * Real.pi * |(k : ℝ)| := by positivity
  have hdenomSq :
      (2 * Real.pi * |(k : ℝ)|) ^ 2 = 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 := by
    simp only [mul_pow, sq_abs]
    ring
  have hfactorSq :
      ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ))) ^ 2‖ =
        1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
    rw [norm_pow, hfactorNorm, ← hdenomSq]
    field_simp [ne_of_gt hdenomPos]
  have hfactorRhsNonneg : 0 ≤ 1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) := by
    positivity
  have hkernel : baseKernelCoefficient h n = fourierCoeffOn hab f k := by
    simpa [f, k] using baseKernelCoefficient_eq_fourierCoeffOn h n
  calc
    ‖baseKernelCoefficient h n‖ =
        ‖(1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) ^ 2 *
          fourierCoeffOn hab (iteratedDeriv 2 f) k‖ := by rw [hkernel, hcoeff]
    _ = ‖(1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) ^ 2‖ *
        ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ := norm_mul _ _
    _ ≤ (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * (81 * B * D) := by
      calc
        _ ≤ (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) *
            ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ :=
          mul_le_mul_of_nonneg_right hfactorSq.le (norm_nonneg _)
        _ ≤ (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * (81 * B * D) :=
          mul_le_mul_of_nonneg_left hcoeffSecond hfactorRhsNonneg
    _ = 81 * B * D / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
      rw [hrealK]
      ring

private theorem baseKernelCoefficient_zero_bound
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    ‖baseKernelCoefficient h 0‖ ≤ D := by
  let f : ℝ → ℂ := baseMultiplierSymbol h
  have hab : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ) := by norm_num
  have hlen : (1 / 2 : ℝ) - (-(1 / 2 : ℝ)) = 1 := by norm_num
  have hboundAE : ∀ᵐ x, x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2) → ‖f x‖ ≤ D := by
    filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 / 2 : ℝ)] with x hx0 hxhalf
    intro hx
    have hxIoc : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
      simpa [Set.uIoc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ (1 / 2))] using hx
    have hxIoo : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxhalf⟩
    by_cases hsmall : |x| ≤ 1 / 8
    · have hψ := ψ_eq_one_of_abs_le x hsmall
      simpa [f, baseMultiplierSymbol, hψ] using h.D_nonneg
    · have hnotzero : x ≠ 0 := by
        intro hz
        subst x
        exact hx0 rfl
      have hbound := h.weightedDerivativeBound x (abs_pos.mpr hnotzero)
        (by rw [abs_lt]; exact ⟨by linarith [hxIoo.1], by linarith [hxIoo.2]⟩)
      have hn1 : 0 ≤ ‖x * deriv m x‖ := norm_nonneg _
      have hn2 : 0 ≤ ‖x ^ 2 * iteratedDeriv 2 m x‖ := norm_nonneg _
      have hm : ‖m x‖ ≤ D := by nlinarith [hbound]
      have hcut : ‖((baseCutoffReal x : ℝ) : ℂ)‖ ≤ 1 := norm_baseCutoffComplex_le x
      change ‖m x * ((baseCutoffReal x : ℝ) : ℂ)‖ ≤ D
      rw [norm_mul]
      calc
        ‖m x‖ * ‖((baseCutoffReal x : ℝ) : ℂ)‖ ≤ D * 1 :=
          mul_le_mul hm hcut (norm_nonneg _) h.D_nonneg
        _ = D := by ring
  have hcoeff := intervalIntegral.norm_integral_le_of_norm_le_const_ae hboundAE
  rw [baseKernelCoefficient_eq_fourierCoeffOn h 0, fourierCoeffOn_eq_integral]
  norm_num [fourier_zero, hlen] at hcoeff ⊢
  exact hcoeff

private theorem sum_nat_shifted_inv_sq_le_two (N : ℕ) :
    (∑ i ∈ Finset.range N, 1 / ((i + 1 : ℝ) ^ 2)) ≤ 2 := by
  calc
    (∑ i ∈ Finset.range N, 1 / ((i + 1 : ℝ) ^ 2)) =
        ∑ i ∈ Finset.Ico 1 (N + 1), 1 / ((i : ℝ) ^ 2) := by
          rw [Finset.sum_Ico_eq_sum_range]
          apply Finset.sum_congr rfl
          intro i hi
          rw [add_comm]
          push_cast
          rfl
    _ = ∑ i ∈ Finset.Ioo 0 (N + 1), 1 / ((i : ℝ) ^ 2) := by
          congr 1
    _ ≤ 2 / ((0 : ℝ) + 1) := by
          simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))
    _ = 2 := by norm_num

private theorem tsum_nat_shifted_inv_sq_le_two :
    (∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ 2)) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (c := 2) (fun n => by positivity)
  exact sum_nat_shifted_inv_sq_le_two

private theorem tsum_pnat_inv_sq_le_two :
    (∑' n : ℕ+, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hEq := tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
  simp only [one_div, Nat.cast_add, Nat.cast_one] at hEq ⊢
  rw [hEq]
  simpa only [one_div] using tsum_nat_shifted_inv_sq_le_two

private theorem tsum_int_inv_sq_le_four :
    (∑' n : ℤ, 1 / ((n : ℝ) ^ 2)) ≤ 4 := by
  have hsummable : Summable (fun n : ℤ => 1 / ((n : ℝ) ^ 2)) := by
    exact (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have heven : Function.Even (fun n : ℤ => 1 / ((n : ℝ) ^ 2)) := by
    intro n
    simp [Int.cast_neg, neg_sq]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsummable]
  have hpnat := tsum_pnat_inv_sq_le_two
  have hzero : (1 / ((0 : ℝ) ^ 2)) = 0 := by norm_num
  simp only [Int.cast_zero, hzero]
  have hpnat' : (∑' n : ℕ+, 1 / ((n : ℝ) ^ 2)) ≤ 2 := by
    simpa only [one_div] using hpnat
  have hpnatInt :
      (∑' n : ℕ+, 1 / (((n : ℤ) : ℝ) ^ 2)) ≤ 2 := by
    simpa only [Int.cast_natCast] using hpnat'
  simp only [two_smul]
  nlinarith [hpnatInt]

theorem baseKernelCoefficient_summable_l1_estimate
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) :
    Summable (fun n : ℤ => ‖baseKernelCoefficient h n‖) ∧
      (∑' n : ℤ, ‖baseKernelCoefficient h n‖) ≤ A * D := by
  let c : ℝ := 81 * B * D / (4 * Real.pi ^ 2)
  let invSq : ℤ → ℝ := fun n => 1 / ((n : ℝ) ^ 2)
  let single : ℤ → ℝ := fun n => if n = 0 then D else 0
  let major : ℤ → ℝ := fun n => single n + c * invSq n
  have hBnonneg : 0 ≤ B := le_of_lt B_pos
  have hD : 0 ≤ D := h.D_nonneg
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hinvSummable : Summable invSq := by
    dsimp [invSq]
    exact (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hsingleSupport : Function.support single ⊆ ({0} : Set ℤ) := by
    intro n hn
    change single n ≠ 0 at hn
    by_cases h0 : n = 0
    · simpa using h0
    · exact False.elim (hn (by simp [single, h0]))
  have hsingle : Summable single := by
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton (0 : ℤ)).subset hsingleSupport
  have hscaled : Summable (fun n : ℤ => c * invSq n) := hinvSummable.mul_left c
  have hmajor : Summable major := by
    simpa [major] using hsingle.add hscaled
  have hpointwise : ∀ n : ℤ, ‖baseKernelCoefficient h n‖ ≤ major n := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hzero := baseKernelCoefficient_zero_bound h
      simp [major, single, invSq, c]
      exact hzero
    · have hnonzero := baseKernelCoefficient_nonzero_bound h n hn
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hfactor : c * invSq n =
          81 * B * D / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
        dsimp [c, invSq]
        field_simp [ne_of_gt Real.pi_pos, hnreal]
        <;> ring
      simpa [major, single, hn, hfactor] using hnonzero
  have hcoeffSummable : Summable (fun n : ℤ => ‖baseKernelCoefficient h n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpointwise hmajor
  have hsumCompare := Summable.tsum_le_tsum hpointwise hcoeffSummable hmajor
  have hsingleTsum : (∑' n : ℤ, single n) = D := by
    rw [tsum_eq_single (0 : ℤ)]
    · simp [single]
    · intro n hn
      simp [single, hn]
  have hInvTsum : (∑' n : ℤ, invSq n) ≤ 4 := by
    simpa [invSq] using tsum_int_inv_sq_le_four
  have hmajorTsum : (∑' n : ℤ, major n) = D + c * (∑' n : ℤ, invSq n) := by
    simp only [major, hsingle.tsum_add hscaled, hsingleTsum,
      hinvSummable.tsum_mul_left c]
  have hseries : c * (∑' n : ℤ, invSq n) ≤ 81 * B * D := by
    have hpiSq : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hnum : 0 ≤ 81 * B * D := by positivity
    calc
      c * (∑' n : ℤ, invSq n) ≤ c * 4 := mul_le_mul_of_nonneg_left hInvTsum hc
      _ = (81 * B * D) / Real.pi ^ 2 := by
        dsimp [c]
        field_simp [ne_of_gt Real.pi_pos]
        <;> ring
      _ ≤ 81 * B * D := div_le_self hnum hpiSq
  have hDB : D ≤ B * D := by
    have hBgeone : 1 ≤ B := by
      unfold B
      linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
    calc
      D = 1 * D := by ring
      _ ≤ B * D := mul_le_mul_of_nonneg_right hBgeone hD
  have h82 : D + 81 * B * D ≤ 82 * B * D := by nlinarith [hDB]
  have hBD : 0 ≤ B * D := mul_nonneg hBnonneg hD
  have hA : 82 * B * D ≤ A * D := by
    calc
      82 * B * D = 82 * (B * D) := by ring
      _ ≤ (2 ^ 16) * (B * D) :=
        mul_le_mul_of_nonneg_right (by norm_num) hBD
      _ = A * D := by rw [A_eq]; ring
  refine ⟨hcoeffSummable, ?_⟩
  calc
    (∑' n : ℤ, ‖baseKernelCoefficient h n‖) ≤ ∑' n : ℤ, major n := hsumCompare
    _ = D + c * (∑' n : ℤ, invSq n) := hmajorTsum
    _ ≤ D + 81 * B * D := by
      simpa only [add_comm] using add_le_add_left hseries D
    _ ≤ 82 * B * D := h82
    _ ≤ A * D := hA

end
end FractionalPrimes.Literature.Multiplier
