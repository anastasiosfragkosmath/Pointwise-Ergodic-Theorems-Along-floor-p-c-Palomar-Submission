module
public import FractionalPrimes.Literature.LongArithmetic.LongOfUnitGlobal
public import FractionalPrimes.Literature.Uniformity.MajorArcUnitResidueNormalization
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalDirichletTaskContract
public import FractionalPrimes.Literature.Polynomial.PolynomialSourceCutoffShortLong
public import FractionalPrimes.Literature.Polynomial.PolynomialDivisorResidueStability
public import FractionalPrimes.Literature.Polynomial.PolynomialPrefixBoundsFromFullResidues
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceCorrelationBound
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
@[expose] public section

/-! The source `LONG + DP` implication toward ordinary short-interval residue
cancellation. This traditional-import bridge is intentionally separate from
the module root because the checked LONG arithmetic chain still contains the
approved OAI legacy imports. -/

noncomputable section

open Finset
open scoped BigOperators

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Uniformity
open MeasureTheory
open scoped BigOperators

def sourceRealResidueAverage
    (X H q : ℕ) (a : ℤ) (f : ℤ → ℝ) : ℝ :=
  (H : ℝ)⁻¹ *
    ∑ n ∈ (Finset.Ioc X (X + H)).filter
      (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
      f (n : ℤ)

/-- Exact identification of the source-cutoff Mellin mean with the natural
open-left, closed-right arithmetic average on an integer interval. -/
theorem outerCutoffWindowData_N_H_eq_natResidueAverage
    (X H q : ℕ) (a : ℤ) (f : ℤ → ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hq : 0 < q)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ)) :
    (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ)
      q a f (by exact_mod_cast hX) (by exact_mod_cast hH)
      (by exact_mod_cast hHX) (by exact_mod_cast hq) hf).N_H =
      (((H : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          f (n : ℤ)) : ℂ) := by
  classical
  have hAvg := (outerCutoffPreservesAverages polynomialKernelRho
    (X : ℝ) (H : ℝ) q a f (by exact_mod_cast hX) (by exact_mod_cast hH)
    (by exact_mod_cast hHX) (by exact_mod_cast hq) hf).2.2
  rw [mellinWindowAverageIndices_nat_eq_Ioc X H] at hAvg
  have hFilter :
      (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => Int.ModEq (q : ℤ) (n : ℤ) a) =
        (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]) := by
    rfl
  rw [hFilter] at hAvg
  change _ = _
  rw [hAvg]
  simp only [Complex.ofReal_sum]

private theorem sourceAverage_at_outerCutoff
    (X H q : ℕ) (a : ℤ) (f : ℤ → ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hq : 0 < q)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ)) :
    (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ)
      q a f (by exact_mod_cast hX) (by exact_mod_cast hH)
      (by exact_mod_cast hHX) (by exact_mod_cast hq) hf).N_H =
      (sourceRealResidueAverage X H q a f : ℂ) := by
  calc
    _ = (((H : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          f (n : ℤ)) : ℂ) :=
      outerCutoffWindowData_N_H_eq_natResidueAverage
        X H q a f hX hH hHX hq hf
    _ = (sourceRealResidueAverage X H q a f : ℂ) := by
      simp [sourceRealResidueAverage, Complex.ofReal_mul, Complex.ofReal_sum]

private theorem sourceAverage_mu_eq_long
    (X H q a : ℕ) (ha : a < q) :
    sourceRealResidueAverage X H q (a : ℤ)
        (fun n => (paperMu n : ℝ)) =
      (H : ℝ)⁻¹ * longMobiusResidueIntervalSum q a X H := by
  classical
  have hmodiff (n : ℕ) :
      (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)] ↔ n % q = a := by
    rw [Int.natCast_modEq_iff]
    change n % q = a % q ↔ n % q = a
    rw [Nat.mod_eq_of_lt ha]
  unfold sourceRealResidueAverage longMobiusResidueIntervalSum
  rw [Finset.sum_filter]
  apply congrArg
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · have hnpos : 0 < n :=
      lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1
    simp [hres, hmodiff, paperMu, mobiusWeight, hnpos]
  · simp [hres, hmodiff]

private theorem sourceAverage_lambdaCramer_eq_long
    (X H q a : ℕ) (ha : a < q) :
    sourceRealResidueAverage X H q (a : ℤ)
        (fun n => paperLambda n) -
      (H : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ) =
      (H : ℝ)⁻¹ * longLambdaCramerResidueIntervalSum q a X H := by
  classical
  have hmodiff (n : ℕ) :
      (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)] ↔ n % q = a := by
    rw [Int.natCast_modEq_iff]
    change n % q = a % q ↔ n % q = a
    rw [Nat.mod_eq_of_lt ha]
  unfold sourceRealResidueAverage longLambdaCramerResidueIntervalSum
  simp_rw [Finset.sum_filter]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg (fun z : ℝ => (H : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · have hnpos : 0 < n :=
      lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1
    simp [hres, hmodiff, paperLambda, vonMangoldtWeight_def, hnpos]
  · simp [hres, hmodiff]

private theorem residuePrefixSum_eq_natIndicatorSum
    (X H q a : ℕ) (w : ℤ → ℂ) (ha : a < q) :
    residuePrefixSum X H q a w =
      ∑ n ∈ Finset.Ioc X (X + H),
        if n % q = a then w (n : ℤ) else 0 := by
  classical
  have hmodiff (n : ℕ) :
      (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)] ↔ n % q = a := by
    rw [Int.natCast_modEq_iff]
    change n % q = a % q ↔ n % q = a
    rw [Nat.mod_eq_of_lt ha]
  rw [residuePrefixSum, Finset.sum_filter]
  rw [realIntegerInterval_sum_eq_nat_Ioc X H]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · simp [hmodiff, hres]
  · simp [hmodiff, hres]

private theorem residuePrefixSum_mu_eq_longCast
    (X H q a : ℕ) (ha : a < q) :
    residuePrefixSum X H q a (fun n => (paperMu n : ℂ)) =
      (longMobiusResidueIntervalSum q a X H : ℂ) := by
  classical
  rw [residuePrefixSum_eq_natIndicatorSum X H q a _ ha]
  unfold longMobiusResidueIntervalSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · have hnpos : 0 < n :=
      lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1
    simp [hres, paperMu, mobiusWeight, hnpos]
  · simp [hres]

private theorem residuePrefixSum_lambdaCramer_eq_longCast
    (X H q a : ℕ) (ha : a < q) :
    residuePrefixSum X H q a (fun n =>
      (paperLambda n : ℂ) -
        (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) =
      (longLambdaCramerResidueIntervalSum q a X H : ℂ) := by
  classical
  rw [residuePrefixSum_eq_natIndicatorSum X H q a _ ha]
  unfold longLambdaCramerResidueIntervalSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · have hnpos : 0 < n :=
      lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1
    simp [hres, paperLambda, vonMangoldtWeight_def, hnpos]
  · simp [hres]

private theorem longMobiusPointwise_le_max
    (X L q a : ℕ) (B : ℝ) (hq : q ∈ longModuliRange X B)
    (ha : a < q) :
    |longMobiusResidueIntervalSum q a X L| ≤
      longMobiusResidueMaximum X L B := by
  have houter := Finset.le_sup
    (f := fun q =>
      (Finset.range q).sup (fun a =>
        (⟨|longMobiusResidueIntervalSum q a X L|,
          abs_nonneg _⟩ : NNReal))) hq
  have hinner := Finset.le_sup
    (f := fun a =>
      (⟨|longMobiusResidueIntervalSum q a X L|,
        abs_nonneg _⟩ : NNReal))
    (Finset.mem_range.mpr ha)
  have hle :
      (⟨|longMobiusResidueIntervalSum q a X L|,
        abs_nonneg _⟩ : NNReal) ≤
        (longModuliRange X B).sup (fun q =>
          (Finset.range q).sup (fun a =>
            (⟨|longMobiusResidueIntervalSum q a X L|,
              abs_nonneg _⟩ : NNReal))) := by
    exact le_trans hinner houter
  unfold longMobiusResidueMaximum
  exact_mod_cast hle

private theorem longLambdaCramerPointwise_le_max
    (X L q a : ℕ) (B : ℝ) (hq : q ∈ longModuliRange X B)
    (ha : a < q) :
    |longLambdaCramerResidueIntervalSum q a X L| ≤
      longLambdaCramerResidueMaximum X L B := by
  have houter := Finset.le_sup
    (f := fun q =>
      (Finset.range q).sup (fun a =>
        (⟨|longLambdaCramerResidueIntervalSum q a X L|,
          abs_nonneg _⟩ : NNReal))) hq
  have hinner := Finset.le_sup
    (f := fun a =>
      (⟨|longLambdaCramerResidueIntervalSum q a X L|,
        abs_nonneg _⟩ : NNReal))
    (Finset.mem_range.mpr ha)
  have hle :
      (⟨|longLambdaCramerResidueIntervalSum q a X L|,
        abs_nonneg _⟩ : NNReal) ≤
        (longModuliRange X B).sup (fun q =>
          (Finset.range q).sup (fun a =>
            (⟨|longLambdaCramerResidueIntervalSum q a X L|,
              abs_nonneg _⟩ : NNReal))) := by
    exact le_trans hinner houter
  unfold longLambdaCramerResidueMaximum
  exact_mod_cast hle

private theorem longResiduePointwiseBounds_of_maxSum
    (X L q a : ℕ) (B M : ℝ)
    (hmax : longMobiusResidueMaximum X L B +
      longLambdaCramerResidueMaximum X L B ≤ M)
    (hq : 1 ≤ q) (hqB : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (ha : a < q) :
    |longMobiusResidueIntervalSum q a X L| ≤ M ∧
      |longLambdaCramerResidueIntervalSum q a X L| ≤ M := by
  have hnonnegMu : 0 ≤ longMobiusResidueMaximum X L B := by
    unfold longMobiusResidueMaximum
    positivity
  have hnonnegLambda : 0 ≤ longLambdaCramerResidueMaximum X L B := by
    unfold longLambdaCramerResidueMaximum
    positivity
  have hMuBound : longMobiusResidueMaximum X L B ≤ M :=
    (le_add_of_nonneg_right hnonnegLambda).trans hmax
  have hLambdaBound : longLambdaCramerResidueMaximum X L B ≤ M := by
    calc
      longLambdaCramerResidueMaximum X L B ≤
          longMobiusResidueMaximum X L B +
            longLambdaCramerResidueMaximum X L B :=
        le_add_of_nonneg_left hnonnegMu
      _ ≤ M := hmax
  have hqmem : q ∈ longModuliRange X B :=
    mem_longModuliRange_iff.mpr ⟨hq, hqB⟩
  exact ⟨(longMobiusPointwise_le_max X L q a B hqmem ha).trans hMuBound,
    (longLambdaCramerPointwise_le_max X L q a B hqmem ha).trans hLambdaBound⟩

/-- The source short-to-long error with `D ≥ A+3` has the exact logarithmic
absorption stated in the LONG+DP proof. -/
private theorem sourceCutoffTransferError_log_bound
    (A D C_D x X : ℝ) (hA : 0 < A) (hD : A + 3 ≤ D)
    (hCD : 0 ≤ C_D) (hx : 2 ≤ x) (hX : 0 < X) :
    128 * (1 + polynomialKernelM1) *
        (2 * x / (x ^ D) ^ 2 +
          ((1 + Real.log (x ^ D)) / Real.sqrt X) *
            (C_D * Real.sqrt X * x ^ (-(A + 3)))) ≤
      128 * (1 + polynomialKernelM1) *
        (2 + (1 + D) * C_D) * x ^ (-(A + 2)) := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hDnonneg : 0 ≤ D := by linarith
  have hlogx_nonneg : 0 ≤ Real.log x := by
    exact Real.log_nonneg (by linarith)
  have hlogx_le : Real.log x ≤ x := by
    exact (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
  have hlogW : 1 + Real.log (x ^ D) ≤ (1 + D) * x := by
    rw [Real.log_rpow hxpos]
    have hmul := mul_le_mul_of_nonneg_left hlogx_le hDnonneg
    nlinarith
  have hpowden : (x ^ D) ^ 2 = x ^ (2 * D) := by
    calc
      (x ^ D) ^ 2 = (x ^ D) ^ (2 : ℝ) := by norm_num
      _ = x ^ (D * 2) := by rw [← Real.rpow_mul hxpos.le]
      _ = x ^ (2 * D) := by congr 1 <;> ring
  have hfirstpow : x / (x ^ D) ^ 2 = x ^ (1 - 2 * D) := by
    calc
      x / (x ^ D) ^ 2 = x ^ (1 : ℝ) / x ^ (2 * D) := by
        rw [Real.rpow_one, hpowden]
      _ = x ^ (1 - 2 * D) := (Real.rpow_sub hxpos 1 (2 * D)).symm
  have hexp : 1 - 2 * D ≤ -(A + 2) := by nlinarith
  have hfirst : 2 * x / (x ^ D) ^ 2 ≤ 2 * x ^ (-(A + 2)) := by
    rw [show 2 * x / (x ^ D) ^ 2 = 2 * (x / (x ^ D) ^ 2) by ring,
      hfirstpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hxone hexp) (by norm_num)
  have hsqrtpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hsecond_eq :
      ((1 + Real.log (x ^ D)) / Real.sqrt X) *
          (C_D * Real.sqrt X * x ^ (-(A + 3))) =
        C_D * (1 + Real.log (x ^ D)) * x ^ (-(A + 3)) := by
    field_simp [hsqrtpos.ne']
  have hpowadd : x * x ^ (-(A + 3)) = x ^ (-(A + 2)) := by
    calc
      x * x ^ (-(A + 3)) = x ^ (1 : ℝ) * x ^ (-(A + 3)) := by
        rw [Real.rpow_one]
      _ = x ^ (1 + (-(A + 3))) :=
        (Real.rpow_add hxpos 1 (-(A + 3))).symm
      _ = x ^ (-(A + 2)) := by congr 1 <;> ring
  have hsecond :
      C_D * (1 + Real.log (x ^ D)) * x ^ (-(A + 3)) ≤
        (1 + D) * C_D * x ^ (-(A + 2)) := by
    calc
      C_D * (1 + Real.log (x ^ D)) * x ^ (-(A + 3)) ≤
          C_D * ((1 + D) * x) * x ^ (-(A + 3)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
            exact mul_le_mul_of_nonneg_left hlogW hCD
      _ = (1 + D) * C_D * (x * x ^ (-(A + 3))) := by ring
      _ = (1 + D) * C_D * x ^ (-(A + 2)) := by rw [hpowadd]
  have hkernel : 0 ≤ 128 * (1 + polynomialKernelM1) := by
    have hM1 : 0 ≤ polynomialKernelM1 := by
      unfold polynomialKernelM1
      exact integral_nonneg fun u =>
        mul_nonneg (abs_nonneg u) (polynomialKernelRho_nonneg u)
    positivity
  calc
    _ = 128 * (1 + polynomialKernelM1) *
          (2 * x / (x ^ D) ^ 2 +
            C_D * (1 + Real.log (x ^ D)) * x ^ (-(A + 3))) := by
            rw [hsecond_eq]
    _ ≤ 128 * (1 + polynomialKernelM1) *
          (2 * x ^ (-(A + 2)) +
            (1 + D) * C_D * x ^ (-(A + 2))) := by
            apply mul_le_mul_of_nonneg_left _ hkernel
            exact add_le_add hfirst hsecond
    _ = 128 * (1 + polynomialKernelM1) *
          (2 + (1 + D) * C_D) * x ^ (-(A + 2)) := by ring

private theorem abs_inv_mul_le_of_abs_le
    {H : ℝ} {S C p : ℝ} (hH : 0 < H)
    (hS : |S| ≤ C * H * p) :
    |H⁻¹ * S| ≤ C * p := by
  have hinv : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
  calc
    |H⁻¹ * S| = H⁻¹ * |S| := by rw [abs_mul, abs_of_nonneg hinv]
    _ ≤ H⁻¹ * (C * H * p) :=
      mul_le_mul_of_nonneg_left hS hinv
    _ = C * p := by field_simp [hH.ne']

/-- The exact finite average form of short-to-long transfer after substituting
the source DP envelope and absorbing its logarithmic factors. -/
theorem sourceResidueAverageDifference_of_meanEnvelope
    (A D C_D W : ℝ) (X H L q : ℕ) (a : ℤ) (f : ℤ → ℝ)
    (hA : 0 < A) (hD : A + 3 ≤ D) (hCD : 0 < C_D)
    (hX : 3 ≤ X) (hlog : 2 ≤ Real.log (X : ℝ))
    (hHpos : 0 < H) (hHX : H ≤ X)
    (hHhalf : Real.rpow (X : ℝ) (1 / 2 : ℝ) ≤ (H : ℝ))
    (hHL : H ≤ L) (hLpos : 0 < L) (hLX : L ≤ X)
    (hLW : (L : ℝ) ≤ (X : ℝ) / W ^ 4)
    (hWdef : W = (Real.log (X : ℝ)) ^ D)
    (hW2 : 2 ≤ W)
    (hWX : W ≤ Real.rpow (X : ℝ) (1 / 100 : ℝ))
    (hq : 0 < q)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ))
    (hMean : dirichletMeanEnvelope
        (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ) q a f
          (by exact_mod_cast hX) (by exact_mod_cast hHpos)
          (by exact_mod_cast hHX) (by exact_mod_cast hq) hf)
        ((X : ℝ) / (H : ℝ)) W ≤
          C_D * Real.sqrt (X : ℝ) *
            (Real.log (X : ℝ)) ^ (-(A + 3))) :
    |sourceRealResidueAverage X H q a f -
      sourceRealResidueAverage X L q a f| ≤
        128 * (1 + polynomialKernelM1) * (2 + (1 + D) * C_D) *
          (Real.log (X : ℝ)) ^ (-(A + 2)) := by
  let transferC := 128 * (1 + polynomialKernelM1) *
    (2 + (1 + D) * C_D)
  let avgH := sourceRealResidueAverage X H q a f
  let avgL := sourceRealResidueAverage X L q a f
  have hXr : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hHpos
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hLpos
  have hHXL : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
  have hHLr : (H : ℝ) ≤ (L : ℝ) := by exact_mod_cast hHL
  have hLXr : (L : ℝ) ≤ (X : ℝ) := by exact_mod_cast hLX
  have hTransfer := outerCutoffShortLongTransfer_fromMeanEnvelope
    (X : ℝ) (H : ℝ) (L : ℝ) W (A + 3) C_D q a f
    hXr hW2 hWX hHhalf hHLr hLW hHr hHXL hLr hLXr hq hf hMean
  have hErr := sourceCutoffTransferError_log_bound A D C_D
    (Real.log (X : ℝ)) (X : ℝ) hA hD (le_of_lt hCD) hlog (by positivity)
  have hErr' :
      128 * (1 + polynomialKernelM1) *
          (2 * Real.log (X : ℝ) / W ^ 2 +
            ((1 + Real.log W) / Real.sqrt (X : ℝ)) *
              (C_D * Real.sqrt (X : ℝ) *
                (Real.log (X : ℝ)) ^ (-(A + 3))) ) ≤
        transferC * (Real.log (X : ℝ)) ^ (-(A + 2)) := by
    simpa [transferC, hWdef] using hErr
  have hNH := sourceAverage_at_outerCutoff X H q a f
    hX hHpos hHX hq hf
  have hNL := sourceAverage_at_outerCutoff X L q a f
    hX hLpos hLX hq hf
  have hcomplex : ‖(avgH : ℂ) - (avgL : ℂ)‖ ≤
      transferC * (Real.log (X : ℝ)) ^ (-(A + 2)) := by
    simpa [avgH, avgL, hNH, hNL] using hTransfer.2.trans hErr'
  have hreal : |avgH - avgL| ≤
      transferC * (Real.log (X : ℝ)) ^ (-(A + 2)) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hcomplex
  simpa [avgH, avgL, transferC] using hreal

private theorem abs_mul_le_of_abs_inv_mul_le
    {H S C p : ℝ} (hH : 0 < H)
    (hAvg : |H⁻¹ * S| ≤ C * p) :
    |S| ≤ H * C * p := by
  have hinv : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
  have hident : H * |H⁻¹ * S| = |S| := by
    rw [abs_mul, abs_of_nonneg hinv]
    field_simp [hH.ne']
  calc
    |S| = H * |H⁻¹ * S| := hident.symm
    _ ≤ H * (C * p) := mul_le_mul_of_nonneg_left hAvg hH.le
    _ = H * C * p := by ring

/-- The exact large-X residue-class assembly from LONG and the two source DP
mean envelopes. This is the fixed-parameter step before the uniform threshold
and the bounded-X branch. -/
theorem ordinaryResidueClassBound_of_LONG_DP_means
    (A B D C_D C_L W : ℝ) (X H L q a : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hD : A + 3 ≤ D)
    (hCD : 0 < C_D) (hCL : 0 < C_L)
    (hX : 3 ≤ X) (hlog : 2 ≤ Real.log (X : ℝ))
    (hHpos : 0 < H) (hHX : H ≤ X)
    (hHhalf : Real.rpow (X : ℝ) (1 / 2 : ℝ) ≤ (H : ℝ))
    (hH58 : Real.rpow (X : ℝ) (5 / 8 : ℝ) ≤ (H : ℝ))
    (hHL : H ≤ L) (hLpos : 0 < L) (hLX : L ≤ X)
    (hLW : (L : ℝ) ≤ (X : ℝ) / W ^ 4)
    (hWdef : W = (Real.log (X : ℝ)) ^ D)
    (hW2 : 2 ≤ W)
    (hWX : W ≤ Real.rpow (X : ℝ) (1 / 100 : ℝ))
    (hq : 1 ≤ q) (hqB : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
    (ha : a < q)
    (hMeanMu : dirichletMeanEnvelope
        (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ) q
          (a : ℤ) (fun n => (paperMu n : ℝ))
          (by exact_mod_cast hX) (by exact_mod_cast hHpos)
          (by exact_mod_cast hHX) (by exact_mod_cast (show 0 < q by omega))
          (Or.inr rfl))
        ((X : ℝ) / (H : ℝ)) W ≤
          C_D * Real.sqrt (X : ℝ) *
            (Real.log (X : ℝ)) ^ (-(A + 3)))
    (hMeanLambda : dirichletMeanEnvelope
        (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ) q
          (a : ℤ) paperLambda
          (by exact_mod_cast hX) (by exact_mod_cast hHpos)
          (by exact_mod_cast hHX) (by exact_mod_cast (show 0 < q by omega))
          (Or.inl rfl))
        ((X : ℝ) / (H : ℝ)) W ≤
          C_D * Real.sqrt (X : ℝ) *
            (Real.log (X : ℝ)) ^ (-(A + 3)))
    (hLong : longMobiusResidueMaximum X L B +
      longLambdaCramerResidueMaximum X L B ≤
        C_L * (L : ℝ) * (Real.log (X : ℝ)) ^ (-(A + 2))) :
    ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ +
      ‖residuePrefixSum X H q a (fun n =>
        (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
      2 * (C_L +
        128 * (1 + polynomialKernelM1) * (2 + (1 + D) * C_D) +
        cramerShortLongStabilityConstant (A + 2)) *
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  classical
  let transferC := 128 * (1 + polynomialKernelM1) *
    (2 + (1 + D) * C_D)
  let stabC := cramerShortLongStabilityConstant (A + 2)
  let K := C_L + transferC + stabC
  let avgMuH := sourceRealResidueAverage X H q (a : ℤ)
    (fun n => (paperMu n : ℝ))
  let avgMuL := sourceRealResidueAverage X L q (a : ℤ)
    (fun n => (paperMu n : ℝ))
  let avgLambdaH := sourceRealResidueAverage X H q (a : ℤ) paperLambda
  let avgLambdaL := sourceRealResidueAverage X L q (a : ℤ) paperLambda
  let modelH := (H : ℝ)⁻¹ *
    ∑ n ∈ (Finset.Ioc X (X + H)).filter
      (fun n : ℕ => (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)]),
      paperShortBlockCramerWeight (X : ℝ) (n : ℤ)
  let modelL := (L : ℝ)⁻¹ *
    ∑ n ∈ (Finset.Ioc X (X + L)).filter
      (fun n : ℕ => (n : ℤ) ≡ (a : ℤ) [ZMOD (q : ℤ)]),
      paperShortBlockCramerWeight (X : ℝ) (n : ℤ)
  let corrH := avgLambdaH - modelH
  let corrL := avgLambdaL - modelL
  have hXr : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hHpos
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hLpos
  have hH58r : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ) := hH58
  have hqr : 0 < q := by omega
  have hCtr : 0 ≤ transferC := by
    dsimp [transferC]
    have hDnonneg : 0 ≤ D := by linarith
    have hM1 : 0 ≤ polynomialKernelM1 := by
      unfold polynomialKernelM1
      exact integral_nonneg fun u =>
        mul_nonneg (abs_nonneg u) (polynomialKernelRho_nonneg u)
    have hright : 0 ≤ 2 + (1 + D) * C_D := by positivity
    exact mul_nonneg (by positivity) hright
  have hStab : 0 ≤ stabC := by
    dsimp [stabC, cramerShortLongStabilityConstant,
      cramerApproximationConstant]
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let p := (Real.log (X : ℝ)) ^ (-(A + 2))
  have hp : 0 ≤ p := Real.rpow_nonneg (by linarith [hlog]) _
  have hDiffMu := sourceResidueAverageDifference_of_meanEnvelope
    A D C_D W X H L q (a : ℤ) (fun n => (paperMu n : ℝ))
    hA hD hCD hX hlog hHpos hHX hHhalf hHL hLpos hLX hLW hWdef hW2 hWX hqr
    (Or.inr rfl) hMeanMu
  have hDiffLambda := sourceResidueAverageDifference_of_meanEnvelope
    A D C_D W X H L q (a : ℤ) paperLambda
    hA hD hCD hX hlog hHpos hHX hHhalf hHL hLpos hLX hLW hWdef hW2 hWX hqr
    (Or.inl rfl) hMeanLambda
  have hStable := cramerShortLongStability
    (A + 2) X H L q (a : ℤ) (by linarith) hX hH58 hHL hLX hqr
  have hDiffMu' : |avgMuH - avgMuL| ≤ transferC * p := by
    simpa [p] using hDiffMu
  have hDiffLambda' : |avgLambdaH - avgLambdaL| ≤ transferC * p := by
    simpa [p] using hDiffLambda
  have hStable' : |modelH - modelL| ≤ stabC * p := by
    simpa [p, stabC, modelH, modelL] using hStable
  have hClass := longResiduePointwiseBounds_of_maxSum
    X L q a B (C_L * (L : ℝ) * (Real.log (X : ℝ)) ^ (-(A + 2)))
    hLong hq hqB ha
  have hAvgMuL : |avgMuL| ≤ C_L * p := by
    dsimp [avgMuL]
    rw [sourceAverage_mu_eq_long X L q a ha]
    simpa [p] using abs_inv_mul_le_of_abs_le hLr hClass.1
  have hAvgCorrL : |corrL| ≤ C_L * p := by
    dsimp [corrL, avgLambdaL, modelL]
    rw [sourceAverage_lambdaCramer_eq_long X L q a ha]
    simpa [p] using abs_inv_mul_le_of_abs_le hLr hClass.2
  have hAvgMuH : |avgMuH| ≤ (C_L + transferC) * p := by
    calc
      |avgMuH| = |(avgMuH - avgMuL) + avgMuL| := by congr 1 <;> ring
      _ ≤ |avgMuH - avgMuL| + |avgMuL| := abs_add_le _ _
      _ ≤ transferC * p + C_L * p := add_le_add hDiffMu' hAvgMuL
      _ = (C_L + transferC) * p := by ring
  have hCorrDiff : |corrH - corrL| ≤ (transferC + stabC) * p := by
    have htriangle :
        |corrH - corrL| ≤ |avgLambdaH - avgLambdaL| + |modelH - modelL| := by
      calc
        |corrH - corrL| = |(avgLambdaH - avgLambdaL) - (modelH - modelL)| := by
          congr 1 <;> dsimp [corrH, corrL] <;> ring
        _ = |(avgLambdaH - avgLambdaL) + -(modelH - modelL)| := by
          congr 1 <;> ring
        _ ≤ |avgLambdaH - avgLambdaL| + |-(modelH - modelL)| := abs_add_le _ _
        _ = |avgLambdaH - avgLambdaL| + |modelH - modelL| := by
          rw [abs_neg]
    calc
      |corrH - corrL| ≤ |avgLambdaH - avgLambdaL| + |modelH - modelL| :=
        htriangle
      _ ≤ transferC * p + stabC * p := add_le_add hDiffLambda' hStable'
      _ = (transferC + stabC) * p := by ring
  have hAvgCorrH : |corrH| ≤ K * p := by
    calc
      |corrH| = |(corrH - corrL) + corrL| := by congr 1 <;> ring
      _ ≤ |corrH - corrL| + |corrL| := abs_add_le _ _
      _ ≤ (transferC + stabC) * p + C_L * p := add_le_add hCorrDiff hAvgCorrL
      _ = K * p := by dsimp [K]; ring
  have hAvgMuH' : |avgMuH| ≤ K * p := by
    calc
      |avgMuH| ≤ (C_L + transferC) * p := hAvgMuH
      _ ≤ K * p := by
        apply mul_le_mul_of_nonneg_right _ hp
        dsimp [K]
        linarith [hStab]
  have hMuInv : |(H : ℝ)⁻¹ * longMobiusResidueIntervalSum q a X H| ≤
      K * p := by
    dsimp [avgMuH] at hAvgMuH'
    rw [sourceAverage_mu_eq_long X H q a ha] at hAvgMuH'
    exact hAvgMuH'
  have hCorrInv : |(H : ℝ)⁻¹ * longLambdaCramerResidueIntervalSum q a X H| ≤
      K * p := by
    dsimp [corrH, avgLambdaH, modelH] at hAvgCorrH
    rw [sourceAverage_lambdaCramer_eq_long X H q a ha] at hAvgCorrH
    exact hAvgCorrH
  have hMuSum := abs_mul_le_of_abs_inv_mul_le hHr hMuInv
  have hLambdaSum := abs_mul_le_of_abs_inv_mul_le hHr hCorrInv
  have hMuPrefix :
      ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ ≤
        (H : ℝ) * K * p := by
    rw [residuePrefixSum_mu_eq_longCast X H q a ha]
    simpa using hMuSum
  have hLambdaPrefix :
      ‖residuePrefixSum X H q a (fun n =>
        (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
        (H : ℝ) * K * p := by
    rw [residuePrefixSum_lambdaCramer_eq_longCast X H q a ha]
    simpa using hLambdaSum
  have hlogPow : p ≤ (Real.log (X : ℝ)) ^ (-A : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hlog])
    linarith
  calc
    _ ≤ (H : ℝ) * K * p + (H : ℝ) * K * p :=
      add_le_add hMuPrefix hLambdaPrefix
    _ = 2 * K * (H : ℝ) * p := by ring
    _ ≤ 2 * K * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      apply mul_le_mul_of_nonneg_left hlogPow
      have hcoef : 0 ≤ 2 * K * (H : ℝ) := by positivity
      exact hcoef
    _ = 2 * (C_L + transferC + stabC) * (H : ℝ) *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by dsimp [K]
    _ = 2 * (C_L +
        128 * (1 + polynomialKernelM1) * (2 + (1 + D) * C_D) +
        cramerShortLongStabilityConstant (A + 2)) *
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          dsimp [transferC, stabC]

private theorem sourceFloorShortLengthBounds
    (A eta D : ℝ) (X H : ℕ)
    (hA : 0 < A) (heta : 0 < eta) (hetaMax : eta < 3 / 16)
    (hD : A + 3 ≤ D) (hX : 3 ≤ X)
    (hlog : 2 ≤ Real.log (X : ℝ))
    (hGrowth : 2 * (Real.log (X : ℝ)) ^ (4 * D + 1) ≤ (X : ℝ) ^ eta)
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - eta)) :
    let L := Nat.floor ((X : ℝ) / (Real.log (X : ℝ)) ^ (4 * D + 1))
    0 < L ∧ L ≤ X ∧ H ≤ L ∧
      (X : ℝ) * (Real.log (X : ℝ)) ^ (-(4 * D + 2)) ≤ (L : ℝ) := by
  classical
  let x := Real.log (X : ℝ)
  let R := 4 * D + 1
  let y := (X : ℝ) / x ^ R
  let L := Nat.floor y
  have hxpos : 0 < x := by linarith [hlog]
  have hxone : 1 ≤ x := by linarith [hlog]
  have hXr : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : 0 < (X : ℝ) := by linarith
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hRnonneg : 0 ≤ R := hRpos.le
  have hEtaLeOne : eta ≤ 1 := by linarith [hetaMax]
  have hXeta : (X : ℝ) ^ eta ≤ (X : ℝ) := by
    calc
      (X : ℝ) ^ eta ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXr hEtaLeOne
      _ = (X : ℝ) := by rw [Real.rpow_one]
  have hGrowthX : 2 * x ^ R ≤ (X : ℝ) := by
    dsimp [x, R] at hGrowth ⊢
    exact hGrowth.trans hXeta
  have hGrowthEta : 2 * x ^ R ≤ (X : ℝ) ^ eta := by
    simpa [x, R] using hGrowth
  have hdenpos : 0 < x ^ R := Real.rpow_pos_of_pos hxpos _
  have hyge : 2 ≤ y := by
    dsimp [y]
    exact (le_div_iff₀ hdenpos).2 hGrowthX
  have hfloorHalf : y / 2 ≤ (L : ℝ) := by
    dsimp [L]
    exact FractionalPrimes.natFloor_half_le_of_one_le
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) hyge)
  have hfloorUpper : (L : ℝ) ≤ y := by
    dsimp [L, y]
    exact Nat.floor_le (div_nonneg (by positivity : 0 ≤ (X : ℝ)) hdenpos.le)
  have hRpowOne : 1 ≤ x ^ R := by
    have hp := Real.rpow_le_rpow_of_exponent_le hxone (show (0 : ℝ) ≤ R by linarith)
    simpa using hp
  have hyUpperX : y ≤ (X : ℝ) := by
    dsimp [y]
    apply (div_le_iff₀ hdenpos).2
    calc
      (X : ℝ) = (X : ℝ) * 1 := by ring
      _ ≤ (X : ℝ) * x ^ R :=
        mul_le_mul_of_nonneg_left hRpowOne (by positivity)
  have hLleXreal : (L : ℝ) ≤ (X : ℝ) := hfloorUpper.trans hyUpperX
  have hLleX : L ≤ X := by exact_mod_cast hLleXreal
  have hLpos : 0 < L := by
    have hLone : (1 : ℝ) ≤ (L : ℝ) := by
      linarith [hfloorHalf]
    exact_mod_cast hLone
  have hdenSmallPos : 0 < 2 * x ^ R := by positivity
  have hXetaPos : 0 < (X : ℝ) ^ eta := Real.rpow_pos_of_pos hXpos _
  have hInvEta : ((X : ℝ) ^ eta)⁻¹ ≤ (2 * x ^ R)⁻¹ :=
    by
      have h := one_div_le_one_div_of_le hdenSmallPos hGrowthEta
      simpa [one_div] using h
  have hquotEta : (X : ℝ) / (X : ℝ) ^ eta ≤
      (X : ℝ) / (2 * x ^ R) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hInvEta (by positivity)
  have hquotEtaEq : (X : ℝ) / (X : ℝ) ^ eta =
      (X : ℝ) ^ (1 - eta) := by
    calc
      (X : ℝ) / (X : ℝ) ^ eta =
          (X : ℝ) ^ (1 : ℝ) / (X : ℝ) ^ eta := by rw [Real.rpow_one]
      _ = (X : ℝ) ^ (1 - eta) := (Real.rpow_sub hXpos 1 eta).symm
  have hyHalfEq : y / 2 = (X : ℝ) / (2 * x ^ R) := by
    dsimp [y]
    field_simp [hdenpos.ne']
  have hfloorLowEta : (X : ℝ) ^ (1 - eta) ≤ (L : ℝ) := by
    calc
      (X : ℝ) ^ (1 - eta) = (X : ℝ) / (X : ℝ) ^ eta := hquotEtaEq.symm
      _ ≤ (X : ℝ) / (2 * x ^ R) := hquotEta
      _ = y / 2 := hyHalfEq.symm
      _ ≤ (L : ℝ) := hfloorHalf
  have hHleLreal : (H : ℝ) ≤ (L : ℝ) := hHupper.trans hfloorLowEta
  have hHleL : H ≤ L := by exact_mod_cast hHleLreal
  have hdenGrow : 2 * x ^ R ≤ x ^ (R + 1) := by
    calc
      2 * x ^ R ≤ x * x ^ R := mul_le_mul_of_nonneg_right hlog
        (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (R + 1) := by
        rw [Real.rpow_add hxpos R 1, Real.rpow_one]
        ring
  have hbigPos : 0 < x ^ (R + 1) := Real.rpow_pos_of_pos hxpos _
  have hInvGrow : (x ^ (R + 1))⁻¹ ≤ (2 * x ^ R)⁻¹ :=
    by
      have h := one_div_le_one_div_of_le hdenSmallPos hdenGrow
      simpa [one_div] using h
  have hquotGrow : (X : ℝ) / x ^ (R + 1) ≤
      (X : ℝ) / (2 * x ^ R) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hInvGrow (by positivity)
  have hfloorLong : (X : ℝ) / x ^ (R + 1) ≤ (L : ℝ) := by
    calc
      (X : ℝ) / x ^ (R + 1) ≤ (X : ℝ) / (2 * x ^ R) := hquotGrow
      _ = y / 2 := hyHalfEq.symm
      _ ≤ (L : ℝ) := hfloorHalf
  have hlongPow : x ^ (-(R + 1)) = (x ^ (R + 1))⁻¹ :=
    Real.rpow_neg hxpos.le (R + 1)
  have hfloorLong' :
      (X : ℝ) * x ^ (-(R + 1)) ≤ (L : ℝ) := by
    calc
      (X : ℝ) * x ^ (-(R + 1)) = (X : ℝ) / x ^ (R + 1) := by
        rw [hlongPow, div_eq_mul_inv]
      _ ≤ (L : ℝ) := hfloorLong
  have hRadd : R + 1 = 4 * D + 2 := by dsimp [R]; ring
  refine ⟨hLpos, hLleX, hHleL, ?_⟩
  simpa [x, hRadd] using hfloorLong'

set_option maxHeartbeats 1000000 in
/-- The exact uniform ordinary full-residue cancellation consequence of the
source LONG and DP contracts.  All thresholds and constants are fixed before
the interval and residue parameters. -/
theorem ordinaryFullResidueCancellation_of_LONG_DP
    (hLONG : LongGlobalProperty)
    (hDP : shortIntervalDirichletTask) :
    ordinaryFullResidueCancellationTask := by
  intro A B eta hA hB heta hetaMax
  have hADP : 0 < A + 3 := by linarith
  obtain ⟨D₀, hD₀, hDwork⟩ := hDP (A + 3) B eta hADP hB heta hetaMax
  let D : ℝ := max D₀ (A + 3)
  have hD₀D : D₀ ≤ D := le_max_left _ _
  have hAD : A + 3 ≤ D := le_max_right _ _
  have hDpos : 0 ≤ D := by linarith
  obtain ⟨C_D, X_D, hC_D, hX_D, hDPbound⟩ := hDwork D hD₀D
  have hA2 : 0 < A + 2 := by linarith
  have hBpos : 0 < B := hB
  have hRpos : 0 < 4 * D + 2 := by positivity
  obtain ⟨C_L, hC_L, hLONGbound⟩ :=
    hLONG (A + 2) B (4 * D + 2) hA2 hBpos hRpos
  let R : ℝ := 4 * D + 1
  let Mη : ℝ := logAbsorptionM eta R
  let t₀ : ℝ := max 2 ((2 / eta) * Real.log (2 * Mη))
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp t₀)
  obtain ⟨N_D, hN_D⟩ := exists_nat_gt X_D
  let Xstar : ℕ := max N_D (max 3 N)
  have hXstar3 : 3 ≤ Xstar := by
    dsimp [Xstar]
    exact Nat.le_trans (Nat.le_max_left 3 N)
      (Nat.le_max_right N_D (max 3 N))
  have hCsmallPos : 0 < (Real.exp 13 + 3) *
      (Real.log (Xstar : ℝ)) ^ (A + 1) := by
    have hXstarpos : 0 < (Xstar : ℝ) := by exact_mod_cast (by omega : 0 < Xstar)
    have hlogpos : 0 < Real.log (Xstar : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < Xstar))
    positivity
  let Csmall : ℝ := (Real.exp 13 + 3) *
    (Real.log (Xstar : ℝ)) ^ (A + 1)
  let Cmain : ℝ := 2 * (C_L +
      128 * (1 + polynomialKernelM1) * (2 + (1 + D) * C_D) +
      cramerShortLongStabilityConstant (A + 2))
  let C_F : ℝ := max Cmain Csmall
  have hCmainPos : 0 < Cmain := by
    dsimp [Cmain]
    have hM1 : 0 ≤ polynomialKernelM1 := by
      unfold polynomialKernelM1
      exact integral_nonneg fun u =>
        mul_nonneg (abs_nonneg u) (polynomialKernelRho_nonneg u)
    have hstab : 0 ≤ cramerShortLongStabilityConstant (A + 2) := by
      dsimp [cramerShortLongStabilityConstant, cramerApproximationConstant]
      positivity
    positivity
  have hC_F : 0 < C_F := by
    dsimp [C_F]
    exact lt_of_lt_of_le hCmainPos (le_max_left _ _)
  refine ⟨C_F, hC_F, ?_⟩
  intro X H hX hHlower hHupper q hq hqB a ha
  have hXr : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hXone : 1 ≤ (X : ℝ) := by linarith
  by_cases hcut : Xstar ≤ X
  · have hXstarleX : (Xstar : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcut
    have hNleXnat : N ≤ X := by
      apply Nat.le_trans (Nat.le_max_right 3 N)
      exact Nat.le_trans (Nat.le_max_right N_D (max 3 N)) hcut
    have hNDleXnat : N_D ≤ X := by
      exact Nat.le_trans (Nat.le_max_left N_D (max 3 N)) hcut
    have hXDreal : X_D ≤ (X : ℝ) := by
      have hNDreal : (N_D : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNDleXnat
      exact le_trans (le_of_lt hN_D) hNDreal
    have hExpTleX : Real.exp t₀ ≤ (X : ℝ) := by
      exact le_trans (le_of_lt hN) (by exact_mod_cast hNleXnat)
    have hlogtwo : 2 ≤ Real.log (X : ℝ) := by
      apply (Real.le_log_iff_exp_le hXpos).2
      exact le_trans (Real.exp_le_exp.mpr (le_max_left 2 _)) hExpTleX
    have ht₀le : t₀ ≤ Real.log (X : ℝ) :=
      (Real.le_log_iff_exp_le hXpos).2 hExpTleX
    have hAbsLarge :
        (2 / eta) * Real.log (2 * logAbsorptionM eta R) ≤
          Real.log (X : ℝ) := by
      calc
        _ ≤ t₀ := le_max_right 2 _
        _ ≤ Real.log (X : ℝ) := ht₀le
    have hGrowth :
        2 * (Real.log (X : ℝ)) ^ (4 * D + 1) ≤ (X : ℝ) ^ eta := by
      have hAbs := log_absorption_bound heta (by dsimp [R]; positivity)
        (by norm_num : (1 : ℝ) ≤ 2) hXone hAbsLarge
      simpa [R] using hAbs
    have hHpos : 0 < H := by
      have hp : 0 < (X : ℝ) ^ ((5 / 8 : ℝ) + eta) :=
        Real.rpow_pos_of_pos hXpos _
      exact_mod_cast (lt_of_lt_of_le hp hHlower)
    have hHX : H ≤ X := by
      have hpow : (X : ℝ) ^ (1 - eta) ≤ (X : ℝ) := by
        have hexp : 1 - eta ≤ (1 : ℝ) := by linarith
        calc
          (X : ℝ) ^ (1 - eta) ≤ (X : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hXone hexp
          _ = (X : ℝ) := by rw [Real.rpow_one]
      exact_mod_cast hHupper.trans hpow
    have hHhalf : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ) := by
      have hpow : (X : ℝ) ^ (1 / 2 : ℝ) ≤
          (X : ℝ) ^ ((5 / 8 : ℝ) + eta) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      exact hpow.trans hHlower
    have hH58 : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ) := by
      have hpow : (X : ℝ) ^ (5 / 8 : ℝ) ≤
          (X : ℝ) ^ ((5 / 8 : ℝ) + eta) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      exact hpow.trans hHlower
    let W : ℝ := (Real.log (X : ℝ)) ^ D
    let T₀ : ℝ := (X : ℝ) / (H : ℝ)
    have hDPX := hDPbound (by exact hX_D) X H hXDreal hHlower hHupper
    have hWindow :
        2 ≤ W ∧ W ≤ (X : ℝ) ^ (1 / 100 : ℝ) ∧ W ≤ T₀ := by
      simpa [W, T₀] using hDPX.1
    have hDPall := hDPX.2
    have hMeanMu : dirichletMeanEnvelope
        (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ) q
          (a : ℤ) (fun n => (paperMu n : ℝ))
          (by exact_mod_cast hX) (by exact_mod_cast hHpos)
          (by exact_mod_cast hHX) (by exact_mod_cast (show 0 < q by omega))
          (Or.inr rfl))
        ((X : ℝ) / (H : ℝ)) W ≤
          C_D * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + 3)) := by
      simpa [W, T₀] using
        hDPall q hq hqB (a : ℤ) (fun n => (paperMu n : ℝ)) (Or.inr rfl)
    have hMeanLambda : dirichletMeanEnvelope
        (outerCutoffWindowData polynomialKernelRho (X : ℝ) (H : ℝ) q
          (a : ℤ) paperLambda
          (by exact_mod_cast hX) (by exact_mod_cast hHpos)
          (by exact_mod_cast hHX) (by exact_mod_cast (show 0 < q by omega))
          (Or.inl rfl))
        ((X : ℝ) / (H : ℝ)) W ≤
          C_D * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + 3)) := by
      simpa [W, T₀] using
        hDPall q hq hqB (a : ℤ) paperLambda (Or.inl rfl)
    let L : ℕ := Nat.floor ((X : ℝ) /
      (Real.log (X : ℝ)) ^ (4 * D + 1))
    have hFloor := sourceFloorShortLengthBounds A eta D X H
      hA heta hetaMax hAD hX hlogtwo hGrowth hHupper
    have hFloor' : 0 < L ∧ L ≤ X ∧ H ≤ L ∧
        (X : ℝ) * (Real.log (X : ℝ)) ^ (-(4 * D + 2)) ≤ (L : ℝ) := by
      simpa [L] using hFloor
    rcases hFloor' with ⟨hLpos, hLX, hHL, hLongLength⟩
    have hLong := hLONGbound X L hX hLongLength hLX
    have hLW : (L : ℝ) ≤ (X : ℝ) / W ^ 4 := by
      have hx : 0 < Real.log (X : ℝ) := by linarith [hlogtwo]
      have hdenSmall : 0 < (Real.log (X : ℝ)) ^ (4 * D) :=
        Real.rpow_pos_of_pos hx _
      have hdenBig : 0 < (Real.log (X : ℝ)) ^ (4 * D + 1) :=
        Real.rpow_pos_of_pos hx _
      have hpow : (Real.log (X : ℝ)) ^ (4 * D) ≤
          (Real.log (X : ℝ)) ^ (4 * D + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hlogtwo]) (by ring_nf; linarith)
      have hfloorUpper : (L : ℝ) ≤
          (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * D + 1) := by
        dsimp [L]
        apply Nat.floor_le
        exact div_nonneg (by positivity) hdenBig.le
      have hdiv : (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * D + 1) ≤
          (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * D) := by
        apply (div_le_div_iff₀ hdenBig hdenSmall).2
        nlinarith [hpow, hXpos]
      have hW4 : W ^ 4 = (Real.log (X : ℝ)) ^ (4 * D) := by
        calc
          W ^ 4 = ((Real.log (X : ℝ)) ^ D) ^ 4 := by rfl
          _ = (Real.log (X : ℝ)) ^ (D * 4) :=
            (Real.rpow_mul_natCast hx.le D 4).symm
          _ = (Real.log (X : ℝ)) ^ (4 * D) := by congr 1 <;> ring
      calc
        (L : ℝ) ≤ (X : ℝ) /
            (Real.log (X : ℝ)) ^ (4 * D + 1) := hfloorUpper
        _ ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ (4 * D) := hdiv
        _ = (X : ℝ) / W ^ 4 := by rw [hW4]
    have hlarge := ordinaryResidueClassBound_of_LONG_DP_means
      (A := A) (B := B) (D := D) (C_D := C_D) (C_L := C_L)
      (W := W) (X := X) (H := H) (L := L) (q := q) (a := a)
      hA hB hAD hC_D hC_L hX hlogtwo hHpos hHX hHhalf hH58 hHL hLpos
      hLX hLW (by rfl) hWindow.1 hWindow.2.1 hq hqB ha hMeanMu hMeanLambda hLong
    have hmainle : Cmain ≤ C_F := by dsimp [C_F]; exact le_max_left _ _
    calc
      _ ≤ 2 * (C_L +
          128 * (1 + polynomialKernelM1) * (2 + (1 + D) * C_D) +
          cramerShortLongStabilityConstant (A + 2)) *
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := hlarge
      _ ≤ C_F * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_nonneg (by linarith [hlogtwo]) _)
        apply mul_le_mul_of_nonneg_right hmainle
        exact_mod_cast (Nat.zero_le H)
  · have hsmallX : X < Xstar := Nat.lt_of_not_ge hcut
    have hHle : H ≤ X := by
      have hpow : (X : ℝ) ^ (1 - eta) ≤ (X : ℝ) := by
        have hexp : 1 - eta ≤ (1 : ℝ) := by linarith
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hXone hexp
      exact_mod_cast hHupper.trans hpow
    have hbound := residuePrefixPair_pointwiseBound X H q a hX hHle
    have hlogXge1 : 1 ≤ Real.log (X : ℝ) := by
      apply (Real.le_log_iff_exp_le hXpos).2
      exact Real.exp_one_lt_three.le.trans hXr
    have hlogXpos : 0 < Real.log (X : ℝ) := lt_of_lt_of_le (by norm_num) hlogXge1
    have hlogle : Real.log (X : ℝ) ≤ Real.log (Xstar : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hsmallX.le)
    have hpowle : (Real.log (X : ℝ)) ^ (A + 1) ≤
        (Real.log (Xstar : ℝ)) ^ (A + 1) :=
      Real.rpow_le_rpow (by linarith) hlogle (by linarith)
    have hpowneg : 0 ≤ (Real.log (X : ℝ)) ^ (-A : ℝ) :=
      Real.rpow_nonneg (by linarith [hlogXge1]) _
    have hpowidentity :
        (Real.log (X : ℝ)) ^ (A + 1) *
            (Real.log (X : ℝ)) ^ (-A : ℝ) = Real.log (X : ℝ) := by
      rw [← Real.rpow_add hlogXpos]
      have hexp : A + 1 + -A = (1 : ℝ) := by ring
      rw [hexp, Real.rpow_one]
    have hlogbound : Real.log (X : ℝ) ≤
        (Real.log (Xstar : ℝ)) ^ (A + 1) *
          (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      calc
        Real.log (X : ℝ) =
            (Real.log (X : ℝ)) ^ (A + 1) *
              (Real.log (X : ℝ)) ^ (-A : ℝ) := hpowidentity.symm
        _ ≤ (Real.log (Xstar : ℝ)) ^ (A + 1) *
              (Real.log (X : ℝ)) ^ (-A : ℝ) :=
            mul_le_mul_of_nonneg_right hpowle hpowneg
    have hsmallBound :
        ‖residuePrefixSum X H q a (fun n => (paperMu n : ℂ))‖ +
          ‖residuePrefixSum X H q a (fun n =>
            (paperLambda n : ℂ) -
              (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ ≤
        Csmall * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      dsimp [Csmall]
      calc
        _ ≤ (Real.exp 13 + 3) * (H : ℝ) * Real.log (X : ℝ) := hbound
        _ ≤ (Real.exp 13 + 3) * (H : ℝ) *
              ((Real.log (Xstar : ℝ)) ^ (A + 1) *
                (Real.log (X : ℝ)) ^ (-A : ℝ)) := by
              apply mul_le_mul_of_nonneg_left hlogbound
              positivity
        _ = (Real.exp 13 + 3) * (Real.log (Xstar : ℝ)) ^ (A + 1) *
              (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by ring
    have hleC : Csmall ≤ C_F := by dsimp [C_F]; exact le_max_right _ _
    calc
      _ ≤ Csmall * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := hsmallBound
      _ ≤ C_F * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith [hlogXge1]) _)
        apply mul_le_mul_of_nonneg_right hleC (by exact_mod_cast (Nat.zero_le H))

/-- LONG and the exact scalar DP task imply the source's positive-degree
polynomial major-arc task, via ordinary full-residue cancellation. -/
theorem polynomialMajorArcTask_of_LONG_DP
    (hLONG : LongGlobalProperty)
    (hDP : shortIntervalDirichletTask) :
    polynomialMajorArcTask :=
  polynomialMajorArcTask_of_ordinaryFullResidueCancellation
    (ordinaryFullResidueCancellation_of_LONG_DP hLONG hDP)

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.ordinaryFullResidueCancellation_of_LONG_DP
#print axioms FractionalPrimes.Literature.Polynomial.polynomialMajorArcTask_of_LONG_DP
