module

public import FractionalPrimes.Literature.Harmonic.FiniteSignSquareFunction
public import FractionalPrimes.Literature.Harmonic.FrequencyProjectionSignedMikhlin
public import FractionalPrimes.Literature.Multiplier.DyadicKernelAbsoluteReconstruction
public import FractionalPrimes.LpConvolutionCLM
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# The finite `ℓᵖ` frequency resolution

This module connects the checked periodic signed-Mikhlin estimate to the
finite Rademacher square-function argument. The all-positive partial sums
give continuous operators for the individual projections, and the signed
Mikhlin multiplier identifies each finite signed operator sum.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped Topology
open scoped BigOperators ENNReal

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier
open FractionalPrimes.Literature.JSW

noncomputable section

local instance : IsProbabilityMeasure torusHaar := torusHaar_isProbability
local instance : NeBot (𝓝[≠] (0 : Torus)) := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  let seq : ℕ → Torus := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : Torus)
  have hseqR : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq : Tendsto seq atTop (𝓝 (0 : Torus)) := by
    exact (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hseqR
  have hfreq : ∃ᶠ n : ℕ in atTop, seq n ∈ {ξ : Torus | ξ ≠ 0} := by
    apply Filter.Eventually.frequently
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    dsimp [seq]
    intro hzero
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : 1 / ((n : ℝ) + 1) < 1 := by
      apply (div_lt_one (by positivity)).2
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hk := (AddCircle.coe_eq_zero_of_pos_iff (p := (1 : ℝ))
      (by norm_num : (0 : ℝ) < (1 : ℝ)) hpos).mp hzero
    rcases hk with ⟨k, hk⟩
    have hkreal : (k : ℝ) = 1 / ((n : ℝ) + 1) := by
      simpa [zsmul_eq_mul] using hk
    have hkne : k ≠ 0 := by
      intro hk0
      subst k
      have hnreal : (0 : ℝ) ≤ n := by positivity
      linarith
    have hkge : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkne)
    linarith
  exact mem_closure_of_frequently_of_tendsto hfreq hseq
local instance : NullSingletonClass torusHaar := by
  unfold torusHaar
  infer_instance
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The finite multiplier symbol obtained by taking all signs positive up to
the indicated scale. -/
def frequencyProjectionPartialSigns : ℕ → ℝ := fun _ => 1

/-- The source `SymbolData` for the positive partial sum through `N`. -/
theorem frequencyProjectionPartialData (c : ℝ) (hc : 1 < c) (N : ℕ) :
    SymbolData
      (finiteFrequencyProjectionSignedLift c N frequencyProjectionPartialSigns)
      frequencyProjectionSignedMikhlinConstant :=
  (finiteFrequencyProjectionSignedMikhlin hc N
    frequencyProjectionPartialSigns
    (by intro h hh; norm_num [frequencyProjectionPartialSigns])).toSymbolData

/-- The bounded multiplier associated to a positive partial sum. -/
def frequencyProjectionPartialLpOperator {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
  finiteMultiplierLpExtension (frequencyProjectionPartialData c hc N) hp1

/-- Uniform operator norm for every positive partial sum. -/
theorem frequencyProjectionPartialLpOperator_opNorm_le {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) :
    ‖frequencyProjectionPartialLpOperator c hc hp1 N‖ ≤
      periodicMultiplierConstant p * frequencyProjectionSignedMikhlinConstant := by
  calc
    ‖frequencyProjectionPartialLpOperator c hc hp1 N‖ ≤
        finiteMultiplierLpNormConstant p * frequencyProjectionSignedMikhlinConstant :=
      finiteMultiplierLpExtension_opNorm_le
        (frequencyProjectionPartialData c hc N) hp1
    _ = periodicMultiplierConstant p * frequencyProjectionSignedMikhlinConstant := by
      rw [← periodicMultiplierConstant_eq_finiteMultiplierLpNormConstant hp1]

/-- The multiplier on circle `L²` associated to an `L∞` symbol class. -/
def frequencyProjectionTmL2FromSymbolLp
    (g : Lp ℂ ⊤ torusHaar) (f : lp (fun _ : ℤ => ℂ) 2) :
    lp (fun _ : ℤ => ℂ) 2 :=
  sequenceToCircleL2.symm (g • sequenceToCircleL2 f)

theorem TmL2_eq_frequencyProjectionTmL2FromSymbolLp
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    TmL2 h f = frequencyProjectionTmL2FromSymbolLp (torusSymbolLp h) f := rfl

/-- The `L²` multiplier is additive in its `L∞` symbol class. -/
theorem frequencyProjectionTmL2FromSymbolLp_add
    (g₁ g₂ : Lp ℂ ⊤ torusHaar) (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp (g₁ + g₂) f =
      frequencyProjectionTmL2FromSymbolLp g₁ f +
        frequencyProjectionTmL2FromSymbolLp g₂ f := by
  simp only [frequencyProjectionTmL2FromSymbolLp, Lp.smul_add, map_add]

/-- The `L²` multiplier is complex-linear in its `L∞` symbol class. -/
theorem frequencyProjectionTmL2FromSymbolLp_smul
    (a : ℂ) (g : Lp ℂ ⊤ torusHaar) (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp (a • g) f =
      a • frequencyProjectionTmL2FromSymbolLp g f := by
  simp only [frequencyProjectionTmL2FromSymbolLp, Lp.smul_assoc, map_smul]

/-- The `L²` multiplier is additive in its `L∞` symbol class. -/
theorem frequencyProjectionTmL2FromSymbolLp_neg
    (g : Lp ℂ ⊤ torusHaar) (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp (-g) f =
      -frequencyProjectionTmL2FromSymbolLp g f := by
  simp only [frequencyProjectionTmL2FromSymbolLp, Lp.neg_smul, map_neg]

/-- Subtraction in the symbol class becomes subtraction of the associated
`L²` multiplier outputs. -/
theorem frequencyProjectionTmL2FromSymbolLp_sub
    (g₁ g₂ : Lp ℂ ⊤ torusHaar) (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp (g₁ - g₂) f =
      frequencyProjectionTmL2FromSymbolLp g₁ f -
        frequencyProjectionTmL2FromSymbolLp g₂ f := by
  rw [show g₁ - g₂ = g₁ + -g₂ by exact sub_eq_add_neg _ _,
    frequencyProjectionTmL2FromSymbolLp_add,
    frequencyProjectionTmL2FromSymbolLp_neg]
  abel

/-- The `L²` multiplier map is linear in the symbol class. -/
def frequencyProjectionTmL2SymbolLinearMap
    (f : lp (fun _ : ℤ => ℂ) 2) :
    Lp ℂ ⊤ torusHaar →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun := fun g => frequencyProjectionTmL2FromSymbolLp g f
  map_add' := fun g₁ g₂ => frequencyProjectionTmL2FromSymbolLp_add g₁ g₂ f
  map_smul' := fun a g => frequencyProjectionTmL2FromSymbolLp_smul a g f

/-- The multiplier of a finite sum of symbol classes is the finite sum of
their `L²` multiplier outputs. -/
theorem frequencyProjectionTmL2FromSymbolLp_sum
    {ι : Type*} (s : Finset ι) (g : ι → Lp ℂ ⊤ torusHaar)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp (∑ i ∈ s, g i) f =
      ∑ i ∈ s, frequencyProjectionTmL2FromSymbolLp (g i) f := by
  change frequencyProjectionTmL2SymbolLinearMap f (∑ i ∈ s, g i) = _
  exact map_sum (frequencyProjectionTmL2SymbolLinearMap f) g s

/-- The torus symbol is additive whenever its real-line periodic lifts are
pointwise additive. -/
theorem torusSymbol_eq_add_of_pointwise
    {m m₁ m₂ : ℝ → ℂ} {D D₁ D₂ : ℝ}
    (h : SymbolData m D) (h₁ : SymbolData m₁ D₁) (h₂ : SymbolData m₂ D₂)
    (hpoint : ∀ x, m x = m₁ x + m₂ x) :
    torusSymbol h = torusSymbol h₁ + torusSymbol h₂ := by
  funext ξ
  induction ξ using QuotientAddGroup.induction_on with
  | H x =>
      change torusSymbol h (x : Torus) =
        torusSymbol h₁ (x : Torus) + torusSymbol h₂ (x : Torus)
      rw [torusSymbol_coe, torusSymbol_coe, torusSymbol_coe]
      exact hpoint x

/-- The `L∞` class of a torus symbol inherits pointwise addition of lifts. -/
theorem torusSymbolLp_eq_add_of_pointwise
    {m m₁ m₂ : ℝ → ℂ} {D D₁ D₂ : ℝ}
    (h : SymbolData m D) (h₁ : SymbolData m₁ D₁) (h₂ : SymbolData m₂ D₂)
    (hpoint : ∀ x, m x = m₁ x + m₂ x) :
    torusSymbolLp h = torusSymbolLp h₁ + torusSymbolLp h₂ := by
  apply Lp.ext
  filter_upwards [torusSymbolLp_coeFn h, torusSymbolLp_coeFn h₁,
    torusSymbolLp_coeFn h₂,
    Lp.coeFn_add (torusSymbolLp h₁) (torusSymbolLp h₂)] with ξ hm hm₁ hm₂ hadd
  calc
    (torusSymbolLp h : Torus → ℂ) ξ = torusSymbol h ξ := hm
    _ = torusSymbol h₁ ξ + torusSymbol h₂ ξ :=
      congrFun (torusSymbol_eq_add_of_pointwise h h₁ h₂ hpoint) ξ
    _ = ((torusSymbolLp h₁ + torusSymbolLp h₂ : Lp ℂ ⊤ torusHaar) :
        Torus → ℂ) ξ := by
      rw [← hm₁, ← hm₂]
      exact hadd.symm

/-- The `L∞` class of a torus symbol inherits pointwise complex scaling of
its periodic lift. -/
theorem torusSymbolLp_eq_smul_of_pointwise
    {m m₁ : ℝ → ℂ} {D D₁ : ℝ} (a : ℂ)
    (h : SymbolData m D) (h₁ : SymbolData m₁ D₁)
    (hpoint : ∀ x, m x = a * m₁ x) :
    torusSymbolLp h = a • torusSymbolLp h₁ := by
  apply Lp.ext
  filter_upwards [torusSymbolLp_coeFn h, torusSymbolLp_coeFn h₁,
    Lp.coeFn_smul a (torusSymbolLp h₁)] with ξ hm hm₁ hsmul
  calc
    (torusSymbolLp h : Torus → ℂ) ξ = torusSymbol h ξ := hm
    _ = a * torusSymbol h₁ ξ := by
      induction ξ using QuotientAddGroup.induction_on with
      | H x =>
          rw [torusSymbol_coe, torusSymbol_coe]
          exact hpoint x
    _ = (a • torusSymbolLp h₁ : Lp ℂ ⊤ torusHaar) ξ := by
      rw [← hm₁]
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul.symm

/-- The `L²` multiplier is additive in compatible periodic symbol data. -/
theorem TmL2_add_of_pointwise
    {m m₁ m₂ : ℝ → ℂ} {D D₁ D₂ : ℝ}
    (h : SymbolData m D) (h₁ : SymbolData m₁ D₁) (h₂ : SymbolData m₂ D₂)
    (hpoint : ∀ x, m x = m₁ x + m₂ x) (f : lp (fun _ : ℤ => ℂ) 2) :
    TmL2 h f = TmL2 h₁ f + TmL2 h₂ f := by
  rw [TmL2_eq_frequencyProjectionTmL2FromSymbolLp,
    torusSymbolLp_eq_add_of_pointwise h h₁ h₂ hpoint,
    frequencyProjectionTmL2FromSymbolLp_add]
  rw [← TmL2_eq_frequencyProjectionTmL2FromSymbolLp,
    ← TmL2_eq_frequencyProjectionTmL2FromSymbolLp]

/-- The `L²` multiplier is complex-linear in compatible periodic symbol
data. -/
theorem TmL2_smul_of_pointwise
    {m m₁ : ℝ → ℂ} {D D₁ : ℝ} (a : ℂ)
    (h : SymbolData m D) (h₁ : SymbolData m₁ D₁)
    (hpoint : ∀ x, m x = a * m₁ x) (f : lp (fun _ : ℤ => ℂ) 2) :
    TmL2 h f = a • TmL2 h₁ f := by
  rw [TmL2_eq_frequencyProjectionTmL2FromSymbolLp,
    torusSymbolLp_eq_smul_of_pointwise a h h₁ hpoint,
    frequencyProjectionTmL2FromSymbolLp_smul,
    ← TmL2_eq_frequencyProjectionTmL2FromSymbolLp]

/-- The torus symbol of a positive partial sum is the finite sum of its
frequency projections. -/
theorem frequencyProjectionPartialData_torusSymbol_eq_sum
    (c : ℝ) (hc : 1 < c) (N : ℕ) (ξ : Torus) :
    torusSymbol (frequencyProjectionPartialData c hc N) ξ =
      ∑ h ∈ Finset.range (N + 1),
        (frequencyProjectionSymbol c (h : ℤ) ξ : ℂ) := by
  induction ξ using QuotientAddGroup.induction_on with
  | H x =>
      rw [torusSymbol_coe]
      unfold finiteFrequencyProjectionSignedLift
      simp only [frequencyProjectionPartialSigns, Complex.ofReal_one, one_mul]
      apply Finset.sum_congr rfl
      intro h hh
      rw [frequencyProjectionPeriodicLift_eq_torusSymbol]

/-- Removing consecutive positive partial sums recovers one projection. -/
theorem frequencyProjectionPartialData_difference_eq_projection
    (c : ℝ) (hc : 1 < c) (h : ℕ) (ξ : Torus) :
    torusSymbol (frequencyProjectionPartialData c hc h) ξ -
        (if h = 0 then 0 else
          torusSymbol (frequencyProjectionPartialData c hc (h - 1)) ξ) =
      (frequencyProjectionSymbol c (h : ℤ) ξ : ℂ) := by
  rw [frequencyProjectionPartialData_torusSymbol_eq_sum c hc,
    frequencyProjectionPartialData_torusSymbol_eq_sum c hc]
  cases h with
  | zero =>
      simp
  | succ h =>
      rw [Finset.sum_range_succ]
      simp

/-- The real-line lift of the positive partial sum through `N`. -/
def frequencyProjectionPartialLift (c : ℝ) (N : ℕ) (ξ : ℝ) : ℂ :=
  finiteFrequencyProjectionSignedLift c N frequencyProjectionPartialSigns ξ

/-- Consecutive positive partial lifts differ by the projection at the new
index. -/
theorem frequencyProjectionPartialLift_difference_eq_projection
    (c : ℝ) (h : ℕ) (ξ : ℝ) :
    frequencyProjectionPartialLift c h ξ -
        (if h = 0 then 0 else frequencyProjectionPartialLift c (h - 1) ξ) =
      frequencyProjectionPeriodicLift c (h : ℤ) ξ := by
  cases h with
  | zero =>
      simp [frequencyProjectionPartialLift, finiteFrequencyProjectionSignedLift,
        frequencyProjectionPartialSigns]
  | succ h =>
      simp [frequencyProjectionPartialLift, finiteFrequencyProjectionSignedLift,
        frequencyProjectionPartialSigns, Finset.sum_range_succ]

/-- Every finite signed lift is the matching finite signed sum of successive
positive-partial differences. -/
theorem finiteFrequencyProjectionSignedLift_eq_sum_partialDifferences
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) (ξ : ℝ) :
    finiteFrequencyProjectionSignedLift c N ε ξ =
      ∑ i : Fin (N + 1), (ε i.val : ℂ) *
        (frequencyProjectionPartialLift c i.val ξ -
          (if i.val = 0 then 0 else
            frequencyProjectionPartialLift c (i.val - 1) ξ)) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (ε i : ℂ) *
      (frequencyProjectionPartialLift c i ξ -
        (if i = 0 then 0 else frequencyProjectionPartialLift c (i - 1) ξ)))
    (N + 1)]
  unfold finiteFrequencyProjectionSignedLift
  apply Finset.sum_congr rfl
  intro i hi
  rw [frequencyProjectionPartialLift_difference_eq_projection]

/-- The positive partial lift agrees with its torus symbol at every
represented point. -/
theorem frequencyProjectionPartialLift_eq_torusSymbol
    (c : ℝ) (hc : 1 < c) (N : ℕ) (ξ : ℝ) :
    frequencyProjectionPartialLift c N ξ =
      torusSymbol (frequencyProjectionPartialData c hc N) (ξ : Torus) := by
  rw [frequencyProjectionPartialData_torusSymbol_eq_sum c hc N]
  unfold frequencyProjectionPartialLift finiteFrequencyProjectionSignedLift
  simp only [frequencyProjectionPartialSigns, Complex.ofReal_one, one_mul]
  apply Finset.sum_congr rfl
  intro h hh
  rw [frequencyProjectionPeriodicLift_eq_torusSymbol]

/-- The checked source data for an arbitrary finite signed resolution. -/
theorem frequencyProjectionSignedData (c : ℝ) (hc : 1 < c) (N : ℕ)
    (ε : ℕ → ℝ) (hε : ∀ h ≤ N, |ε h| = 1) :
    SymbolData (finiteFrequencyProjectionSignedLift c N ε)
      frequencyProjectionSignedMikhlinConstant :=
  (finiteFrequencyProjectionSignedMikhlin hc N ε hε).toSymbolData

/-- Recursive JSW signs, in the coordinate order used by `jswSignSum`. -/
def frequencyProjectionRademacherCoordinate :
    (n : ℕ) → jswSignSpace n → Fin n → ℝ
  | 0, _, i => Fin.elim0 i
  | n + 1, (b, ω), i =>
      Fin.cases (jswSign b)
        (fun j => frequencyProjectionRademacherCoordinate n ω j) i

theorem frequencyProjectionRademacherCoordinate_abs_eq_one
    (n : ℕ) (ω : jswSignSpace n) (i : Fin n) :
    |frequencyProjectionRademacherCoordinate n ω i| = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases ω with
      | mk b ω =>
          cases i using Fin.cases with
          | zero => cases b <;> norm_num [frequencyProjectionRademacherCoordinate, jswSign]
          | succ i => exact ih ω i

/-- The recursive JSW signed sum is the coordinate sum for the sign
coordinates above. -/
theorem frequencyProjectionRademacherSum_eq_coordinateSum
    (n : ℕ) (ω : jswSignSpace n) (z : Fin n → ℂ) :
    jswSignSum n ω z =
      ∑ i : Fin n,
        (frequencyProjectionRademacherCoordinate n ω i : ℂ) * z i := by
  induction n with
  | zero => simp [jswSignSum, frequencyProjectionRademacherCoordinate]
  | succ n ih =>
      cases ω with
      | mk b ω =>
          rw [jswSignSum]
          simp [frequencyProjectionRademacherCoordinate, Fin.sum_univ_succ, ih]

/-- Extend the coordinate signs by zero after the finite range. -/
def frequencyProjectionRademacherExtension
    (N : ℕ) (ω : jswSignSpace (N + 1)) (j : ℕ) : ℝ :=
  if hj : j ≤ N then
    frequencyProjectionRademacherCoordinate (N + 1) ω ⟨j, by omega⟩
  else 0

theorem frequencyProjectionRademacherExtension_abs_eq_one
    (N : ℕ) (ω : jswSignSpace (N + 1)) (j : ℕ) (hj : j ≤ N) :
    |frequencyProjectionRademacherExtension N ω j| = 1 := by
  simp [frequencyProjectionRademacherExtension, hj,
    frequencyProjectionRademacherCoordinate_abs_eq_one]

/-- The signed torus symbol equals the signed sum of positive partial
differences. -/
theorem frequencyProjectionSignedData_torusSymbol_eq_sumPartialDifferences
    (c : ℝ) (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) (ξ : Torus) :
    torusSymbol (frequencyProjectionSignedData c hc N ε hε) ξ =
      ∑ i : Fin (N + 1), (ε i.val : ℂ) *
        (torusSymbol (frequencyProjectionPartialData c hc i.val) ξ -
          (if i.val = 0 then 0 else
            torusSymbol (frequencyProjectionPartialData c hc (i.val - 1)) ξ)) := by
  induction ξ using QuotientAddGroup.induction_on with
  | H x =>
      rw [torusSymbol_coe]
      rw [finiteFrequencyProjectionSignedLift_eq_sum_partialDifferences]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← frequencyProjectionPartialLift_eq_torusSymbol c hc i.val x]
      rfl

/-- The `L∞` class of a positive partial difference. -/
def frequencyProjectionPartialSymbolDifferenceLp
    (c : ℝ) (hc : 1 < c) (i : ℕ) : Lp ℂ ⊤ torusHaar :=
  torusSymbolLp (frequencyProjectionPartialData c hc i) -
    if i = 0 then 0 else
      torusSymbolLp (frequencyProjectionPartialData c hc (i - 1))

/-- The continuous `ℓᵖ` operator for one source projection, realized as the
difference of its consecutive positive partial multipliers. -/
def frequencyProjectionLpOperatorFamily {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) :
    Fin (N + 1) →
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
        lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
  fun i =>
    if i.val = 0 then frequencyProjectionPartialLpOperator c hc hp1 0
    else frequencyProjectionPartialLpOperator c hc hp1 i.val -
      frequencyProjectionPartialLpOperator c hc hp1 (i.val - 1)

/-- The finite signed multiplier operator supplied by the Mikhlin adapter. -/
def frequencyProjectionSignedLpOperator {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
  finiteMultiplierLpExtension (frequencyProjectionSignedData c hc N ε hε) hp1

/-- The finite signed multiplier inherits the exact source multiplier norm
bound, uniformly over its finite sign choices. -/
theorem frequencyProjectionSignedLpOperator_opNorm_le {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) :
    ‖frequencyProjectionSignedLpOperator c hc hp1 N ε hε‖ ≤
      periodicMultiplierConstant p * frequencyProjectionSignedMikhlinConstant := by
  calc
    ‖frequencyProjectionSignedLpOperator c hc hp1 N ε hε‖ ≤
        finiteMultiplierLpNormConstant p * frequencyProjectionSignedMikhlinConstant :=
      finiteMultiplierLpExtension_opNorm_le
        (frequencyProjectionSignedData c hc N ε hε) hp1
    _ = periodicMultiplierConstant p * frequencyProjectionSignedMikhlinConstant := by
      rw [← periodicMultiplierConstant_eq_finiteMultiplierLpNormConstant hp1]

private theorem lp_coeFn_finset_sum_ae {α E : Type*} {p : ENNReal}
    [NormedAddCommGroup E] (s : Finset α) (f : α → Lp E p torusHaar) :
    (↑(∑ i ∈ s, f i) : Torus → E) =ᵐ[torusHaar]
      fun ξ => ∑ i ∈ s, f i ξ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero E p torusHaar] with ξ hz
      simpa using hz
  | @insert a s has ih =>
      rw [Finset.sum_insert has]
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ξ hadd hs
      calc
        ((f a + ∑ i ∈ s, f i : Lp E p torusHaar) : Torus → E) ξ =
            ((f a : Torus → E) + (↑↑(∑ i ∈ s, f i) : Torus → E)) ξ := hadd
        _ = f a ξ + (↑↑(∑ i ∈ s, f i) : Torus → E) ξ := rfl
        _ = f a ξ + ∑ i ∈ s, f i ξ := by rw [hs]
        _ = ∑ i ∈ insert a s, f i ξ := by rw [Finset.sum_insert has]

/-- The `L∞` class of the signed multiplier is the same finite signed sum
of the classes of consecutive positive partial differences. -/
theorem frequencyProjectionSignedData_torusSymbolLp_eq_sumPartialDifferences
    (c : ℝ) (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) :
    torusSymbolLp (frequencyProjectionSignedData c hc N ε hε) =
      ∑ i : Fin (N + 1), (ε i.val : ℂ) •
        frequencyProjectionPartialSymbolDifferenceLp c hc i.val := by
  apply Lp.ext
  have hsum := lp_coeFn_finset_sum_ae (Finset.univ : Finset (Fin (N + 1)))
    (fun i : Fin (N + 1) => (ε i.val : ℂ) •
      frequencyProjectionPartialSymbolDifferenceLp c hc i.val)
  have hterm (i : Fin (N + 1)) : ∀ᵐ ξ ∂torusHaar,
      ((ε i.val : ℂ) • frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
        Lp ℂ ⊤ torusHaar) ξ =
        (ε i.val : ℂ) *
          (torusSymbol (frequencyProjectionPartialData c hc i.val) ξ -
            (if i.val = 0 then 0 else
              torusSymbol (frequencyProjectionPartialData c hc (i.val - 1)) ξ)) := by
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst i
      filter_upwards [Lp.coeFn_smul (ε 0 : ℂ)
          (frequencyProjectionPartialSymbolDifferenceLp c hc 0),
        torusSymbolLp_coeFn (frequencyProjectionPartialData c hc 0)] with ξ hmul hdata
      calc
        ((ε 0 : ℂ) • frequencyProjectionPartialSymbolDifferenceLp c hc 0 :
            Lp ℂ ⊤ torusHaar) ξ =
            ((ε 0 : ℂ) • (frequencyProjectionPartialSymbolDifferenceLp c hc 0 :
              Torus → ℂ)) ξ := hmul
        _ = (ε 0 : ℂ) * torusSymbol (frequencyProjectionPartialData c hc 0) ξ := by
          simp [frequencyProjectionPartialSymbolDifferenceLp, hdata,
            Pi.smul_apply, smul_eq_mul]
        _ = (ε 0 : ℂ) *
            (torusSymbol (frequencyProjectionPartialData c hc 0) ξ -
              (if 0 = 0 then 0 else
                torusSymbol (frequencyProjectionPartialData c hc 0) ξ)) := by simp
    · filter_upwards [Lp.coeFn_smul (ε i.val : ℂ)
          (frequencyProjectionPartialSymbolDifferenceLp c hc i.val),
        Lp.coeFn_sub (torusSymbolLp (frequencyProjectionPartialData c hc i.val))
          (torusSymbolLp (frequencyProjectionPartialData c hc (i.val - 1))),
        torusSymbolLp_coeFn (frequencyProjectionPartialData c hc i.val),
        torusSymbolLp_coeFn (frequencyProjectionPartialData c hc (i.val - 1))]
        with ξ hmul hsub hdata hprev
      calc
        ((ε i.val : ℂ) • frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
            Lp ℂ ⊤ torusHaar) ξ =
            ((ε i.val : ℂ) •
              (frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
                Torus → ℂ)) ξ := hmul
        _ = (ε i.val : ℂ) *
            (frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
              Torus → ℂ) ξ := by simp [Pi.smul_apply, smul_eq_mul]
        _ = (ε i.val : ℂ) *
            ((torusSymbolLp (frequencyProjectionPartialData c hc i.val) -
              torusSymbolLp (frequencyProjectionPartialData c hc (i.val - 1)) :
                Lp ℂ ⊤ torusHaar) : Torus → ℂ) ξ := by
              congr 1
              simp [frequencyProjectionPartialSymbolDifferenceLp, hi0]
        _ = (ε i.val : ℂ) *
            ((torusSymbolLp (frequencyProjectionPartialData c hc i.val) :
                Torus → ℂ) ξ -
              (torusSymbolLp (frequencyProjectionPartialData c hc (i.val - 1)) :
                Torus → ℂ) ξ) := by
          exact congrArg (fun z : ℂ => (ε i.val : ℂ) * z) hsub
        _ = (ε i.val : ℂ) *
            (torusSymbol (frequencyProjectionPartialData c hc i.val) ξ -
              (if i.val = 0 then 0 else
                torusSymbol (frequencyProjectionPartialData c hc (i.val - 1)) ξ)) := by
              rw [hdata, hprev]
              simp [hi0]
  have hall : ∀ᵐ ξ ∂torusHaar, ∀ i : Fin (N + 1),
      ((ε i.val : ℂ) • frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
        Lp ℂ ⊤ torusHaar) ξ =
        (ε i.val : ℂ) *
          (torusSymbol (frequencyProjectionPartialData c hc i.val) ξ -
            (if i.val = 0 then 0 else
              torusSymbol (frequencyProjectionPartialData c hc (i.val - 1)) ξ)) := by
    rw [ae_all_iff]
    intro i
    exact hterm i
  filter_upwards [torusSymbolLp_coeFn (frequencyProjectionSignedData c hc N ε hε),
    hsum, hall] with ξ hdata hsum hterms
  calc
    (torusSymbolLp (frequencyProjectionSignedData c hc N ε hε) : Torus → ℂ) ξ =
        torusSymbol (frequencyProjectionSignedData c hc N ε hε) ξ := hdata
    _ = ∑ i : Fin (N + 1), (ε i.val : ℂ) *
        (torusSymbol (frequencyProjectionPartialData c hc i.val) ξ -
          (if i.val = 0 then 0 else
            torusSymbol (frequencyProjectionPartialData c hc (i.val - 1)) ξ)) :=
      frequencyProjectionSignedData_torusSymbol_eq_sumPartialDifferences
        c hc N ε hε ξ
    _ = ∑ i : Fin (N + 1),
        ((ε i.val : ℂ) • frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
          Lp ℂ ⊤ torusHaar) ξ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hterms i).symm
    _ = (∑ i : Fin (N + 1),
        (ε i.val : ℂ) • frequencyProjectionPartialSymbolDifferenceLp c hc i.val :
          Lp ℂ ⊤ torusHaar) ξ := hsum.symm

/-- On `ℓ²` finite inputs, the signed multiplier acts as the corresponding
finite signed sum of projection outputs. -/
theorem TmL2_frequencyProjectionSignedData_eq_sumPartialDifferences
    (c : ℝ) (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) (f : lp (fun _ : ℤ => ℂ) 2) :
    TmL2 (frequencyProjectionSignedData c hc N ε hε) f =
      ∑ i : Fin (N + 1), (ε i.val : ℂ) •
        (TmL2 (frequencyProjectionPartialData c hc i.val) f -
          (if i.val = 0 then 0 else
            TmL2 (frequencyProjectionPartialData c hc (i.val - 1)) f)) := by
  rw [TmL2_eq_frequencyProjectionTmL2FromSymbolLp
      (frequencyProjectionSignedData c hc N ε hε) f,
    frequencyProjectionSignedData_torusSymbolLp_eq_sumPartialDifferences c hc N ε hε,
    frequencyProjectionTmL2FromSymbolLp_sum
      (Finset.univ : Finset (Fin (N + 1)))
      (fun i => (ε i.val : ℂ) • frequencyProjectionPartialSymbolDifferenceLp
        c hc i.val) f]
  apply Finset.sum_congr rfl
  intro i hi
  rw [frequencyProjectionTmL2FromSymbolLp_smul]
  by_cases hi0 : i.val = 0
  · have hiFin : i = 0 := Fin.ext hi0
    subst i
    simp [frequencyProjectionPartialSymbolDifferenceLp,
      TmL2_eq_frequencyProjectionTmL2FromSymbolLp]
  · simp [frequencyProjectionPartialSymbolDifferenceLp, hi0,
      frequencyProjectionTmL2FromSymbolLp_sub,
      TmL2_eq_frequencyProjectionTmL2FromSymbolLp]

/-- On a finite input, one `ℓᵖ` projection operator has the exact `ℓ²`
Fourier multiplier action prescribed by its source symbol. -/
theorem frequencyProjectionLpOperatorFamily_apply_finite
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) (i : Fin (N + 1)) (f : ℤ →₀ ℂ) (x : ℤ) :
    frequencyProjectionLpOperatorFamily c hc hp1 N i
        (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) x =
      TmL2 (frequencyProjectionPartialData c hc i.val)
          (finiteSequenceL2 f) x -
        (if i.val = 0 then 0 else
          TmL2 (frequencyProjectionPartialData c hc (i.val - 1))
            (finiteSequenceL2 f) x) := by
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    simp [frequencyProjectionLpOperatorFamily, frequencyProjectionPartialLpOperator,
      finiteMultiplierLpExtension_apply_finite, finiteMultiplierLpMap_apply]
  · simp [frequencyProjectionLpOperatorFamily, hi0,
      frequencyProjectionPartialLpOperator,
      finiteMultiplierLpExtension_apply_finite, finiteMultiplierLpMap_apply]

/-- The recursive signed sum of the `ℓᵖ` projections is exactly the
Mikhlin multiplier for the corresponding finite source sign sequence. -/
theorem finiteSignedProjectionOperator_eq_frequencyProjectionSignedLpOperator
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) (ω : jswSignSpace (N + 1)) :
    finiteSignedProjectionOperator (N + 1) ω
        (frequencyProjectionLpOperatorFamily c hc hp1 N) =
      frequencyProjectionSignedLpOperator c hc hp1 N
        (frequencyProjectionRademacherExtension N ω)
        (fun j hj => frequencyProjectionRademacherExtension_abs_eq_one N ω j hj) := by
  let ε := frequencyProjectionRademacherExtension N ω
  let hε : ∀ j ≤ N, |ε j| = 1 := by
    intro j hj
    exact frequencyProjectionRademacherExtension_abs_eq_one N ω j hj
  let hdata := frequencyProjectionSignedData c hc N ε hε
  let G := finiteSignedProjectionOperator (N + 1) ω
    (frequencyProjectionLpOperatorFamily c hc hp1 N)
  have hrestriction :
      G.toLinearMap.comp
        (finiteSupportLpInclusion (P := ENNReal.ofReal p)) =
        finiteMultiplierLpMap (p := p) hdata hp1 := by
    apply LinearMap.ext
    intro f
    apply lp.ext
    funext x
    calc
      G (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) x =
          jswSignSum (N + 1) ω
            (fun i => frequencyProjectionLpOperatorFamily c hc hp1 N i
              (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) x) := by
                change finiteSignedProjectionOperator (N + 1) ω
                  (frequencyProjectionLpOperatorFamily c hc hp1 N)
                  (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) x = _
                rw [finiteSignedProjectionOperator_apply]
      _ = ∑ i : Fin (N + 1),
          (frequencyProjectionRademacherCoordinate (N + 1) ω i : ℂ) *
            frequencyProjectionLpOperatorFamily c hc hp1 N i
              (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) x :=
        frequencyProjectionRademacherSum_eq_coordinateSum (N + 1) ω _
      _ = ∑ i : Fin (N + 1),
          (frequencyProjectionRademacherCoordinate (N + 1) ω i : ℂ) *
            (TmL2 (frequencyProjectionPartialData c hc i.val)
                (finiteSequenceL2 f) x -
              (if i.val = 0 then 0 else
                TmL2 (frequencyProjectionPartialData c hc (i.val - 1))
                  (finiteSequenceL2 f) x)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [frequencyProjectionLpOperatorFamily_apply_finite]
      _ = (finiteMultiplierLpMap (p := p) hdata hp1 f) x := by
        have hcoefficient (i : Fin (N + 1)) :
            (frequencyProjectionRademacherExtension N ω i.val : ℂ) =
              (frequencyProjectionRademacherCoordinate (N + 1) ω i : ℂ) := by
          have hiNat : i.val ≤ N := by omega
          have hiFin : (⟨i.val, by omega⟩ : Fin (N + 1)) = i := by
            exact Fin.ext rfl
          simp [frequencyProjectionRademacherExtension, hiNat, hiFin]
        rw [finiteMultiplierLpMap_apply]
        rw [TmL2_frequencyProjectionSignedData_eq_sumPartialDifferences
          c hc N ε hε (finiteSequenceL2 f)]
        simp only [lp.coeFn_sum, lp.coeFn_smul, lp.coeFn_sub, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoefficient i]
        by_cases hi0 : i.val = 0
        · have hiFin : i = 0 := Fin.ext hi0
          subst i
          simp only [if_pos hi0, lp.coeFn_sub, lp.coeFn_zero,
            Pi.sub_apply, Pi.zero_apply, sub_zero]
        · simp only [if_neg hi0, lp.coeFn_sub, lp.coeFn_zero,
            Pi.sub_apply, Pi.zero_apply]
  have hext := finiteMultiplierLpExtension_unique hdata hp1 G hrestriction
  change G = finiteMultiplierLpExtension hdata hp1
  exact hext.symm

/-- A nonnegative fixed constant controlling every finite signed
frequency-resolution multiplier. -/
def frequencyProjectionSignedLpBound (p : ℝ) : ℝ :=
  periodicMultiplierConstant p * frequencyProjectionSignedMikhlinConstant

theorem frequencyProjectionSignedMikhlinConstant_nonneg :
    0 ≤ frequencyProjectionSignedMikhlinConstant := by
  unfold frequencyProjectionSignedMikhlinConstant
  positivity [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]

theorem frequencyProjectionSignedLpBound_nonneg {p : ℝ} (hp1 : 1 < p) :
    0 ≤ frequencyProjectionSignedLpBound p := by
  unfold frequencyProjectionSignedLpBound
  rw [periodicMultiplierConstant_eq_finiteMultiplierLpNormConstant hp1]
  exact mul_nonneg (finiteMultiplierLpNormConstant_nonneg hp1)
    frequencyProjectionSignedMikhlinConstant_nonneg

/-- Exact constant in the finite-coordinate square-function estimate. -/
def frequencyProjectionFiniteSquareFunctionBound (p : ℝ) : ℝ :=
  Real.sqrt 2 * Real.rpow 12 (1 / p) * frequencyProjectionSignedLpBound p

/-- The finite inhomogeneous square function satisfies the source finite-sign
bound in `ℓᵖ`, uniformly in the truncation. -/
theorem frequencyProjectionFiniteSquareFunction_memLp_norm_le
    {p : ℝ} (hp1 : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (c : ℝ) (hc : 1 < c) (N : ℕ)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, g x = finiteProjectionSquareFunction (N + 1)
        (frequencyProjectionLpOperatorFamily c hc hp1 N) f x) ∧
      ‖g‖ ≤ frequencyProjectionFiniteSquareFunctionBound p * ‖f‖ := by
  let T := frequencyProjectionLpOperatorFamily c hc hp1 N
  let M := frequencyProjectionSignedLpBound p
  have hM : 0 ≤ M := frequencyProjectionSignedLpBound_nonneg hp1
  have hT : ∀ ω : jswSignSpace (N + 1),
      ‖finiteSignedProjectionOperator (N + 1) ω T‖ ≤ M := by
    intro ω
    rw [finiteSignedProjectionOperator_eq_frequencyProjectionSignedLpOperator
      c hc hp1 N ω]
    exact frequencyProjectionSignedLpOperator_opNorm_le c hc hp1 N
      (frequencyProjectionRademacherExtension N ω)
      (fun j hj => frequencyProjectionRademacherExtension_abs_eq_one N ω j hj)
  rcases finiteProjectionSquareFunction_memLp_norm_le hp1 hM T hT f with
    ⟨g, hg, hnorm⟩
  refine ⟨g, ?_, ?_⟩
  · exact hg
  · calc
      ‖g‖ ≤ Real.sqrt 2 * Real.rpow 12 (1 / p) * (M * ‖f‖) := hnorm
      _ = frequencyProjectionFiniteSquareFunctionBound p * ‖f‖ := by
        dsimp [frequencyProjectionFiniteSquareFunctionBound,
          frequencyProjectionSignedLpBound, M]
        ring

/-- One nonnegative-frequency projection, defined as the difference of the
positive partial sums. The source projections with negative integer index
are zero, so the natural index here records exactly the nonzero family. -/
def frequencyProjectionLpProjection {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (h : ℕ) :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
  if h = 0 then frequencyProjectionPartialLpOperator c hc hp1 0
  else frequencyProjectionPartialLpOperator c hc hp1 h -
    frequencyProjectionPartialLpOperator c hc hp1 (h - 1)

theorem frequencyProjectionLpOperatorFamily_eq_projection {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) (i : Fin (N + 1)) :
    frequencyProjectionLpOperatorFamily c hc hp1 N i =
      frequencyProjectionLpProjection c hc hp1 i.val := rfl

/-- The full inhomogeneous square function. Negative source indices vanish,
so its defining sum runs over the natural indices `h ≥ 0`. -/
def frequencyProjectionSquareFunction {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (x : ℤ) : ℝ :=
  Real.sqrt (∑' h : ℕ,
    ‖frequencyProjectionLpProjection c hc hp1 h f x‖ ^ 2)

theorem finiteProjectionSquareFunction_eq_range {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (hc : 1 < c)
    (hp1 : 1 < p) (N : ℕ) (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (x : ℤ) :
    finiteProjectionSquareFunction (N + 1)
        (frequencyProjectionLpOperatorFamily c hc hp1 N) f x =
      Real.sqrt (∑ h ∈ Finset.range (N + 1),
        ‖frequencyProjectionLpProjection c hc hp1 h f x‖ ^ 2) := by
  change Real.sqrt (∑ i : Fin (N + 1),
      ‖frequencyProjectionLpOperatorFamily c hc hp1 N i f x‖ ^ 2) = _
  congr 1
  calc
    (∑ i : Fin (N + 1),
        ‖frequencyProjectionLpOperatorFamily c hc hp1 N i f x‖ ^ 2) =
        ∑ i : Fin (N + 1),
          ‖frequencyProjectionLpProjection c hc hp1 i.val f x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [frequencyProjectionLpOperatorFamily_eq_projection]
    _ = ∑ h ∈ Finset.range (N + 1),
        ‖frequencyProjectionLpProjection c hc hp1 h f x‖ ^ 2 :=
      Fin.sum_univ_eq_sum_range
        (fun h : ℕ => ‖frequencyProjectionLpProjection c hc hp1 h f x‖ ^ 2)
        (N + 1)

/-- Monotone passage from the source finite-sign estimate gives the full
`\ell^p` Littlewood--Paley square-function bound. The result retains the
same constant as the finite sign estimate. -/
theorem frequencyProjectionSquareFunction_memLp_norm_le
    {p : ℝ} (hp1 : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (c : ℝ) (hc : 1 < c)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, g x = frequencyProjectionSquareFunction c hc hp1 f x) ∧
      ‖g‖ ≤ frequencyProjectionFiniteSquareFunctionBound p * ‖f‖ := by
  classical
  let B := frequencyProjectionFiniteSquareFunctionBound p * ‖f‖
  have hconst : 0 ≤ frequencyProjectionFiniteSquareFunctionBound p := by
    unfold frequencyProjectionFiniteSquareFunctionBound
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (frequencyProjectionSignedLpBound_nonneg hp1)
  have hB : 0 ≤ B := mul_nonneg hconst (norm_nonneg _)
  let gseq : ℕ → lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p) := fun N =>
    Classical.choose (frequencyProjectionFiniteSquareFunction_memLp_norm_le
      hp1 c hc N f)
  have hgseq_spec (N : ℕ) :=
    Classical.choose_spec (frequencyProjectionFiniteSquareFunction_memLp_norm_le
      hp1 c hc N f)
  have hgseq_apply (N : ℕ) (x : ℤ) :
      gseq N x = finiteProjectionSquareFunction (N + 1)
        (frequencyProjectionLpOperatorFamily c hc hp1 N) f x :=
    (hgseq_spec N).1 x
  have hgseq_norm (N : ℕ) : ‖gseq N‖ ≤ B := by
    dsimp [B]
    exact (hgseq_spec N).2
  have hpointwise (x : ℤ) :
      Tendsto (fun N => gseq N x) atTop
        (𝓝 (frequencyProjectionSquareFunction c hc hp1 f x)) := by
    let a : ℕ → ℝ := fun h =>
      ‖frequencyProjectionLpProjection c hc hp1 h f x‖ ^ 2
    have hsum_bound (N : ℕ) :
        ∑ h ∈ Finset.range (N + 1), a h ≤ B ^ 2 := by
      have hcoord := hgseq_apply N x
      rw [finiteProjectionSquareFunction_eq_range] at hcoord
      have hnonneg_coord : 0 ≤ gseq N x := by
        rw [hgseq_apply]
        exact Real.sqrt_nonneg _
      have hnorm_coord : gseq N x ≤ B := by
        calc
          gseq N x = ‖gseq N x‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_coord]
          _ ≤ ‖gseq N‖ := lp.norm_apply_le_norm
            (ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp1))
            (gseq N) x
          _ ≤ B := hgseq_norm N
      have hsum_nonneg : 0 ≤ ∑ h ∈ Finset.range (N + 1), a h :=
        Finset.sum_nonneg fun h hh => sq_nonneg _
      have hsqrt_sq :
          (Real.sqrt (∑ h ∈ Finset.range (N + 1), a h)) ^ 2 =
            ∑ h ∈ Finset.range (N + 1), a h := Real.sq_sqrt hsum_nonneg
      rw [← hcoord] at hsqrt_sq
      rw [← hsqrt_sq]
      nlinarith [hnonneg_coord, hnorm_coord, hB]
    have ha_bound (N : ℕ) : ∑ h ∈ Finset.range N, a h ≤ B ^ 2 := by
      calc
        ∑ h ∈ Finset.range N, a h ≤
            ∑ h ∈ Finset.range (N + 1), a h :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_succ N)) (by intro h hh hnot; exact sq_nonneg _)
        _ ≤ B ^ 2 := hsum_bound N
    have ha : Summable a :=
      summable_of_sum_range_le (fun h => sq_nonneg _) ha_bound
    have hsum_tendsto :
        Tendsto (fun N => ∑ h ∈ Finset.range (N + 1), a h) atTop
          (𝓝 (∑' h, a h)) :=
      ha.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hsqrt_tendsto :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsum_tendsto
    have hseq_eq (N : ℕ) :
        gseq N x = Real.sqrt (∑ h ∈ Finset.range (N + 1), a h) := by
      rw [hgseq_apply, finiteProjectionSquareFunction_eq_range]
    simpa [frequencyProjectionSquareFunction, a] using
      hsqrt_tendsto.congr' (Filter.Eventually.of_forall fun N => (hseq_eq N).symm)
  have hpi : Tendsto (fun N => (gseq N : ℤ → ℝ)) atTop
      (𝓝 (frequencyProjectionSquareFunction c hc hp1 f)) := by
    rw [tendsto_pi_nhds]
    intro x
    exact hpointwise x
  have hbounded : Bornology.IsBounded (Set.range gseq) := by
    apply Metric.isBounded_range_iff.mpr
    refine ⟨2 * B, fun i j => ?_⟩
    rw [dist_eq_norm]
    calc
      ‖gseq i - gseq j‖ ≤ ‖gseq i‖ + ‖gseq j‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hgseq_norm i) (hgseq_norm j)
      _ = 2 * B := by ring
  let g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p) :=
    ⟨frequencyProjectionSquareFunction c hc hp1 f,
      lp.memℓp_of_tendsto hbounded hpi⟩
  refine ⟨g, ?_, ?_⟩
  · intro x
    rfl
  · exact lp.norm_le_of_tendsto
      (Filter.Eventually.of_forall hgseq_norm) hpi

/-- The low-frequency cutoff complementary to the positive partial sum. -/
def frequencyProjectionLowpassSymbolLp
    (c : ℝ) (hc : 1 < c) (N : ℕ) : Lp ℂ ⊤ torusHaar :=
  Lp.const ⊤ torusHaar (1 : ℂ) -
    torusSymbolLp (frequencyProjectionPartialData c hc N)

private theorem frequencyProjectionCutoff_dilation_tendsto_zero
    (c : ℝ) (hc : 1 < c) (ξ : ℝ) (hξ : ξ ≠ 0) :
    Tendsto (fun N : ℕ => frequencyProjectionCutoff
      (Real.rpow 2 ((N : ℝ) * c) * ξ)) atTop (𝓝 0) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hb : 1 < Real.rpow 2 c := Real.one_lt_rpow (by norm_num) hcpos
  have hpow : Tendsto (fun N : ℕ => (Real.rpow 2 c) ^ N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  have hscale_eq (N : ℕ) :
      Real.rpow 2 ((N : ℝ) * c) = (Real.rpow 2 c) ^ N := by
    have hmul :
        Real.rpow 2 (c * (N : ℝ)) = (Real.rpow 2 c) ^ N :=
      Real.rpow_mul_natCast (x := (2 : ℝ)) (by norm_num) c N
    rw [show (N : ℝ) * c = c * (N : ℝ) by ring]
    exact hmul
  have hscale : Tendsto (fun N : ℕ => Real.rpow 2 ((N : ℝ) * c)) atTop atTop :=
    hpow.congr' (Filter.Eventually.of_forall fun N => (hscale_eq N).symm)
  have harg : Tendsto
      (fun N : ℕ => Real.rpow 2 ((N : ℝ) * c) * |ξ|) atTop atTop :=
    Tendsto.atTop_mul_const (abs_pos.mpr hξ) hscale
  have hzero : ∀ᶠ N : ℕ in atTop,
      frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) * ξ) = 0 := by
    filter_upwards [harg.eventually_gt_atTop (3 / 8 : ℝ)] with N hN
    apply frequencyProjectionCutoff_eq_zero_of_three_eighths_lt_abs
    have hnonneg : 0 ≤ Real.rpow 2 ((N : ℝ) * c) :=
      Real.rpow_nonneg (by norm_num) _
    rw [abs_mul, abs_of_nonneg hnonneg]
    exact hN
  exact tendsto_const_nhds.congr' (hzero.mono fun N hN => hN.symm)

private theorem frequencyProjectionPartialData_torusSymbol_eq_dilatedCutoff
    (c : ℝ) (hc : 1 < c) (N : ℕ) (ξ : Torus) :
    torusSymbol (frequencyProjectionPartialData c hc N) ξ =
      (1 - frequencyProjectionCutoff
        (Real.rpow 2 ((N : ℝ) * c) *
          (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) : ℝ) := by
  let r : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ
  have hr : (r : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring] using r.property
  have hrval : (r : ℝ) =
      (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ) := rfl
  have hcoe : (r : Torus) = ξ := AddCircle.coe_equivIoc
  have hsum := frequencyProjectionPartialData_torusSymbol_eq_sum c hc N (r : Torus)
  have hsumRep :
      (∑ h ∈ Finset.range (N + 1),
        (frequencyProjectionSymbol c (h : ℤ) (r : Torus) : ℂ)) =
      (∑ h ∈ Finset.range (N + 1),
        (frequencyProjectionSymbolRepresentative c (h : ℤ) r : ℂ)) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [frequencyProjectionSymbol_coe (c := c) (h := (h : ℤ)) hr]
  have hreal :
      ∑ h ∈ Finset.range (N + 1),
        frequencyProjectionSymbolRepresentative c (h : ℤ) r =
      1 - frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) * r) :=
    frequencyProjectionSymbolRepresentative_sum_range c r N
  have hreal' :
      ∑ h ∈ Finset.range (N + 1),
        frequencyProjectionSymbolRepresentative c (h : ℤ) r =
      1 - frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) *
        (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) := by
    rw [hrval]
    exact hreal
  calc
    torusSymbol (frequencyProjectionPartialData c hc N) ξ =
        torusSymbol (frequencyProjectionPartialData c hc N) (r : Torus) := by
          rw [hcoe]
    _ = ∑ h ∈ Finset.range (N + 1),
          (frequencyProjectionSymbol c (h : ℤ) (r : Torus) : ℂ) := hsum
    _ = ∑ h ∈ Finset.range (N + 1),
          (frequencyProjectionSymbolRepresentative c (h : ℤ) r : ℂ) := hsumRep
    _ = Complex.ofReal (1 - frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) *
        (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ))) := by
          rw [← Complex.ofReal_sum]
          exact congrArg Complex.ofReal hreal'

private theorem frequencyProjectionLowpassSymbolLp_coeFn
    (c : ℝ) (hc : 1 < c) (N : ℕ) :
    (frequencyProjectionLowpassSymbolLp c hc N : Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => (frequencyProjectionCutoff
        (Real.rpow 2 ((N : ℝ) * c) *
          (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) : ℂ) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hsub :
      (frequencyProjectionLowpassSymbolLp c hc N : Torus → ℂ) =ᵐ[torusHaar]
        Lp.const ⊤ torusHaar (1 : ℂ) -
          torusSymbolLp (frequencyProjectionPartialData c hc N) :=
    Lp.coeFn_sub _ _
  have hone :
      ((Lp.const ⊤ torusHaar (1 : ℂ) : Lp ℂ ⊤ torusHaar) : Torus → ℂ) =ᵐ[torusHaar]
        fun _ => (1 : ℂ) := by
    exact Lp.coeFn_const ⊤ torusHaar (1 : ℂ)
  filter_upwards [hsub, hone,
    torusSymbolLp_coeFn (frequencyProjectionPartialData c hc N)] with ξ hsub hone hsym
  calc
    (frequencyProjectionLowpassSymbolLp c hc N : Torus → ℂ) ξ =
        (((Lp.const ⊤ torusHaar (1 : ℂ) : Torus → ℂ) -
          (torusSymbolLp (frequencyProjectionPartialData c hc N) : Torus → ℂ)) ξ) := hsub
    _ = ((Lp.const ⊤ torusHaar (1 : ℂ) : Torus → ℂ) ξ) -
          ((torusSymbolLp (frequencyProjectionPartialData c hc N) : Torus → ℂ) ξ) := rfl
    _ = 1 - torusSymbol (frequencyProjectionPartialData c hc N) ξ := by
      rw [hone, hsym]
    _ = (frequencyProjectionCutoff
        (Real.rpow 2 ((N : ℝ) * c) *
          (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) : ℂ) := by
      rw [frequencyProjectionPartialData_torusSymbol_eq_dilatedCutoff c hc N ξ]
      simp

private theorem frequencyProjectionLowpassSymbolLp_smul_tendsto_zero
    (c : ℝ) (hc : 1 < c) (F : Lp ℂ 2 torusHaar) :
    Tendsto (fun N => frequencyProjectionLowpassSymbolLp c hc N • F)
      atTop (𝓝 (0 : Lp ℂ 2 torusHaar)) := by
  let fseq : ℕ → Torus → ℂ := fun N =>
    (frequencyProjectionLowpassSymbolLp c hc N • F : Lp ℂ 2 torusHaar)
  have hproduct (N : ℕ) : fseq N =ᵐ[torusHaar]
      fun ξ => (frequencyProjectionCutoff
        (Real.rpow 2 ((N : ℝ) * c) *
          (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) : ℂ) *
        (F : Torus → ℂ) ξ := by
    filter_upwards [frequencyProjectionLowpassSymbolLp_coeFn c hc N,
      Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (frequencyProjectionLowpassSymbolLp c hc N) F] with ξ hcut hmul
    have hmul' :
        (frequencyProjectionLowpassSymbolLp c hc N • F : Lp ℂ 2 torusHaar) ξ =
          (frequencyProjectionLowpassSymbolLp c hc N : Torus → ℂ) ξ *
            (F : Torus → ℂ) ξ := by
      change (frequencyProjectionLowpassSymbolLp c hc N • F :
        Lp ℂ 2 torusHaar) ξ = _
      simpa only [Pi.smul_apply', smul_eq_mul] using hmul
    change (frequencyProjectionLowpassSymbolLp c hc N • F :
      Lp ℂ 2 torusHaar) ξ = _
    rw [hmul', hcut]
  have hpointwise : ∀ᵐ ξ ∂torusHaar,
      Tendsto (fun N => fseq N ξ) atTop (𝓝 (0 : ℂ)) := by
    have hall : ∀ᵐ ξ ∂torusHaar, ∀ N, fseq N ξ =
        (frequencyProjectionCutoff
          (Real.rpow 2 ((N : ℝ) * c) *
            (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) : ℂ) *
          (F : Torus → ℂ) ξ := by
      rw [ae_all_iff]
      exact fun N => hproduct N
    filter_upwards [hall, Measure.ae_ne torusHaar (0 : Torus)] with ξ hall hξ
    let r : ℝ := (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)
    have hcoe : (r : Torus) = ξ := by
      dsimp [r]
      exact AddCircle.coe_equivIoc
    have hr : r ≠ 0 := by
      intro hr
      apply hξ
      calc
        ξ = (r : Torus) := hcoe.symm
        _ = 0 := by simp [hr]
    have hcut := frequencyProjectionCutoff_dilation_tendsto_zero c hc r hr
    have hcutC : Tendsto
        (fun N : ℕ => (frequencyProjectionCutoff (Real.rpow 2 ((N : ℝ) * c) * r) : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
      have hcoe : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) :=
        (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto
      simpa [Function.comp_def] using hcoe.comp hcut
    have hprod := hcutC.mul_const ((F : Torus → ℂ) ξ)
    simpa only [zero_mul] using hprod.congr'
      (Filter.Eventually.of_forall fun N => by simpa [r] using (hall N).symm)
  have hmeas : ∀ N, AEStronglyMeasurable (fseq N) torusHaar := by
    intro N
    exact Lp.aestronglyMeasurable _
  have hui : UnifIntegrable fseq 2 torusHaar := by
    apply (unifIntegrable_const (p := (2 : ℝ≥0∞))
      (μ := torusHaar) (g := (F : Torus → ℂ)) (by norm_num) (by norm_num)
      (Lp.memLp F)).ae_mono hmeas
    intro N
    filter_upwards [hproduct N] with ξ hξ
    rw [hξ]
    apply (enorm_le_iff_norm_le).2
    rw [norm_mul]
    have hcutnorm : ‖(frequencyProjectionCutoff
        (Real.rpow 2 ((N : ℝ) * c) *
          (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) : ℂ)‖ ≤ 1 := by
      calc
        _ = |frequencyProjectionCutoff
            (Real.rpow 2 ((N : ℝ) * c) *
              (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ))| :=
          RCLike.norm_ofReal _
        _ = frequencyProjectionCutoff
            (Real.rpow 2 ((N : ℝ) * c) *
              (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ)) :=
          abs_of_nonneg (frequencyProjectionCutoff_nonneg _)
        _ ≤ 1 := frequencyProjectionCutoff_le_one _
    exact mul_le_of_le_one_left (norm_nonneg _) hcutnorm
  have hLpNorm' : Tendsto
      (fun N => eLpNorm (fseq N - fun _ : Torus => (0 : ℂ)) 2 torusHaar)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : 1 ≤ (2 : ℝ≥0∞))
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hmeas
      (memLp_const (0 : ℂ)) hui hpointwise
  have hLpNorm : Tendsto (fun N => eLpNorm (fseq N) 2 torusHaar)
      atTop (𝓝 0) := by
    refine hLpNorm'.congr' (Filter.Eventually.of_forall fun N => ?_)
    apply eLpNorm_congr_ae
    filter_upwards with ξ
    simp
  have hLp : Tendsto (fun N => frequencyProjectionLowpassSymbolLp c hc N • F)
      atTop (𝓝 (0 : Lp ℂ 2 torusHaar)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun N =>
      frequencyProjectionLowpassSymbolLp c hc N • F) 0]
    refine hLpNorm.congr' (Filter.Eventually.of_forall fun N => ?_)
    apply eLpNorm_congr_ae
    filter_upwards with ξ
    simp [fseq]
  exact hLp

/-- The real-valued `L²` exponent agrees with the multiplier's `ENNReal`
exponent. -/
theorem frequencyProjectionLpTwoExponent :
    ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  norm_num

private theorem frequencyProjectionLpCast_apply
    {p q : ℝ≥0∞} (hpq : p = q) (F : lp (fun _ : ℤ => ℂ) p) (k : ℤ) :
    (hpq ▸ F) k = F k := by
  cases hpq
  rfl

/-- Reindex a sequence `ℓ²` element into the exponent type used by the
multiplier extension. -/
def frequencyProjectionLpTwoToMultiplier
    (f : lp (fun _ : ℤ => ℂ) 2) :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)) :=
  frequencyProjectionLpTwoExponent.symm ▸ f

/-- The positive partial multiplier on `ℓ²`. The cast only identifies the
exponent `ENNReal.ofReal 2` used by the multiplier extension with the
literal exponent `2` used by the Fourier unitary. -/
def frequencyProjectionPartialLpOperatorL2
    (c : ℝ) (hc : 1 < c) (N : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    lp (fun _ : ℤ => ℂ) 2 :=
  frequencyProjectionLpTwoExponent ▸
    frequencyProjectionPartialLpOperator (p := 2) c hc (by norm_num) N
      (frequencyProjectionLpTwoToMultiplier f)

private theorem frequencyProjectionPartialLpOperator_eq_TmL2FromSymbolLp
    (c : ℝ) (hc : 1 < c) (N : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionPartialLpOperatorL2 c hc N f =
      frequencyProjectionTmL2FromSymbolLp
        (torusSymbolLp (frequencyProjectionPartialData c hc N)) f := by
  have hFU :
      (frequencyProjectionLpTwoToMultiplier f : ℤ → ℂ) = (f : ℤ → ℂ) := by
    funext k
    exact frequencyProjectionLpCast_apply frequencyProjectionLpTwoExponent.symm f k
  have h := finiteMultiplierLpExtension_eq_TmL2_of_lp2
    (frequencyProjectionPartialData c hc N) (by norm_num)
    (frequencyProjectionLpTwoToMultiplier f) f hFU
  apply lp.ext
  funext k
  change (frequencyProjectionLpTwoExponent ▸
      frequencyProjectionPartialLpOperator (p := 2) c hc (by norm_num) N
        (frequencyProjectionLpTwoToMultiplier f) :
        lp (fun _ : ℤ => ℂ) 2) k = _
  rw [frequencyProjectionLpCast_apply frequencyProjectionLpTwoExponent]
  simpa [frequencyProjectionPartialLpOperator,
    TmL2_eq_frequencyProjectionTmL2FromSymbolLp] using congrFun h k

private theorem frequencyProjectionTmL2FromSymbolLp_const_one
    (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp
      (Lp.const ⊤ torusHaar (1 : ℂ)) f = f := by
  apply sequenceToCircleL2.injective
  simp only [frequencyProjectionTmL2FromSymbolLp,
    LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (Lp.const ⊤ torusHaar (1 : ℂ)) (sequenceToCircleL2 f),
    Lp.coeFn_const ⊤ torusHaar (1 : ℂ)] with ξ hsmul hone
  have hsmul' :
      (Lp.const ⊤ torusHaar (1 : ℂ) • sequenceToCircleL2 f :
        Lp ℂ 2 torusHaar) ξ =
        (Lp.const ⊤ torusHaar (1 : ℂ) : Torus → ℂ) ξ *
          (sequenceToCircleL2 f : Torus → ℂ) ξ := by
    change (Lp.const ⊤ torusHaar (1 : ℂ) • sequenceToCircleL2 f :
      Lp ℂ 2 torusHaar) ξ = _
    simpa only [Pi.smul_apply', smul_eq_mul] using hsmul
  rw [hsmul', hone]
  simp

private theorem frequencyProjectionPartialLpOperator_complement
    (c : ℝ) (hc : 1 < c) (N : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    frequencyProjectionTmL2FromSymbolLp
      (frequencyProjectionLowpassSymbolLp c hc N) f =
        f - frequencyProjectionPartialLpOperatorL2 c hc N f := by
  calc
    frequencyProjectionTmL2FromSymbolLp
        (frequencyProjectionLowpassSymbolLp c hc N) f =
        frequencyProjectionTmL2FromSymbolLp
          (Lp.const ⊤ torusHaar (1 : ℂ) -
            torusSymbolLp (frequencyProjectionPartialData c hc N)) f := rfl
    _ = frequencyProjectionTmL2FromSymbolLp
          (Lp.const ⊤ torusHaar (1 : ℂ)) f -
        frequencyProjectionTmL2FromSymbolLp
          (torusSymbolLp (frequencyProjectionPartialData c hc N)) f :=
      frequencyProjectionTmL2FromSymbolLp_sub _ _ f
    _ = f - frequencyProjectionPartialLpOperatorL2 c hc N f := by
      rw [frequencyProjectionTmL2FromSymbolLp_const_one,
        ← frequencyProjectionPartialLpOperator_eq_TmL2FromSymbolLp]

/-- The positive finite partial sums converge strongly to the identity on
`ℓ²`; the complementary cutoff vanishes away from the Haar-null zero
frequency. -/
theorem frequencyProjectionPartialLpOperator_tendsto_L2
    (c : ℝ) (hc : 1 < c) (f : lp (fun _ : ℤ => ℂ) 2) :
    Tendsto (fun N => frequencyProjectionPartialLpOperatorL2 c hc N f)
      atTop (𝓝 f) := by
  let F := sequenceToCircleL2 f
  have hlow := frequencyProjectionLowpassSymbolLp_smul_tendsto_zero c hc F
  have hTm : Tendsto (fun N => frequencyProjectionTmL2FromSymbolLp
      (frequencyProjectionLowpassSymbolLp c hc N) f) atTop
      (𝓝 (0 : lp (fun _ : ℤ => ℂ) 2)) := by
    simpa [frequencyProjectionTmL2FromSymbolLp, Function.comp_def, F] using
      (sequenceToCircleL2.symm.continuousAt.tendsto).comp hlow
  have hmap : Tendsto (fun N => f - frequencyProjectionTmL2FromSymbolLp
      (frequencyProjectionLowpassSymbolLp c hc N) f) atTop (𝓝 f) := by
    simpa [Function.comp_def] using
      ((continuous_const.sub continuous_id).continuousAt.tendsto).comp hTm
  have hpartial (N : ℕ) :
      frequencyProjectionPartialLpOperatorL2 c hc N f =
        f - frequencyProjectionTmL2FromSymbolLp
          (frequencyProjectionLowpassSymbolLp c hc N) f := by
    rw [frequencyProjectionPartialLpOperator_complement c hc N f]
    simp
  exact hmap.congr' (Filter.Eventually.of_forall fun N => (hpartial N).symm)

/-- Every positive partial frequency sum is a globally `C²` periodic lift.
This follows from the checked smooth lift of each individual projection. -/
private theorem frequencyProjectionPartialLift_contDiff
    (c : ℝ) (hc : 1 < c) (N : ℕ) :
    ContDiff ℝ 2 (frequencyProjectionPartialLift c N) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  unfold frequencyProjectionPartialLift finiteFrequencyProjectionSignedLift
  change ContDiffAt ℝ 2
    (fun ξ : ℝ => ∑ h ∈ Finset.range (N + 1),
      (frequencyProjectionPartialSigns h : ℂ) *
        frequencyProjectionPeriodicLift c (h : ℤ) ξ) ξ
  simp only [frequencyProjectionPartialSigns, Complex.ofReal_one, one_mul]
  apply ContDiffAt.sum
  intro h hh
  exact frequencyProjectionPeriodicLift_contDiffAt hc (h : ℤ) ξ

private theorem frequencyProjectionPartialLift_periodic
    (c : ℝ) (N : ℕ) :
    Function.Periodic (frequencyProjectionPartialLift c N) 1 := by
  simpa [frequencyProjectionPartialLift] using
    finiteFrequencyProjectionSignedLift_periodic c N
      frequencyProjectionPartialSigns

/-- The second derivative of a positive partial lift is bounded on the
fundamental interval, by compactness and its checked `C²` regularity. -/
private noncomputable def frequencyProjectionPartialSecondDerivativeBound
    (c : ℝ) (hc : 1 < c) (N : ℕ) : ℝ :=
  sSup ((fun ξ : ℝ => ‖iteratedDeriv 2 (frequencyProjectionPartialLift c N) ξ‖) ''
    Set.Icc (-(1 / 2 : ℝ)) (1 / 2))

private theorem frequencyProjectionPartialSecondDerivativeBound_spec
    (c : ℝ) (hc : 1 < c) (N : ℕ) :
    0 ≤ frequencyProjectionPartialSecondDerivativeBound c hc N ∧
      ∀ ξ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        ‖iteratedDeriv 2 (frequencyProjectionPartialLift c N) ξ‖ ≤
          frequencyProjectionPartialSecondDerivativeBound c hc N := by
  let f : ℝ → ℂ := frequencyProjectionPartialLift c N
  have hf : ContDiff ℝ 2 f := by
    simpa [f] using frequencyProjectionPartialLift_contDiff c hc N
  have hcont : ContinuousOn (fun ξ : ℝ => ‖iteratedDeriv 2 f ξ‖)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    exact (hf.continuous_iteratedDeriv 2 (by norm_num)).continuousOn.norm
  have hbounded : BddAbove
      ((fun ξ : ℝ => ‖iteratedDeriv 2 f ξ‖) ''
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    isCompact_Icc.bddAbove_image hcont
  have hbound (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      ‖iteratedDeriv 2 f ξ‖ ≤
        sSup ((fun ξ : ℝ => ‖iteratedDeriv 2 f ξ‖) ''
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    le_csSup hbounded ⟨ξ, hξ, rfl⟩
  constructor
  · have hzero := hbound 0 (by constructor <;> norm_num)
    exact (norm_nonneg _).trans hzero
  · intro ξ hξ
    simpa [f, frequencyProjectionPartialSecondDerivativeBound] using hbound ξ hξ

private theorem frequencyProjectionPartialKernelCoefficient_nonzero_bound
    (c : ℝ) (hc : 1 < c) (N : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖kernelCoefficient
        (torusSymbol (frequencyProjectionPartialData c hc N)) n‖ ≤
      frequencyProjectionPartialSecondDerivativeBound c hc N /
        (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  let f : ℝ → ℂ := frequencyProjectionPartialLift c N
  let k : ℤ := -n
  let C := frequencyProjectionPartialSecondDerivativeBound c hc N
  have hf : ContDiff ℝ 2 f := by
    simpa [f] using frequencyProjectionPartialLift_contDiff c hc N
  have hab : (-(1 / 2 : ℝ)) < (1 / 2 : ℝ) := by norm_num
  have hlen : (1 / 2 : ℝ) - (-(1 / 2 : ℝ)) = 1 := by norm_num
  have hk : k ≠ 0 := by
    dsimp [k]
    exact neg_ne_zero.mpr hn
  have hcontAt (x : ℝ) : ContDiffAt ℝ 2 f x := hf.contDiffAt
  have hfContOn : ContinuousOn f (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    intro x hx
    exact (hcontAt x).continuousAt.continuousWithinAt
  have hfDerivContOn :
      ContinuousOn (deriv f) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    intro x hx
    have hdf : ContDiffAt ℝ 0 (deriv f) x :=
      (hcontAt x).derivWithin (m := 0) (by norm_num)
    exact hdf.continuousAt.continuousWithinAt
  have hfSecondContOn :
      ContinuousOn (iteratedDeriv 2 f)
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    intro x hx
    have hdf : ContDiffAt ℝ 1 (deriv f) x :=
      (hcontAt x).derivWithin (m := 1) (by norm_num)
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
      IntervalIntegrable (iteratedDeriv 2 f) volume
        (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
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
      (hcontAt x).of_le (by norm_num)
    exact hcontAtOne.differentiableAt_one.hasDerivAt.hasDerivWithinAt
  have hfDerivDiff : ∀ x, x ∈ Set.Ioo (min (-(1 / 2 : ℝ)) (1 / 2))
      (max (-(1 / 2 : ℝ)) (1 / 2)) →
        HasDerivWithinAt (deriv f) (iteratedDeriv 2 f x) (Set.Ioi x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa [min_eq_left hab.le, max_eq_right hab.le] using hx
    have hxIcc : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
    have hdf : ContDiffAt ℝ 1 (deriv f) x :=
      (hcontAt x).derivWithin (m := 1) (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      hdf.differentiableAt_one.hasDerivAt.hasDerivWithinAt
  have hperiodic := frequencyProjectionPartialLift_periodic c N
  have hseam0 : f (1 / 2) = f (-(1 / 2 : ℝ)) := by
    simpa only [f, show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num] using
      hperiodic (-(1 / 2 : ℝ))
  have hseam1 : deriv f (1 / 2) = deriv f (-(1 / 2 : ℝ)) := by
    have h := deriv_periodic_one f hperiodic (-(1 / 2 : ℝ))
    simpa only [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num] using h
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
  have hCspec := frequencyProjectionPartialSecondDerivativeBound_spec c hc N
  have hboundAE : ∀ᵐ x, x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2) →
      ‖fourier (-k) (x : Torus) • iteratedDeriv 2 f x‖ ≤ C := by
    filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with x hxb
    intro hx
    have hxIoc : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa [Set.uIoc_of_le hab.le] using hx
    have hxIcc : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hbound := hCspec.2 x hxIcc
    have hfourier : ‖fourier (-k) (x : Torus)‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    rw [norm_smul, hfourier, one_mul]
    exact hbound
  have hcoeffSecond :
      ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ ≤ C := by
    calc
      ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ =
          ‖∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
              fourier (-k) (x : Torus) • iteratedDeriv 2 f x ∂volume‖ := by
        rw [fourierCoeffOn_eq_integral]
        rw [hlen]
        simp
      _ ≤ C * |(1 / 2 : ℝ) - (-(1 / 2 : ℝ))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const_ae hboundAE
      _ = C := by norm_num
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
  have hkernel :
      kernelCoefficient (torusSymbol (frequencyProjectionPartialData c hc N)) n =
        fourierCoeffOn hab f k := by
    change kernelCoefficient (torusSymbol (frequencyProjectionPartialData c hc N)) n =
      fourierCoeffOn hab
        (finiteFrequencyProjectionSignedLift c N frequencyProjectionPartialSigns) (-n)
    exact kernelCoefficient_torusSymbol_eq_fourierCoeffOn
      (frequencyProjectionPartialData c hc N) n
  calc
    ‖kernelCoefficient (torusSymbol (frequencyProjectionPartialData c hc N)) n‖ =
        ‖(1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) ^ 2 *
          fourierCoeffOn hab (iteratedDeriv 2 f) k‖ := by
            rw [hkernel, hcoeff]
    _ = ‖(1 / (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) ^ 2‖ *
        ‖fourierCoeffOn hab (iteratedDeriv 2 f) k‖ := norm_mul _ _
    _ ≤ (1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * C :=
      mul_le_mul hfactorSq.le hcoeffSecond (norm_nonneg _) hfactorRhsNonneg
    _ = C / (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
      rw [hrealK]
      ring

theorem frequencyProjectionPartialKernel_summable
    (c : ℝ) (hc : 1 < c) (N : ℕ) :
    Summable (fun n : ℤ =>
      ‖kernelCoefficient
        (torusSymbol (frequencyProjectionPartialData c hc N)) n‖) := by
  let invSq : ℤ → ℝ := fun n => 1 / ((n : ℝ) ^ 2)
  let C := frequencyProjectionPartialSecondDerivativeBound c hc N /
    (4 * Real.pi ^ 2)
  let b0 := ‖kernelCoefficient
      (torusSymbol (frequencyProjectionPartialData c hc N)) 0‖ + C
  let single : ℤ → ℝ := fun n => if n = 0 then b0 else 0
  let major : ℤ → ℝ := fun n => single n + b0 * invSq n
  have hCspec := frequencyProjectionPartialSecondDerivativeBound_spec c hc N
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg hCspec.1 (by positivity)
  have hb0 : 0 ≤ b0 := by
    dsimp [b0]
    positivity
  have hinv : Summable invSq := by
    dsimp [invSq]
    exact (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hsingleSupport : Function.support single ⊆ ({0} : Set ℤ) := by
    intro n hn
    change single n ≠ 0 at hn
    by_cases h0 : n = 0
    · simpa using h0
    · simp [single, h0] at hn
  have hsingle : Summable single :=
    summable_of_hasFiniteSupport ((Set.finite_singleton (0 : ℤ)).subset
      hsingleSupport)
  have hscaled : Summable (fun n : ℤ => b0 * invSq n) := hinv.mul_left b0
  have hmajor : Summable major := by
    simpa [major] using hsingle.add hscaled
  have hpoint : ∀ n : ℤ,
      ‖kernelCoefficient
        (torusSymbol (frequencyProjectionPartialData c hc N)) n‖ ≤ major n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [major, single, invSq, b0]
      linarith [hC]
    · have hcoef := frequencyProjectionPartialKernelCoefficient_nonzero_bound
        c hc N n hn
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hfac : C * invSq n =
          frequencyProjectionPartialSecondDerivativeBound c hc N /
            (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
        dsimp [C, invSq]
        field_simp [ne_of_gt Real.pi_pos, hnreal]
        <;> ring
      have hCineq : C * invSq n ≤ b0 * invSq n := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [invSq]; positivity)
        dsimp [b0]
        linarith [norm_nonneg
          (kernelCoefficient
            (torusSymbol (frequencyProjectionPartialData c hc N)) 0)]
      calc
        _ ≤ frequencyProjectionPartialSecondDerivativeBound c hc N /
            (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := hcoef
        _ = C * invSq n := hfac.symm
        _ ≤ b0 * invSq n := hCineq
        _ = major n := by simp [major, single, hn]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpoint hmajor

/-- The Fourier coefficients of the positive partial multiplier form an
absolutely summable integer kernel. The proof uses the source's smooth lift
and two integrations by parts on one period. -/
noncomputable def frequencyProjectionPartialIntegerKernel
    (c : ℝ) (hc : 1 < c) (N : ℕ) : IntegerL1Kernel where
  coeff := fun n => kernelCoefficient
    (torusSymbol (frequencyProjectionPartialData c hc N)) n
  summable_norm := frequencyProjectionPartialKernel_summable c hc N

/-- The source projection kernel is the first positive partial kernel at
index zero, and the difference of consecutive positive partial kernels at
every positive index. -/
noncomputable def frequencyProjectionIntegerKernel
    (c : ℝ) (hc : 1 < c) (h : ℕ) : IntegerL1Kernel := by
  classical
  by_cases hh : h = 0
  · subst h
    exact frequencyProjectionPartialIntegerKernel c hc 0
  · refine ⟨fun n =>
      (frequencyProjectionPartialIntegerKernel c hc h).coeff n -
        (frequencyProjectionPartialIntegerKernel c hc (h - 1)).coeff n, ?_⟩
    have hmajor : Summable (fun n : ℤ =>
        ‖(frequencyProjectionPartialIntegerKernel c hc h).coeff n‖ +
          ‖(frequencyProjectionPartialIntegerKernel c hc (h - 1)).coeff n‖) := by
      simpa using
        (frequencyProjectionPartialIntegerKernel c hc h).summable_norm.add
          (frequencyProjectionPartialIntegerKernel c hc (h - 1)).summable_norm
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (by
      intro n
      exact norm_sub_le _ _) hmajor

/-- Convolution by each source projection kernel acts boundedly on every
counting-measure `Lᵖ` space in the full range `1 ≤ p ≤ ∞`. In particular,
this includes both endpoint spaces in `ℓ¹+ℓ∞`. -/
theorem frequencyProjectionIntegerKernel_eLpNorm_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) (c : ℝ) (hc : 1 < c) (h : ℕ)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    eLpNorm
        (integerKernelConvolution (frequencyProjectionIntegerKernel c hc h)
          (f : ℤ → ℂ)) p Measure.count ≤
      (∑' n : ℤ,
        ‖(frequencyProjectionIntegerKernel c hc h).coeff n‖ₑ) *
        eLpNorm (f : ℤ → ℂ) p Measure.count := by
  exact eLpNorm_integerKernelConvolution_le hp
    (frequencyProjectionIntegerKernel c hc h) f

private theorem frequencyProjectionPartialLpOperator_apply_finite
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (c : ℝ) (hc : 1 < c) (hp1 : 1 < p) (N : ℕ)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    (frequencyProjectionPartialLpOperator c hc hp1 N
      (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) : ℤ → ℂ) x =
      ∑ n ∈ f.support,
        kernelCoefficient
          (torusSymbol (frequencyProjectionPartialData c hc N)) (x - n) * f n := by
  rw [frequencyProjectionPartialLpOperator,
    finiteMultiplierLpExtension_apply_finite,
    finiteMultiplierLpMap_apply]
  exact TmL2_finite_convolution (frequencyProjectionPartialData c hc N) f x

/-- On a finitely supported input, each source projection is exactly finite
convolution with the coefficients of its absolutely summable kernel. -/
theorem frequencyProjectionLpProjection_apply_finite
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (c : ℝ) (hc : 1 < c) (hp1 : 1 < p) (h : ℕ)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    (frequencyProjectionLpProjection c hc hp1 h
      (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) : ℤ → ℂ) x =
      ∑ n ∈ f.support,
        (frequencyProjectionIntegerKernel c hc h).coeff (x - n) * f n := by
  classical
  by_cases hh : h = 0
  · subst h
    change (frequencyProjectionPartialLpOperator c hc hp1 0
      (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) : ℤ → ℂ) x = _
    rw [frequencyProjectionPartialLpOperator_apply_finite
      c hc hp1 0 f x]
    apply Finset.sum_congr rfl
    intro n hn
    simp [frequencyProjectionIntegerKernel,
      frequencyProjectionPartialIntegerKernel]
  · simp only [frequencyProjectionLpProjection, if_neg hh,
      ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply]
    rw [frequencyProjectionPartialLpOperator_apply_finite
        c hc hp1 h f x,
      frequencyProjectionPartialLpOperator_apply_finite
        c hc hp1 (h - 1) f x]
    calc
      (∑ n ∈ f.support,
          kernelCoefficient
            (torusSymbol (frequencyProjectionPartialData c hc h)) (x - n) * f n) -
        ∑ n ∈ f.support,
          kernelCoefficient
            (torusSymbol (frequencyProjectionPartialData c hc (h - 1)))
              (x - n) * f n =
        ∑ n ∈ f.support,
          (kernelCoefficient
              (torusSymbol (frequencyProjectionPartialData c hc h)) (x - n) -
            kernelCoefficient
              (torusSymbol (frequencyProjectionPartialData c hc (h - 1)))
                (x - n)) * f n := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = ∑ n ∈ f.support,
          (frequencyProjectionIntegerKernel c hc h).coeff (x - n) * f n := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [frequencyProjectionIntegerKernel, hh,
            frequencyProjectionPartialIntegerKernel]

/-- Convolution is pointwise additive on an `L¹ + L∞` decomposition. The
integrability hypotheses needed to identify Mathlib's measure convolution
with its series are supplied by the endpoint `Lp` bounds, rather than being
extra assumptions on the decomposition. -/
theorem integerKernelConvolution_add_L1_LInf
    (K : IntegerL1Kernel)
    (f₁ : Lp ℂ 1 (Measure.count : Measure ℤ))
    (fInf : Lp ℂ ⊤ (Measure.count : Measure ℤ)) (x : ℤ) :
    integerKernelConvolution K
        ((f₁ : ℤ → ℂ) + (fInf : ℤ → ℂ)) x =
      integerKernelConvolution K (f₁ : ℤ → ℂ) x +
        integerKernelConvolution K (fInf : ℤ → ℂ) x := by
  have h₁exists := integerKernelConvolutionExistsAt_of_Lp
    (by norm_num : 1 ≤ (1 : ℝ≥0∞)) K f₁ x
  have hInfExists := integerKernelConvolutionExistsAt_of_Lp
    (by simp : 1 ≤ (⊤ : ℝ≥0∞)) K fInf x
  have h₁int : Integrable
      (fun m : ℤ => K.coeff m * (f₁ : ℤ → ℂ) (x - m)) Measure.count := by
    change IntegerKernelConvolutionExistsAt K (f₁ : ℤ → ℂ) x at h₁exists
    exact h₁exists
  have hInfInt : Integrable
      (fun m : ℤ => K.coeff m * (fInf : ℤ → ℂ) (x - m)) Measure.count := by
    change IntegerKernelConvolutionExistsAt K (fInf : ℤ → ℂ) x at hInfExists
    exact hInfExists
  have h₁sum : Summable
      (fun m : ℤ => K.coeff m * (f₁ : ℤ → ℂ) (x - m)) :=
    Summable.of_norm (MeasureTheory.integrable_count_iff.mp h₁int)
  have hInfSum : Summable
      (fun m : ℤ => K.coeff m * (fInf : ℤ → ℂ) (x - m)) :=
    Summable.of_norm (MeasureTheory.integrable_count_iff.mp hInfInt)
  have hsum : Summable
      (fun m : ℤ => K.coeff m *
        ((f₁ : ℤ → ℂ) (x - m) + (fInf : ℤ → ℂ) (x - m))) := by
    simpa only [mul_add] using h₁sum.add hInfSum
  have hsumInt : Integrable
      (fun m : ℤ => K.coeff m *
        ((f₁ : ℤ → ℂ) (x - m) + (fInf : ℤ → ℂ) (x - m))) Measure.count := by
    rw [MeasureTheory.integrable_count_iff]
    exact hsum.norm
  have hsumExists : IntegerKernelConvolutionExistsAt K
      ((f₁ : ℤ → ℂ) + (fInf : ℤ → ℂ)) x := by
    change Integrable
      (fun m : ℤ => K.coeff m *
        (((f₁ : ℤ → ℂ) + (fInf : ℤ → ℂ)) (x - m))) Measure.count
    simpa only [Pi.add_apply] using hsumInt
  rw [integerKernelConvolution_eq_tsum K _ x hsumExists,
    integerKernelConvolution_eq_tsum K _ x h₁exists,
    integerKernelConvolution_eq_tsum K _ x hInfExists]
  simp only [Pi.add_apply, mul_add]
  rw [Summable.tsum_add h₁sum hInfSum]

/-- Each source projection acts on the algebraic sum `ℓ¹ + ℓ∞`: it sends a
decomposition to the sum of its endpoint convolution outputs, with the full
Young bound on both output components. -/
theorem frequencyProjectionIntegerKernel_L1PlusLInf_action
    (c : ℝ) (hc : 1 < c) (h : ℕ)
    (f₁ : Lp ℂ 1 (Measure.count : Measure ℤ))
    (fInf : Lp ℂ ⊤ (Measure.count : Measure ℤ)) :
    (∀ x : ℤ, integerKernelConvolution
        (frequencyProjectionIntegerKernel c hc h)
        ((f₁ : ℤ → ℂ) + (fInf : ℤ → ℂ)) x =
      integerKernelConvolution (frequencyProjectionIntegerKernel c hc h)
        (f₁ : ℤ → ℂ) x +
      integerKernelConvolution (frequencyProjectionIntegerKernel c hc h)
        (fInf : ℤ → ℂ) x) ∧
    eLpNorm (integerKernelConvolution
        (frequencyProjectionIntegerKernel c hc h) (f₁ : ℤ → ℂ))
        1 Measure.count ≤
      (∑' n : ℤ,
        ‖(frequencyProjectionIntegerKernel c hc h).coeff n‖ₑ) *
        eLpNorm (f₁ : ℤ → ℂ) 1 Measure.count ∧
    eLpNorm (integerKernelConvolution
        (frequencyProjectionIntegerKernel c hc h) (fInf : ℤ → ℂ))
        ⊤ Measure.count ≤
      (∑' n : ℤ,
        ‖(frequencyProjectionIntegerKernel c hc h).coeff n‖ₑ) *
        eLpNorm (fInf : ℤ → ℂ) ⊤ Measure.count := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact integerKernelConvolution_add_L1_LInf
      (frequencyProjectionIntegerKernel c hc h) f₁ fInf x
  · exact eLpNorm_integerKernelConvolution_le
      (by norm_num : 1 ≤ (1 : ℝ≥0∞))
      (frequencyProjectionIntegerKernel c hc h) f₁
  · exact eLpNorm_integerKernelConvolution_le
      (by simp : 1 ≤ (⊤ : ℝ≥0∞))
      (frequencyProjectionIntegerKernel c hc h) fInf

/-- The completed `ha:lp` package: the projections have summable convolution
kernels and the exact finite-input formula; the kernels act on `ℓ¹+ℓ∞`;
the finite positive partial sums converge strongly on `ℓ²`; the full square
function has the source bound; and the support restrictions hold. -/
abbrev frequencyProjectionResolutionAndSquareFunctionStatement
    (c : ℝ) (hc : 1 < c) : Prop :=
    (∀ h : ℕ, Summable (fun n : ℤ =>
      ‖(frequencyProjectionIntegerKernel c hc h).coeff n‖)) ∧
    (∀ {p : ℝ} (hp1 : 1 < p),
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
      ∀ (h : ℕ) (f : ℤ →₀ ℂ) (x : ℤ),
        (frequencyProjectionLpProjection c hc hp1 h
          (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) : ℤ → ℂ) x =
          ∑ n ∈ f.support,
            (frequencyProjectionIntegerKernel c hc h).coeff (x - n) * f n) ∧
    (∀ (h : ℕ)
      (f₁ : Lp ℂ 1 (Measure.count : Measure ℤ))
      (fInf : Lp ℂ ⊤ (Measure.count : Measure ℤ)),
      (∀ x : ℤ, integerKernelConvolution
          (frequencyProjectionIntegerKernel c hc h)
          ((f₁ : ℤ → ℂ) + (fInf : ℤ → ℂ)) x =
        integerKernelConvolution (frequencyProjectionIntegerKernel c hc h)
          (f₁ : ℤ → ℂ) x +
        integerKernelConvolution (frequencyProjectionIntegerKernel c hc h)
          (fInf : ℤ → ℂ) x) ∧
      eLpNorm (integerKernelConvolution
          (frequencyProjectionIntegerKernel c hc h) (f₁ : ℤ → ℂ))
          1 Measure.count ≤
        (∑' n : ℤ,
          ‖(frequencyProjectionIntegerKernel c hc h).coeff n‖ₑ) *
          eLpNorm (f₁ : ℤ → ℂ) 1 Measure.count ∧
      eLpNorm (integerKernelConvolution
          (frequencyProjectionIntegerKernel c hc h) (fInf : ℤ → ℂ))
          ⊤ Measure.count ≤
        (∑' n : ℤ,
          ‖(frequencyProjectionIntegerKernel c hc h).coeff n‖ₑ) *
          eLpNorm (fInf : ℤ → ℂ) ⊤ Measure.count) ∧
    (∀ (N : ℕ) (ξ : Torus),
      torusSymbol (frequencyProjectionPartialData c hc N) ξ =
        ∑ h ∈ Finset.range (N + 1),
          (frequencyProjectionSymbol c (h : ℤ) ξ : ℂ)) ∧
    (∀ (N : ℕ) (ξ : Torus),
      torusSymbol (frequencyProjectionPartialData c hc N) ξ -
        (if N = 0 then 0 else
          torusSymbol (frequencyProjectionPartialData c hc (N - 1)) ξ) =
        (frequencyProjectionSymbol c (N : ℤ) ξ : ℂ)) ∧
    (∀ f : lp (fun _ : ℤ => ℂ) 2,
      Tendsto (fun N => frequencyProjectionPartialLpOperatorL2 c hc N f)
        atTop (𝓝 f)) ∧
    (∀ {p : ℝ} (hp1 : 1 < p),
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
      ∀ (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)),
        ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
          (∀ x, g x = frequencyProjectionSquareFunction c hc hp1 f x) ∧
          ‖g‖ ≤ frequencyProjectionFiniteSquareFunctionBound p * ‖f‖) ∧
    (∀ ξ : ℝ, ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) →
      frequencyProjectionSymbol c 0 ξ ≠ 0 → 1 / 4 < |ξ|) ∧
    (∀ {h : ℤ} (hh : 1 ≤ h) {ξ : ℝ},
      ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) →
      frequencyProjectionSymbol c h ξ ≠ 0 →
        (1 / 4 : ℝ) * Real.rpow 2 (-((h : ℝ) * c)) < |ξ| ∧
          |ξ| < (1 / 2 : ℝ) * Real.rpow 2 (-(((h : ℝ) - 1) * c)))

theorem frequencyProjectionResolutionAndSquareFunction
    (c : ℝ) (hc : 1 < c) :
    frequencyProjectionResolutionAndSquareFunctionStatement c hc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (frequencyProjectionIntegerKernel c hc h).summable_norm
  · intro p hp1
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
    intro h f x
    exact frequencyProjectionLpProjection_apply_finite c hc hp1 h f x
  · intro h f₁ fInf
    exact frequencyProjectionIntegerKernel_L1PlusLInf_action c hc h f₁ fInf
  · exact frequencyProjectionPartialData_torusSymbol_eq_sum c hc
  · exact frequencyProjectionPartialData_difference_eq_projection c hc
  · exact frequencyProjectionPartialLpOperator_tendsto_L2 c hc
  · intro p hp1
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
    intro f
    exact frequencyProjectionSquareFunction_memLp_norm_le hp1 c hc f
  · intro ξ hξ hs
    exact frequencyProjectionSymbol_support_zero hξ hs
  · intro h hh ξ hξ hs
    exact frequencyProjectionSymbol_support_positive hc hh hξ hs

end

end FractionalPrimes.Literature.Harmonic

namespace FractionalPrimes

/-- The paper-facing `ha:lp` declaration, assembled from the checked
projection-kernel, resolution, square-function, and support statements. -/
theorem frequencyResolutionSquareFunction
    (c : ℝ) (hc : 1 < c) :
    Literature.Harmonic.frequencyProjectionResolutionAndSquareFunctionStatement c hc :=
  Literature.Harmonic.frequencyProjectionResolutionAndSquareFunction c hc

end FractionalPrimes

end
