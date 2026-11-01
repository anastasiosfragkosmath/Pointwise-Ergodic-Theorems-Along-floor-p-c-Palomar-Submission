module

public import FractionalPrimes.Literature.Harmonic.SchwartzCutoff
public import FractionalPrimes.VariationAbsoluteSum
public import FractionalPrimes.Literature.Variation.FiniteChainVariation
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Schwartz extension and sampling

This module formalizes the extension and variation-sampling bounds in
`ha:sampling`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

/-- The integral constant `L_ω` from `ha:sampling`. -/
def schwartzExtensionL (ω : SchwartzMap ℝ ℂ) : ℝ :=
  ∫ y : ℝ, ‖ω y‖

/-- The uniform lattice-sum constant `S_ω` from `ha:sampling`. -/
def schwartzExtensionS (ω : SchwartzMap ℝ ℂ) : ℝ :=
  sSup (Set.range fun y : ℝ => ∑' n : ℤ, ‖ω ((n : ℝ) - y)‖)

def integerInverseSquare (n : ℤ) : ℝ :=
  1 / (1 + |(n : ℝ)|) ^ 2

private theorem summable_integerInverseSquare : Summable integerInverseSquare := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
      simpa [one_div] using
        (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 hbase
    refine hshift.congr ?_
    intro n
    simp only [integerInverseSquare, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity), add_comm]
  · have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
      simpa [one_div] using
        (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 hbase
    refine hshift.congr ?_
    intro n
    simp only [integerInverseSquare, Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity), add_comm]

noncomputable def integerInverseSquareSum : ℝ :=
  ∑' n : ℤ, integerInverseSquare n

private theorem integerInverseSquareSum_nonneg : 0 ≤ integerInverseSquareSum :=
  tsum_nonneg (fun n => by unfold integerInverseSquare; positivity)

private theorem integerInverseSquareSum_eq_tsum :
    integerInverseSquareSum = ∑' n : ℤ, integerInverseSquare n := rfl

def schwartzSamplingDecayConstant (ω : SchwartzMap ℝ ℂ) : ℝ :=
  ((Finset.Iic (2, 0)).sup fun ij => SchwartzMap.seminorm ℝ ij.1 ij.2) ω

private theorem schwartzSamplingDecay_bound (ω : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖ω x‖ ≤
      4 * schwartzSamplingDecayConstant ω / (1 + |x|) ^ 2 := by
  have hdecay := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0) (by norm_num) (by norm_num) ω x
  have hpos : 0 < (1 + |x| : ℝ) := by positivity
  have hpow : 0 < (1 + |x| : ℝ) ^ 2 := by positivity
  have hbound : (1 + |x| : ℝ) ^ 2 * ‖ω x‖ ≤
      4 * schwartzSamplingDecayConstant ω := by
    have hdecay' := hdecay
    norm_num at hdecay'
    simpa [schwartzSamplingDecayConstant, Real.norm_eq_abs] using hdecay'
  apply (le_div_iff₀ hpow).2
  nlinarith [hbound]

private theorem shiftedInverseSquare_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℤ) :
    1 / (1 + |(m : ℝ) - t| : ℝ) ^ 2 ≤
      4 * integerInverseSquare m := by
  have hdist : |(m : ℝ)| ≤ |(m : ℝ) - t| + 1 := by
    calc
      |(m : ℝ)| = |((m : ℝ) - t) + t| := by congr 1; ring
      _ ≤ |(m : ℝ) - t| + |t| := abs_add_le _ _
      _ ≤ |(m : ℝ) - t| + 1 := by
        gcongr
        exact abs_le.mpr ⟨by linarith, ht1.trans (by norm_num)⟩
  have hsum : 1 + |(m : ℝ)| ≤ 2 * (1 + |(m : ℝ) - t|) := by
    nlinarith [hdist, abs_nonneg ((m : ℝ) - t)]
  have hpos₁ : 0 < (1 + |(m : ℝ)| : ℝ) := by positivity
  have hpow : (1 + |(m : ℝ)| : ℝ) ^ 2 ≤
      4 * (1 + |(m : ℝ) - t| : ℝ) ^ 2 := by nlinarith [hsum]
  have hratio :
      1 / (1 + |(m : ℝ) - t| : ℝ) ^ 2 ≤
        4 / (1 + |(m : ℝ)| : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < (1 + |(m : ℝ) - t| : ℝ) ^ 2)
      (by positivity : 0 < (1 + |(m : ℝ)| : ℝ) ^ 2)]
    nlinarith [hpow]
  simpa [integerInverseSquare, div_eq_mul_inv] using hratio

private theorem schwartzSamplingPeriodization_bound (ω : SchwartzMap ℝ ℂ)
    (y : ℝ) :
    ∑' n : ℤ, ‖ω ((n : ℝ) - y)‖ ≤
      16 * schwartzSamplingDecayConstant ω * integerInverseSquareSum := by
  let k : ℤ := Int.floor y
  let t : ℝ := Int.fract y
  have ht0 : 0 ≤ t := by exact Int.fract_nonneg y
  have ht1 : t ≤ 1 := (Int.fract_lt_one y).le
  have hy : y = (k : ℝ) + t := by
    calc
      y = Int.fract y + (Int.floor y : ℝ) := (Int.fract_add_floor y).symm
      _ = (Int.floor y : ℝ) + Int.fract y := by ring
  have hshift : (∑' n : ℤ, ‖ω ((n : ℝ) - y)‖) =
      ∑' m : ℤ, ‖ω ((m : ℝ) - t)‖ := by
    rw [← Equiv.tsum_eq (Equiv.subRight k)
      (fun m : ℤ => ‖ω ((m : ℝ) - t)‖)]
    apply tsum_congr
    intro n
    dsimp only [Equiv.subRight]
    change ‖ω ((n : ℝ) - y)‖ = ‖ω (((n - k : ℤ) : ℝ) - t)‖
    rw [hy]
    congr 2
    push_cast
    ring
  rw [hshift]
  have hmajor : ∀ m : ℤ,
      ‖ω ((m : ℝ) - t)‖ ≤
        16 * schwartzSamplingDecayConstant ω * integerInverseSquare m := by
    intro m
    calc
      ‖ω ((m : ℝ) - t)‖ ≤
          4 * schwartzSamplingDecayConstant ω /
            (1 + |(m : ℝ) - t| : ℝ) ^ 2 :=
          schwartzSamplingDecay_bound ω _
      _ ≤ 16 * schwartzSamplingDecayConstant ω * integerInverseSquare m := by
          have hD : 0 ≤ 4 * schwartzSamplingDecayConstant ω := by
            have h := schwartzSamplingDecay_bound ω 0
            norm_num at h
            nlinarith [norm_nonneg (ω 0)]
          calc
            4 * schwartzSamplingDecayConstant ω /
                (1 + |(m : ℝ) - t| : ℝ) ^ 2 =
              4 * schwartzSamplingDecayConstant ω *
                (1 / (1 + |(m : ℝ) - t| : ℝ) ^ 2) := by ring
            _ ≤ 4 * schwartzSamplingDecayConstant ω *
                (4 * integerInverseSquare m) :=
              mul_le_mul_of_nonneg_left
                (shiftedInverseSquare_le t ht0 ht1 m) hD
            _ = 16 * schwartzSamplingDecayConstant ω * integerInverseSquare m := by ring
  have hsummable : Summable (fun m : ℤ =>
      16 * schwartzSamplingDecayConstant ω * integerInverseSquare m) := by
    exact (summable_integerInverseSquare.mul_left _)
  have hleft : Summable (fun m : ℤ => ‖ω ((m : ℝ) - t)‖) :=
    hsummable.of_nonneg_of_le (fun _ => norm_nonneg _ ) hmajor
  calc
    _ ≤ ∑' m : ℤ,
          16 * schwartzSamplingDecayConstant ω * integerInverseSquare m :=
        hleft.tsum_le_tsum hmajor hsummable
    _ = 16 * schwartzSamplingDecayConstant ω * integerInverseSquareSum := by
        rw [tsum_mul_left, integerInverseSquareSum_eq_tsum]

/-- The lattice-sum constant is finite and is bounded by a Schwartz seminorm. -/
theorem schwartzExtensionS_le (ω : SchwartzMap ℝ ℂ) :
    schwartzExtensionS ω ≤
      16 * schwartzSamplingDecayConstant ω * integerInverseSquareSum := by
  apply csSup_le
  · exact ⟨_, ⟨0, rfl⟩⟩
  · rintro z ⟨y, rfl⟩
    exact schwartzSamplingPeriodization_bound ω y

/-- The Schwartz kernel has finite first moment `L_ω`. -/
theorem schwartzExtensionL_integrable (ω : SchwartzMap ℝ ℂ) :
    Integrable (fun y : ℝ => ‖ω y‖) volume :=
  ω.integrable.norm

/-- Both source constants are nonnegative. -/
theorem schwartzExtensionL_nonneg (ω : SchwartzMap ℝ ℂ) :
    0 ≤ schwartzExtensionL ω := by
  exact integral_nonneg (fun y => norm_nonneg (ω y))

theorem schwartzExtensionS_nonneg (ω : SchwartzMap ℝ ℂ) :
    0 ≤ schwartzExtensionS ω := by
  let B := 16 * schwartzSamplingDecayConstant ω * integerInverseSquareSum
  have hbounded : BddAbove
      (Set.range fun y : ℝ => ∑' n : ℤ, ‖ω ((n : ℝ) - y)‖) := by
    refine ⟨B, ?_⟩
    rintro z ⟨y, rfl⟩
    exact schwartzSamplingPeriodization_bound ω y
  have hmem : (∑' n : ℤ, ‖ω ((n : ℝ) - 0)‖) ∈
      Set.range fun y : ℝ => ∑' n : ℤ, ‖ω ((n : ℝ) - y)‖ := ⟨0, rfl⟩
  have hsum : 0 ≤ ∑' n : ℤ, ‖ω ((n : ℝ) - 0)‖ :=
    tsum_nonneg (fun n => norm_nonneg _)
  unfold schwartzExtensionS
  exact hsum.trans (le_csSup hbounded hmem)

/-- Continuous extension of a finitely supported lattice function by a
Schwartz kernel. -/
def schwartzExtension (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) : ℝ → ℂ :=
  fun y => ∑ n ∈ f.support, f n * ω (y - (n : ℝ))

theorem continuous_schwartzExtension (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) :
    Continuous (schwartzExtension ω f) := by
  unfold schwartzExtension
  fun_prop

private theorem schwartzSamplingPeriodization_summable (ω : SchwartzMap ℝ ℂ)
    (y : ℝ) : Summable (fun n : ℤ => ‖ω ((n : ℝ) - y)‖) := by
  let k : ℤ := Int.floor y
  let t : ℝ := Int.fract y
  have hy : y = (k : ℝ) + t := by
    calc
      y = Int.fract y + (Int.floor y : ℝ) := (Int.fract_add_floor y).symm
      _ = (Int.floor y : ℝ) + Int.fract y := by ring
  have hbase : Summable (fun n : ℤ => integerInverseSquare (n - k)) :=
    summable_integerInverseSquare.comp_injective (Equiv.subRight k).injective
  have hsummable : Summable (fun n : ℤ =>
      16 * schwartzSamplingDecayConstant ω * integerInverseSquare (n - k)) :=
    hbase.mul_left _
  have hmajor : ∀ n : ℤ,
      ‖ω ((n : ℝ) - y)‖ ≤
        16 * schwartzSamplingDecayConstant ω * integerInverseSquare (n - k) := by
    intro n
    have hshift :
        (n : ℝ) - y = ((n - k : ℤ) : ℝ) - t := by
      rw [hy]
      push_cast
      ring
    rw [hshift]
    calc
      ‖ω (((n - k : ℤ) : ℝ) - t)‖ ≤
          4 * schwartzSamplingDecayConstant ω /
            (1 + |((n - k : ℤ) : ℝ) - t| : ℝ) ^ 2 :=
          schwartzSamplingDecay_bound ω _
      _ ≤ 16 * schwartzSamplingDecayConstant ω * integerInverseSquare (n - k) := by
          have hD : 0 ≤ 4 * schwartzSamplingDecayConstant ω := by
            have h := schwartzSamplingDecay_bound ω 0
            norm_num at h
            nlinarith [norm_nonneg (ω 0)]
          calc
            4 * schwartzSamplingDecayConstant ω /
                (1 + |((n - k : ℤ) : ℝ) - t| : ℝ) ^ 2 =
              4 * schwartzSamplingDecayConstant ω *
                (1 / (1 + |((n - k : ℤ) : ℝ) - t| : ℝ) ^ 2) := by ring
            _ ≤ 4 * schwartzSamplingDecayConstant ω *
                (4 * integerInverseSquare (n - k)) :=
              mul_le_mul_of_nonneg_left
                (shiftedInverseSquare_le t (Int.fract_nonneg y)
                  (Int.fract_lt_one y).le (n - k)) hD
            _ = 16 * schwartzSamplingDecayConstant ω *
                integerInverseSquare (n - k) := by ring
  exact hsummable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor

/-- The finite kernel weights in the extension are bounded by `S_ω`. -/
theorem schwartzExtension_weight_sum_le (ω : SchwartzMap ℝ ℂ)
    (f : ℤ →₀ ℂ) (y : ℝ) :
    (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖) ≤ schwartzExtensionS ω := by
  have hsum := schwartzSamplingPeriodization_summable ω (-y)
  have hsumFlipped : Summable (fun n : ℤ => ‖ω (y - (n : ℝ))‖) := by
    have h := hsum.comp_injective neg_injective
    change Summable (fun n : ℤ => ‖ω (((-n : ℤ) : ℝ) - (-y))‖) at h
    apply h.congr
    intro n
    congr 2
    push_cast
    ring
  have hfinite :
      (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖) ≤
        ∑' n : ℤ, ‖ω (y - (n : ℝ))‖ :=
    hsumFlipped.sum_le_tsum f.support (fun n hn => norm_nonneg _)
  have hflip : (∑' n : ℤ, ‖ω (y - (n : ℝ))‖) =
      ∑' n : ℤ, ‖ω ((n : ℝ) - (-y))‖ := by
    rw [show (fun n : ℤ => ‖ω (y - (n : ℝ))‖) =
      (fun n : ℤ => ‖ω ((n : ℝ) - (-y))‖) ∘ (Equiv.neg ℤ) by
        funext n
        simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
        congr 2
        push_cast
        ring]
    exact (Equiv.neg ℤ).tsum_eq
      (fun n : ℤ => ‖ω ((n : ℝ) - (-y))‖)
  have hbounded : BddAbove
      (Set.range fun z : ℝ => ∑' n : ℤ, ‖ω ((n : ℝ) - z)‖) := by
    refine ⟨16 * schwartzSamplingDecayConstant ω * integerInverseSquareSum, ?_⟩
    rintro z ⟨z, rfl⟩
    exact schwartzSamplingPeriodization_bound ω z
  have hsup : (∑' n : ℤ, ‖ω ((n : ℝ) - (-y))‖) ≤ schwartzExtensionS ω :=
    le_csSup hbounded ⟨-y, rfl⟩
  calc
    (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖) ≤
        ∑' n : ℤ, ‖ω (y - (n : ℝ))‖ := hfinite
    _ = ∑' n : ℤ, ‖ω ((n : ℝ) - (-y))‖ := hflip
    _ ≤ schwartzExtensionS ω := hsup

/-- Pointwise weighted Hölder estimate for the finite Schwartz extension. -/
theorem schwartzExtension_pointwise_holder {p : ℝ} (hp : 1 ≤ p)
    (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) (y : ℝ) :
    ‖schwartzExtension ω f y‖ ≤
      (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖) ^ (1 - p⁻¹) *
        (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) ^ p⁻¹ := by
  have htri :
      ‖schwartzExtension ω f y‖ ≤
        ∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ := by
    unfold schwartzExtension
    calc
      ‖∑ n ∈ f.support, f n * ω (y - (n : ℝ))‖ ≤
          ∑ n ∈ f.support, ‖f n * ω (y - (n : ℝ))‖ := norm_sum_le _ _
      _ = ∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul, mul_comm]
  exact htri.trans (Real.inner_le_weight_mul_Lp_of_nonneg f.support hp
    (fun n => ‖ω (y - (n : ℝ))‖) (fun n => ‖f n‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))

theorem schwartzExtension_pointwise_holder_bound {p : ℝ} (hp : 1 ≤ p)
    (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) (y : ℝ) :
    ‖schwartzExtension ω f y‖ ≤
      (schwartzExtensionS ω) ^ (1 - p⁻¹) *
        (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) ^ p⁻¹ := by
  have hw := schwartzExtension_weight_sum_le ω f y
  have hsum_nonneg : 0 ≤ ∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS_nonneg := schwartzExtensionS_nonneg ω
  have hp0 : 0 < p := by linarith
  have hp_exp : 0 ≤ 1 - p⁻¹ := by
    have hinv : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp
    linarith
  have hpow := Real.rpow_le_rpow hsum_nonneg hw hp_exp
  have hsecond : 0 ≤
      (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) ^ p⁻¹ := by
    exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)) _
  exact (schwartzExtension_pointwise_holder hp ω f y).trans
    (mul_le_mul_of_nonneg_right hpow hsecond)

/-- A finite extension of a Schwartz function belongs to every finite `Lᵖ`. -/
theorem schwartzExtension_memLp {p : ℝ} (hp : 1 ≤ p)
    (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) :
    MemLp (schwartzExtension ω f) (ENNReal.ofReal p) (volume : Measure ℝ) := by
  classical
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hω : MemLp ω q (volume : Measure ℝ) := ω.memLp q volume
  have hsum : ∀ s : Finset ℤ,
      MemLp (fun y : ℝ => ∑ n ∈ s, f n * ω (y - (n : ℝ))) q volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        have hterm : MemLp (fun y : ℝ => f a * ω (y - (a : ℝ))) q volume := by
          change MemLp (fun y : ℝ => f a • ω (y - (a : ℝ))) q volume
          exact
            (hω.comp_measurePreserving
              (measurePreserving_sub_right volume (a : ℝ))).const_smul (f a)
        exact hterm.add ih
  change MemLp (fun y : ℝ => ∑ n ∈ f.support, f n * ω (y - (n : ℝ))) q volume
  exact hsum f.support

private theorem translatedSchwartzNorm_integrable (ω : SchwartzMap ℝ ℂ) (t : ℝ) :
    Integrable (fun y : ℝ => ‖ω (y - t)‖) (volume : Measure ℝ) := by
  exact (measurePreserving_sub_right (volume : Measure ℝ) t).integrable_comp_of_integrable
    (schwartzExtensionL_integrable ω)

private theorem translatedSchwartzNorm_integral (ω : SchwartzMap ℝ ℂ) (t : ℝ) :
    ∫ y : ℝ, ‖ω (y - t)‖ = schwartzExtensionL ω := by
  have hmeas : MeasurableEmbedding (fun y : ℝ => y - t) := by
    convert (MeasurableEquiv.addRight (-t)).measurableEmbedding using 1 <;>
      ext y <;> simp [sub_eq_add_neg]
  calc
    ∫ y : ℝ, ‖ω (y - t)‖ = ∫ y : ℝ, ‖ω y‖ :=
      (measurePreserving_sub_right (volume : Measure ℝ) t).integral_comp hmeas
        (fun x : ℝ => ‖ω x‖)
    _ = schwartzExtensionL ω := rfl

private theorem finsupp_lpNorm_eq_sum_rpow {p : ℝ} (hp : 1 ≤ p)
    (f : ℤ →₀ ℂ) :
    lpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) =
      (∑ n ∈ f.support, ‖f n‖ ^ p) ^ p⁻¹ := by
  classical
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hsum : Summable (fun n : ℤ => ‖f n‖ ^ p) := by
    apply summable_of_ne_finset_zero (s := f.support)
    intro n hn
    have hzero : f n = 0 := by simpa using hn
    simp [hzero, hp0.ne']
  have hint : Integrable (fun n : ℤ => ‖f n‖ ^ p) (Measure.count : Measure ℤ) := by
    apply integrable_count_iff.mpr
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hsum
  have hformula :
      ∫ n : ℤ, ‖f n‖ ^ p ∂(Measure.count : Measure ℤ) =
        ∑ n ∈ f.support, ‖f n‖ ^ p := by
    rw [MeasureTheory.integral_countable hint]
    simp only [Measure.real_def]
    rw [tsum_eq_sum (s := f.support)]
    · simp
    · intro n hn
      have hzero : f n = 0 := by simpa using hn
      simp [hzero, hp0.ne']
  rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop (by fun_prop),
    show (ENNReal.ofReal p).toReal = p from ENNReal.toReal_ofReal hp0.le,
    hformula]

private theorem finiteChainVariation_eq_piLp_norm {I : Type*} [LinearOrder I]
    {r : ℝ} (hr : 1 ≤ r) (u : I → ℂ) {length : ℕ}
    (chain : FractionalPrimes.Literature.Variation.StrictOrderedChain I length) :
    FractionalPrimes.Literature.Variation.finiteChainVariation r u chain =
    ENNReal.ofReal ‖WithLp.toLp (ENNReal.ofReal r)
        (fun i : Fin length =>
          u (chain.point i.succ) - u (chain.point i.castSucc))‖ := by
  classical
  let q : ℝ≥0∞ := ENNReal.ofReal r
  have hr0 : 0 < r := by linarith
  have hqToReal : q.toReal = r := ENNReal.toReal_ofReal hr0.le
  letI : Fact (1 ≤ q) := ⟨by
    change 1 ≤ ENNReal.ofReal r
    exact ENNReal.one_le_ofReal.mpr hr⟩
  have hsum_nonneg :
      0 ≤ ∑ i : Fin length,
        ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hnorm :
      ‖WithLp.toLp q (fun i : Fin length =>
        u (chain.point i.succ) - u (chain.point i.castSucc))‖ =
        (∑ i : Fin length,
          ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r) ^ r⁻¹ := by
    rw [PiLp.norm_eq_sum (by rw [hqToReal]; exact hr0)]
    simp only [PiLp.toLp_apply, hqToReal]
    congr 2
    simp [one_div]
  rw [FractionalPrimes.Literature.Variation.finiteChainVariation,
    hnorm]
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.ofReal_rpow_of_nonneg hsum_nonneg (inv_nonneg.mpr hr0.le)]
  have hterms : ∀ i : Fin length, i ∈ Finset.univ →
      0 ≤ ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r := by
    intro i hi
    exact Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.ofReal_sum_of_nonneg hterms]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]

private theorem finiteChainVariation_sample_le_lintegral {I : Type*}
    [LinearOrder I] {r : ℝ} (hr : 1 ≤ r) (ω : SchwartzMap ℝ ℂ)
    (G : I → ℝ → ℂ) {length : ℕ}
    (chain : FractionalPrimes.Literature.Variation.StrictOrderedChain I length)
    (x : ℝ)
    (hrep : ∀ j z, G j z = ∫ y : ℝ, ω (z - y) * G j y)
    (hint : ∀ j z, Integrable (fun y : ℝ => ω (z - y) * G j y)
      (volume : Measure ℝ)) :
    FractionalPrimes.Literature.Variation.finiteChainVariation r
        (fun j => G j x) chain ≤
      ∫⁻ y : ℝ, ‖ω (x - y)‖ₑ *
        FractionalPrimes.Literature.Variation.finiteChainVariation r
          (fun j => G j y) chain := by
  classical
  let q : ℝ≥0∞ := ENNReal.ofReal r
  have hr0 : 0 < r := by linarith
  letI : Fact (1 ≤ q) := ⟨by
    change 1 ≤ ENNReal.ofReal r
    exact ENNReal.one_le_ofReal.mpr hr⟩
  let D : ℝ → PiLp q (fun _ : Fin length => ℂ) := fun y =>
    WithLp.toLp q (fun i : Fin length =>
      G (chain.point i.succ) y - G (chain.point i.castSucc) y)
  let H : ℝ → PiLp q (fun _ : Fin length => ℂ) :=
    fun y => ω (x - y) • D y
  have hcoords : ∀ i : Fin length,
      Integrable (fun y : ℝ => ω (x - y) *
        (G (chain.point i.succ) y - G (chain.point i.castSucc) y))
        (volume : Measure ℝ) := by
    intro i
    have h₂ := hint (chain.point i.succ) x
    have h₁ := hint (chain.point i.castSucc) x
    have hdiff : Integrable
        (fun y : ℝ => ω (x - y) * G (chain.point i.succ) y -
          ω (x - y) * G (chain.point i.castSucc) y) (volume : Measure ℝ) :=
      h₂.sub h₁
    apply hdiff.congr
    filter_upwards [] with y
    ring
  have hHcoords : ∀ i : Fin length, Integrable (H · i) (volume : Measure ℝ) := by
    intro i
    change Integrable (fun y : ℝ => ω (x - y) *
      (G (chain.point i.succ) y - G (chain.point i.castSucc) y)) _
    exact hcoords i
  have hHint : Integrable H (volume : Measure ℝ) :=
    Integrable.of_eval_piLp hHcoords
  have hEq : (∫ y : ℝ, H y ∂(volume : Measure ℝ)) =
      WithLp.toLp q (fun i : Fin length =>
        G (chain.point i.succ) x - G (chain.point i.castSucc) x) := by
    apply PiLp.ext
    intro i
    rw [MeasureTheory.eval_integral_piLp hHcoords i]
    change (∫ y : ℝ, ω (x - y) *
      (G (chain.point i.succ) y - G (chain.point i.castSucc) y)) = _
    calc
      _ = (∫ y : ℝ, ω (x - y) * G (chain.point i.succ) y) -
            ∫ y : ℝ, ω (x - y) * G (chain.point i.castSucc) y := by
          rw [← integral_sub (hint (chain.point i.succ) x)
            (hint (chain.point i.castSucc) x)]
          congr 1
          funext y
          ring
      _ = G (chain.point i.succ) x - G (chain.point i.castSucc) x := by
          rw [← hrep (chain.point i.succ) x,
            ← hrep (chain.point i.castSucc) x]
  have hsample :
      FractionalPrimes.Literature.Variation.finiteChainVariation r
          (fun j => G j x) chain =
        ‖∫ y : ℝ, H y ∂(volume : Measure ℝ)‖ₑ := by
    rw [finiteChainVariation_eq_piLp_norm hr (fun j => G j x) chain, ← hEq]
    exact ofReal_norm (∫ y : ℝ, H y ∂(volume : Measure ℝ))
  have hnorm (y : ℝ) : ‖H y‖ₑ = ‖ω (x - y)‖ₑ *
      FractionalPrimes.Literature.Variation.finiteChainVariation r
        (fun j => G j y) chain := by
    calc
      ‖H y‖ₑ = ‖ω (x - y)‖ₑ * ‖D y‖ₑ := by simp [H, enorm_smul]
      _ = ‖ω (x - y)‖ₑ *
          FractionalPrimes.Literature.Variation.finiteChainVariation r
            (fun j => G j y) chain := by
        rw [finiteChainVariation_eq_piLp_norm hr (fun j => G j y) chain]
        simp [D, q]
  calc
    FractionalPrimes.Literature.Variation.finiteChainVariation r
        (fun j => G j x) chain =
        ‖∫ y : ℝ, H y ∂(volume : Measure ℝ)‖ₑ := hsample
    _ ≤ ∫⁻ y : ℝ, ‖H y‖ₑ := enorm_integral_le_lintegral_enorm H
    _ = ∫⁻ y : ℝ, ‖ω (x - y)‖ₑ *
          FractionalPrimes.Literature.Variation.finiteChainVariation r
            (fun j => G j y) chain := by simp_rw [hnorm]

private theorem weighted_lintegral_rpow_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p q : ℝ} (hpq : p.HolderConjugate q)
    {k F : α → ℝ≥0∞} (hk : AEMeasurable k μ) (hF : AEMeasurable F μ) :
    (∫⁻ x, k x * F x ∂μ) ^ p ≤
      (∫⁻ x, k x ∂μ) ^ (p - 1) * ∫⁻ x, k x * F x ^ p ∂μ := by
  let a : α → ℝ≥0∞ := fun x => F x * k x ^ p⁻¹
  let b : α → ℝ≥0∞ := fun x => k x ^ p⁻¹
  have hkpow : AEMeasurable (fun x => k x ^ p⁻¹) μ :=
    (ENNReal.continuous_rpow_const (y := p⁻¹)).measurable.comp_aemeasurable hk
  have ha : AEMeasurable a μ := hF.mul hkpow
  have hb : AEMeasurable b μ := hkpow
  have hholder := ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
    hpq ha hb
  have hleft : ∫⁻ x, a x * b x ^ (p - 1) ∂μ = ∫⁻ x, k x * F x ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [] with x
    dsimp [a, b]
    rw [← ENNReal.rpow_mul]
    have hexp : p⁻¹ + p⁻¹ * (p - 1) = 1 := by
      field_simp [hpq.pos.ne']
      ring
    calc
      F x * k x ^ p⁻¹ * k x ^ (p⁻¹ * (p - 1)) =
          F x * (k x ^ p⁻¹ * k x ^ (p⁻¹ * (p - 1))) := by ac_rfl
      _ = F x * k x ^ (p⁻¹ + p⁻¹ * (p - 1)) := by
        rw [← ENNReal.rpow_add_of_nonneg p⁻¹ (p⁻¹ * (p - 1))
          (inv_nonneg.mpr hpq.pos.le)
          (mul_nonneg (inv_nonneg.mpr hpq.pos.le)
            (sub_nonneg.mpr (by linarith [hpq.sub_one_pos])))]
      _ = k x * F x := by rw [hexp, ENNReal.rpow_one]; ac_rfl
  have hfirst : ∫⁻ x, a x ^ p ∂μ = ∫⁻ x, F x ^ p * k x ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [] with x
    dsimp [a]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.pos.le, ← ENNReal.rpow_mul]
    have hexp : p⁻¹ * p = 1 := inv_mul_cancel₀ hpq.pos.ne'
    rw [hexp, ENNReal.rpow_one]
  have hsecond : ∫⁻ x, b x ^ p ∂μ = ∫⁻ x, k x ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [] with x
    dsimp [b]
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hpq.pos.ne', ENNReal.rpow_one]
  have hholder' :
      (∫⁻ x, k x * F x ∂μ) ≤
        (∫⁻ x, F x ^ p * k x ∂μ) ^ p⁻¹ *
          (∫⁻ x, k x ∂μ) ^ q⁻¹ := by
    rw [hleft, hfirst, hsecond] at hholder
    simpa only [one_div] using hholder
  have hexp : q⁻¹ * p = p - 1 := by
    have hrecip := hpq.one_div_add_one_div
    field_simp [hpq.pos.ne', hpq.symm.pos.ne'] at hrecip ⊢
    linarith
  calc
    (∫⁻ x, k x * F x ∂μ) ^ p ≤
        ((∫⁻ x, F x ^ p * k x ∂μ) ^ p⁻¹ *
          (∫⁻ x, k x ∂μ) ^ q⁻¹) ^ p :=
      ENNReal.rpow_le_rpow hholder' hpq.pos.le
    _ = (∫⁻ x, F x ^ p * k x ∂μ) ^ (p⁻¹ * p) *
          (∫⁻ x, k x ∂μ) ^ (q⁻¹ * p) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.pos.le,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ = (∫⁻ x, F x ^ p * k x ∂μ) *
          (∫⁻ x, k x ∂μ) ^ (p - 1) := by
      rw [inv_mul_cancel₀ hpq.pos.ne', hexp, ENNReal.rpow_one]
    _ = (∫⁻ x, k x ∂μ) ^ (p - 1) *
          ∫⁻ x, k x * F x ^ p ∂μ := by
      rw [mul_comm]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [mul_comm]

private theorem integralKernel_eLpNorm'_le {p : ℝ} (hp : 1 ≤ p)
    (k : ℤ → ℝ → ℝ≥0∞) (F : ℝ → ℝ≥0∞) (L S : ℝ≥0∞)
    (hStop : S ≠ ∞)
    (hk : ∀ n, AEMeasurable (k n) (volume : Measure ℝ))
    (hF : AEMeasurable F (volume : Measure ℝ))
    (hrow : ∀ n, ∫⁻ y : ℝ, k n y ≤ L)
    (hcol : ∀ y : ℝ, ∑' n : ℤ, k n y ≤ S) :
    MeasureTheory.eLpNorm' (fun n : ℤ => ∫⁻ y : ℝ, k n y * F y)
        p (Measure.count : Measure ℤ) ≤
      L ^ (1 - p⁻¹) * S ^ p⁻¹ *
        MeasureTheory.eLpNorm' F p (volume : Measure ℝ) := by
  classical
  let T : ℤ → ℝ≥0∞ := fun n => ∫⁻ y : ℝ, k n y * F y
  have hFp : AEMeasurable (fun y : ℝ => F y ^ p) (volume : Measure ℝ) :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable hF
  have hterm : ∀ n : ℤ,
      AEMeasurable (fun y : ℝ => k n y * F y ^ p) (volume : Measure ℝ) :=
    fun n => (hk n).mul hFp
  have hTonelli :
      (∑' n : ℤ, ∫⁻ y : ℝ, k n y * F y ^ p) =
        ∫⁻ y : ℝ, ∑' n : ℤ, k n y * F y ^ p := by
    symm
    exact lintegral_tsum hterm
  have hcolumn :
      ∫⁻ y : ℝ, ∑' n : ℤ, k n y * F y ^ p ≤
        S * ∫⁻ y : ℝ, F y ^ p := by
    calc
      ∫⁻ y : ℝ, ∑' n : ℤ, k n y * F y ^ p =
          ∫⁻ y : ℝ, (∑' n : ℤ, k n y) * F y ^ p := by
        congr 1
        funext y
        rw [ENNReal.tsum_mul_right]
      _ ≤ ∫⁻ y : ℝ, S * F y ^ p := by
        apply lintegral_mono
        intro y
        exact mul_le_mul_of_nonneg_right (hcol y) (by positivity)
      _ = S * ∫⁻ y : ℝ, F y ^ p := by
        rw [lintegral_const_mul' S _ hStop]
  by_cases hp1 : p = 1
  · have hTsum :
        MeasureTheory.eLpNorm' T 1 (Measure.count : Measure ℤ) = ∑' n : ℤ, T n := by
      rw [MeasureTheory.eLpNorm'_eq_lintegral_enorm]
      norm_num
      rw [lintegral_count]
    have hTonelliOne :
        (∑' n : ℤ, T n) = ∫⁻ y : ℝ, (∑' n : ℤ, k n y) * F y := by
      calc
        _ = ∫⁻ y : ℝ, ∑' n : ℤ, k n y * F y := by
          symm
          apply lintegral_tsum
          intro n
          exact (hk n).mul hF
        _ = ∫⁻ y : ℝ, (∑' n : ℤ, k n y) * F y := by
          congr 1
          funext y
          rw [ENNReal.tsum_mul_right]
    have hbound :
        ∫⁻ y : ℝ, (∑' n : ℤ, k n y) * F y ≤
          S * ∫⁻ y : ℝ, F y := by
      calc
        _ ≤ ∫⁻ y : ℝ, S * F y := by
          apply lintegral_mono
          intro y
          exact mul_le_mul_of_nonneg_right (hcol y) (by positivity)
        _ = S * ∫⁻ y : ℝ, F y := by
          rw [lintegral_const_mul' S _ hStop]
    have hFone : MeasureTheory.eLpNorm' F 1 (volume : Measure ℝ) =
        ∫⁻ y : ℝ, F y := by
      rw [MeasureTheory.eLpNorm'_eq_lintegral_enorm]
      norm_num
    rw [hp1, hTsum, hTonelliOne, hFone]
    simp
    exact hbound
  · have hpgt : 1 < p := by
      rcases lt_or_eq_of_le hp with h | h
      · exact h
      · exact (hp1 h.symm).elim
    let q : ℝ := p / (p - 1)
    have hpq : p.HolderConjugate q := by
      apply Real.holderConjugate_iff_eq_conjExponent hpgt |>.2
      rfl
    have hFpNorm : MeasureTheory.eLpNorm' F p (volume : Measure ℝ) =
        (∫⁻ y : ℝ, F y ^ p) ^ p⁻¹ := by
      rw [MeasureTheory.eLpNorm'_eq_lintegral_enorm]
      simp only [one_div]
      congr 1
    have hsumBound :
        (∑' n : ℤ, T n ^ p) ≤
          L ^ (p - 1) * S * ∫⁻ y : ℝ, F y ^ p := by
      calc
        (∑' n : ℤ, T n ^ p) ≤
            ∑' n : ℤ, L ^ (p - 1) * ∫⁻ y : ℝ, k n y * F y ^ p := by
          apply ENNReal.tsum_le_tsum
          intro n
          have hweighted := weighted_lintegral_rpow_le hpq (hk n) hF
          have hrowpow : (∫⁻ y : ℝ, k n y) ^ (p - 1) ≤ L ^ (p - 1) :=
            ENNReal.rpow_le_rpow (hrow n) (sub_nonneg.mpr (le_of_lt (by linarith)))
          calc
            T n ^ p ≤ (∫⁻ y : ℝ, k n y) ^ (p - 1) *
                ∫⁻ y : ℝ, k n y * F y ^ p := by
              simpa [T] using hweighted
            _ ≤ L ^ (p - 1) * ∫⁻ y : ℝ, k n y * F y ^ p :=
              mul_le_mul_of_nonneg_right hrowpow (by positivity)
        _ = L ^ (p - 1) *
              ∑' n : ℤ, ∫⁻ y : ℝ, k n y * F y ^ p := by
          rw [ENNReal.tsum_mul_left]
        _ = L ^ (p - 1) *
              ∫⁻ y : ℝ, ∑' n : ℤ, k n y * F y ^ p := by
          rw [hTonelli]
        _ ≤ L ^ (p - 1) * (S * ∫⁻ y : ℝ, F y ^ p) :=
          mul_le_mul_of_nonneg_left hcolumn (by positivity)
        _ = L ^ (p - 1) * S * ∫⁻ y : ℝ, F y ^ p := by ac_rfl
    have hTintegral :
        ∫⁻ n : ℤ, ‖T n‖ₑ ^ p ∂(Measure.count : Measure ℤ) =
          ∑' n : ℤ, T n ^ p := by
      rw [lintegral_count]
      apply tsum_congr
      intro n
      simp [T]
    have hpInv : 0 ≤ p⁻¹ := inv_nonneg.mpr (by linarith)
    have hcoeff :
        (L ^ (p - 1) * S * ∫⁻ y : ℝ, F y ^ p) ^ p⁻¹ =
          L ^ (1 - p⁻¹) * S ^ p⁻¹ *
            MeasureTheory.eLpNorm' F p (volume : Measure ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpInv,
        ENNReal.mul_rpow_of_nonneg _ _ hpInv,
        ← ENNReal.rpow_mul]
      have hexp : (p - 1) * p⁻¹ = 1 - p⁻¹ := by
        field_simp [hpgt.ne']
      rw [hexp, hFpNorm]
    calc
      MeasureTheory.eLpNorm' T p (Measure.count : Measure ℤ) =
          (∫⁻ n : ℤ, ‖T n‖ₑ ^ p ∂(Measure.count : Measure ℤ)) ^ p⁻¹ := by
        rw [MeasureTheory.eLpNorm'_eq_lintegral_enorm, one_div]
      _ = (∑' n : ℤ, T n ^ p) ^ p⁻¹ := by rw [hTintegral]
      _ ≤ (L ^ (p - 1) * S * ∫⁻ y : ℝ, F y ^ p) ^ p⁻¹ :=
        ENNReal.rpow_le_rpow hsumBound hpInv
      _ = L ^ (1 - p⁻¹) * S ^ p⁻¹ *
          MeasureTheory.eLpNorm' F p (volume : Measure ℝ) := hcoeff

private theorem schwartzKernel_lintegral_eq (ω : SchwartzMap ℝ ℂ) (n : ℤ) :
    ∫⁻ y : ℝ, ‖ω ((n : ℝ) - y)‖ₑ =
      ENNReal.ofReal (schwartzExtensionL ω) := by
  have hmp : MeasurePreserving (fun y : ℝ => (n : ℝ) - y) volume volume :=
    volume.measurePreserving_sub_left (n : ℝ)
  have hmeas : MeasurableEmbedding (fun y : ℝ => (n : ℝ) - y) := by
    convert ((MeasurableEquiv.neg ℝ).trans
      (MeasurableEquiv.addRight (n : ℝ))).measurableEmbedding using 1 <;>
      ext y <;> simp [sub_eq_add_neg, add_comm]
  have hint : Integrable (fun y : ℝ => ω ((n : ℝ) - y)) volume :=
    hmp.integrable_comp_of_integrable ω.integrable
  calc
    ∫⁻ y : ℝ, ‖ω ((n : ℝ) - y)‖ₑ =
        ENNReal.ofReal (∫ y : ℝ, ‖ω ((n : ℝ) - y)‖) :=
      (ofReal_integral_norm_eq_lintegral_enorm hint).symm
    _ = ENNReal.ofReal (∫ y : ℝ, ‖ω y‖) := by
      rw [hmp.integral_comp hmeas (fun y : ℝ => ‖ω y‖)]
    _ = ENNReal.ofReal (schwartzExtensionL ω) := rfl

private theorem schwartzKernel_periodization_le (ω : SchwartzMap ℝ ℂ) (y : ℝ) :
    ∑' n : ℤ, ‖ω ((n : ℝ) - y)‖ₑ ≤ ENNReal.ofReal (schwartzExtensionS ω) := by
  have hsummable := schwartzSamplingPeriodization_summable ω y
  have htsum :
      (∑' n : ℤ, ‖ω ((n : ℝ) - y)‖ₑ) =
        ENNReal.ofReal (∑' n : ℤ, ‖ω ((n : ℝ) - y)‖) := by
    calc
      _ = ∑' n : ℤ, ENNReal.ofReal ‖ω ((n : ℝ) - y)‖ := by
        congr 1
        funext n
        exact (ofReal_norm _).symm
      _ = ENNReal.ofReal (∑' n : ℤ, ‖ω ((n : ℝ) - y)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hsummable).symm
  have hbounded : BddAbove
      (Set.range fun z : ℝ => ∑' n : ℤ, ‖ω ((n : ℝ) - z)‖) := by
    refine ⟨16 * schwartzSamplingDecayConstant ω * integerInverseSquareSum, ?_⟩
    rintro z ⟨z, rfl⟩
    exact schwartzSamplingPeriodization_bound ω z
  have hsup : (∑' n : ℤ, ‖ω ((n : ℝ) - y)‖) ≤ schwartzExtensionS ω :=
    le_csSup hbounded ⟨y, rfl⟩
  rw [htsum]
  exact ENNReal.ofReal_le_ofReal hsup

/-- The mathematical fixed-point condition `G_j = ω * G_j`.  The Bochner
integral notation in Lean is total and returns zero when its integrand is not
integrable.  Thus integrability is included here as part of what it means for
the convolution `ω * G_j` to be defined; it is not an additional smoothness or
size hypothesis beyond the source convolution identity. -/
def IsSchwartzConvolutionFixedPoint {I : Type*} (ω : SchwartzMap ℝ ℂ)
    (G : I → ℝ → ℂ) : Prop :=
  ∀ j z, Integrable (fun y : ℝ => ω (z - y) * G j y) (volume : Measure ℝ) ∧
    G j z = ∫ y : ℝ, ω (z - y) * G j y

/-- Pointwise sampling bound for variation, with the same ordered index set
used at the lattice points and in the continuous model. -/
theorem orderedRVariation_pointwise_sampling_le {I : Type*} [LinearOrder I]
    {r : ℝ} (hr : 1 ≤ r) (ω : SchwartzMap ℝ ℂ) (G : I → ℝ → ℂ)
    (hfixed : IsSchwartzConvolutionFixedPoint ω G) (n : ℤ) :
    FractionalPrimes.Literature.Variation.orderedRVariation r
        (fun j => G j n) ≤
      ∫⁻ y : ℝ, ‖ω ((n : ℝ) - y)‖ₑ *
        FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun j => G j y) := by
  classical
  have hrep : ∀ j z, G j z = ∫ y : ℝ, ω (z - y) * G j y :=
    fun j z => (hfixed j z).2
  have hint : ∀ j z, Integrable (fun y : ℝ => ω (z - y) * G j y)
      (volume : Measure ℝ) := fun j z => (hfixed j z).1
  unfold FractionalPrimes.Literature.Variation.orderedRVariation
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  calc
    FractionalPrimes.Literature.Variation.finiteChainVariation r
        (fun j => G j n) chain ≤
      ∫⁻ y : ℝ, ‖ω ((n : ℝ) - y)‖ₑ *
        FractionalPrimes.Literature.Variation.finiteChainVariation r
          (fun j => G j y) chain :=
      finiteChainVariation_sample_le_lintegral hr ω G chain n hrep hint
    _ ≤ ∫⁻ y : ℝ, ‖ω ((n : ℝ) - y)‖ₑ *
        FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun j => G j y) := by
      apply lintegral_mono
      intro y
      exact mul_le_mul_of_nonneg_left
        (FractionalPrimes.Literature.Variation.finiteChainVariation_le_orderedRVariation
          r (fun j => G j y) chain) (by positivity)

/-- The exact `ha:sampling` variation estimate, in the extended-real `Lᵖ`
seminorm notation.  The exponent range is `1 ≤ p < ∞`, and `r ≥ 1`; both
variation expressions use the same countable linear order. -/
theorem schwartzVariationSampling_eLpNorm'_le {I : Type*} [LinearOrder I]
    [Countable I] {p r : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (ω : SchwartzMap ℝ ℂ) (G : I → ℝ → ℂ)
    (hcont : ∀ j, Continuous (G j))
    (hfixed : IsSchwartzConvolutionFixedPoint ω G) :
    MeasureTheory.eLpNorm' (fun n : ℤ =>
        FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun j => G j n)) p (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal (schwartzExtensionL ω) ^ (1 - p⁻¹) *
        ENNReal.ofReal (schwartzExtensionS ω) ^ p⁻¹ *
          MeasureTheory.eLpNorm' (fun y : ℝ =>
            FractionalPrimes.Literature.Variation.orderedRVariation r
              (fun j => G j y)) p (volume : Measure ℝ) := by
  classical
  let F : ℝ → ℝ≥0∞ := fun y =>
    FractionalPrimes.Literature.Variation.orderedRVariation r
      (fun j => G j y)
  let k : ℤ → ℝ → ℝ≥0∞ := fun n y => ‖ω ((n : ℝ) - y)‖ₑ
  have hGmeas : ∀ j, Measurable (G j) := fun j => (hcont j).measurable
  have hFmeas : Measurable F := by
    change Measurable
      (FractionalPrimes.Literature.Variation.orderedRVariationFun r G)
    exact FractionalPrimes.Literature.Variation.measurable_orderedRVariationFun
      r G hGmeas
  have hF : AEMeasurable F (volume : Measure ℝ) := hFmeas.aemeasurable
  have hk : ∀ n, AEMeasurable (k n) (volume : Measure ℝ) := by
    intro n
    apply (show Continuous (fun y : ℝ => ‖ω ((n : ℝ) - y)‖ₑ) by fun_prop).measurable.aemeasurable
  have hrow : ∀ n, ∫⁻ y : ℝ, k n y ≤ ENNReal.ofReal (schwartzExtensionL ω) := by
    intro n
    rw [show k n = (fun y : ℝ => ‖ω ((n : ℝ) - y)‖ₑ) by rfl,
      schwartzKernel_lintegral_eq]
  have hcol : ∀ y : ℝ, ∑' n : ℤ, k n y ≤
      ENNReal.ofReal (schwartzExtensionS ω) := by
    intro y
    exact schwartzKernel_periodization_le ω y
  have hpoint : ∀ n : ℤ,
      FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun j => G j n) ≤ ∫⁻ y : ℝ, k n y * F y := by
    intro n
    simpa [F, k] using
      orderedRVariation_pointwise_sampling_le hr ω G hfixed n
  have hkernel := integralKernel_eLpNorm'_le hp k F
    (ENNReal.ofReal (schwartzExtensionL ω))
    (ENNReal.ofReal (schwartzExtensionS ω)) ENNReal.ofReal_ne_top hk hF hrow hcol
  have hp0 : 0 ≤ p := by linarith
  exact (MeasureTheory.eLpNorm'_mono_enorm_ae hp0
    (ae_of_all (Measure.count : Measure ℤ)
      fun n => by simpa using hpoint n)).trans hkernel

/-- The `ha:sampling` variation estimate in standard `Lᵖ` seminorm notation.
The coefficient is the source coefficient `Lω^(1−1/p) Sω^(1/p)`. -/
theorem schwartzVariationSampling_eLpNorm_le {I : Type*} [LinearOrder I]
    [Countable I] {p r : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (ω : SchwartzMap ℝ ℂ) (G : I → ℝ → ℂ)
    (hcont : ∀ j, Continuous (G j))
    (hfixed : IsSchwartzConvolutionFixedPoint ω G) :
    MeasureTheory.eLpNorm (fun n : ℤ =>
        FractionalPrimes.Literature.Variation.orderedRVariation r
          (fun j => G j n)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal
          (schwartzExtensionL ω ^ (1 - p⁻¹) *
            schwartzExtensionS ω ^ p⁻¹) *
        MeasureTheory.eLpNorm (fun y : ℝ =>
          FractionalPrimes.Literature.Variation.orderedRVariation r
            (fun j => G j y)) (ENNReal.ofReal p) (volume : Measure ℝ) := by
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hqToReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  let F : ℝ → ℝ≥0∞ := fun y =>
    FractionalPrimes.Literature.Variation.orderedRVariation r
      (fun j => G j y)
  let g : ℤ → ℝ≥0∞ := fun n =>
    FractionalPrimes.Literature.Variation.orderedRVariation r
      (fun j => G j n)
  have hGmeas : ∀ j, Measurable (G j) := fun j => (hcont j).measurable
  have hFmeas : Measurable F := by
    change Measurable
      (FractionalPrimes.Literature.Variation.orderedRVariationFun r G)
    exact FractionalPrimes.Literature.Variation.measurable_orderedRVariationFun
      r G hGmeas
  have hFstrong : AEStronglyMeasurable F (volume : Measure ℝ) :=
    hFmeas.aestronglyMeasurable
  have hgstrong : AEStronglyMeasurable g (Measure.count : Measure ℤ) :=
    AEStronglyMeasurable.of_discrete
  have hleft : MeasureTheory.eLpNorm g (ENNReal.ofReal p)
      (Measure.count : Measure ℤ) = MeasureTheory.eLpNorm' g p
        (Measure.count : Measure ℤ) := by
    rw [MeasureTheory.eLpNorm_eq_eLpNorm' hq0 hqtop hgstrong, hqToReal]
  have hright : MeasureTheory.eLpNorm F (ENNReal.ofReal p)
      (volume : Measure ℝ) = MeasureTheory.eLpNorm' F p
        (volume : Measure ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_eLpNorm' hq0 hqtop hFstrong, hqToReal]
  have hL := schwartzExtensionL_nonneg ω
  have hS := schwartzExtensionS_nonneg ω
  have hexpS : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hexpL : 0 ≤ 1 - p⁻¹ := by
    have hinv : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp
    linarith
  have hcoef :
      ENNReal.ofReal (schwartzExtensionL ω ^ (1 - p⁻¹) *
          schwartzExtensionS ω ^ p⁻¹) =
        ENNReal.ofReal (schwartzExtensionL ω) ^ (1 - p⁻¹) *
          ENNReal.ofReal (schwartzExtensionS ω) ^ p⁻¹ := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hL _),
      ENNReal.ofReal_rpow_of_nonneg hL hexpL,
      ENNReal.ofReal_rpow_of_nonneg hS hexpS]
  rw [hleft, hright]
  simpa [g, F, hcoef] using
    schwartzVariationSampling_eLpNorm'_le hp hr ω G hcont hfixed

private theorem schwartzExtension_weightedSum_integrable {p : ℝ}
    (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) :
    Integrable
      (fun y : ℝ => ∑ n ∈ f.support,
        ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) (volume : Measure ℝ) := by
  classical
  apply integrable_finsetSum f.support
  intro n hn
  have h := translatedSchwartzNorm_integrable ω (n : ℝ)
  simpa [mul_comm] using h.const_mul (‖f n‖ ^ p)

private theorem schwartzExtension_weightedSum_integral {p : ℝ}
    (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) :
    ∫ y : ℝ, ∑ n ∈ f.support,
        ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p =
      (∑ n ∈ f.support, ‖f n‖ ^ p) * schwartzExtensionL ω := by
  classical
  have hterm : ∀ n ∈ f.support,
      Integrable (fun y : ℝ => ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p)
        (volume : Measure ℝ) := by
    intro n hn
    have h := translatedSchwartzNorm_integrable ω (n : ℝ)
    simpa [mul_comm] using h.const_mul (‖f n‖ ^ p)
  rw [integral_finsetSum f.support hterm]
  calc
    (∑ n ∈ f.support,
        ∫ y : ℝ, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) =
      ∑ n ∈ f.support, ‖f n‖ ^ p * schwartzExtensionL ω := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [integral_mul_const, translatedSchwartzNorm_integral]
        ring
    _ = (∑ n ∈ f.support, ‖f n‖ ^ p) * schwartzExtensionL ω := by
      rw [← Finset.sum_mul]

/-- Sharp finite-`p` estimate for the discrete-to-continuous extension. -/
theorem schwartzExtension_lpNorm_le {p : ℝ} (hp : 1 ≤ p)
    (ω : SchwartzMap ℝ ℂ) (f : ℤ →₀ ℂ) :
    lpNorm (schwartzExtension ω f) (ENNReal.ofReal p) (volume : Measure ℝ) ≤
      schwartzExtensionS ω ^ (1 - p⁻¹) *
        schwartzExtensionL ω ^ p⁻¹ *
          lpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  classical
  have hp0 : 0 < p := by linarith
  have hpInvNonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hqToReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hS := schwartzExtensionS_nonneg ω
  have hL := schwartzExtensionL_nonneg ω
  let A : ℝ := schwartzExtensionS ω ^ (p - 1)
  let B : ℝ := ∑ n ∈ f.support, ‖f n‖ ^ p
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun n hn => Real.rpow_nonneg (norm_nonneg _) _
  have hA : 0 ≤ A := by
    exact Real.rpow_nonneg hS _
  have hleftMem := schwartzExtension_memLp hp ω f
  have hleftRpow : MemLp (fun y : ℝ => ‖schwartzExtension ω f y‖ ^ p) 1
      (volume : Measure ℝ) := by
    simpa [hqToReal] using hleftMem.norm_rpow hq0 hqTop
  have hleftInt : Integrable
      (fun y : ℝ => ‖schwartzExtension ω f y‖ ^ p) (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp hleftRpow
  have hweightInt := schwartzExtension_weightedSum_integrable (p := p) ω f
  have hrightInt : Integrable
      (fun y : ℝ => A * ∑ n ∈ f.support,
        ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) (volume : Measure ℝ) := by
    simpa [A] using hweightInt.const_mul (schwartzExtensionS ω ^ (p - 1))
  have hexp : (1 - p⁻¹) * p = p - 1 := by
    field_simp [hp0.ne']
  have hexp' : (p - 1) * p⁻¹ = 1 - p⁻¹ := by
    field_simp [hp0.ne']
  have hinvexp : p⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
  have hpointwise : ∀ y : ℝ,
      ‖schwartzExtension ω f y‖ ^ p ≤
        A * ∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p := by
    intro y
    have hweight := schwartzExtension_pointwise_holder_bound hp ω f y
    have hweightNonneg : 0 ≤
        ∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p := by
      exact Finset.sum_nonneg fun n hn =>
        mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
    have hpow :
        (schwartzExtensionS ω ^ (1 - p⁻¹) *
          (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) ^ p⁻¹) ^ p =
        A * ∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg hS _) (Real.rpow_nonneg hweightNonneg _),
        ← Real.rpow_mul hS, ← Real.rpow_mul hweightNonneg, hexp, hinvexp,
        Real.rpow_one]
    calc
      ‖schwartzExtension ω f y‖ ^ p ≤
          (schwartzExtensionS ω ^ (1 - p⁻¹) *
            (∑ n ∈ f.support, ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p) ^ p⁻¹) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) hweight hp0.le
      _ = A * ∑ n ∈ f.support,
          ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p := hpow
  have hintegral :
      ∫ y : ℝ, ‖schwartzExtension ω f y‖ ^ p ≤ A * B * schwartzExtensionL ω := by
    calc
      ∫ y : ℝ, ‖schwartzExtension ω f y‖ ^ p ≤
          ∫ y : ℝ, A * ∑ n ∈ f.support,
            ‖ω (y - (n : ℝ))‖ * ‖f n‖ ^ p :=
          integral_mono_ae hleftInt hrightInt (ae_of_all _ hpointwise)
      _ = A * (B * schwartzExtensionL ω) := by
          rw [integral_const_mul, schwartzExtension_weightedSum_integral (p := p)]
      _ = A * B * schwartzExtensionL ω := by ring
  have hroot := Real.rpow_le_rpow
    (integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) _))
    hintegral hpInvNonneg
  have hrootBase : A * B * schwartzExtensionL ω =
      schwartzExtensionS ω ^ (p - 1) * schwartzExtensionL ω * B := by
    dsimp [A]
    ring
  rw [hrootBase] at hroot
  have hcoeff :
      (schwartzExtensionS ω ^ (p - 1) * schwartzExtensionL ω * B) ^ p⁻¹ =
        schwartzExtensionS ω ^ (1 - p⁻¹) *
          schwartzExtensionL ω ^ p⁻¹ * B ^ p⁻¹ := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hS _) hL) hB,
      Real.mul_rpow (Real.rpow_nonneg hS _) hL,
      ← Real.rpow_mul hS, hexp']
  calc
    lpNorm (schwartzExtension ω f) (ENNReal.ofReal p) (volume : Measure ℝ) =
        (∫ y : ℝ, ‖schwartzExtension ω f y‖ ^ p) ^ p⁻¹ := by
          rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqTop
            (continuous_schwartzExtension ω f).aestronglyMeasurable, hqToReal]
    _ ≤ (schwartzExtensionS ω ^ (p - 1) * schwartzExtensionL ω * B) ^ p⁻¹ := hroot
    _ = schwartzExtensionS ω ^ (1 - p⁻¹) *
          schwartzExtensionL ω ^ p⁻¹ * B ^ p⁻¹ := hcoeff
    _ = schwartzExtensionS ω ^ (1 - p⁻¹) *
          schwartzExtensionL ω ^ p⁻¹ *
            lpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
          dsimp [B]
          rw [finsupp_lpNorm_eq_sum_rpow hp f]

end

end FractionalPrimes.Literature.Harmonic
