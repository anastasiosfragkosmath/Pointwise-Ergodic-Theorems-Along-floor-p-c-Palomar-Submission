module

public import FractionalPrimes.Literature.Variation.FiniteChainVariation
public import FractionalPrimes.Literature.Variation.FiniteJumpCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Finite-chain proof infrastructure for weak variation from jumps

This file records the blueprint-faithful p-moment form of `lv:weak-variation`
and formalizes its finite-chain dyadic decomposition and Chebyshev reduction.
The moment assumptions are the pth powers of the two stated Lp bounds. The
remaining scalar normalization identifies the resulting ENNReal sum with the
displayed `W_{p,r}^p` constant.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory
open Filter
open scoped ENNReal
open scoped Topology

noncomputable section

/-- The pth-power integral representing the pth power of the Lp quasi-norm
of a complex-valued function. -/
def complexLpMoment {X : Type*} [MeasurableSpace X]
    (p : ℝ) (μ : Measure X) (f : X → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, (ENNReal.ofReal ‖f x‖).rpow p ∂μ

/-- The jump control function `λ J_λ(F)^{1/2}` for a finite ordered family. -/
def jumpAmplitude {I X : Type*} [LinearOrder I] [MeasurableSpace X]
    (F : I → X → ℂ) (threshold : ℝ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal threshold *
    (separatedJumpCount (fun i => F i x) threshold).rpow (1 / 2 : ℝ)

/-- Measurability of the jump control function for a countable ordered
family of measurable functions. -/
theorem measurable_jumpAmplitude {I X : Type*} [LinearOrder I] [Countable I]
    [MeasurableSpace X] (F : I → X → ℂ) (threshold : ℝ)
    (hF : ∀ i, Measurable (F i)) :
    Measurable (jumpAmplitude F threshold) := by
  have hcount :
      Measurable (fun x => separatedJumpCount (fun i => F i x) threshold) :=
    measurable_separatedJumpCount F threshold hF
  have hroot : Measurable (fun x =>
      (separatedJumpCount (fun i => F i x) threshold).rpow (1 / 2 : ℝ)) :=
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).measurable.comp hcount
  have hscalar : Measurable (fun _ : X => ENNReal.ofReal threshold) := measurable_const
  change Measurable (fun x => ENNReal.ofReal threshold *
    (separatedJumpCount (fun i => F i x) threshold).rpow (1 / 2 : ℝ))
  exact hscalar.mul hroot

/-- ENNReal Chebyshev inequality for a strict superlevel set, written in the
pth-moment form used by the weak-variation proof. -/
private theorem measure_ge_le_rpow_moment_div
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℝ≥0∞) (hg : Measurable g) {p : ℝ} (hp : 0 < p)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    μ {x | ε ≤ g x} ≤ (∫⁻ x, (g x).rpow p ∂μ) / ε.rpow p := by
  have hgpow : Measurable (fun x => (g x).rpow p) :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp hg
  have hεpowPos : 0 < ε.rpow p :=
    ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hε) hp.le
  have hεpowTop : ε.rpow p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le hεtop
  calc
    μ {x | ε ≤ g x} ≤ μ {x | ε.rpow p ≤ (g x).rpow p} := by
      apply measure_mono
      intro x hx
      exact ENNReal.rpow_le_rpow hx hp.le
    _ ≤ (∫⁻ x, (g x).rpow p ∂μ) / ε.rpow p :=
      MeasureTheory.meas_ge_le_lintegral_div hgpow.aemeasurable
        hεpowPos.ne' hεpowTop

private theorem ennreal_ofReal_rpow_div
    {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hp : 0 ≤ p) :
    (ENNReal.ofReal x) ^ p / (ENNReal.ofReal y) ^ p =
      ENNReal.ofReal (Real.rpow x p) * (ENNReal.ofReal y) ^ (-p) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx hp, div_eq_mul_inv, ENNReal.rpow_neg]
  rfl

private theorem ennreal_ofReal_rpow_div_mul
    {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hp : 0 ≤ p)
    (M : ℝ≥0∞) :
    ((ENNReal.ofReal x) ^ p * M) / (ENNReal.ofReal y) ^ p =
      ENNReal.ofReal (Real.rpow x p) * (ENNReal.ofReal y) ^ (-p) * M := by
  have hfactor :
      ((ENNReal.ofReal x) ^ p * M) / (ENNReal.ofReal y) ^ p =
        ((ENNReal.ofReal x) ^ p / (ENNReal.ofReal y) ^ p) * M := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hfactor, ennreal_ofReal_rpow_div hx hy hp]

private theorem ennreal_ofReal_half_neg_rpow
    {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    (ENNReal.ofReal (t / 2)) ^ (-p) =
      ENNReal.ofReal (Real.rpow 2 p) * (ENNReal.ofReal t) ^ (-p) := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have htpowPos : 0 < (ENNReal.ofReal t) ^ p :=
    ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr ht) hp
  have htPowTop : (ENNReal.ofReal t) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
  have htwoPowTop : (ENNReal.ofReal 2) ^ p ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
  calc
    (ENNReal.ofReal (t / 2)) ^ (-p) =
        ((ENNReal.ofReal (t / 2)) ^ p)⁻¹ := by rw [ENNReal.rpow_neg]
    _ = ((ENNReal.ofReal t / ENNReal.ofReal 2) ^ p)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos htwo]
    _ = ((ENNReal.ofReal t) ^ p / (ENNReal.ofReal 2) ^ p)⁻¹ := by
      rw [ENNReal.div_rpow_of_nonneg _ _ hp]
    _ = (ENNReal.ofReal 2) ^ p / (ENNReal.ofReal t) ^ p :=
      ENNReal.inv_div (Or.inl htwoPowTop) (Or.inr htpowPos.ne')
    _ = ENNReal.ofReal (Real.rpow 2 p) * (ENNReal.ofReal t) ^ (-p) := by
      rw [ENNReal.ofReal_rpow_of_pos htwo, div_eq_mul_inv, ENNReal.rpow_neg]
      rfl

private theorem weakVariation_fixed_quotient_normalize
    {p t C : ℝ} (ht : 0 < t) (hp : 0 < p) (hC : 0 ≤ C)
    (M : ℝ≥0∞) :
    ((ENNReal.ofReal C) ^ p * M) / (ENNReal.ofReal (t / 2)) ^ p =
      ENNReal.ofReal (Real.rpow 2 p * Real.rpow C p) *
        (ENNReal.ofReal t) ^ (-p) * M := by
  have h2nonneg : 0 ≤ Real.rpow 2 p := Real.rpow_nonneg (by norm_num) _
  calc
    ((ENNReal.ofReal C) ^ p * M) / (ENNReal.ofReal (t / 2)) ^ p =
        ENNReal.ofReal (Real.rpow C p) *
          (ENNReal.ofReal (t / 2)) ^ (-p) * M :=
      ennreal_ofReal_rpow_div_mul hC (by linarith) hp.le M
    _ = (ENNReal.ofReal (Real.rpow C p) * ENNReal.ofReal (Real.rpow 2 p)) *
          (ENNReal.ofReal t) ^ (-p) * M := by
      rw [ennreal_ofReal_half_neg_rpow ht hp.le]
      ac_rfl
    _ = ENNReal.ofReal (Real.rpow 2 p * Real.rpow C p) *
          (ENNReal.ofReal t) ^ (-p) * M := by
      rw [mul_comm (ENNReal.ofReal (Real.rpow C p))
        (ENNReal.ofReal (Real.rpow 2 p))]
      rw [← ENNReal.ofReal_mul h2nonneg]

/-- A single separated jump of size greater than `λ` forces the jump
amplitude `λ J_λ^{1/2}` to be at least `λ`. -/
private theorem ofReal_le_of_largeSeparatedPair
    {I : Type*} [LinearOrder I] (u : I → ℂ) {threshold : ℝ}
    {s t : I} (hst : s < t) (hinc : threshold < ‖u t - u s‖) :
    ENNReal.ofReal threshold ≤
      ENNReal.ofReal threshold *
        (separatedJumpCount u threshold).rpow (1 / 2 : ℝ) := by
  let left : Fin 1 → I := fun _ => s
  let right : Fin 1 → I := fun _ => t
  have hfamily : SeparatedJumpFamily u threshold left right := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact hst
    · intro i j hij
      have hEq : i = j := Subsingleton.elim _ _
      subst j
      exact False.elim ((lt_irrefl i) hij)
    · intro i
      exact hinc
  have hcount : (1 : ℝ≥0∞) ≤ separatedJumpCount u threshold := by
    simpa using ofNat_le_separatedJumpCount_of_family u threshold left right hfamily
  have hroot :
      (1 : ℝ≥0∞) ≤ (separatedJumpCount u threshold).rpow (1 / 2 : ℝ) := by
    simpa using ENNReal.rpow_le_rpow hcount (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    ENNReal.ofReal threshold = ENNReal.ofReal threshold * 1 := by simp
    _ ≤ ENNReal.ofReal threshold *
          (separatedJumpCount u threshold).rpow (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot zero_le

/-- The maximum event is controlled by one fixed value and the jump event at
`t/2`, with the exact anchor decomposition in `lv:weak-variation`. -/
theorem maxNormEvent_subset_anchor_or_jump
    {I X : Type*} [LinearOrder I] [MeasurableSpace X]
    (F : I → X → ℂ) (anchor : I) {t : ℝ} (ht : 0 < t) :
    {x | ∃ i, t < ‖F i x‖} ⊆
      {x | t / 2 < ‖F anchor x‖} ∪
        {x | ENNReal.ofReal (t / 2) ≤ jumpAmplitude F (t / 2) x} := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  by_cases hanchor : t / 2 < ‖F anchor x‖
  · exact Or.inl hanchor
  · right
    have hdiff : t / 2 < ‖F i x - F anchor x‖ := by
      have hnorm := norm_sub_norm_le (F i x) (F anchor x)
      have hanchor' : ‖F anchor x‖ ≤ t / 2 := le_of_not_gt hanchor
      linarith
    have hne : i ≠ anchor := by
      intro heq
      subst i
      simp at hdiff
      linarith
    rcases lt_or_gt_of_ne hne with hia | hai
    · have hpair : t / 2 < ‖F anchor x - F i x‖ := by
        simpa [norm_sub_rev] using hdiff
      have hamp := ofReal_le_of_largeSeparatedPair
        (fun j => F j x) hia hpair
      simpa [jumpAmplitude] using hamp
    · have hamp := ofReal_le_of_largeSeparatedPair
        (fun j => F j x) hai hdiff
      simpa [jumpAmplitude] using hamp

/-- In one fixed increasing chain, any finite set of edges with increments
larger than `λ` is a separated jump family.  The order embedding enumerates
the selected edges in their original order, including adjacent edges whose
intervals meet at an endpoint. -/
theorem finiteChainLargeIncrementCard_le_separatedJumpCount
    {I : Type*} [LinearOrder I] {u : I → ℂ} {threshold : ℝ} {length : ℕ}
    (chain : StrictOrderedChain I length) (E : Finset (Fin length))
    (hE : ∀ i ∈ E,
      threshold < ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖) :
    (E.card : ℝ≥0∞) ≤ separatedJumpCount u threshold := by
  classical
  let e : Fin E.card ↪o Fin length := E.orderEmbOfFin rfl
  let s : Fin E.card → I := fun i => chain.point (e i).castSucc
  let t : Fin E.card → I := fun i => chain.point (e i).succ
  have hfamily : SeparatedJumpFamily u threshold s t := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact chain.strictMono (e i).castSucc_lt_succ
    · intro i j hij
      have he : e i < e j := e.strictMono hij
      exact chain.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr he)
    · intro i
      exact hE (e i) (Finset.orderEmbOfFin_mem E rfl i)
  exact ofNat_le_separatedJumpCount_of_family u threshold s t hfamily

/-- Real constants from the weak-variation estimate in `lv:weak-variation`.
The last definition is the exact coefficient called `W_{p,r}^p` in the
blueprint. -/
def weakVariationGamma (r : ℝ) : ℝ := (r - 2) / 2

def weakVariationD (r : ℝ) : ℝ :=
  Real.rpow 2 (-r / 2) * Real.sqrt (1 - Real.rpow 2 (-weakVariationGamma r))

/-- The scale `2^{-ell}` of the `ell`th dyadic increment bin. -/
def weakVariationDyadicScale (ell : ℕ) : ℝ := Real.rpow 2 (-(ell : ℝ))

/-- The exact count cutoff for the `ell`th dyadic bin in the proof of
`lv:weak-variation`: `2^{-r}(1-2^{-gamma})2^{(r-gamma)ell}`. -/
def weakVariationDyadicCountCutoff (r : ℝ) (ell : ℕ) : ℝ :=
  Real.rpow 2 (-r) * (1 - Real.rpow 2 (-weakVariationGamma r)) *
    Real.rpow 2 ((r - weakVariationGamma r) * (ell : ℝ))

private theorem weakVariationDyadicCountCutoff_pos
    {r : ℝ} (hr : 2 < r) (ell : ℕ) :
    0 < weakVariationDyadicCountCutoff r ell := by
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hrho : Real.rpow 2 (-weakVariationGamma r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold weakVariationDyadicCountCutoff
  exact mul_pos
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr hrho))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The jump-amplitude threshold corresponding to the exact count cutoff. -/
def weakVariationDyadicJumpThreshold (r t : ℝ) (ell : ℕ) : ℝ :=
  t * weakVariationDyadicScale ell *
    Real.sqrt (weakVariationDyadicCountCutoff r ell)

/-- A violation of the exact count cutoff forces the associated dyadic jump
amplitude to exceed `d_r t 2^{gamma ell/2}`. -/
theorem weakVariation_countViolation_implies_dyadicAmplitude
    {I X : Type*} [LinearOrder I] [MeasurableSpace X]
    (F : I → X → ℂ) {t r : ℝ} (ht : 0 < t) (hr : 2 < r)
    (ell : ℕ) (x : X)
    (hcount : ENNReal.ofReal (weakVariationDyadicCountCutoff r ell) <
      separatedJumpCount (fun i => F i x)
        (t * weakVariationDyadicScale ell)) :
    ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell) <
      jumpAmplitude F (t * weakVariationDyadicScale ell) x := by
  have hscalePos : 0 < t * weakVariationDyadicScale ell :=
    mul_pos ht (Real.rpow_pos_of_pos (by norm_num) _)
  have hcutoff := weakVariationDyadicCountCutoff_pos hr ell
  have hroot :
      (ENNReal.ofReal (weakVariationDyadicCountCutoff r ell)).rpow
          (1 / 2 : ℝ) <
        (separatedJumpCount (fun i => F i x)
          (t * weakVariationDyadicScale ell)).rpow (1 / 2 : ℝ) :=
    ENNReal.rpow_lt_rpow hcount (by norm_num)
  have hmul :
      ENNReal.ofReal (t * weakVariationDyadicScale ell) *
          (ENNReal.ofReal (weakVariationDyadicCountCutoff r ell)).rpow
            (1 / 2 : ℝ) <
        ENNReal.ofReal (t * weakVariationDyadicScale ell) *
          (separatedJumpCount (fun i => F i x)
            (t * weakVariationDyadicScale ell)).rpow (1 / 2 : ℝ) :=
    ENNReal.mul_lt_mul_right
      (ENNReal.ofReal_pos.mpr hscalePos).ne' ENNReal.ofReal_ne_top hroot
  have hrootEq :
      (ENNReal.ofReal (weakVariationDyadicCountCutoff r ell)).rpow
          (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (weakVariationDyadicCountCutoff r ell)) := by
    rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hcutoff,
      Real.sqrt_eq_rpow]
  have hmulEq :
      ENNReal.ofReal (t * weakVariationDyadicScale ell) *
          ENNReal.ofReal (Real.sqrt (weakVariationDyadicCountCutoff r ell)) =
        ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell) := by
    rw [← ENNReal.ofReal_mul (le_of_lt hscalePos)]
    rfl
  rw [hrootEq, hmulEq] at hmul
  simpa [jumpAmplitude] using hmul

/-- The square-root cutoff threshold is exactly the blueprint threshold
`d_r t 2^{gamma ell/2}`. -/
theorem weakVariation_dyadic_jump_threshold_eq
    {t r : ℝ} (hr : 2 < r) (ell : ℕ) :
    weakVariationDyadicJumpThreshold r t ell =
      weakVariationD r * t *
        Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2) := by
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hrho : Real.rpow 2 (-weakVariationGamma r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let a : ℝ := Real.rpow 2 (-r)
  let b : ℝ := 1 - Real.rpow 2 (-weakVariationGamma r)
  let c : ℝ := Real.rpow 2 ((r - weakVariationGamma r) * (ell : ℝ))
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 < b := sub_pos.mpr hrho
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hsqrta : Real.sqrt a = Real.rpow 2 (-r / 2) := by
    dsimp [a]
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) (-r) (1 / 2 : ℝ)]
    congr 1
    ring
  have hsqrtc : Real.sqrt c =
      Real.rpow 2 (((r - weakVariationGamma r) * (ell : ℝ)) / 2) := by
    dsimp [c]
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))
        ((r - weakVariationGamma r) * (ell : ℝ)) (1 / 2 : ℝ)]
    congr 1
    ring
  have hsqrttotal :
      Real.sqrt (weakVariationDyadicCountCutoff r ell) =
        Real.rpow 2 (-r / 2) * Real.sqrt b *
          Real.rpow 2 (((r - weakVariationGamma r) * (ell : ℝ)) / 2) := by
    unfold weakVariationDyadicCountCutoff
    change Real.sqrt (a * b * c) = _
    rw [Real.sqrt_mul (mul_nonneg ha.le hb.le), Real.sqrt_mul ha.le,
      hsqrta, hsqrtc]
  have hpow :
      Real.rpow 2 (-(ell : ℝ)) * Real.rpow 2 (-r / 2) *
        Real.rpow 2 (((r - weakVariationGamma r) * (ell : ℝ)) / 2) =
      Real.rpow 2 (-r / 2) *
        Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))
        (-(ell : ℝ)) (-r / 2),
      ← Real.rpow_add (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))
        (-(ell : ℝ) + -r / 2)
        (((r - weakVariationGamma r) * (ell : ℝ)) / 2),
      ← Real.rpow_add (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))
        (-r / 2) (weakVariationGamma r * (ell : ℝ) / 2)]
    congr 1
    dsimp [weakVariationGamma]
    ring
  unfold weakVariationDyadicJumpThreshold weakVariationDyadicScale weakVariationD
  rw [hsqrttotal]
  calc
    _ = t * Real.sqrt b *
          (Real.rpow 2 (-(ell : ℝ)) * Real.rpow 2 (-r / 2) *
            Real.rpow 2 (((r - weakVariationGamma r) * (ell : ℝ)) / 2)) := by ring
    _ = t * Real.sqrt b *
          (Real.rpow 2 (-r / 2) *
            Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) := by rw [hpow]
    _ = (Real.rpow 2 (-r / 2) * Real.sqrt b) * t *
          Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2) := by ring

private theorem weakVariationD_pos {r : ℝ} (hr : 2 < r) :
    0 < weakVariationD r := by
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hrho : Real.rpow 2 (-weakVariationGamma r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold weakVariationD
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.sqrt_pos_of_pos (sub_pos.mpr hrho))

private theorem weakVariation_dyadic_quotient_normalize
    {r t p A : ℝ} (hr : 2 < r) (ht : 0 < t) (hp : 0 < p)
    (hA : 0 ≤ A) (ell : ℕ) (M : ℝ≥0∞) :
    ((ENNReal.ofReal A) ^ p * M) /
        (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)) ^ p =
      ENNReal.ofReal
          (Real.rpow A p * Real.rpow (weakVariationD r) (-p) *
            (Real.rpow 2 (-weakVariationGamma r * p / 2)) ^ ell) *
        (ENNReal.ofReal t) ^ (-p) * M := by
  have hD : 0 < weakVariationD r := weakVariationD_pos hr
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hscale : 0 < Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hq : 0 ≤ Real.rpow 2 (-weakVariationGamma r * p / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hthreshold :
      weakVariationDyadicJumpThreshold r t ell =
        weakVariationD r * t * Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2) :=
    weakVariation_dyadic_jump_threshold_eq hr ell
  have hthresholdOfReal :
      ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell) =
        ENNReal.ofReal (weakVariationD r) * ENNReal.ofReal t *
          ENNReal.ofReal (Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) := by
    rw [hthreshold]
    calc
      ENNReal.ofReal
          (weakVariationD r * t * Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) =
          ENNReal.ofReal
            ((weakVariationD r * t) * Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) := by
              congr 1
      _ = ENNReal.ofReal (weakVariationD r * t) *
            ENNReal.ofReal (Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) :=
        ENNReal.ofReal_mul (mul_nonneg hD.le ht.le)
      _ = ENNReal.ofReal (weakVariationD r) * ENNReal.ofReal t *
            ENNReal.ofReal (Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) := by
        rw [ENNReal.ofReal_mul hD.le]
  have hdENN : ENNReal.ofReal (weakVariationD r) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hD).ne'
  have htENN : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  have hsENN :
      ENNReal.ofReal (Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hscale).ne'
  have hproductRpow :
      (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)) ^ (-p) =
        (ENNReal.ofReal (weakVariationD r)) ^ (-p) *
          (ENNReal.ofReal t) ^ (-p) *
            (ENNReal.ofReal (Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2))) ^ (-p) := by
    rw [hthresholdOfReal]
    rw [ENNReal.mul_rpow_of_ne_zero (mul_ne_zero hdENN htENN) hsENN]
    rw [ENNReal.mul_rpow_of_ne_zero hdENN htENN]
  have hsPower :
      (Real.rpow 2 (weakVariationGamma r * (ell : ℝ) / 2)) ^ (-p) =
        (Real.rpow 2 (-weakVariationGamma r * p / 2)) ^ ell := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (x := (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))
      (weakVariationGamma r * (ell : ℝ) / 2) (-p)]
    rw [show (weakVariationGamma r * (ell : ℝ) / 2) * (-p) =
      (-weakVariationGamma r * p / 2) * (ell : ℝ) by ring]
    rw [Real.rpow_mul_natCast (x := (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))
      (-weakVariationGamma r * p / 2) ell]
  calc
    ((ENNReal.ofReal A) ^ p * M) /
        (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)) ^ p =
      ENNReal.ofReal (Real.rpow A p) *
        (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)) ^ (-p) * M :=
      ennreal_ofReal_rpow_div_mul hA (by rw [hthreshold]; positivity) hp.le M
    _ = ENNReal.ofReal (Real.rpow A p) *
          (ENNReal.ofReal (weakVariationD r)) ^ (-p) *
          (ENNReal.ofReal t) ^ (-p) *
          (ENNReal.ofReal (Real.rpow 2
            (weakVariationGamma r * (ell : ℝ) / 2))) ^ (-p) * M := by
      rw [hproductRpow]
      ac_rfl
    _ = ENNReal.ofReal
          (Real.rpow A p * Real.rpow (weakVariationD r) (-p) *
            (Real.rpow 2 (-weakVariationGamma r * p / 2)) ^ ell) *
          (ENNReal.ofReal t) ^ (-p) * M := by
      rw [ENNReal.ofReal_rpow_of_pos hD,
        ENNReal.ofReal_rpow_of_pos hscale,
        hsPower]
      simp only [Real.rpow_eq_pow]
      calc
        _ = (ENNReal.ofReal (Real.rpow A p) *
              ENNReal.ofReal (Real.rpow (weakVariationD r) (-p)) *
              ENNReal.ofReal (Real.rpow 2 (-weakVariationGamma r * p / 2) ^ ell)) *
              (ENNReal.ofReal t) ^ (-p) * M := by
          simp only [Real.rpow_eq_pow]
          ac_rfl
        _ = (ENNReal.ofReal
              (Real.rpow A p * Real.rpow (weakVariationD r) (-p)) *
              ENNReal.ofReal (Real.rpow 2 (-weakVariationGamma r * p / 2) ^ ell)) *
              (ENNReal.ofReal t) ^ (-p) * M := by
          simp only [Real.rpow_eq_pow]
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA p)]
        _ = ENNReal.ofReal
              (Real.rpow A p * Real.rpow (weakVariationD r) (-p) *
                Real.rpow 2 (-weakVariationGamma r * p / 2) ^ ell) *
              (ENNReal.ofReal t) ^ (-p) * M := by
          simp only [Real.rpow_eq_pow]
          rw [← ENNReal.ofReal_mul
            (mul_nonneg (Real.rpow_nonneg hA p)
              (Real.rpow_nonneg hD.le (-p)))]

private theorem ennreal_ofReal_geometric_tsum
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρlt : ρ < 1) :
    (∑' ell : ℕ, ENNReal.ofReal (ρ ^ ell)) =
      ENNReal.ofReal ((1 - ρ)⁻¹) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun ell => pow_nonneg hρ ell)
    (summable_geometric_of_lt_one hρ hρlt), tsum_geometric_of_lt_one hρ hρlt]

private theorem weakVariation_dyadic_tsum_normalize
    {r t p A : ℝ} (hr : 2 < r) (ht : 0 < t) (hp : 0 < p)
    (hA : 0 ≤ A) (M : ℝ≥0∞) :
    (∑' ell : ℕ,
      ((ENNReal.ofReal A) ^ p * M) /
        (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)) ^ p) =
      ENNReal.ofReal
          (Real.rpow A p * Real.rpow (weakVariationD r) (-p) /
            (1 - Real.rpow 2 (-weakVariationGamma r * p / 2))) *
        (ENNReal.ofReal t) ^ (-p) * M := by
  have hD : 0 < weakVariationD r := weakVariationD_pos hr
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hρ : 0 ≤ Real.rpow 2 (-weakVariationGamma r * p / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hρlt : Real.rpow 2 (-weakVariationGamma r * p / 2) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : 0 < weakVariationGamma r * p / 2 := by positivity
    linarith
  have hdenom : 0 < 1 - Real.rpow 2 (-weakVariationGamma r * p / 2) :=
    sub_pos.mpr hρlt
  let C : ℝ := Real.rpow A p * Real.rpow (weakVariationD r) (-p)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.rpow_nonneg hA p) (Real.rpow_nonneg hD.le (-p))
  have hgeom := ennreal_ofReal_geometric_tsum hρ hρlt
  calc
    (∑' ell : ℕ,
      ((ENNReal.ofReal A) ^ p * M) /
        (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)) ^ p) =
      ∑' ell : ℕ,
        ENNReal.ofReal (C * (Real.rpow 2
          (-weakVariationGamma r * p / 2)) ^ ell) *
          (ENNReal.ofReal t) ^ (-p) * M := by
            apply tsum_congr
            intro ell
            simpa [C] using weakVariation_dyadic_quotient_normalize
              hr ht hp hA ell M
    _ = ∑' ell : ℕ,
          (ENNReal.ofReal C * (ENNReal.ofReal t) ^ (-p) * M) *
            ENNReal.ofReal ((Real.rpow 2
              (-weakVariationGamma r * p / 2)) ^ ell) := by
      apply tsum_congr
      intro ell
      rw [ENNReal.ofReal_mul hC]
      ac_rfl
    _ = (ENNReal.ofReal C * (ENNReal.ofReal t) ^ (-p) * M) *
          (∑' ell : ℕ,
            ENNReal.ofReal ((Real.rpow 2
              (-weakVariationGamma r * p / 2)) ^ ell)) := ENNReal.tsum_mul_left
    _ = (ENNReal.ofReal C * (ENNReal.ofReal t) ^ (-p) * M) *
          ENNReal.ofReal
            ((1 - Real.rpow 2 (-weakVariationGamma r * p / 2))⁻¹) := by
      rw [hgeom]
    _ = ENNReal.ofReal
          (Real.rpow A p * Real.rpow (weakVariationD r) (-p) /
            (1 - Real.rpow 2 (-weakVariationGamma r * p / 2))) *
          (ENNReal.ofReal t) ^ (-p) * M := by
      have hquot :
          ENNReal.ofReal C *
              ENNReal.ofReal
                ((1 - Real.rpow 2 (-weakVariationGamma r * p / 2))⁻¹) =
            ENNReal.ofReal
              (C / (1 - Real.rpow 2 (-weakVariationGamma r * p / 2))) := by
        rw [ENNReal.ofReal_inv_of_pos hdenom, ← div_eq_mul_inv,
          ← ENNReal.ofReal_div_of_pos hdenom]
      rw [show
        (ENNReal.ofReal C * (ENNReal.ofReal t) ^ (-p) * M) *
            ENNReal.ofReal
              ((1 - Real.rpow 2 (-weakVariationGamma r * p / 2))⁻¹) =
          (ENNReal.ofReal C *
            ENNReal.ofReal
              ((1 - Real.rpow 2 (-weakVariationGamma r * p / 2))⁻¹)) *
              (ENNReal.ofReal t) ^ (-p) * M by ac_rfl]
      rw [hquot]

/-- Multiplying the blueprint count cutoff by the `r`th power of the upper
endpoint `2t 2^{-ell}` gives the exact geometric-series contribution. -/
theorem weakVariation_dyadic_level_contribution
    {t r : ℝ} (ht : 0 < t) (ell : ℕ) :
    weakVariationDyadicCountCutoff r ell *
        (2 * t * weakVariationDyadicScale ell) ^ r =
      t ^ r * (1 - Real.rpow 2 (-weakVariationGamma r)) *
        (Real.rpow 2 (-weakVariationGamma r)) ^ ell := by
  have hupper :
      (2 * t * Real.rpow 2 (-(ell : ℝ))) ^ r =
        Real.rpow 2 r * t ^ r * Real.rpow 2 (-(ell : ℝ) * r) := by
    rw [show 2 * t * Real.rpow 2 (-(ell : ℝ)) =
        (2 * t) * Real.rpow 2 (-(ell : ℝ)) by ring]
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (x := 2 * t) (y := (2 : ℝ) ^ (-(ell : ℝ)))
      (by positivity) (by positivity)]
    rw [Real.mul_rpow (x := (2 : ℝ)) (y := t) (by norm_num) (le_of_lt ht)]
    rw [← Real.rpow_mul (x := (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))
      (-(ell : ℝ)) r]
  unfold weakVariationDyadicCountCutoff weakVariationDyadicScale
  rw [hupper]
  calc
    _ = t ^ r * (1 - Real.rpow 2 (-weakVariationGamma r)) *
          (Real.rpow 2 (-r) * Real.rpow 2 r *
            Real.rpow 2 ((r - weakVariationGamma r) * (ell : ℝ)) *
            Real.rpow 2 (-(ell : ℝ) * r)) := by ring
    _ = t ^ r * (1 - Real.rpow 2 (-weakVariationGamma r)) *
          Real.rpow 2
            (((r - weakVariationGamma r) * (ell : ℝ)) + (-(ell : ℝ) * r)) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ)) (-r) r,
        ← Real.rpow_add (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ)) (-r + r)
          ((r - weakVariationGamma r) * (ell : ℝ)),
        ← Real.rpow_add (x := (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))
          ((-r + r) + (r - weakVariationGamma r) * (ell : ℝ))
          (-(ell : ℝ) * r)]
      simp only [neg_add_cancel, zero_add]
    _ = t ^ r * (1 - Real.rpow 2 (-weakVariationGamma r)) *
          Real.rpow 2 ((-weakVariationGamma r) * (ell : ℝ)) := by
      rw [show ((r - weakVariationGamma r) * (ell : ℝ) +
          -(ell : ℝ) * r) = (-weakVariationGamma r) * (ell : ℝ) by ring]
    _ = t ^ r * (1 - Real.rpow 2 (-weakVariationGamma r)) *
          (Real.rpow 2 (-weakVariationGamma r)) ^ ell := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_mul_natCast (x := (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))
        (-weakVariationGamma r) ell]

/-- Every nonzero increment at most `2t` belongs to one of the blueprint's
dyadic bins `(t 2^{-ell}, 2t 2^{-ell}]`, `ell ≥ 0`. -/
theorem exists_weakVariation_dyadic_bin {t a : ℝ} (ht : 0 < t)
    (ha : 0 < a) (ha2 : a ≤ 2 * t) :
    ∃ ell : ℕ,
      t * weakVariationDyadicScale ell < a ∧
        a ≤ 2 * t * weakVariationDyadicScale ell := by
  have hscale_eq (ell : ℕ) :
      weakVariationDyadicScale ell = ((1 / 2 : ℝ) ^ ell) := by
    unfold weakVariationDyadicScale
    simp only [Real.rpow_eq_pow]
    rw [show -(ell : ℝ) = (-1) * (ell : ℝ) by ring,
      Real.rpow_mul_natCast (x := (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ)) (-1) ell,
      Real.rpow_neg_one]
    norm_num
  have hpowlim :
      Tendsto (fun ell : ℕ => ((1 / 2 : ℝ) ^ ell)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ ell : ℕ in atTop, ((1 / 2 : ℝ) ^ ell) < a / t :=
    hpowlim.eventually (Iio_mem_nhds (div_pos ha ht))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  have hscaleSmall : weakVariationDyadicScale N < a / t := by
    rw [hscale_eq]
    exact hN N le_rfl
  have hex : ∃ ell : ℕ, t * weakVariationDyadicScale ell < a :=
    ⟨N, by simpa [mul_comm] using (lt_div_iff₀ ht).mp hscaleSmall⟩
  cases hfind : Nat.find hex with
  | zero =>
      have hspec := Nat.find_spec hex
      rw [hfind] at hspec
      exact ⟨0, by simpa [weakVariationDyadicScale] using hspec,
        by simpa [weakVariationDyadicScale] using ha2⟩
  | succ n =>
      have hspec := Nat.find_spec hex
      have hlt : n < Nat.find hex := by
        rw [hfind]
        exact Nat.lt_succ_self n
      have hnnot : ¬ t * weakVariationDyadicScale n < a :=
        Nat.find_min hex hlt
      have hscale :
          2 * weakVariationDyadicScale (n + 1) = weakVariationDyadicScale n := by
        rw [hscale_eq, hscale_eq, pow_succ]
        ring
      have hupper : a ≤ 2 * t * weakVariationDyadicScale (n + 1) := by
        calc
          a ≤ t * weakVariationDyadicScale n := le_of_not_gt hnnot
          _ = t * (2 * weakVariationDyadicScale (n + 1)) := by rw [hscale]
          _ = 2 * t * weakVariationDyadicScale (n + 1) := by ring
      exact ⟨n + 1, by simpa [hfind] using hspec, hupper⟩

/-- Finite dyadic partition/sum lemma.  The set `E` consists of the nonzero
increments assigned to dyadic bins `(t 2^{-ell}, 2t 2^{-ell}]`.  If each bin
has at most the blueprint threshold
`2^{-r}(1-2^{-gamma})2^{(r-gamma)ell}` members, then the sum of the `r`th
powers of all increments in `E` is at most `t^r`. -/
theorem finiteDyadicPartition_sum_rpow_le
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (a : ι → ℝ)
    (level : ι → ℕ) {t r : ℝ} (ht : 0 < t) (hr : 2 < r)
    (ha : ∀ i ∈ E, 0 ≤ a i)
    (hbinLow : ∀ i ∈ E,
      t * weakVariationDyadicScale (level i) < a i)
    (hbinHigh : ∀ i ∈ E,
      a i ≤ 2 * t * weakVariationDyadicScale (level i))
    (hcount : ∀ ell : ℕ,
      ((E.filter (fun i => level i = ell)).card : ℝ) ≤
        weakVariationDyadicCountCutoff r ell) :
    ∑ i ∈ E, a i ^ r ≤ t ^ r := by
  classical
  let levels : Finset ℕ := E.image level
  have hmaps : ∀ i ∈ E, level i ∈ levels := by
    intro i hi
    exact Finset.mem_image_of_mem level hi
  have hparts :
      (∑ i ∈ E, a i ^ r) =
        ∑ ell ∈ levels, ∑ i ∈ E with level i = ell, a i ^ r := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun i => a i ^ r)
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  let ρ : ℝ := Real.rpow 2 (-weakVariationGamma r)
  have hρnonneg : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρlt : ρ < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeometric : Summable fun ell : ℕ => ρ ^ ell :=
    summable_geometric_of_lt_one hρnonneg hρlt
  have hgeometricBound :
      (∑ ell ∈ levels, ρ ^ ell) ≤ (1 - ρ)⁻¹ := by
    calc
      (∑ ell ∈ levels, ρ ^ ell) ≤ ∑' ell : ℕ, ρ ^ ell :=
        hgeometric.sum_le_tsum levels (by
          intro ell hell
          exact pow_nonneg hρnonneg ell)
      _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρnonneg hρlt
  have hfactor_nonneg : 0 ≤ t ^ r * (1 - ρ) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (sub_nonneg.mpr hρlt.le)
  calc
    ∑ i ∈ E, a i ^ r =
        ∑ ell ∈ levels, ∑ i ∈ E with level i = ell, a i ^ r := hparts
    _ ≤ ∑ ell ∈ levels,
          ((E.filter (fun i => level i = ell)).card : ℝ) *
            (2 * t * weakVariationDyadicScale ell) ^ r := by
      apply Finset.sum_le_sum
      intro ell hell
      calc
        (∑ i ∈ E with level i = ell, a i ^ r) ≤
            ∑ i ∈ E with level i = ell,
              (2 * t * weakVariationDyadicScale ell) ^ r := by
          apply Finset.sum_le_sum
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨hiE, hlevel⟩
          have hupper : a i ≤ 2 * t * weakVariationDyadicScale ell := by
            simpa [hlevel] using hbinHigh i hiE
          exact Real.rpow_le_rpow (ha i hiE) hupper (by linarith)
        _ = ((E.filter (fun i => level i = ell)).card : ℝ) *
              (2 * t * weakVariationDyadicScale ell) ^ r := by
          simp [mul_comm]
    _ ≤ ∑ ell ∈ levels,
          weakVariationDyadicCountCutoff r ell *
            (2 * t * weakVariationDyadicScale ell) ^ r := by
      apply Finset.sum_le_sum
      intro ell hell
      have hscale : 0 < weakVariationDyadicScale ell := by
        unfold weakVariationDyadicScale
        exact Real.rpow_pos_of_pos (by norm_num) _
      have hbase : 0 ≤ 2 * t * weakVariationDyadicScale ell := by
        positivity
      exact mul_le_mul_of_nonneg_right (hcount ell)
        (Real.rpow_nonneg hbase _)
    _ = ∑ ell ∈ levels, t ^ r * (1 - ρ) * ρ ^ ell := by
      apply Finset.sum_congr rfl
      intro ell hell
      simpa [ρ] using weakVariation_dyadic_level_contribution ht ell
    _ = t ^ r * (1 - ρ) * ∑ ell ∈ levels, ρ ^ ell := by
      rw [← Finset.mul_sum]
    _ ≤ t ^ r * (1 - ρ) * (1 - ρ)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeometricBound hfactor_nonneg
    _ = t ^ r := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hρlt)), mul_one]

/-- Outside the maximum event, every edge of a finite chain has size at most
`2t`; if all dyadic jump counts are below their exact cutoffs, the raw
`r`-moment of the chain increments is at most `t^r`. -/
theorem finiteChain_rpow_sum_le_of_dyadic_jump_count_cutoffs
    {I : Type*} [LinearOrder I] {u : I → ℂ} {length : ℕ}
    (chain : StrictOrderedChain I length) {t r : ℝ} (ht : 0 < t) (hr : 2 < r)
    (hmax : ∀ i : Fin length,
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ≤ 2 * t)
    (hjump : ∀ ell : ℕ,
      separatedJumpCount u (t * weakVariationDyadicScale ell) ≤
        ENNReal.ofReal (weakVariationDyadicCountCutoff r ell)) :
    ∑ i : Fin length,
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r ≤ t ^ r := by
  classical
  let a : Fin length → ℝ := fun i =>
    ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖
  let E : Finset (Fin length) := Finset.univ.filter (fun i => 0 < a i)
  have ha : ∀ i, 0 ≤ a i := fun i => norm_nonneg _
  have hsumFilterNot :
      (∑ i : Fin length, a i ^ r) = ∑ i ∈ E, a i ^ r := by
    have hzero :
        (∑ i ∈ Finset.univ.filter (fun i : Fin length => ¬ 0 < a i), a i ^ r) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hnot : ¬ 0 < a i := (Finset.mem_filter.mp hi).2
      have hzeroi : a i = 0 := le_antisymm (not_lt.mp hnot) (ha i)
      simp [hzeroi, Real.zero_rpow (by linarith : r ≠ 0)]
    have hzero' :
        (∑ i ∈ Finset.univ.filter (fun i : Fin length => a i ≤ 0), a i ^ r) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hnonpos : a i ≤ 0 := (Finset.mem_filter.mp hi).2
      have hzeroi : a i = 0 := le_antisymm hnonpos (ha i)
      simp [hzeroi, Real.zero_rpow (by linarith : r ≠ 0)]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin length))) (p := fun i => 0 < a i)]
    simp [E, hzero, hzero']
  have hbinExists : ∀ i, i ∈ E →
      ∃ ell : ℕ,
        t * weakVariationDyadicScale ell < a i ∧
          a i ≤ 2 * t * weakVariationDyadicScale ell := by
    intro i hi
    exact exists_weakVariation_dyadic_bin ht ((Finset.mem_filter.mp hi).2)
      (by simpa [a] using hmax i)
  let level : Fin length → ℕ := fun i =>
    if hi : i ∈ E then Classical.choose (hbinExists i hi) else 0
  have hbin : ∀ i ∈ E,
      t * weakVariationDyadicScale (level i) < a i ∧
        a i ≤ 2 * t * weakVariationDyadicScale (level i) := by
    intro i hi
    dsimp [level]
    rw [dif_pos hi]
    exact Classical.choose_spec (hbinExists i hi)
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hrhoLt : Real.rpow 2 (-weakVariationGamma r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hcutoffNonneg (ell : ℕ) :
      0 ≤ weakVariationDyadicCountCutoff r ell := by
    unfold weakVariationDyadicCountCutoff
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (sub_nonneg.mpr hrhoLt.le))
      (Real.rpow_nonneg (by norm_num) _)
  have hcount : ∀ ell : ℕ,
      ((E.filter (fun i => level i = ell)).card : ℝ) ≤
        weakVariationDyadicCountCutoff r ell := by
    intro ell
    let Eell : Finset (Fin length) := E.filter (fun i => level i = ell)
    have hlarge : ∀ i ∈ Eell,
        t * weakVariationDyadicScale ell <
          ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiE, hlevel⟩
      have := (hbin i hiE).1
      simpa [a, hlevel] using this
    have hcard := finiteChainLargeIncrementCard_le_separatedJumpCount
      chain Eell hlarge
    have hcardBound := hcard.trans (hjump ell)
    have hcardReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcardBound
    simpa [Eell, ENNReal.toReal_ofReal (hcutoffNonneg ell)] using hcardReal
  have hsum := finiteDyadicPartition_sum_rpow_le E a level ht hr
    (fun i hi => ha i) (fun i hi => (hbin i hi).1)
    (fun i hi => (hbin i hi).2) hcount
  calc
    ∑ i : Fin length,
        ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r =
        ∑ i : Fin length, a i ^ r := by rfl
    _ = ∑ i ∈ E, a i ^ r := hsumFilterNot
    _ ≤ t ^ r := hsum

/-- Convert a finite real `r`-moment bound on chain increments to the
corresponding ENNReal homogeneous chain variation bound. -/
private theorem finiteChainVariation_le_of_rpow_sum_le
    {I : Type*} [LinearOrder I] (u : I → ℂ) {length : ℕ}
    (chain : StrictOrderedChain I length) {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hsum : ∑ i : Fin length,
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r ≤ t ^ r) :
    finiteChainVariation r u chain ≤ ENNReal.ofReal t := by
  have hsumENN :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.point i.succ) -
          u (chain.point i.castSucc)‖).rpow r) =
        ENNReal.ofReal (∑ i : Fin length,
          ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r) := by
    calc
      _ = ∑ i : Fin length,
          ENNReal.ofReal (‖u (chain.point i.succ) -
            u (chain.point i.castSucc)‖ ^ r) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_nonneg
            (norm_nonneg _) hr.le]
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Real.rpow_nonneg (norm_nonneg _) _)).symm
  have hsumENN_le :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.point i.succ) -
          u (chain.point i.castSucc)‖).rpow r) ≤
        (ENNReal.ofReal t).rpow r := by
    calc
      _ = ENNReal.ofReal (∑ i : Fin length,
          ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ r) := hsumENN
      _ ≤ ENNReal.ofReal (t ^ r) := ENNReal.ofReal_le_ofReal hsum
      _ = (ENNReal.ofReal t).rpow r :=
        (ENNReal.ofReal_rpow_of_pos ht).symm
  have hpow := ENNReal.rpow_le_rpow hsumENN_le
    (one_div_nonneg.mpr hr.le)
  simpa [finiteChainVariation, ENNReal.rpow_rpow_inv hr.ne'] using hpow

/-- If the pointwise maximum is at most `t` and every dyadic jump count is
below its cutoff, then the full ordered `r`-variation is at most `t`. -/
theorem orderedRVariation_le_of_max_and_dyadic_counts
    {I : Type*} [LinearOrder I] (u : I → ℂ) {t r : ℝ}
    (ht : 0 < t) (hr : 2 < r)
    (hmax : ∀ i, ‖u i‖ ≤ t)
    (hjump : ∀ ell : ℕ,
      separatedJumpCount u (t * weakVariationDyadicScale ell) ≤
        ENNReal.ofReal (weakVariationDyadicCountCutoff r ell)) :
    orderedRVariation r u ≤ ENNReal.ofReal t := by
  unfold orderedRVariation
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  have hinc : ∀ i : Fin length,
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ≤ 2 * t := by
    intro i
    calc
      _ ≤ ‖u (chain.point i.succ)‖ +
            ‖u (chain.point i.castSucc)‖ := norm_sub_le _ _
      _ ≤ t + t := add_le_add (hmax _) (hmax _)
      _ = 2 * t := by ring
  have hsum := finiteChain_rpow_sum_le_of_dyadic_jump_count_cutoffs
    chain ht hr hinc hjump
  exact finiteChainVariation_le_of_rpow_sum_le u chain ht
    (by linarith) hsum

/-- The variation superlevel event is contained in the maximum event or in
one of the dyadic count-violation events.  This is the deterministic
max-event elimination and dyadic decomposition in `lv:weak-variation`. -/
theorem weakVariationLevelSet_subset_max_or_dyadicCount
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (F : I → X → ℂ) {t r : ℝ} (ht : 0 < t) (hr : 2 < r) :
    {x | ENNReal.ofReal t < orderedRVariationFun r F x} ⊆
      {x | ∃ i, t < ‖F i x‖} ∪
        ⋃ ell : ℕ,
          {x | ENNReal.ofReal (weakVariationDyadicCountCutoff r ell) <
            separatedJumpCount (fun i => F i x)
              (t * weakVariationDyadicScale ell)} := by
  intro x hx
  change ENNReal.ofReal t <
    orderedRVariation r (fun i => F i x) at hx
  by_cases hmax : ∃ i, t < ‖F i x‖
  · exact Or.inl hmax
  · right
    by_contra hnot
    have hnorm : ∀ i, ‖F i x‖ ≤ t := by
      intro i
      exact le_of_not_gt (fun hi => hmax ⟨i, hi⟩)
    have hjump : ∀ ell : ℕ,
        separatedJumpCount (fun i => F i x)
            (t * weakVariationDyadicScale ell) ≤
          ENNReal.ofReal (weakVariationDyadicCountCutoff r ell) := by
      intro ell
      apply le_of_not_gt
      intro hcount
      exact hnot (Set.mem_iUnion.mpr ⟨ell, hcount⟩)
    have hvariation := orderedRVariation_le_of_max_and_dyadic_counts
      (fun i => F i x) ht hr hnorm hjump
    exact (not_lt_of_ge hvariation) hx

/-- The dyadic count-violation alternative can be written directly as a
strict superlevel set of the jump-amplitude function. -/
theorem weakVariationLevelSet_subset_max_or_dyadicAmplitude
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (F : I → X → ℂ) {t r : ℝ} (ht : 0 < t) (hr : 2 < r) :
    {x | ENNReal.ofReal t < orderedRVariationFun r F x} ⊆
      {x | ∃ i, t < ‖F i x‖} ∪
        ⋃ ell : ℕ,
          {x | ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell) <
            jumpAmplitude F (t * weakVariationDyadicScale ell) x} := by
  intro x hx
  rcases weakVariationLevelSet_subset_max_or_dyadicCount F ht hr hx with
    hmax | hcount
  · exact Or.inl hmax
  · right
    rcases Set.mem_iUnion.mp hcount with ⟨ell, hcount⟩
    exact Set.mem_iUnion.mpr ⟨ell,
      weakVariation_countViolation_implies_dyadicAmplitude F ht hr ell x hcount⟩

/-- Chebyshev assembly for the weak-variation level set.  The denominators
are kept in exact ENNReal `rpow` form here; the separate scalar identity
reduces them to the displayed `W_{p,r}^p t^{-p}` coefficient. -/
theorem weakVariationLevelSet_measure_le_chebyshev
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) {p r A B : ℝ} (F : I → X → ℂ) (f : X → ℂ)
    (hp : 0 < p) (hr : 2 < r) (anchor : I)
    (hF : ∀ i, Measurable (F i))
    (hfixed : ∀ i, complexLpMoment p μ (F i) ≤
      (ENNReal.ofReal B).rpow p * complexLpMoment p μ f)
    (hjump : ∀ threshold : ℝ, 0 < threshold →
      ∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ ≤
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f)
    {t : ℝ} (ht : 0 < t) :
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
      ((ENNReal.ofReal B).rpow p * complexLpMoment p μ f /
          (ENNReal.ofReal (t / 2)).rpow p +
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f /
          (ENNReal.ofReal (t / 2)).rpow p) +
        ∑' ell : ℕ,
          ((ENNReal.ofReal A).rpow p * complexLpMoment p μ f /
            (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)).rpow p) := by
  classical
  let maxEvent : Set X := {x | ∃ i, t < ‖F i x‖}
  let anchorEvent : Set X := {x | t / 2 < ‖F anchor x‖}
  let anchorJumpEvent : Set X :=
    {x | ENNReal.ofReal (t / 2) ≤ jumpAmplitude F (t / 2) x}
  let dyadicEvent (ell : ℕ) : Set X :=
    {x | ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell) <
      jumpAmplitude F (t * weakVariationDyadicScale ell) x}
  let anchorEpsilon : ℝ≥0∞ := ENNReal.ofReal (t / 2)
  have hhalf : 0 < t / 2 := by linarith
  have hanchorEpsilon : anchorEpsilon ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hhalf).ne'
  have hanchorEpsilonTop : anchorEpsilon ≠ ∞ := ENNReal.ofReal_ne_top
  have hanchorNormMeas : Measurable (fun x => ENNReal.ofReal ‖F anchor x‖) :=
    Measurable.ennreal_ofReal (hF anchor).norm
  have hanchorJumpMeas : Measurable (jumpAmplitude F (t / 2)) :=
    measurable_jumpAmplitude F (t / 2) hF
  have hanchorNormCheb := measure_ge_le_rpow_moment_div μ
    (fun x => ENNReal.ofReal ‖F anchor x‖) hanchorNormMeas hp
    hanchorEpsilon hanchorEpsilonTop
  have hanchorJumpCheb := measure_ge_le_rpow_moment_div μ
    (jumpAmplitude F (t / 2)) hanchorJumpMeas hp
    hanchorEpsilon hanchorEpsilonTop
  have hanchorNormSet : anchorEvent ⊆
      {x | anchorEpsilon ≤ ENNReal.ofReal ‖F anchor x‖} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal hx.le
  have hanchorMeasure :
      μ anchorEvent ≤
        ((ENNReal.ofReal B).rpow p * complexLpMoment p μ f) /
          (ENNReal.ofReal (t / 2)).rpow p := by
    calc
      μ anchorEvent ≤ μ {x | anchorEpsilon ≤ ENNReal.ofReal ‖F anchor x‖} :=
        measure_mono hanchorNormSet
      _ ≤ complexLpMoment p μ (F anchor) / anchorEpsilon.rpow p := by
        simpa [complexLpMoment, anchorEpsilon] using hanchorNormCheb
      _ ≤ ((ENNReal.ofReal B).rpow p * complexLpMoment p μ f) /
            (ENNReal.ofReal (t / 2)).rpow p :=
        ENNReal.div_le_div_right (hfixed anchor) _
  have hanchorJumpMeasure :
      μ anchorJumpEvent ≤
        ((ENNReal.ofReal A).rpow p * complexLpMoment p μ f) /
          (ENNReal.ofReal (t / 2)).rpow p := by
    calc
      μ anchorJumpEvent ≤
          (∫⁻ x, (jumpAmplitude F (t / 2) x).rpow p ∂μ) /
            anchorEpsilon.rpow p := by
        simpa [anchorJumpEvent, anchorEpsilon] using hanchorJumpCheb
      _ ≤ ((ENNReal.ofReal A).rpow p * complexLpMoment p μ f) /
            (ENNReal.ofReal (t / 2)).rpow p := by
        simpa [anchorEpsilon] using ENNReal.div_le_div_right
          (hjump (t / 2) hhalf) (anchorEpsilon.rpow p)
  have hmaxMeasure :
      μ maxEvent ≤ μ anchorEvent + μ anchorJumpEvent := by
    calc
      μ maxEvent ≤ μ (anchorEvent ∪ anchorJumpEvent) :=
        measure_mono (maxNormEvent_subset_anchor_or_jump F anchor ht)
      _ ≤ μ anchorEvent + μ anchorJumpEvent := measure_union_le _ _
  have hdyadicMeasure (ell : ℕ) :
      μ (dyadicEvent ell) ≤
        ((ENNReal.ofReal A).rpow p * complexLpMoment p μ f) /
          (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)).rpow p := by
    have hscalePos : 0 < t * weakVariationDyadicScale ell :=
      mul_pos ht (Real.rpow_pos_of_pos (by norm_num) _)
    have htheta : 0 < weakVariationDyadicJumpThreshold r t ell := by
      unfold weakVariationDyadicJumpThreshold
      exact mul_pos (mul_pos ht (Real.rpow_pos_of_pos (by norm_num) _))
        (Real.sqrt_pos_of_pos (weakVariationDyadicCountCutoff_pos hr ell))
    let epsilon : ℝ≥0∞ :=
      ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)
    have hepsilon : epsilon ≠ 0 := (ENNReal.ofReal_pos.mpr htheta).ne'
    have hepsilonTop : epsilon ≠ ∞ := ENNReal.ofReal_ne_top
    have hmeas := measurable_jumpAmplitude F
      (t * weakVariationDyadicScale ell) hF
    have hcheb := measure_ge_le_rpow_moment_div μ
      (jumpAmplitude F (t * weakVariationDyadicScale ell)) hmeas hp
      hepsilon hepsilonTop
    have hsubset : dyadicEvent ell ⊆
        {x | epsilon ≤ jumpAmplitude F (t * weakVariationDyadicScale ell) x} := by
      intro x hx
      exact le_of_lt (by simpa [dyadicEvent, epsilon] using hx)
    calc
      μ (dyadicEvent ell) ≤
          μ {x | epsilon ≤ jumpAmplitude F (t * weakVariationDyadicScale ell) x} :=
        measure_mono hsubset
      _ ≤ (∫⁻ x,
            (jumpAmplitude F (t * weakVariationDyadicScale ell) x).rpow p ∂μ) /
              epsilon.rpow p := hcheb
      _ ≤ ((ENNReal.ofReal A).rpow p * complexLpMoment p μ f) /
            (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)).rpow p := by
        simpa [epsilon] using ENNReal.div_le_div_right
          (hjump (t * weakVariationDyadicScale ell) hscalePos) (epsilon.rpow p)
  have hlevelSubset := weakVariationLevelSet_subset_max_or_dyadicAmplitude
    F ht hr
  have hsetBound :
      μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
        μ maxEvent + ∑' ell : ℕ, μ (dyadicEvent ell) := by
    calc
      μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
          μ (maxEvent ∪ ⋃ ell : ℕ, dyadicEvent ell) :=
        measure_mono hlevelSubset
      _ ≤ μ maxEvent + μ (⋃ ell : ℕ, dyadicEvent ell) := measure_union_le _ _
      _ ≤ μ maxEvent + ∑' ell : ℕ, μ (dyadicEvent ell) :=
        add_le_add_right (measure_iUnion_le dyadicEvent) _
  calc
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
        μ maxEvent + ∑' ell : ℕ, μ (dyadicEvent ell) := hsetBound
    _ ≤ (μ anchorEvent + μ anchorJumpEvent) +
          ∑' ell : ℕ, μ (dyadicEvent ell) :=
      add_le_add_left hmaxMeasure _
    _ ≤ _ := by
      apply add_le_add
      · exact add_le_add hanchorMeasure hanchorJumpMeasure
      · exact ENNReal.tsum_le_tsum hdyadicMeasure

def weakVariationConstantPow (p r A B : ℝ) : ℝ :=
  Real.rpow 2 p * (Real.rpow B p + Real.rpow A p) +
    Real.rpow (weakVariationD r) (-p) * Real.rpow A p /
      (1 - Real.rpow 2 (-weakVariationGamma r * p / 2))

/-- Scalar normalization of the Chebyshev assembly to the exact
`W_{p,r}^p` coefficient in `lv:weak-variation`. -/
theorem weakVariationLevelSet_measure_le_constantPow
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) {p r A B : ℝ} (F : I → X → ℂ) (f : X → ℂ)
    (hp : 0 < p) (hr : 2 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (anchor : I)
    (hF : ∀ i, Measurable (F i))
    (hfixed : ∀ i, complexLpMoment p μ (F i) ≤
      (ENNReal.ofReal B).rpow p * complexLpMoment p μ f)
    (hjump : ∀ threshold : ℝ, 0 < threshold →
      ∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ ≤
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f)
    {t : ℝ} (ht : 0 < t) :
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
      ENNReal.ofReal (weakVariationConstantPow p r A B) *
        (ENNReal.ofReal t).rpow (-p) * complexLpMoment p μ f := by
  let ρ : ℝ := Real.rpow 2 (-weakVariationGamma r * p / 2)
  let Cb : ℝ := Real.rpow 2 p * Real.rpow B p
  let Ca : ℝ := Real.rpow 2 p * Real.rpow A p
  let Cd : ℝ := Real.rpow A p * Real.rpow (weakVariationD r) (-p) /
    (1 - ρ)
  have hgamma : 0 < weakVariationGamma r := by
    dsimp [weakVariationGamma]
    linarith
  have hρnonneg : 0 ≤ ρ := by
    dsimp [ρ]
    exact Real.rpow_nonneg (by norm_num) _
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have hneg : -weakVariationGamma r * p / 2 < 0 := by
      rw [div_lt_iff₀ (by norm_num : 0 < (2 : ℝ))]
      have hprod : 0 < weakVariationGamma r * p := mul_pos hgamma hp
      linarith
    exact hneg
  have hdenom : 0 < 1 - ρ := sub_pos.mpr hρlt
  have hCb : 0 ≤ Cb := by
    dsimp [Cb]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) p)
      (Real.rpow_nonneg hB p)
  have hCa : 0 ≤ Ca := by
    dsimp [Ca]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) p)
      (Real.rpow_nonneg hA p)
  have hCd : 0 ≤ Cd := by
    dsimp [Cd]
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg hA p)
        (Real.rpow_nonneg (weakVariationD_pos hr).le (-p))) hdenom.le
  have hcoeff : Cb + Ca + Cd = weakVariationConstantPow p r A B := by
    dsimp [Cb, Ca, Cd, ρ, weakVariationConstantPow]
    ring
  have hcoeff_nonneg : 0 ≤ weakVariationConstantPow p r A B := by
    rw [← hcoeff]
    exact add_nonneg (add_nonneg hCb hCa) hCd
  have hfixedB := weakVariation_fixed_quotient_normalize ht hp hB
    (complexLpMoment p μ f)
  have hfixedA := weakVariation_fixed_quotient_normalize ht hp hA
    (complexLpMoment p μ f)
  have hdyadic := weakVariation_dyadic_tsum_normalize hr ht hp hA
    (complexLpMoment p μ f)
  have hcheb := weakVariationLevelSet_measure_le_chebyshev μ F f hp hr anchor
    hF hfixed hjump ht
  let K : ℝ≥0∞ := (ENNReal.ofReal t) ^ (-p) * complexLpMoment p μ f
  have hsumNormalize :
      (((ENNReal.ofReal Cb * K) + (ENNReal.ofReal Ca * K)) +
          ENNReal.ofReal Cd * K) = ENNReal.ofReal (Cb + Ca + Cd) * K := by
    calc
      _ = ((ENNReal.ofReal Cb + ENNReal.ofReal Ca) + ENNReal.ofReal Cd) * K := by
        rw [← add_mul, ← add_mul]
      _ = ENNReal.ofReal (Cb + Ca + Cd) * K := by
        rw [← ENNReal.ofReal_add hCb hCa,
          ← ENNReal.ofReal_add (add_nonneg hCb hCa) hCd]
  calc
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
        (((ENNReal.ofReal B).rpow p * complexLpMoment p μ f) /
            (ENNReal.ofReal (t / 2)).rpow p +
          (ENNReal.ofReal A).rpow p * complexLpMoment p μ f /
            (ENNReal.ofReal (t / 2)).rpow p) +
          ∑' ell : ℕ,
            ((ENNReal.ofReal A).rpow p * complexLpMoment p μ f) /
              (ENNReal.ofReal (weakVariationDyadicJumpThreshold r t ell)).rpow p := hcheb
    _ = ((ENNReal.ofReal Cb * K) + (ENNReal.ofReal Ca * K)) +
          ENNReal.ofReal Cd * K := by
      simp only [ENNReal.rpow_eq_pow]
      rw [hfixedB, hfixedA, hdyadic]
      dsimp [Cb, Ca, Cd, ρ, K]
      ac_rfl
    _ = ENNReal.ofReal (weakVariationConstantPow p r A B) * K := by
      rw [hsumNormalize, hcoeff]
    _ = ENNReal.ofReal (weakVariationConstantPow p r A B) *
          (ENNReal.ofReal t).rpow (-p) * complexLpMoment p μ f := by
      dsimp [K]
      ac_rfl

/-- Statement of the blueprint weak-variation estimate in pth-moment form.
For `p > 0`, `complexLpMoment` is precisely the pth power of the Lp
quasi-norm; similarly, the jump moment is the pth power of the stated jump
quasi-norm. -/
def weakVariationOfJumpStatement {I X : Type*} [LinearOrder I] [Fintype I]
    [MeasurableSpace X] (μ : Measure X) (p r A B : ℝ)
    (F : I → X → ℂ) (f : X → ℂ)
    (hp : 0 < p) (hr : 2 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ i, Measurable (F i)) (hf : Measurable f)
    (hfixed : ∀ i, complexLpMoment p μ (F i) ≤
      (ENNReal.ofReal B).rpow p * complexLpMoment p μ f)
    (hjump : ∀ threshold : ℝ, 0 < threshold →
      ∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ ≤
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f) : Prop :=
  ∀ t : ℝ, 0 < t →
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
      ENNReal.ofReal (weakVariationConstantPow p r A B) *
        (ENNReal.ofReal t).rpow (-p) * complexLpMoment p μ f

/-- Weak variation from the fixed-time and jump bounds, with the exact
`W_{p,r}^p` coefficient from the blueprint. -/
theorem weakVariationOfJump {I X : Type*} [LinearOrder I] [Fintype I]
    [MeasurableSpace X] (μ : Measure X) (p r A B : ℝ)
    (F : I → X → ℂ) (f : X → ℂ)
    (hp : 0 < p) (hr : 2 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ i, Measurable (F i)) (hf : Measurable f)
    (hfixed : ∀ i, complexLpMoment p μ (F i) ≤
      (ENNReal.ofReal B).rpow p * complexLpMoment p μ f)
    (hjump : ∀ threshold : ℝ, 0 < threshold →
      ∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ ≤
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f) :
    weakVariationOfJumpStatement μ p r A B F f hp hr hA hB hF hf hfixed hjump := by
  classical
  intro t ht
  by_cases hI : Nonempty I
  · exact weakVariationLevelSet_measure_le_constantPow μ F f hp hr hA hB
      (Classical.choice hI) hF hfixed hjump ht
  · have hvariation : ∀ x,
        orderedRVariation r (fun i => F i x) = 0 := by
      intro x
      unfold orderedRVariation
      apply le_antisymm
      · apply iSup_le
        intro length
        apply iSup_le
        intro chain
        exact (hI ⟨chain.point 0⟩).elim
      · exact zero_le
    have hzeroSet :
        {x | ENNReal.ofReal t < orderedRVariationFun r F x} = ∅ := by
      have hε : 0 < ENNReal.ofReal t := ENNReal.ofReal_pos.mpr ht
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      simpa [orderedRVariationFun, hvariation x] using
        (not_lt_of_ge hε.le : ¬ ENNReal.ofReal t < (0 : ℝ≥0∞))
    simpa [hzeroSet] using
      (zero_le (ENNReal.ofReal (weakVariationConstantPow p r A B) *
        (ENNReal.ofReal t).rpow (-p) * complexLpMoment p μ f))

end

end FractionalPrimes.Literature.Variation
