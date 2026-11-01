module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import FractionalPrimes.Literature.Uniformity.StretchedExponentialAbsorption
public import FractionalPrimes.Literature.Uniformity.LogAbsorption

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LongArithmetic

open FractionalPrimes.Literature.Uniformity

/-- The first scale clause in (L1) of `lal:long-of-unit`: every fixed
polylogarithmic modulus lies strictly below the stretched-exponential
Cramér cutoff once the logarithmic scale is large enough. -/
theorem longPolylog_lt_stretchedExp_eventually (B : ℝ) (hB : 0 < B) :
    ∀ᶠ t : ℝ in Filter.atTop,
      t ^ B < Real.exp (t ^ (1 / 10 : ℝ)) := by
  have hc : 0 < (1 / (2 * B) : ℝ) := by positivity
  have hsmall :=
    (isLittleO_log_rpow_atTop
      (by norm_num : 0 < (1 / 10 : ℝ))).def hc
  filter_upwards [hsmall, Filter.eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have htpos : 0 < t := by linarith
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hpow : 0 < t ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos htpos _
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hpow.le] at ht
  have hbound : B * Real.log t ≤ (1 / 2 : ℝ) * t ^ (1 / 10 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left ht hB.le
    have hfactor : B * (1 / (2 * B) : ℝ) = 1 / 2 := by
      field_simp [hB.ne']
    simpa only [← mul_assoc, hfactor] using hmul
  have hstrict : B * Real.log t < t ^ (1 / 10 : ℝ) := by
    nlinarith
  rw [Real.rpow_def_of_pos htpos B]
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- The second scale clause in (L1): the stretched-exponential cutoff lies
below the auxiliary divisor level `X^(1/16)` at large logarithmic scale. -/
theorem longStretchedExponent_le_sixteenth_eventually :
    ∀ᶠ t : ℝ in Filter.atTop,
      t ^ (1 / 10 : ℝ) ≤ t / 16 := by
  have hlarge :=
    (tendsto_rpow_atTop (by norm_num : 0 < (9 / 10 : ℝ))).eventually
      (Filter.eventually_ge_atTop (16 : ℝ))
  filter_upwards [hlarge, Filter.eventually_gt_atTop (1 : ℝ)] with t hpow9 ht1
  have htpos : 0 < t := by linarith
  have hpow1 : 0 ≤ t ^ (1 / 10 : ℝ) := (Real.rpow_pos_of_pos htpos _).le
  have hproduct : t ^ (1 / 10 : ℝ) * t ^ (9 / 10 : ℝ) = t := by
    rw [← Real.rpow_add htpos]
    norm_num
  have hbound := mul_le_mul_of_nonneg_left hpow9 hpow1
  nlinarith

/-- A single finite threshold supplies both Cramér cutoff clauses in (L1),
in the exact order needed by `longCramerResidueCutoff_of_threshold`. -/
theorem longCramerCutoffThreshold (B : ℝ) (hB : 0 < B) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      t ^ B < Real.exp (t ^ (1 / 10 : ℝ)) ∧
      t ^ (1 / 10 : ℝ) ≤ t / 16 := by
  have hfirst := longPolylog_lt_stretchedExp_eventually B hB
  have hsecond := longStretchedExponent_le_sixteenth_eventually
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1
    (hfirst.and hsecond |>.and (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨t₀, (ht₀ t₀ le_rfl).2, ?_⟩
  intro t ht
  exact (ht₀ t ht).1

/-- The first Cramér-mean error clause in (L1), with its exact coefficient
and exponent. A one-power stronger application of the checked absorption
lemma makes the coefficient removable above a finite threshold. -/
theorem longFirstCramerErrorThreshold (A D : ℝ) (hA : 0 < A)
    (hD : 0 ≤ D) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      D * Real.exp (-(t ^ (9 / 10 : ℝ)) / 16) ≤ t ^ (-A) := by
  let E : ℝ := A + 1
  let C : ℝ := (10 * E / (9 * Real.exp 1 * (1 / 16 : ℝ))) ^ (10 * E / 9)
  have hE : 0 < E := by dsimp [E]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨max 1 (D * C), le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := by linarith
  have hDC : D * C ≤ t := (le_max_right _ _).trans ht
  have habs := stretchedExponentialAbsorption E (1 / 16) t
    hE (by norm_num) htpos
  have hterm :
      D * Real.exp (-(t ^ (9 / 10 : ℝ)) / 16) ≤ D * C * t ^ (-E) := by
    have hmul := mul_le_mul_of_nonneg_left habs hD
    have harg : -(t ^ (9 / 10 : ℝ)) / 16 =
        -(1 / 16 * t ^ (9 / 10 : ℝ)) := by ring
    rw [harg]
    calc
      _ ≤ D * ((10 * E / (9 * Real.exp 1 * (1 / 16 : ℝ))) ^
          (10 * E / 9) * t ^ (-E)) := hmul
      _ = D * C * t ^ (-E) := by dsimp [C]; ring
  calc
    D * Real.exp (-(t ^ (9 / 10 : ℝ)) / 16) ≤
        D * C * t ^ (-E) := hterm
    _ ≤ t * t ^ (-E) :=
      mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg htpos.le _)
    _ = t ^ (-A) := by
      conv_lhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add htpos]
      congr 1
      dsimp [E]
      ring

/-- The last Cramér-mean error clause in (L1), derived with the exact
coefficient `exp 13` from the checked logarithmic absorption theorem. -/
theorem longSecondCramerErrorThreshold (A R : ℝ)
    (hA : 0 < A) (hR : 0 < R) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      Real.exp 13 * t ^ (R + 2 / 5 : ℝ) *
        Real.exp (-15 * t / 16) ≤ t ^ (-A) := by
  let a : ℝ := 15 / 16
  let b : ℝ := A + R + 2 / 5
  let K : ℝ := Real.exp 13
  let T : ℝ := (2 / a) * Real.log (K * logAbsorptionM a b)
  have ha : 0 < a := by dsimp [a]; norm_num
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [Real.add_one_le_exp (13 : ℝ)]
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := by linarith
  have hT : T ≤ t := (le_max_right _ _).trans ht
  have hX : 1 ≤ Real.exp t := by
    have := Real.add_one_le_exp t
    linarith
  have hlarge : (2 / a) * Real.log (K * logAbsorptionM a b) ≤
      Real.log (Real.exp t) := by
    simpa [T] using hT
  have habs := log_absorption_bound ha hb hK hX hlarge
  have hexp : (Real.exp t) ^ a = Real.exp (15 * t / 16) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
    congr 1
    dsimp [a]
    ring
  have hmain : K * t ^ b ≤ Real.exp (15 * t / 16) := by
    simpa only [Real.log_exp, hexp] using habs
  have hpow : t ^ b = t ^ A * t ^ (R + 2 / 5 : ℝ) := by
    rw [← Real.rpow_add htpos]
    congr 1
    dsimp [b]
    ring
  have hcancel : t ^ A * t ^ (-A) = 1 := by
    rw [← Real.rpow_add htpos]
    simp
  have hfactorNonneg :
      0 ≤ Real.exp (-15 * t / 16) * t ^ (-A) :=
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg htpos.le _)
  have hmul := mul_le_mul_of_nonneg_right hmain hfactorNonneg
  calc
    Real.exp 13 * t ^ (R + 2 / 5 : ℝ) *
        Real.exp (-15 * t / 16) =
      (K * t ^ b) *
        (Real.exp (-15 * t / 16) * t ^ (-A)) := by
          rw [hpow]
          dsimp [K]
          calc
            _ = Real.exp 13 * (t ^ A * t ^ (-A)) *
                t ^ (R + 2 / 5 : ℝ) * Real.exp (-15 * t / 16) := by
                  rw [hcancel]
                  ring
            _ = _ := by ring
    _ ≤ Real.exp (15 * t / 16) *
        (Real.exp (-15 * t / 16) * t ^ (-A)) := hmul
    _ = t ^ (-A) := by
      rw [← mul_assoc, ← Real.exp_add]
      have : 15 * t / 16 + -15 * t / 16 = 0 := by ring
      rw [this, Real.exp_zero, one_mul]

/-- One threshold simultaneously supplies the four exact (L1) clauses
consumed by the coprime `Λ-Cr_X` adapter. The separate nonunit and small-scale
clauses of `lal:long-of-unit` are deliberately left to their own lemmas. -/
theorem longCoprimeCramerL1Threshold (A B R D : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hD : 0 ≤ D) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      t ^ B < Real.exp (t ^ (1 / 10 : ℝ)) ∧
      t ^ (1 / 10 : ℝ) ≤ t / 16 ∧
      D * Real.exp (-(t ^ (9 / 10 : ℝ)) / 16) ≤ t ^ (-A) ∧
      Real.exp 13 * t ^ (R + 2 / 5 : ℝ) *
        Real.exp (-15 * t / 16) ≤ t ^ (-A) := by
  obtain ⟨tCut, htCut2, hCut⟩ := longCramerCutoffThreshold B hB
  obtain ⟨tFirst, _, hFirst⟩ := longFirstCramerErrorThreshold A D hA hD
  obtain ⟨tSecond, _, hSecond⟩ := longSecondCramerErrorThreshold A R hA hR
  refine ⟨max tCut (max tFirst tSecond),
    htCut2.trans (le_max_left _ _), ?_⟩
  intro t ht
  have hCutT : tCut ≤ t := (le_max_left _ _).trans ht
  have hFirstT : tFirst ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hSecondT : tSecond ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  exact ⟨(hCut t hCutT).1, (hCut t hCutT).2,
    hFirst t hFirstT, hSecond t hSecondT⟩

/-- The logarithmic and constant-scale clauses in (L1) needed for the
nonunit Möbius gcd reduction. -/
theorem longNonunitMobiusElementaryThreshold (B : ℝ) (hB : 0 < B) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      B * Real.log t ≤ t / 2 ∧
      max (Real.log 3) (2 ^ B) ≤ t / 2 := by
  have hc : 0 < (1 / (2 * B) : ℝ) := by positivity
  have hsmall :=
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 : ℝ))).def hc
  have hlarge : ∀ᶠ t : ℝ in Filter.atTop,
      B * Real.log t ≤ t / 2 ∧
      max (Real.log 3) (2 ^ B) ≤ t / 2 := by
    filter_upwards [hsmall, Filter.eventually_ge_atTop (2 : ℝ),
      Filter.eventually_ge_atTop
        (2 * max (Real.log 3) (2 ^ B))] with t ht ht2 htMax
    have htpos : 0 < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg hlog, Real.rpow_one,
      Real.norm_of_nonneg htpos.le] at ht
    have hfactor : B * (1 / (2 * B) : ℝ) = 1 / 2 := by
      field_simp [hB.ne']
    have hbound := mul_le_mul_of_nonneg_left ht hB.le
    constructor
    · calc
        B * Real.log t ≤ B * ((1 / (2 * B) : ℝ) * t) := hbound
        _ = t / 2 := by rw [← mul_assoc, hfactor]; ring
    · linarith
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1
    (hlarge.and (Filter.eventually_ge_atTop (2 : ℝ)))
  exact ⟨t₀, (ht₀ t₀ le_rfl).2, fun t ht => (ht₀ t ht).1⟩

/-- The remaining mixed logarithmic factor in (L1). It is bounded by
`K t²`, then the checked logarithmic absorption estimate supplies the
exponential gain with the exact target exponent `-A-R`. -/
theorem longNonunitLambdaMixedThreshold (A B R : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      (B * Real.log t / Real.log 2) * (t + Real.log 2) ≤
        Real.exp t * t ^ (-A - R) := by
  let b : ℝ := A + R + 2
  let K : ℝ := max 1 (2 * B / Real.log 2)
  let T : ℝ := 2 * Real.log (K * logAbsorptionM 1 b)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 1 ≤ K := le_max_left _ _
  have hKcoeff : 2 * B / Real.log 2 ≤ K := le_max_right _ _
  refine ⟨max 2 T, le_max_left _ _, ?_⟩
  intro t ht
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := by linarith
  have hT : T ≤ t := (le_max_right _ _).trans ht
  have hX : 1 ≤ Real.exp t := by
    linarith [Real.add_one_le_exp t]
  have hlarge : (2 / (1 : ℝ)) *
      Real.log (K * logAbsorptionM 1 b) ≤
        Real.log (Real.exp t) := by
    have hdiv : (2 / (1 : ℝ)) = 2 := by norm_num
    rw [hdiv, Real.log_exp]
    exact hT
  have habs := log_absorption_bound
    (a := (1 : ℝ)) (b := b) (K := K) (X := Real.exp t)
    (by norm_num) hb hK hX hlarge
  have hexp : (Real.exp t) ^ (1 : ℝ) = Real.exp t := by simp
  have hmain : K * t ^ b ≤ Real.exp t := by
    simpa only [Real.log_exp, hexp] using habs
  have hlogt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos htpos
    linarith
  have hlog2le : Real.log 2 ≤ t := by
    have hlog2one := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfirst : B * Real.log t / Real.log 2 ≤ B * t / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    exact mul_le_mul_of_nonneg_left hlogt hB.le
  have hsecond : t + Real.log 2 ≤ 2 * t := by linarith
  have hleftNonneg : 0 ≤ B * Real.log t / Real.log 2 := by
    apply div_nonneg (mul_nonneg hB.le ?_) hlog2.le
    exact Real.log_nonneg (by linarith)
  have hrightNonneg : 0 ≤ B * t / Real.log 2 := by positivity
  have hpoly :
      (B * Real.log t / Real.log 2) * (t + Real.log 2) ≤
        K * t ^ (2 : ℕ) := by
    calc
      _ ≤ (B * t / Real.log 2) * (t + Real.log 2) :=
        mul_le_mul_of_nonneg_right hfirst (by positivity)
      _ ≤ (B * t / Real.log 2) * (2 * t) :=
        mul_le_mul_of_nonneg_left hsecond hrightNonneg
      _ = (2 * B / Real.log 2) * t ^ (2 : ℕ) := by ring
      _ ≤ K * t ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hKcoeff (by positivity)
  have hpow : t ^ b = t ^ (2 : ℕ) * t ^ (A + R) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add htpos]
    congr 1
    dsimp [b]
    ring
  have hcancel : t ^ (A + R) * t ^ (-(A + R)) = 1 := by
    rw [← Real.rpow_add htpos]
    simp
  have hscaled : K * t ^ (2 : ℕ) ≤
      Real.exp t * t ^ (-A - R) := by
    have hmul := mul_le_mul_of_nonneg_right hmain
      (Real.rpow_nonneg htpos.le (-(A + R)))
    have hexponent : -A - R = -(A + R) := by ring
    rw [hexponent]
    calc
      K * t ^ (2 : ℕ) = (K * t ^ b) * t ^ (-(A + R)) := by
        rw [hpow]
        calc
          _ = K * t ^ (2 : ℕ) *
              (t ^ (A + R) * t ^ (-(A + R))) := by
                rw [hcancel, mul_one]
          _ = _ := by ring
      _ ≤ Real.exp t * t ^ (-(A + R)) := hmul
  exact hpoly.trans hscaled

/-- One source-faithful finite threshold for all eight displayed clauses
of (L1) in blueprint `lal:long-of-unit`, including `t ≥ 2`. -/
theorem longOfUnitL1Threshold (A B R D : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hD : 0 ≤ D) :
    ∃ t₀ : ℝ, 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      t ^ B < Real.exp (t ^ (1 / 10 : ℝ)) ∧
      t ^ (1 / 10 : ℝ) ≤ t / 16 ∧
      B * Real.log t ≤ t / 2 ∧
      max (Real.log 3) (2 ^ B) ≤ t / 2 ∧
      (B * Real.log t / Real.log 2) * (t + Real.log 2) ≤
        Real.exp t * t ^ (-A - R) ∧
      D * Real.exp (-(t ^ (9 / 10 : ℝ)) / 16) ≤ t ^ (-A) ∧
      Real.exp 13 * t ^ (R + 2 / 5 : ℝ) *
        Real.exp (-15 * t / 16) ≤ t ^ (-A) := by
  obtain ⟨tCr, htCr2, hCr⟩ :=
    longCoprimeCramerL1Threshold A B R D hA hB hR hD
  obtain ⟨tMu, _, hMu⟩ := longNonunitMobiusElementaryThreshold B hB
  obtain ⟨tLam, _, hLam⟩ := longNonunitLambdaMixedThreshold A B R hA hB hR
  refine ⟨max tCr (max tMu tLam), htCr2.trans (le_max_left _ _), ?_⟩
  intro t ht
  have hCrT : tCr ≤ t := (le_max_left _ _).trans ht
  have hMuT : tMu ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hLamT : tLam ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  obtain ⟨h1, h2, h6, h7⟩ := hCr t hCrT
  obtain ⟨h3, h4⟩ := hMu t hMuT
  exact ⟨h1, h2, h3, h4, hLam t hLamT, h6, h7⟩

/-- The exact modulus-exponent shift in the nonunit Möbius part of
`lal:long-of-unit`: `t^B ≤ (t/2)^(B+1)` once `t/2 ≥ 2^B`. -/
theorem longNonunitModulusShift {t q B : ℝ} (ht : 0 < t)
    (hq : q ≤ t ^ B) (hhalf : 2 ^ B ≤ t / 2) :
    q ≤ (t / 2) ^ (B + 1) := by
  have hhalfpos : 0 < t / 2 := by positivity
  have hdecomp : t ^ B = (t / 2) ^ B * 2 ^ B := by
    conv_lhs => rw [show t = (t / 2) * 2 by ring]
    rw [Real.mul_rpow hhalfpos.le (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (t / 2) ^ (B + 1) = (t / 2) ^ B * (t / 2) := by
    rw [Real.rpow_add hhalfpos]
    simp
  calc
    q ≤ t ^ B := hq
    _ = (t / 2) ^ B * 2 ^ B := hdecomp
    _ ≤ (t / 2) ^ B * (t / 2) :=
      mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hhalfpos.le _)
    _ = (t / 2) ^ (B + 1) := hpow.symm

/-- The endpoint quotient has at least half the original logarithm.
This is the exact logarithmic hypothesis for the nonunit Möbius interval
adapter, valid at both `Y=X` and `Y=X+L`. -/
theorem longNonunitQuotientHalfLog {X Y g q B : ℝ}
    (hX : 0 < X) (hY : X ≤ Y) (hg : 1 ≤ g)
    (hgq : g ≤ q) (hq : q ≤ (Real.log X) ^ B)
    (ht : 0 < Real.log X)
    (hBlog : B * Real.log (Real.log X) ≤ Real.log X / 2) :
    Real.log X / 2 ≤ Real.log (Y / g) := by
  have hgpos : 0 < g := by linarith
  have hqpos : 0 < q := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hX hY
  have hloggq : Real.log g ≤ Real.log q :=
    Real.log_le_log hgpos hgq
  have hlogqt : Real.log q ≤ Real.log ((Real.log X) ^ B) :=
    Real.log_le_log hqpos hq
  have hlogtpow : Real.log ((Real.log X) ^ B) =
      B * Real.log (Real.log X) := by
    rw [Real.log_rpow ht]
  have hlogXY : Real.log X ≤ Real.log Y := Real.log_le_log hX hY
  rw [Real.log_div hYpos.ne' hgpos.ne']
  linarith

/-- All three nonunit endpoint hypotheses for the checked Möbius interval
adapter, from precisely the modulus and two (L1) scale clauses. -/
theorem longNonunitEndpointRange {X Y g q B : ℝ}
    (hX : 0 < X) (hY : X ≤ Y) (hg : 1 ≤ g)
    (hgq : g ≤ q) (hq : q ≤ (Real.log X) ^ B)
    (hB : 0 < B) (ht : 0 < Real.log X)
    (hBlog : B * Real.log (Real.log X) ≤ Real.log X / 2)
    (hhalf : max (Real.log 3) (2 ^ B) ≤ Real.log X / 2) :
    3 ≤ Y / g ∧
      q ≤ (Real.log (Y / g)) ^ (B + 1) ∧
      Real.log X / 2 ≤ Real.log (Y / g) := by
  have hgpos : 0 < g := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hX hY
  have hYgpos : 0 < Y / g := div_pos hYpos hgpos
  have hloghalf := longNonunitQuotientHalfLog
    hX hY hg hgq hq ht hBlog
  have hlog3 : Real.log 3 ≤ Real.log (Y / g) :=
    (le_max_left _ _).trans hhalf |>.trans hloghalf
  have hYg3 : (3 : ℝ) ≤ Y / g := by
    have hexp := Real.exp_le_exp.mpr hlog3
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3),
      Real.exp_log hYgpos] using hexp
  have htwo : (2 : ℝ) ^ B ≤ Real.log X / 2 :=
    (le_max_right _ _).trans hhalf
  have hshift : q ≤ (Real.log X / 2) ^ (B + 1) :=
    longNonunitModulusShift ht hq htwo
  have hpower : (Real.log X / 2) ^ (B + 1) ≤
      (Real.log (Y / g)) ^ (B + 1) :=
    Real.rpow_le_rpow (by positivity) hloghalf (by linarith)
  exact ⟨hYg3, hshift.trans hpower, hloghalf⟩

/-- The exact numerical absorption after `lal:nonunit-lambda`: the
nonunit interval factor is at most the LONG target once the mixed (L1)
clause holds. -/
theorem longNonunitLambdaAbsorption {X L q A B R : ℝ}
    (hX : 3 ≤ X) (hL : 0 ≤ L) (hLX : L ≤ X)
    (hXL : X * (Real.log X) ^ (-R) ≤ L)
    (hq : 1 ≤ q) (hqX : q ≤ (Real.log X) ^ B)
    (hmixed :
      (B * Real.log (Real.log X) / Real.log 2) *
          (Real.log X + Real.log 2) ≤
        Real.exp (Real.log X) * (Real.log X) ^ (-A - R)) :
    (Real.log q / Real.log 2) * Real.log (X + L) ≤
      L * (Real.log X) ^ (-A) := by
  have hXpos : 0 < X := by linarith
  have hqpos : 0 < q := by linarith
  have htpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hYpos : 0 < X + L := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log q ≤ B * Real.log (Real.log X) := by
    calc
      Real.log q ≤ Real.log ((Real.log X) ^ B) :=
        Real.log_le_log hqpos hqX
      _ = B * Real.log (Real.log X) := by rw [Real.log_rpow htpos]
  have hlogq2 : Real.log q / Real.log 2 ≤
      B * Real.log (Real.log X) / Real.log 2 :=
    div_le_div_of_nonneg_right hlogq hlog2.le
  have hleftNonneg : 0 ≤ B * Real.log (Real.log X) / Real.log 2 := by
    exact (div_nonneg (Real.log_nonneg hq) hlog2.le).trans hlogq2
  have hYle : X + L ≤ 2 * X := by linarith
  have hlogY : Real.log (X + L) ≤ Real.log X + Real.log 2 := by
    calc
      Real.log (X + L) ≤ Real.log (2 * X) :=
        Real.log_le_log hYpos hYle
      _ = Real.log X + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
        ring
  have hlogYnonneg : 0 ≤ Real.log (X + L) :=
    Real.log_nonneg (by linarith)
  have hpow : (Real.log X) ^ (-A - R) =
      (Real.log X) ^ (-R) * (Real.log X) ^ (-A) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  calc
    (Real.log q / Real.log 2) * Real.log (X + L) ≤
      (B * Real.log (Real.log X) / Real.log 2) *
        Real.log (X + L) :=
      mul_le_mul_of_nonneg_right hlogq2 hlogYnonneg
    _ ≤ (B * Real.log (Real.log X) / Real.log 2) *
        (Real.log X + Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogY hleftNonneg
    _ ≤ Real.exp (Real.log X) * (Real.log X) ^ (-A - R) := hmixed
    _ = (X * (Real.log X) ^ (-R)) * (Real.log X) ^ (-A) := by
      rw [Real.exp_log hXpos, hpow]
      ring
    _ ≤ L * (Real.log X) ^ (-A) :=
      mul_le_mul_of_nonneg_right hXL (Real.rpow_nonneg htpos.le _)

#print axioms FractionalPrimes.Literature.LongArithmetic.longPolylog_lt_stretchedExp_eventually
#print axioms FractionalPrimes.Literature.LongArithmetic.longStretchedExponent_le_sixteenth_eventually
#print axioms FractionalPrimes.Literature.LongArithmetic.longCramerCutoffThreshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longFirstCramerErrorThreshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longSecondCramerErrorThreshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longCoprimeCramerL1Threshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitMobiusElementaryThreshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitLambdaMixedThreshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longOfUnitL1Threshold
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitModulusShift
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitQuotientHalfLog
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitEndpointRange
#print axioms FractionalPrimes.Literature.LongArithmetic.longNonunitLambdaAbsorption

end FractionalPrimes.Literature.LongArithmetic

end
