module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearSmallFactor
public import FractionalPrimes.Literature.Polynomial.ShortIntervalDirichletMeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The large-factor dyadic-cell estimate in the proof of `ldm:trilinear`.

This module keeps the exact factor-and-square level estimates as explicit
inputs while the separate `ldm:power-levels` proof is being completed.

Blueprint: `expanded-blueprint.tex:5930-5973`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-mean-closure.tex:260-299`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletMean

open MeasureTheory

noncomputable section

private lemma mul_min_sq_div (t p q : ℝ) (ht : t ≠ 0)
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (t * min p q) ^ 2 / t = t * min (p ^ 2) (q ^ 2) := by
  by_cases hpq : p ≤ q
  · have hpqSq : p ^ 2 ≤ q ^ 2 := by
      have hnonneg : 0 ≤ q + p := add_nonneg hq hp
      have := mul_nonneg (sub_nonneg.mpr hpq) hnonneg
      nlinarith
    rw [min_eq_left hpq, min_eq_left hpqSq]
    field_simp [ht] <;> ring
  · have hqp : q ≤ p := le_of_not_ge hpq
    have hqpSq : q ^ 2 ≤ p ^ 2 := by
      have hnonneg : 0 ≤ p + q := add_nonneg hp hq
      have := mul_nonneg (sub_nonneg.mpr hqp) hnonneg
      nlinarith
    rw [min_eq_right hqp, min_eq_right hqpSq]
    field_simp [ht] <;> ring

private lemma rpow_nat_pow (X e : ℝ) (hX : 0 ≤ X) (n : ℕ) :
    (X ^ e) ^ n = X ^ ((n : ℝ) * e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  congr 1
  ring

private lemma dyadic_factor_alternative
    (X T N V m R kL eps t v w r : ℝ)
    (hX : 1 < X) (hT : 0 < T) (hN : 0 < N) (hV : 0 < V)
    (hkL : 0 < kL)
    (hRdef : R = m / (2 * kL))
    (hNpow : N = X ^ v) (hVpow : V = X ^ w) (hRpow : R = X ^ r)
    (ht : t = 3 / 8 - eps) (hTpow : T ≤ X ^ t)
    (hlevelOne : m ≤ kL *
      (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)))
    (hlevelTwo : m ≤ kL *
      (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12))) :
    factorAlternative eps r v w := by
  let A := N / V ^ 2
  let B := T * min (1 / V ^ 2) (N / V ^ 6)
  have hApos : 0 < A := by dsimp [A]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hA2 : N ^ 2 / V ^ 4 = A ^ 2 := by
    dsimp [A]
    field_simp [hV.ne'] <;> ring
  have hB2 : B ^ 2 / T = T * min (1 / V ^ 4) (N ^ 2 / V ^ 12) := by
    dsimp [B]
    rw [mul_min_sq_div T (1 / V ^ 2) (N / V ^ 6) hT.ne'
      (by positivity) (by positivity)]
    have hp : (1 / V ^ 2) ^ 2 = 1 / V ^ 4 := by field_simp [hV.ne'] <;> ring
    have hq : (N / V ^ 6) ^ 2 = N ^ 2 / V ^ 12 := by
      field_simp [hV.ne'] <;> ring
    rw [hp, hq]
  have hRmaxOne : R ≤ max A B := by
    have hdiv : m / (2 * kL) ≤ kL * (A + B) / (2 * kL) := by
      simpa [A, B] using div_le_div_of_nonneg_right hlevelOne
        (show 0 ≤ 2 * kL by positivity)
    have hnorm : kL * (A + B) / (2 * kL) = (A + B) / 2 := by
      field_simp [ne_of_gt hkL] <;> ring
    have havg : (A + B) / 2 ≤ max A B := by
      have := le_max_left A B
      have := le_max_right A B
      linarith
    calc
      R = m / (2 * kL) := hRdef
      _ ≤ (A + B) / 2 := hdiv.trans_eq hnorm
      _ ≤ max A B := havg
  have hRmaxTwo : R ≤ max (A ^ 2) (B ^ 2 / T) := by
    have hdiv : m / (2 * kL) ≤ kL * (A ^ 2 + B ^ 2 / T) / (2 * kL) := by
      simpa [hA2, hB2] using div_le_div_of_nonneg_right hlevelTwo
        (show 0 ≤ 2 * kL by positivity)
    have hnorm : kL * (A ^ 2 + B ^ 2 / T) / (2 * kL) =
        (A ^ 2 + B ^ 2 / T) / 2 := by
      field_simp [ne_of_gt hkL] <;> ring
    have havg : (A ^ 2 + B ^ 2 / T) / 2 ≤ max (A ^ 2) (B ^ 2 / T) := by
      have := le_max_left (A ^ 2) (B ^ 2 / T)
      have := le_max_right (A ^ 2) (B ^ 2 / T)
      linarith
    calc
      R = m / (2 * kL) := hRdef
      _ ≤ (A ^ 2 + B ^ 2 / T) / 2 := hdiv.trans_eq hnorm
      _ ≤ max (A ^ 2) (B ^ 2 / T) := havg
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hAexp : A = X ^ (v - 2 * w) := by
    dsimp [A]
    have hV2 : V ^ 2 = X ^ (2 * w) := by
      rw [hVpow, rpow_nat_pow X w hXpos.le 2]
      congr 1 <;> ring
    rw [hNpow, hV2, ← Real.rpow_sub hXpos]
  have hBexp : B = T * min (X ^ (-2 * w)) (X ^ (v - 6 * w)) := by
    dsimp [B]
    have hV2 : V ^ 2 = X ^ (2 * w) := by
      rw [hVpow, rpow_nat_pow X w hXpos.le 2]
      congr 1 <;> ring
    have hV6 : V ^ 6 = X ^ (6 * w) := by
      rw [hVpow, rpow_nat_pow X w hXpos.le 6]
      congr 1 <;> ring
    have hrecip : 1 / V ^ 2 = X ^ (-2 * w) := by
      rw [hV2]
      calc
        1 / X ^ (2 * w) = (X ^ (2 * w))⁻¹ := by
          rw [div_eq_mul_inv]
          ring
        _ = X ^ (-(2 * w)) := (Real.rpow_neg hXpos.le (2 * w)).symm
        _ = X ^ (-2 * w) := by
          exact congrArg (fun e : ℝ => X ^ e) (by ring)
    have hquot : N / V ^ 6 = X ^ (v - 6 * w) := by
      rw [hNpow, hV6, ← Real.rpow_sub hXpos]
    rw [hrecip, hquot]
  have hB2exp : B ^ 2 / T =
      T * min (X ^ (-4 * w)) (X ^ (2 * v - 12 * w)) := by
    rw [hBexp]
    rw [mul_min_sq_div T (X ^ (-2 * w)) (X ^ (v - 6 * w)) hT.ne'
      (Real.rpow_nonneg hXpos.le _) (Real.rpow_nonneg hXpos.le _)]
    rw [rpow_nat_pow X (-2 * w) hXpos.le 2,
      rpow_nat_pow X (v - 6 * w) hXpos.le 2]
    have hfirst : X ^ ((2 : ℝ) * (-2 * w)) = X ^ (-4 * w) :=
      congrArg (fun e : ℝ => X ^ e) (by ring)
    have hsecond : X ^ ((2 : ℝ) * (v - 6 * w)) = X ^ (2 * v - 12 * w) :=
      congrArg (fun e : ℝ => X ^ e) (by ring)
    change T * min (X ^ ((2 : ℝ) * (-2 * w)))
      (X ^ ((2 : ℝ) * (v - 6 * w))) = _
    rw [hfirst, hsecond]
  have hBboundOne : B ≤ X ^ (t - 2 * w) := by
    rw [hBexp]
    calc
      T * min (X ^ (-2 * w)) (X ^ (v - 6 * w)) ≤
          T * X ^ (-2 * w) := mul_le_mul_of_nonneg_left (min_le_left _ _) hT.le
      _ ≤ X ^ t * X ^ (-2 * w) := mul_le_mul_of_nonneg_right hTpow
        (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (t - 2 * w) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hBboundTwo : B ≤ X ^ (t + v - 6 * w) := by
    rw [hBexp]
    calc
      T * min (X ^ (-2 * w)) (X ^ (v - 6 * w)) ≤
          T * X ^ (v - 6 * w) := mul_le_mul_of_nonneg_left (min_le_right _ _) hT.le
      _ ≤ X ^ t * X ^ (v - 6 * w) := mul_le_mul_of_nonneg_right hTpow
        (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (t + v - 6 * w) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hBpowBoundOne : B ^ 2 / T ≤ X ^ (t - 4 * w) := by
    rw [hB2exp]
    calc
      T * min (X ^ (-4 * w)) (X ^ (2 * v - 12 * w)) ≤
          T * X ^ (-4 * w) := mul_le_mul_of_nonneg_left (min_le_left _ _) hT.le
      _ ≤ X ^ t * X ^ (-4 * w) := mul_le_mul_of_nonneg_right hTpow
        (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (t - 4 * w) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hBpowBoundTwo : B ^ 2 / T ≤ X ^ (t + 2 * v - 12 * w) := by
    rw [hB2exp]
    calc
      T * min (X ^ (-4 * w)) (X ^ (2 * v - 12 * w)) ≤
          T * X ^ (2 * v - 12 * w) := mul_le_mul_of_nonneg_left (min_le_right _ _) hT.le
      _ ≤ X ^ t * X ^ (2 * v - 12 * w) := mul_le_mul_of_nonneg_right hTpow
        (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (t + 2 * v - 12 * w) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hA2exp : A ^ 2 = X ^ (2 * v - 4 * w) := by
    rw [hAexp, rpow_nat_pow X (v - 2 * w) hXpos.le 2]
    exact congrArg (fun e : ℝ => X ^ e) (by ring)
  by_cases hAB : A ≥ B
  · have hRA : R ≤ A := by
      rw [max_eq_left hAB] at hRmaxOne
      exact hRmaxOne
    have hpow : X ^ r ≤ X ^ (v - 2 * w) := by
      rw [← hRpow, ← hAexp]
      exact hRA
    have hr := (Real.rpow_le_rpow_left_iff hX).1 hpow
    exact Or.inl hr
  · have hAB' : A ≤ B := le_of_not_ge hAB
    have hRB : R ≤ B := by
      rw [max_eq_right hAB'] at hRmaxOne
      exact hRmaxOne
    have hRBone : R ≤ X ^ (t - 2 * w) := hRB.trans hBboundOne
    have hrB1 : r ≤ t - 2 * w := by
      apply (Real.rpow_le_rpow_left_iff hX).1
      rw [← hRpow]
      exact hRBone
    have hRBtwo : R ≤ X ^ (t + v - 6 * w) := hRB.trans hBboundTwo
    have hrB2 : r ≤ t + v - 6 * w := by
      apply (Real.rpow_le_rpow_left_iff hX).1
      rw [← hRpow]
      exact hRBtwo
    by_cases hA2B2 : A ^ 2 ≥ B ^ 2 / T
    · have hRA2 : R ≤ A ^ 2 := by
        rw [max_eq_left hA2B2] at hRmaxTwo
        exact hRmaxTwo
      have hRA2exp : R ≤ X ^ (2 * v - 4 * w) := by
        rw [← hA2exp]
        exact hRA2
      have hrB3 : r ≤ 2 * v - 4 * w := by
        apply (Real.rpow_le_rpow_left_iff hX).1
        rw [← hRpow]
        exact hRA2exp
      have hrB1' : r ≤ 3 / 8 - eps - 2 * w := by simpa [ht] using hrB1
      have hrB2' : r ≤ 3 / 8 - eps + v - 6 * w := by simpa [ht] using hrB2
      exact Or.inr (Or.inl ⟨hrB1', hrB2', hrB3⟩)
    · have hA2leB2 : A ^ 2 ≤ B ^ 2 / T := le_of_not_ge hA2B2
      have hRB2 : R ≤ B ^ 2 / T := by
        rw [max_eq_right hA2leB2] at hRmaxTwo
        exact hRmaxTwo
      have hRB2one : R ≤ X ^ (t - 4 * w) := hRB2.trans hBpowBoundOne
      have hrD1 : r ≤ t - 4 * w := by
        apply (Real.rpow_le_rpow_left_iff hX).1
        rw [← hRpow]
        exact hRB2one
      have hRB2two : R ≤ X ^ (t + 2 * v - 12 * w) := hRB2.trans hBpowBoundTwo
      have hrD2 : r ≤ t + 2 * v - 12 * w := by
        apply (Real.rpow_le_rpow_left_iff hX).1
        rw [← hRpow]
        exact hRB2two
      have hrD1' : r ≤ 3 / 8 - eps - 4 * w := by simpa [ht] using hrD1
      have hrD2' : r ≤ 3 / 8 - eps + 2 * v - 12 * w := by simpa [ht] using hrD2
      exact Or.inr (Or.inr ⟨hrD1', hrD2'⟩)

/-- The exact two level estimates for each factor imply the three alternatives
in `ldm:exponent-inequality`; the resulting product of dyadic levels has the
source `sqrt X * X^(-h/16)` bound. -/
theorem trilinearLargeDyadicCellExponentBound
    (X T kL eps h a b c x y z r N1 N2 N3 V1 V2 V3 m R : ℝ)
    (hX : 1 < X) (hT : 0 < T) (hkL : 0 < kL)
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hN3 : 0 < N3)
    (hV1 : 0 < V1) (hV2 : 0 < V2) (hV3 : 0 < V3)
    (hRdef : R = m / (2 * kL))
    (hN1pow : N1 = X ^ a) (hN2pow : N2 = X ^ b) (hN3pow : N3 = X ^ c)
    (hV1pow : V1 = X ^ x) (hV2pow : V2 = X ^ y) (hV3pow : V3 = X ^ z)
    (hRpow : R = X ^ r)
    (hTpow : T ≤ X ^ (3 / 8 - eps))
    (hlevelOne1 : m ≤ kL *
      (N1 / V1 ^ 2 + T * min (1 / V1 ^ 2) (N1 / V1 ^ 6)))
    (hlevelTwo1 : m ≤ kL *
      (N1 ^ 2 / V1 ^ 4 + T * min (1 / V1 ^ 4) (N1 ^ 2 / V1 ^ 12)))
    (hlevelOne2 : m ≤ kL *
      (N2 / V2 ^ 2 + T * min (1 / V2 ^ 2) (N2 / V2 ^ 6)))
    (hlevelTwo2 : m ≤ kL *
      (N2 ^ 2 / V2 ^ 4 + T * min (1 / V2 ^ 4) (N2 ^ 2 / V2 ^ 12)))
    (hlevelOne3 : m ≤ kL *
      (N3 / V3 ^ 2 + T * min (1 / V3 ^ 2) (N3 / V3 ^ 6)))
    (hlevelTwo3 : m ≤ kL *
      (N3 ^ 2 / V3 ^ 4 + T * min (1 / V3 ^ 4) (N3 ^ 2 / V3 ^ 12)))
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 3 / 16)
    (hh0 : 0 ≤ h) (hh1 : h ≤ eps)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hr0 : 0 ≤ r)
    (hsum : a + b + c = 1)
    (ha1 : 1 / 4 - eps / 100 ≤ a)
    (ha2 : a ≤ 1 / 2 + eps / 100)
    (hbalance : |b - c| ≤ 1 / 4 + eps / 100)
    (hx1 : x ≤ a / 2 - h) (hy1 : y ≤ b / 2) (hz1 : z ≤ c / 2) :
    R * V1 * V2 * V3 ≤ Real.sqrt X * X ^ (-h / 16) := by
  have hAlt1 := dyadic_factor_alternative X T N1 V1 m R kL eps
    (3 / 8 - eps) a x r hX hT hN1 hV1 hkL hRdef
    hN1pow hV1pow hRpow rfl hTpow hlevelOne1 hlevelTwo1
  have hAlt2 := dyadic_factor_alternative X T N2 V2 m R kL eps
    (3 / 8 - eps) b y r hX hT hN2 hV2 hkL hRdef
    hN2pow hV2pow hRpow rfl hTpow hlevelOne2 hlevelTwo2
  have hAlt3 := dyadic_factor_alternative X T N3 V3 m R kL eps
    (3 / 8 - eps) c z r hX hT hN3 hV3 hkL hRdef
    hN3pow hV3pow hRpow rfl hTpow hlevelOne3 hlevelTwo3
  have hExponent := trilinearExponentInequality eps h a b c x y z r
    heps0 heps1 hh0 hh1 ha0 hb0 hc0 hx0 hy0 hz0 hr0 hsum ha1 ha2 hbalance
    hx1 hy1 hz1 hAlt1 hAlt2 hAlt3
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hProduct : R * V1 * V2 * V3 = X ^ (r + x + y + z) := by
    calc
      R * V1 * V2 * V3 = X ^ r * X ^ x * X ^ y * X ^ z := by
        rw [hRpow, hV1pow, hV2pow, hV3pow]
      _ = X ^ (r + x + y + z) := by
        rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
  have hsource : X ^ (1 / 2 - h / 16) = Real.sqrt X * X ^ (-h / 16) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (1 / 2 - h / 16 : ℝ) = 1 / 2 + (-h / 16) by ring,
      Real.rpow_add hXpos]
  calc
    R * V1 * V2 * V3 = X ^ (r + x + y + z) := hProduct
    _ ≤ X ^ (1 / 2 - h / 16) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) hExponent
    _ = Real.sqrt X * X ^ (-h / 16) := hsource

/-- Pointwise control on a measurable cell gives the exact finite integral
bound `8 V₁V₂V₃ |E|` used in the dyadic summation. -/
theorem trilinearDyadicCellIntegral_le_levelVolume
    (T V1 V2 V3 : ℝ) (F1 F2 F3 : ℝ → ℂ) (E : Set ℝ)
    (hEmeas : MeasurableSet E) (hEsubset : E ⊆ Set.Icc (-T) T)
    (hpoint : ∀ t ∈ E, ‖F1 t * F2 t * F3 t‖ ≤ 8 * V1 * V2 * V3)
    (hcont1 : Continuous F1) (hcont2 : Continuous F2) (hcont3 : Continuous F3) :
    ∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume ≤
      8 * V1 * V2 * V3 * volume.real E := by
  classical
  let I := Set.Icc (-T) T
  let f : ℝ → ℝ := fun t => ‖F1 t * F2 t * F3 t‖
  have hcontf : Continuous f := by
    dsimp [f]
    fun_prop
  have hfiI : IntegrableOn f I := by
    dsimp [I]
    exact hcontf.continuousOn.integrableOn_compact isCompact_Icc
  have hμmono : volume.restrict E ≤ volume.restrict I := by
    dsimp [I]
    exact Measure.restrict_mono_set volume hEsubset
  have hfiI' : Integrable f (volume.restrict I) := hfiI
  have hfiE' : Integrable f (volume.restrict E) := hfiI'.mono_measure hμmono
  have hfiE : IntegrableOn f E := hfiE'
  have hEfinite : volume E < ⊤ := by
    calc
      volume E ≤ volume I := measure_mono hEsubset
      _ < ⊤ := by simp [I, Real.volume_Icc]
  have hconst : IntegrableOn (fun _ : ℝ => 8 * V1 * V2 * V3) E :=
    integrableOn_const (ne_of_lt hEfinite)
  have hmono := MeasureTheory.setIntegral_mono_on hfiE hconst hEmeas hpoint
  calc
    (∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume) ≤
        ∫ t in E, (8 * V1 * V2 * V3 : ℝ) ∂volume := hmono
    _ = volume.real E * (8 * V1 * V2 * V3) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ = 8 * V1 * V2 * V3 * volume.real E := by ring

/-- Combining the dyadic cell mass `m=2K_LR`, its finite integral bound, and
the exponent estimate gives the exact `16 K_L sqrt(X) X^(-h/16)` cell cost. -/
theorem trilinearLargeDyadicCellIntegralBound
    (T kL R V1 V2 V3 m X h : ℝ)
    (F1 F2 F3 : ℝ → ℂ) (E : Set ℝ)
    (hkL : 0 ≤ kL) (hmass : m = 2 * kL * R)
    (hvolume : volume.real E = m)
    (hEmeas : MeasurableSet E) (hEsubset : E ⊆ Set.Icc (-T) T)
    (hpoint : ∀ t ∈ E, ‖F1 t * F2 t * F3 t‖ ≤ 8 * V1 * V2 * V3)
    (hcont1 : Continuous F1) (hcont2 : Continuous F2) (hcont3 : Continuous F3)
    (hExponentBound : R * V1 * V2 * V3 ≤ Real.sqrt X * X ^ (-h / 16)) :
    ∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume ≤
      16 * kL * Real.sqrt X * X ^ (-h / 16) := by
  calc
    (∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume) ≤
        8 * V1 * V2 * V3 * m := by
      calc
        (∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume) ≤
            8 * V1 * V2 * V3 * volume.real E :=
          trilinearDyadicCellIntegral_le_levelVolume T V1 V2 V3 F1 F2 F3 E
            hEmeas hEsubset hpoint hcont1 hcont2 hcont3
        _ = 8 * V1 * V2 * V3 * m := by rw [hvolume]
    _ = 16 * kL * (R * V1 * V2 * V3) := by rw [hmass]; ring
    _ ≤ 16 * kL * (Real.sqrt X * X ^ (-h / 16)) :=
      mul_le_mul_of_nonneg_left hExponentBound (by positivity)
    _ = 16 * kL * Real.sqrt X * X ^ (-h / 16) := by ring

/-- With `h=min(eps,-log(delta)/log(X))`, the decay in the finite exponent
lemma is exactly the maximum of the two terms in `ldm:trilinear`. -/
theorem trilinearDyadicDecayIdentity
    (X eps delta : ℝ) (hX : 1 < X) (heps : 0 ≤ eps)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    X ^ (-min eps (-Real.log delta / Real.log X) / 16) =
      max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
  let q := -Real.log delta / Real.log X
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hlogX : 0 < Real.log X := Real.log_pos hX
  by_cases hcmp : eps ≤ q
  · have hlogBound : Real.log delta ≤ Real.log (X ^ (-eps)) := by
      rw [Real.log_rpow hXpos]
      have hmul := (le_div_iff₀ hlogX).1 (show eps ≤ q from hcmp)
      change eps * Real.log X ≤ -Real.log delta at hmul
      linarith
    have hbaseBound : delta ≤ X ^ (-eps) :=
      (Real.log_le_log_iff hdelta0 (Real.rpow_pos_of_pos hXpos _)).1 hlogBound
    have hpowBound : delta ^ (1 / 16 : ℝ) ≤ X ^ (-eps / 16) := by
      have hpow := (Real.rpow_le_rpow_iff (le_of_lt hdelta0)
        (Real.rpow_nonneg hXpos.le _) (by norm_num : (0 : ℝ) < 1 / 16)).2 hbaseBound
      have hpowEq : (X ^ (-eps)) ^ (1 / 16 : ℝ) = X ^ (-eps / 16) := by
        rw [← Real.rpow_mul hXpos.le]
        exact congrArg (fun u : ℝ => X ^ u) (by ring)
      exact hpow.trans_eq hpowEq
    rw [min_eq_left hcmp, max_eq_left hpowBound]
  · have hqeps : q ≤ eps := le_of_not_ge hcmp
    have hbase : X ^ (Real.log delta / Real.log X) = delta := by
      apply (Real.mul_log_eq_log_iff hXpos hdelta0).1
      field_simp [ne_of_gt hlogX]
    have hqExponent : -q / 16 = (Real.log delta / Real.log X) * (1 / 16 : ℝ) := by
      dsimp [q]
      field_simp [ne_of_gt hlogX] <;> ring
    have hqPower : X ^ (-q / 16) = delta ^ (1 / 16 : ℝ) := by
      calc
        X ^ (-q / 16) = X ^ ((Real.log delta / Real.log X) * (1 / 16 : ℝ)) := by
          rw [hqExponent]
        _ = (X ^ (Real.log delta / Real.log X)) ^ (1 / 16 : ℝ) := by
          rw [Real.rpow_mul hXpos.le]
        _ = delta ^ (1 / 16 : ℝ) := by rw [hbase]
    have hsmallDecay : X ^ (-eps / 16) ≤ X ^ (-q / 16) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hX)
        (by dsimp [q]; nlinarith)
    rw [min_eq_right hqeps, max_eq_right (hsmallDecay.trans_eq hqPower)]
    exact hqPower

/-- A cell of mass at most `2 kL` uses the pointwise product cap. This also
covers empty cells and preserves the source half-open endpoint convention. -/
theorem trilinearSmallMassDyadicCellIntegralBound
    (T V1 V2 V3 m kL X eps delta : ℝ)
    (F1 F2 F3 : ℝ → ℂ) (E : Set ℝ)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hV1 : 0 ≤ V1) (hV2 : 0 ≤ V2) (hV3 : 0 ≤ V3)
    (hkL : 0 ≤ kL) (hmass : m = volume.real E) (hsmallMass : m ≤ 2 * kL)
    (hproductCap : V1 * V2 * V3 ≤ delta * Real.sqrt X)
    (hEmeas : MeasurableSet E) (hEsubset : E ⊆ Set.Icc (-T) T)
    (hpoint : ∀ t ∈ E, ‖F1 t * F2 t * F3 t‖ ≤ 8 * V1 * V2 * V3)
    (hcont1 : Continuous F1) (hcont2 : Continuous F2)
    (hcont3 : Continuous F3) :
    ∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume ≤
      16 * kL * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
  have hdeltaRoot : delta ≤ delta ^ (1 / 16 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hdelta0 hdelta1
        (by norm_num : (1 / 16 : ℝ) ≤ 1)
  have hlargeIntegral := trilinearDyadicCellIntegral_le_levelVolume
    T V1 V2 V3 F1 F2 F3 E hEmeas hEsubset hpoint hcont1 hcont2 hcont3
  calc
    (∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume) ≤
        8 * V1 * V2 * V3 * volume.real E := hlargeIntegral
    _ = 8 * (V1 * V2 * V3) * m := by rw [hmass]; ring
    _ ≤ 8 * (V1 * V2 * V3) * (2 * kL) :=
      mul_le_mul_of_nonneg_left hsmallMass (by positivity)
    _ = 16 * kL * (V1 * V2 * V3) := by ring
    _ ≤ 16 * kL * (delta * Real.sqrt X) :=
      mul_le_mul_of_nonneg_left hproductCap (by positivity)
    _ = 16 * kL * Real.sqrt X * delta := by ring
    _ ≤ 16 * kL * Real.sqrt X * delta ^ (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left hdeltaRoot (by positivity)
    _ ≤ 16 * kL * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-- A large-mass cell uses the exact large-cell exponent estimate and the
identity converting its minimum exponent to the source maximum. -/
theorem trilinearLargeMassDyadicCellIntegralBound
    (T kL R V1 V2 V3 m X eps delta : ℝ)
    (F1 F2 F3 : ℝ → ℂ) (E : Set ℝ)
    (hX : 1 < X) (heps0 : 0 ≤ eps) (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) (hkL : 0 ≤ kL)
    (hmass : m = 2 * kL * R) (hvolume : volume.real E = m)
    (hEmeas : MeasurableSet E) (hEsubset : E ⊆ Set.Icc (-T) T)
    (hpoint : ∀ t ∈ E, ‖F1 t * F2 t * F3 t‖ ≤ 8 * V1 * V2 * V3)
    (hcont1 : Continuous F1) (hcont2 : Continuous F2) (hcont3 : Continuous F3)
    (hExponentBound : R * V1 * V2 * V3 ≤
      Real.sqrt X * X ^ (-(min eps (-Real.log delta / Real.log X)) / 16)) :
    ∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume ≤
      16 * kL * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
  have hlarge := trilinearLargeDyadicCellIntegralBound T kL R V1 V2 V3 m X
    (min eps (-Real.log delta / Real.log X)) F1 F2 F3 E hkL hmass hvolume
    hEmeas hEsubset hpoint hcont1 hcont2 hcont3 hExponentBound
  have hdecay := trilinearDyadicDecayIdentity X eps delta hX heps0
    hdelta0 hdelta1
  rw [hdecay] at hlarge
  exact hlarge

/-- Exact mass dichotomy for one dyadic cell. Small cells use the pointwise
product cap; large cells use the factor/square level estimates through the
explicit exponent premise. -/
theorem trilinearDyadicCellIntegralBound_by_mass
    (T V1 V2 V3 m kL X eps delta : ℝ)
    (F1 F2 F3 : ℝ → ℂ) (E : Set ℝ)
    (hX : 1 < X) (heps0 : 0 ≤ eps) (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) (hkL : 0 < kL)
    (hV1 : 0 ≤ V1) (hV2 : 0 ≤ V2) (hV3 : 0 ≤ V3)
    (hvolume : volume.real E = m)
    (hEmeas : MeasurableSet E) (hEsubset : E ⊆ Set.Icc (-T) T)
    (hpoint : ∀ t ∈ E, ‖F1 t * F2 t * F3 t‖ ≤ 8 * V1 * V2 * V3)
    (hcont1 : Continuous F1) (hcont2 : Continuous F2) (hcont3 : Continuous F3)
    (hsmallCap : m ≤ 2 * kL → V1 * V2 * V3 ≤ delta * Real.sqrt X)
    (hlargeExponent : 2 * kL < m →
      (m / (2 * kL)) * V1 * V2 * V3 ≤
        Real.sqrt X * X ^ (-(min eps (-Real.log delta / Real.log X)) / 16)) :
    ∫ t in E, ‖F1 t * F2 t * F3 t‖ ∂volume ≤
      16 * kL * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
  by_cases hsmallMass : m ≤ 2 * kL
  · have hsmall := trilinearSmallMassDyadicCellIntegralBound T V1 V2 V3 m
      kL X eps delta F1 F2 F3 E hdelta0 hdelta1 hV1 hV2 hV3
      hkL.le (hvolume.symm) hsmallMass (hsmallCap hsmallMass)
      hEmeas hEsubset hpoint hcont1 hcont2 hcont3
    exact hsmall
  · have hlargeMass : 2 * kL < m := lt_of_not_ge hsmallMass
    let R := m / (2 * kL)
    have hmass : m = 2 * kL * R := by
      dsimp [R]
      field_simp [ne_of_gt hkL]
    exact trilinearLargeMassDyadicCellIntegralBound T kL R V1 V2 V3 m X
      eps delta F1 F2 F3 E hX heps0 hdelta0 hdelta1 hkL.le hmass hvolume
      hEmeas hEsubset hpoint hcont1 hcont2 hcont3 (hlargeExponent hlargeMass)

/-- The full finite Cartesian product of three dyadic level ranges has at
most `8 L^3` indices when each factor has at most `2L` choices. -/
def trilinearDyadicTripleIndices (M : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range M).product ((Finset.range M).product (Finset.range M))

theorem trilinearDyadicTripleCardBound (M : ℕ) (L : ℝ)
    (hM : (M : ℝ) ≤ 2 * L) :
    ((trilinearDyadicTripleIndices M).card : ℝ) ≤ 8 * L ^ 3 := by
  have hcard : (trilinearDyadicTripleIndices M).card = M ^ 3 := by
    simp [trilinearDyadicTripleIndices, Finset.card_product, Finset.card_range]
    ring
  have hcardR : ((trilinearDyadicTripleIndices M).card : ℝ) =
      (M : ℝ) ^ 3 := by exact_mod_cast hcard
  calc
    ((trilinearDyadicTripleIndices M).card : ℝ) = (M : ℝ) ^ 3 := hcardR
    _ ≤ (2 * L) ^ 3 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg M) hM 3
    _ = 8 * L ^ 3 := by ring

/-- The source cutoff for dyadic levels has at most `2 log(4X)` choices.
The cutoff is `Nat.log2 (floor X)+1`, so every level with `2^m ≤ sqrt X`
is included. -/
theorem trilinearDyadicLevelCutoffBound (X : ℝ) (hX : 2 ^ 16 ≤ X) :
    ((Nat.log2 (Nat.floor X) + 1 : ℕ) : ℝ) ≤ 2 * Real.log (4 * X) := by
  have hbase : (0 : ℝ) < 2 ^ 16 := by positivity
  have hXpos : 0 < X := by linarith
  have hXlarge : (2 : ℝ) ≤ X := by norm_num at hX ⊢; linarith
  have hfloor : 2 ≤ Nat.floor X := Nat.le_floor hXlarge
  have hfloorReal : (Nat.floor X : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lower : 2 / 3 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hLpos : 0 ≤ Real.log (4 * X) := by
    apply Real.log_nonneg
    nlinarith
  have hNatLog := Real.log2_le_logb (Nat.floor X)
  rw [Real.logb] at hNatLog
  have hlogArg : 0 < (Nat.floor X : ℝ) := by exact_mod_cast (by omega : 0 < Nat.floor X)
  have hlogCompare : Real.log (Nat.floor X : ℝ) ≤ Real.log (4 * X) := by
    apply Real.log_le_log hlogArg
    nlinarith
  have hNatLogBound : (Nat.log2 (Nat.floor X) : ℝ) ≤
      (3 / 2 : ℝ) * Real.log (4 * X) := by
    have hdiv := div_le_div_of_nonneg_right hlogCompare hlog2pos.le
    have hscale : 1 ≤ (3 / 2 : ℝ) * Real.log 2 := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hscale hLpos
    have hLscale : Real.log (4 * X) ≤
        (3 / 2 : ℝ) * Real.log (4 * X) * Real.log 2 := by
      calc
        Real.log (4 * X) = Real.log (4 * X) * 1 := by ring
        _ ≤ Real.log (4 * X) * ((3 / 2 : ℝ) * Real.log 2) := hscaled
        _ = (3 / 2 : ℝ) * Real.log (4 * X) * Real.log 2 := by ring
    have hfinalDiv : Real.log (4 * X) / Real.log 2 ≤
        (3 / 2 : ℝ) * Real.log (4 * X) :=
      (div_le_iff₀ hlog2pos).2 (by nlinarith [hLscale])
    exact (hNatLog.trans hdiv).trans hfinalDiv
  have hLlarge : 2 ≤ Real.log (4 * X) := by
    have hpow : (2 : ℝ) ^ 18 ≤ 4 * X := by norm_num at hX ⊢; nlinarith
    have hlogpow : Real.log ((2 : ℝ) ^ 18) ≤ Real.log (4 * X) :=
      Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at hlogpow
    calc
      2 ≤ (18 : ℝ) * (2 / 3) := by norm_num
      _ ≤ 18 * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2lower (by norm_num)
      _ ≤ Real.log (4 * X) := hlogpow
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith [hNatLogBound, hLlarge]

/-- The actual finite product of source dyadic levels has at most `8L_X^3`
indices for `L_X=log(4X)`. -/
theorem trilinearDyadicLevelTripleCardBound (X : ℝ)
    (hX : 2 ^ 16 ≤ X) :
    ((trilinearDyadicTripleIndices (Nat.log2 (Nat.floor X) + 1)).card : ℝ) ≤
      8 * Real.log (4 * X) ^ 3 := by
  exact trilinearDyadicTripleCardBound
    (Nat.log2 (Nat.floor X) + 1) (Real.log (4 * X))
    (trilinearDyadicLevelCutoffBound X hX)

/-- Any dyadic level whose lower endpoint is at most `sqrt X` lies below the
finite cutoff used in the trilinear partition. -/
theorem trilinearDyadicLevelIndex_lt_cutoff (X : ℝ) (hX : 2 ^ 16 ≤ X)
    (m : ℕ) (hlevel : (2 : ℝ) ^ m ≤ Real.sqrt X) :
    m < Nat.log2 (Nat.floor X) + 1 := by
  have hbase : (0 : ℝ) < 2 ^ 16 := by positivity
  have hXpos : 0 < X := by linarith
  have hXlarge : (1 : ℝ) ≤ X := by norm_num at hX ⊢; linarith
  have hsqrt : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hpowReal : ((2 ^ m : ℕ) : ℝ) ≤ X := by
    calc
      ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by norm_cast
      _ ≤ Real.sqrt X := hlevel
      _ ≤ X := hsqrt
  have hpowFloor : 2 ^ m ≤ Nat.floor X := Nat.le_floor hpowReal
  have hfloorPos : Nat.floor X ≠ 0 := by
    have hf : 2 ≤ Nat.floor X := Nat.le_floor (by norm_num at hX ⊢; linarith)
    omega
  have hmLog : m ≤ Nat.log 2 (Nat.floor X) :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hfloorPos).2 hpowFloor
  have hm : m ≤ Nat.log2 (Nat.floor X) := by
    simpa only [Nat.log2_eq_log_two] using hmLog
  exact Nat.lt_succ_of_le hm

/-- Assign a positive scalar to its unique half-open dyadic level. -/
noncomputable def trilinearDyadicLevel (u : ℝ) : ℕ :=
  Nat.floor (Real.log u / Real.log 2)

/-- The floor-log assignment gives the exact half-open interval, including
when `u` is itself a power of two. -/
theorem trilinearDyadicLevelBounds (u : ℝ) (hu : 1 < u) :
    (2 : ℝ) ^ trilinearDyadicLevel u ≤ u ∧
      u < (2 : ℝ) ^ (trilinearDyadicLevel u + 1) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogu : 0 < Real.log u := Real.log_pos hu
  let q := Real.log u / Real.log 2
  have hq : 0 < q := div_pos hlogu hlog2
  have hfloorLo : (Nat.floor q : ℝ) ≤ q := Nat.floor_le hq.le
  have hfloorHi : q < (Nat.floor q : ℝ) + 1 := Nat.lt_floor_add_one q
  have hqmul : q * Real.log 2 = Real.log u := by
    dsimp [q]
    field_simp [ne_of_gt hlog2]
  have hlogLo : Real.log ((2 : ℝ) ^ Nat.floor q) ≤ Real.log u := by
    calc
      Real.log ((2 : ℝ) ^ Nat.floor q) =
          (Nat.floor q : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ q * Real.log 2 := mul_le_mul_of_nonneg_right hfloorLo hlog2.le
      _ = Real.log u := hqmul
  have hlogHi : Real.log u <
      Real.log ((2 : ℝ) ^ (Nat.floor q + 1)) := by
    have hmulHi := mul_lt_mul_of_pos_right hfloorHi hlog2
    calc
      Real.log u = q * Real.log 2 := hqmul.symm
      _ < ((Nat.floor q : ℝ) + 1) * Real.log 2 := hmulHi
      _ = Real.log ((2 : ℝ) ^ (Nat.floor q + 1)) := by
        rw [Real.log_pow]
        norm_cast
  have hpowLo : (2 : ℝ) ^ Nat.floor q ≤ u :=
    (Real.log_le_log_iff (by positivity) hu0).1 hlogLo
  have hpowHi : u < (2 : ℝ) ^ (Nat.floor q + 1) :=
    (Real.log_lt_log_iff hu0 (by positivity)).1 hlogHi
  simpa [trilinearDyadicLevel, q] using And.intro hpowLo hpowHi

/-- Half-open dyadic intervals have unique natural level assignments. -/
theorem trilinearDyadicLevel_unique (u : ℝ) {m n : ℕ}
    (hmLo : (2 : ℝ) ^ m ≤ u) (hmHi : u < (2 : ℝ) ^ (m + 1))
    (hnLo : (2 : ℝ) ^ n ≤ u) (hnHi : u < (2 : ℝ) ^ (n + 1)) :
    m = n := by
  by_contra hmn
  rcases lt_or_gt_of_ne hmn with hmn' | hnm'
  · have hstep : m + 1 ≤ n := Nat.succ_le_iff.mpr hmn'
    have hpow : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ n := by
      exact pow_le_pow_right₀ (by norm_num) hstep
    linarith
  · have hstep : n + 1 ≤ m := Nat.succ_le_iff.mpr hnm'
    have hpow : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m := by
      exact pow_le_pow_right₀ (by norm_num) hstep
    linarith

/-- The real-time set where a continuous factor has dyadic size `2^m`. -/
def trilinearDyadicScalarCell (F : ℝ → ℂ) (m : ℕ) : Set ℝ :=
  {t | ‖F t‖ ∈ Set.Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1))}

/-- Continuity makes each half-open scalar level cell measurable. -/
theorem trilinearDyadicScalarCell_measurable (F : ℝ → ℂ) (m : ℕ)
    (hF : Continuous F) : MeasurableSet (trilinearDyadicScalarCell F m) := by
  unfold trilinearDyadicScalarCell
  exact measurableSet_Ico.preimage hF.norm.measurable

/-- Distinct scalar dyadic level cells are disjoint. -/
theorem trilinearDyadicScalarCell_disjoint (F : ℝ → ℂ) {m n : ℕ}
    (hmn : m ≠ n) : Disjoint (trilinearDyadicScalarCell F m)
      (trilinearDyadicScalarCell F n) := by
  rw [Set.disjoint_left]
  intro t htm htn
  have htm' : ‖F t‖ ∈ Set.Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1)) := htm
  have htn' : ‖F t‖ ∈ Set.Ico ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)) := htn
  have hmnEq := trilinearDyadicLevel_unique (‖F t‖)
    htm'.1 htm'.2 htn'.1 htn'.2
  exact hmn hmnEq

/-- A magnitude above one lies in exactly its assigned half-open dyadic cell. -/
theorem trilinearDyadicScalarCell_mem_level (F : ℝ → ℂ) (t : ℝ)
    (hF : 1 < ‖F t‖) :
    t ∈ trilinearDyadicScalarCell F (trilinearDyadicLevel ‖F t‖) := by
  exact trilinearDyadicLevelBounds ‖F t‖ hF

/-- The assigned scalar level is one of the finite levels retained below
`sqrt X`. -/
theorem trilinearDyadicLevel_mem_range (X u : ℝ) (hX : 2 ^ 16 ≤ X)
    (hu : 1 < u) (huX : u ≤ Real.sqrt X) :
    trilinearDyadicLevel u ∈
      Finset.range (Nat.log2 (Nat.floor X) + 1) := by
  apply Finset.mem_range.mpr
  apply trilinearDyadicLevelIndex_lt_cutoff X hX
  exact (trilinearDyadicLevelBounds u hu).1.trans huX

/-- The product level cell for three factors. The right-associated product
index matches the finite Cartesian product counted above. -/
def trilinearDyadicTripleCell (F₁ F₂ F₃ : ℝ → ℂ)
    (idx : ℕ × ℕ × ℕ) : Set ℝ :=
  trilinearDyadicScalarCell F₁ idx.1 ∩
    (trilinearDyadicScalarCell F₂ idx.2.1 ∩
      trilinearDyadicScalarCell F₃ idx.2.2)

/-- Every product level cell is measurable for continuous factors. -/
theorem trilinearDyadicTripleCell_measurable (F₁ F₂ F₃ : ℝ → ℂ)
    (idx : ℕ × ℕ × ℕ) (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hF₃ : Continuous F₃) :
    MeasurableSet (trilinearDyadicTripleCell F₁ F₂ F₃ idx) := by
  unfold trilinearDyadicTripleCell
  exact (trilinearDyadicScalarCell_measurable F₁ idx.1 hF₁).inter
    ((trilinearDyadicScalarCell_measurable F₂ idx.2.1 hF₂).inter
      (trilinearDyadicScalarCell_measurable F₃ idx.2.2 hF₃))

/-- Distinct product indices give disjoint cells, with exact half-open
endpoint handling inherited coordinatewise. -/
theorem trilinearDyadicTripleCell_disjoint (F₁ F₂ F₃ : ℝ → ℂ)
    {idx jdx : ℕ × ℕ × ℕ} (hne : idx ≠ jdx) :
    Disjoint (trilinearDyadicTripleCell F₁ F₂ F₃ idx)
      (trilinearDyadicTripleCell F₁ F₂ F₃ jdx) := by
  rw [Set.disjoint_left]
  intro t htidx htjdx
  rcases idx with ⟨m₁, m₂m₃⟩
  rcases m₂m₃ with ⟨m₂, m₃⟩
  rcases jdx with ⟨n₁, n₂n₃⟩
  rcases n₂n₃ with ⟨n₂, n₃⟩
  simp only [trilinearDyadicTripleCell, Set.mem_inter_iff] at htidx htjdx
  rcases htidx with ⟨⟨hm₁lo, hm₁hi⟩, ⟨⟨hm₂lo, hm₂hi⟩, hm₃⟩⟩
  rcases htjdx with ⟨⟨hn₁lo, hn₁hi⟩, ⟨⟨hn₂lo, hn₂hi⟩, hn₃⟩⟩
  have heq₁ := trilinearDyadicLevel_unique (‖F₁ t‖)
    hm₁lo hm₁hi hn₁lo hn₁hi
  have heq₂ := trilinearDyadicLevel_unique (‖F₂ t‖)
    hm₂lo hm₂hi hn₂lo hn₂hi
  have heq₃ := trilinearDyadicLevel_unique (‖F₃ t‖)
    hm₃.1 hm₃.2 hn₃.1 hn₃.2
  apply hne
  apply Prod.ext
  · exact heq₁
  · apply Prod.ext
    · exact heq₂
    · exact heq₃

/-- A point where all three factor magnitudes exceed one and are at most
`sqrt X` belongs to its unique cell in the finite product index set. -/
theorem trilinearDyadicTripleCell_mem_finite_cover
    (X : ℝ) (hX : 2 ^ 16 ≤ X) (F₁ F₂ F₃ : ℝ → ℂ) (t : ℝ)
    (hF₁lo : 1 < ‖F₁ t‖) (hF₂lo : 1 < ‖F₂ t‖) (hF₃lo : 1 < ‖F₃ t‖)
    (hF₁hi : ‖F₁ t‖ ≤ Real.sqrt X)
    (hF₂hi : ‖F₂ t‖ ≤ Real.sqrt X)
    (hF₃hi : ‖F₃ t‖ ≤ Real.sqrt X) :
    (trilinearDyadicLevel ‖F₁ t‖,
      (trilinearDyadicLevel ‖F₂ t‖,
        trilinearDyadicLevel ‖F₃ t‖)) ∈
        trilinearDyadicTripleIndices (Nat.log2 (Nat.floor X) + 1) ∧
      t ∈ trilinearDyadicTripleCell F₁ F₂ F₃
        (trilinearDyadicLevel ‖F₁ t‖,
          (trilinearDyadicLevel ‖F₂ t‖,
            trilinearDyadicLevel ‖F₃ t‖)) := by
  have hidx₁ := trilinearDyadicLevel_mem_range X ‖F₁ t‖ hX hF₁lo hF₁hi
  have hidx₂ := trilinearDyadicLevel_mem_range X ‖F₂ t‖ hX hF₂lo hF₂hi
  have hidx₃ := trilinearDyadicLevel_mem_range X ‖F₃ t‖ hX hF₃lo hF₃hi
  constructor
  · exact Finset.mem_product.mpr
      ⟨hidx₁, Finset.mem_product.mpr ⟨hidx₂, hidx₃⟩⟩
  · simp only [trilinearDyadicTripleCell, Set.mem_inter_iff]
    exact ⟨trilinearDyadicScalarCell_mem_level F₁ t hF₁lo,
      trilinearDyadicScalarCell_mem_level F₂ t hF₂lo,
      trilinearDyadicScalarCell_mem_level F₃ t hF₃lo⟩

/-- The part of an input measurable set where all three factors are in the
large-modulus branch. -/
def trilinearDyadicLargeFactorDomain (A : Set ℝ)
    (F₁ F₂ F₃ : ℝ → ℂ) : Set ℝ :=
  {t | t ∈ A ∧ 1 < ‖F₁ t‖ ∧ 1 < ‖F₂ t‖ ∧ 1 < ‖F₃ t‖}

/-- A product dyadic cell restricted to the large-modulus branch and the
given measurable domain. -/
def trilinearDyadicLargeFactorCell (A : Set ℝ)
    (F₁ F₂ F₃ : ℝ → ℂ) (idx : ℕ × ℕ × ℕ) : Set ℝ :=
  trilinearDyadicLargeFactorDomain A F₁ F₂ F₃ ∩
    trilinearDyadicTripleCell F₁ F₂ F₃ idx

/-- The large-modulus domain is measurable for continuous factors and a
measurable input set. -/
theorem trilinearDyadicLargeFactorDomain_measurable (A : Set ℝ)
    (F₁ F₂ F₃ : ℝ → ℂ) (hA : MeasurableSet A)
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂) (hF₃ : Continuous F₃) :
    MeasurableSet (trilinearDyadicLargeFactorDomain A F₁ F₂ F₃) := by
  unfold trilinearDyadicLargeFactorDomain
  have h1 : MeasurableSet {t : ℝ | 1 < ‖F₁ t‖} :=
    measurableSet_Ioi.preimage hF₁.norm.measurable
  have h2 : MeasurableSet {t : ℝ | 1 < ‖F₂ t‖} :=
    measurableSet_Ioi.preimage hF₂.norm.measurable
  have h3 : MeasurableSet {t : ℝ | 1 < ‖F₃ t‖} :=
    measurableSet_Ioi.preimage hF₃.norm.measurable
  exact hA.inter (h1.inter (h2.inter h3))

/-- Restricted product cells are measurable. -/
theorem trilinearDyadicLargeFactorCell_measurable (A : Set ℝ)
    (F₁ F₂ F₃ : ℝ → ℂ) (idx : ℕ × ℕ × ℕ) (hA : MeasurableSet A)
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂) (hF₃ : Continuous F₃) :
    MeasurableSet (trilinearDyadicLargeFactorCell A F₁ F₂ F₃ idx) := by
  unfold trilinearDyadicLargeFactorCell
  exact (trilinearDyadicLargeFactorDomain_measurable A F₁ F₂ F₃ hA
    hF₁ hF₂ hF₃).inter
      (trilinearDyadicTripleCell_measurable F₁ F₂ F₃ idx hF₁ hF₂ hF₃)

/-- Restricted product cells are pairwise disjoint at distinct indices. -/
theorem trilinearDyadicLargeFactorCell_disjoint (A : Set ℝ)
    (F₁ F₂ F₃ : ℝ → ℂ) {idx jdx : ℕ × ℕ × ℕ} (hne : idx ≠ jdx) :
    Disjoint (trilinearDyadicLargeFactorCell A F₁ F₂ F₃ idx)
      (trilinearDyadicLargeFactorCell A F₁ F₂ F₃ jdx) := by
  apply Disjoint.mono (by intro t ht; exact ht.2) (by intro t ht; exact ht.2)
  exact trilinearDyadicTripleCell_disjoint F₁ F₂ F₃ hne

/-- The large-modulus domain is exactly the finite union of its restricted
product dyadic cells, provided the input factors are bounded by `sqrt X`. -/
theorem trilinearDyadicLargeFactorDomain_eq_finiteCells
    (X : ℝ) (hX : 2 ^ 16 ≤ X) (A : Set ℝ) (F₁ F₂ F₃ : ℝ → ℂ)
    (hbound₁ : ∀ t ∈ A, ‖F₁ t‖ ≤ Real.sqrt X)
    (hbound₂ : ∀ t ∈ A, ‖F₂ t‖ ≤ Real.sqrt X)
    (hbound₃ : ∀ t ∈ A, ‖F₃ t‖ ≤ Real.sqrt X) :
    trilinearDyadicLargeFactorDomain A F₁ F₂ F₃ =
      ⋃ idx ∈ trilinearDyadicTripleIndices (Nat.log2 (Nat.floor X) + 1),
        trilinearDyadicLargeFactorCell A F₁ F₂ F₃ idx := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨htA, h₁, h₂, h₃⟩
    have hdom : t ∈ trilinearDyadicLargeFactorDomain A F₁ F₂ F₃ :=
      ⟨htA, h₁, h₂, h₃⟩
    let idx : ℕ × ℕ × ℕ :=
      (trilinearDyadicLevel ‖F₁ t‖,
        (trilinearDyadicLevel ‖F₂ t‖, trilinearDyadicLevel ‖F₃ t‖))
    have hcover := trilinearDyadicTripleCell_mem_finite_cover X hX F₁ F₂ F₃ t
      h₁ h₂ h₃ (hbound₁ t htA) (hbound₂ t htA) (hbound₃ t htA)
    rcases hcover with ⟨hidx, hcell⟩
    have htcell : t ∈ trilinearDyadicLargeFactorCell A F₁ F₂ F₃ idx := by
      exact ⟨hdom, hcell⟩
    exact Set.mem_iUnion.mpr ⟨idx,
      Set.mem_iUnion.mpr ⟨hidx, htcell⟩⟩
  · intro ht
    rcases Set.mem_iUnion.mp ht with ⟨idx, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨_, htcell⟩
    exact htcell.1

/-- The integral over the large-modulus domain is the exact finite sum of its
disjoint dyadic-cell integrals; no limiting passage is involved. -/
theorem trilinearDyadicLargeFactorDomain_integral_eq_sum
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (A : Set ℝ) (cells : ι → Set ℝ) (f : ℝ → ℝ)
    (hcover : A = ⋃ i ∈ S, cells i)
    (hmeas : ∀ i ∈ S, MeasurableSet (cells i))
    (hdisjoint : Set.Pairwise (↑S) (fun i j => Disjoint (cells i) (cells j)))
    (hIntegrable : IntegrableOn f A) :
    ∫ t in A, f t ∂volume = ∑ i ∈ S, ∫ t in cells i, f t ∂volume := by
  rw [hcover]
  apply MeasureTheory.integral_biUnion_finset S hmeas hdisjoint
  intro i hi
  apply hIntegrable.mono_set
  have hsub : cells i ⊆ A := by
    rw [hcover]
    exact Set.subset_iUnion₂ (s := fun j (_ : j ∈ S) => cells j) i hi
  exact hsub

/-- Summing the exact per-cell costs over the source number of dyadic
product cells contributes the `128 K L^3` prefactor. -/
theorem trilinearDyadicCellSumBound
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (L kL X h : ℝ)
    (cellCost : ι → ℝ) (hkL : 0 ≤ kL) (hX : 0 ≤ X)
    (hcount : (S.card : ℝ) ≤ 8 * L ^ 3)
    (hcell : ∀ i ∈ S,
      cellCost i ≤ 16 * kL * Real.sqrt X * X ^ (-h / 16)) :
    (∑ i ∈ S, cellCost i) ≤
      128 * kL * L ^ 3 * Real.sqrt X * X ^ (-h / 16) := by
  have htermNonneg : 0 ≤ 16 * kL * Real.sqrt X * X ^ (-h / 16) := by
    positivity
  calc
    (∑ i ∈ S, cellCost i) ≤
        ∑ i ∈ S, 16 * kL * Real.sqrt X * X ^ (-h / 16) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcell i hi
    _ = (S.card : ℝ) * (16 * kL * Real.sqrt X * X ^ (-h / 16)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 * L ^ 3) * (16 * kL * Real.sqrt X * X ^ (-h / 16)) :=
      mul_le_mul_of_nonneg_right hcount htermNonneg
    _ = 128 * kL * L ^ 3 * Real.sqrt X * X ^ (-h / 16) := by ring

/-- The same finite summation applies uniformly to all cells after the
small-mass and large-mass cases have each been bounded by the source maximum. -/
theorem trilinearDyadicCellSumBound_max
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (L kL X D : ℝ)
    (cellCost : ι → ℝ) (hkL : 0 ≤ kL) (hX : 0 ≤ X) (hD : 0 ≤ D)
    (hcount : (S.card : ℝ) ≤ 8 * L ^ 3)
    (hcell : ∀ i ∈ S, cellCost i ≤ 16 * kL * Real.sqrt X * D) :
    (∑ i ∈ S, cellCost i) ≤ 128 * kL * L ^ 3 * Real.sqrt X * D := by
  have htermNonneg : 0 ≤ 16 * kL * Real.sqrt X * D := by positivity
  calc
    (∑ i ∈ S, cellCost i) ≤
        ∑ i ∈ S, 16 * kL * Real.sqrt X * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcell i hi
    _ = (S.card : ℝ) * (16 * kL * Real.sqrt X * D) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 * L ^ 3) * (16 * kL * Real.sqrt X * D) :=
      mul_le_mul_of_nonneg_right hcount htermNonneg
    _ = 128 * kL * L ^ 3 * Real.sqrt X * D := by ring

/-- The three possible small-factor regions, each bounded by the exact
`2 K_C L_X^{b_C} X^(15/32)` estimate, together contribute the source factor
`6 K_C L_X^{b_C} sqrt(X) X^(-eps/16)`. -/
theorem trilinearThreeSmallFactorDecayBound
    (X eps kL s₁ s₂ s₃ : ℝ) (hX : 1 < X)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 3 / 16) (hkL : 0 ≤ kL)
    (hs₁ : s₁ ≤ 2 * kL * X ^ ((15 : ℝ) / 32))
    (hs₂ : s₂ ≤ 2 * kL * X ^ ((15 : ℝ) / 32))
    (hs₃ : s₃ ≤ 2 * kL * X ^ ((15 : ℝ) / 32)) :
    s₁ + s₂ + s₃ ≤ 6 * kL * Real.sqrt X * X ^ (-eps / 16) := by
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hExponent : (15 : ℝ) / 32 ≤ 1 / 2 - eps / 16 := by nlinarith
  have hpower : X ^ ((15 : ℝ) / 32) ≤
      Real.sqrt X * X ^ (-eps / 16) := by
    calc
      X ^ ((15 : ℝ) / 32) ≤ X ^ (1 / 2 - eps / 16) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) hExponent
      _ = Real.sqrt X * X ^ (-eps / 16) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]
        congr 1
        ring
  calc
    s₁ + s₂ + s₃ ≤
        2 * kL * X ^ ((15 : ℝ) / 32) +
          2 * kL * X ^ ((15 : ℝ) / 32) +
          2 * kL * X ^ ((15 : ℝ) / 32) := by
      exact add_le_add (add_le_add hs₁ hs₂) hs₃
    _ = 6 * kL * X ^ ((15 : ℝ) / 32) := by ring
    _ ≤ 6 * kL * Real.sqrt X * X ^ (-eps / 16) := by
      have hcoeff : 0 ≤ 6 * kL := by positivity
      calc
        6 * kL * X ^ ((15 : ℝ) / 32) ≤
            6 * kL * (Real.sqrt X * X ^ (-eps / 16)) :=
          mul_le_mul_of_nonneg_left hpower hcoeff
        _ = 6 * kL * Real.sqrt X * X ^ (-eps / 16) := by ring

/-- Finite assembly of the source small-factor estimate and the large dyadic
cells. The exact two level estimates remain the explicit cell premises; once
they are supplied, the source `J_C=2^8 K_C` prefactor follows without a limit
or any unrecorded analytic input. -/
theorem trilinearDyadicAndSmallFactorAssembly
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (L kL X eps delta s₁ s₂ s₃ : ℝ)
    (cellCost : ι → ℝ)
    (hX : 1 < X) (hL : 1 ≤ L) (hkL : 0 ≤ kL)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 3 / 16)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcount : (S.card : ℝ) ≤ 8 * L ^ 3)
    (hcell : ∀ i ∈ S,
      cellCost i ≤ 16 * kL * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)))
    (hs₁ : s₁ ≤ 2 * kL * X ^ ((15 : ℝ) / 32))
    (hs₂ : s₂ ≤ 2 * kL * X ^ ((15 : ℝ) / 32))
    (hs₃ : s₃ ≤ 2 * kL * X ^ ((15 : ℝ) / 32)) :
    s₁ + s₂ + s₃ + (∑ i ∈ S, cellCost i) ≤
      256 * kL * L ^ 3 * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by
  have hsmall := trilinearThreeSmallFactorDecayBound X eps kL s₁ s₂ s₃
    hX heps0 heps1 hkL hs₁ hs₂ hs₃
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  let D := max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ))
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hcell' : ∀ i ∈ S, cellCost i ≤ 16 * kL * Real.sqrt X * D := by
    intro i hi
    simpa [D] using hcell i hi
  have hlarge := trilinearDyadicCellSumBound_max S L kL X D cellCost
    hkL hXpos.le hDnonneg hcount hcell'
  have hsmallD : s₁ + s₂ + s₃ ≤ 6 * kL * Real.sqrt X * D := by
    calc
      s₁ + s₂ + s₃ ≤ 6 * kL * Real.sqrt X * X ^ (-eps / 16) := hsmall
      _ ≤ 6 * kL * Real.sqrt X * D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 6 * kL * Real.sqrt X)
        dsimp [D]
        exact le_max_left _ _
  have hLcube : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hsmallScaled : s₁ + s₂ + s₃ ≤ 6 * kL * L ^ 3 * Real.sqrt X * D := by
    calc
      s₁ + s₂ + s₃ ≤ 6 * kL * Real.sqrt X * D := hsmallD
      _ = (6 * kL * Real.sqrt X * D) * 1 := by ring
      _ ≤ (6 * kL * Real.sqrt X * D) * L ^ 3 :=
        mul_le_mul_of_nonneg_left hLcube (by positivity)
      _ = 6 * kL * L ^ 3 * Real.sqrt X * D := by ring
  have hlarge' : (∑ i ∈ S, cellCost i) ≤
      128 * kL * L ^ 3 * Real.sqrt X * D := by
    exact hlarge
  have hbase : 0 ≤ kL * L ^ 3 * Real.sqrt X * D := by positivity
  calc
    s₁ + s₂ + s₃ + (∑ i ∈ S, cellCost i) ≤
        6 * kL * L ^ 3 * Real.sqrt X * D +
          128 * kL * L ^ 3 * Real.sqrt X * D :=
      add_le_add hsmallScaled hlarge'
    _ ≤ 256 * kL * L ^ 3 * Real.sqrt X * D := by nlinarith [hbase]
    _ = 256 * kL * L ^ 3 * Real.sqrt X *
        max (X ^ (-eps / 16)) (delta ^ (1 / 16 : ℝ)) := by rfl

end

end FractionalPrimes.Literature.DirichletMean

end

#print axioms FractionalPrimes.Literature.DirichletMean.trilinearLargeDyadicCellExponentBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicCellIntegral_le_levelVolume
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearLargeDyadicCellIntegralBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicTripleCardBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLevelCutoffBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLevelIndex_lt_cutoff
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLevelBounds
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLevel_unique
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicScalarCell_measurable
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicScalarCell_disjoint
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLevel_mem_range
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicTripleCell_measurable
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicTripleCell_disjoint
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicTripleCell_mem_finite_cover
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLargeFactorDomain_measurable
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLargeFactorCell_measurable
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLargeFactorCell_disjoint
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLargeFactorDomain_eq_finiteCells
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLargeFactorDomain_integral_eq_sum
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicCellSumBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicDecayIdentity
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearSmallMassDyadicCellIntegralBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearLargeMassDyadicCellIntegralBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicCellIntegralBound_by_mass
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearThreeSmallFactorDecayBound
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicCellSumBound_max
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicAndSmallFactorAssembly
#print axioms FractionalPrimes.Literature.DirichletMean.trilinearDyadicLevelTripleCardBound
