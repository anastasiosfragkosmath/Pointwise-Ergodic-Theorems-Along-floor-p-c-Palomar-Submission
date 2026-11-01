module
public import FractionalPrimes.Literature.Reciprocal.TwistedMobiusFactorOfFixedHalfPlane
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section

noncomputable section

open Finset MeasureTheory Set
open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Uniformity

namespace FractionalPrimes.Literature.Reciprocal

/-- The zero-frequency Möbius character coefficient, as used in `lml:global-mobius`.
The imported shifted coefficient gives the character its Dirichlet extension by zero. -/
def globalMobiusCharacterCoefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  twistedMobiusRectangleCoefficient 1 χ 0 n

/-- The sharp real-cutoff sum `M_χ(x)` from blueprint item `lml:global-mobius`. -/
def globalMobiusCharacterSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), globalMobiusCharacterCoefficient χ n

@[simp]
theorem globalMobiusCharacterCoefficient_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) :
    globalMobiusCharacterCoefficient χ n =
      (ArithmeticFunction.moebius n : ℂ) * dirichletCharacterNatHom χ n := by
  simp [globalMobiusCharacterCoefficient, twistedMobiusRectangleCoefficient,
    shiftedCharacterMobiusCoefficient, mobiusMultiplierCoefficient, hn]

private theorem globalMobiusCharacterCoefficient_norm_le_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖globalMobiusCharacterCoefficient χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [globalMobiusCharacterCoefficient, twistedMobiusRectangleCoefficient,
      shiftedCharacterMobiusCoefficient, mobiusMultiplierCoefficient]
  · rw [globalMobiusCharacterCoefficient_eq χ hn, norm_mul]
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    have hχ := dirichletCharacterNatHom_norm_le_one χ hn
    calc
      ‖(ArithmeticFunction.moebius n : ℂ)‖ *
          ‖dirichletCharacterNatHom χ n‖ ≤ 1 * 1 :=
        mul_le_mul hμ hχ (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

private def globalMobiusWeightedCoefficient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  globalMobiusCharacterCoefficient χ n * inverseSqrtWeight (n : ℝ)

private def globalMobiusCutoffSequence {q : ℕ} [NeZero q]
    (N : ℝ) (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if N < (n : ℝ) then globalMobiusWeightedCoefficient χ n else 0

private theorem globalMobiusPrefix_cutoff_eq_Ioc
    (m k : ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 0 k, if m < n then b n else 0) =
      ∑ n ∈ Finset.Ioc m k, b n := by
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  omega

private theorem globalMobiusCutoffPrefix_eq_Ioc {N z : ℝ}
    (hN : 0 ≤ N) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 0 (Nat.floor z), globalMobiusCutoffSequence N χ n) =
      ∑ n ∈ Finset.Ioc (Nat.floor N) (Nat.floor z),
        globalMobiusWeightedCoefficient χ n := by
  have hterms (n : ℕ) : globalMobiusCutoffSequence N χ n =
      (if Nat.floor N < n then globalMobiusWeightedCoefficient χ n else 0) := by
    have hcond : (Nat.floor N < n) ↔ N < (n : ℝ) := Nat.floor_lt hN
    by_cases hn : Nat.floor N < n
    · simp [globalMobiusCutoffSequence, hcond.mp hn, hn]
    · simp [globalMobiusCutoffSequence, hcond, hn]
  calc
    _ = ∑ n ∈ Finset.Icc 0 (Nat.floor z),
          (if Nat.floor N < n then globalMobiusWeightedCoefficient χ n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterms n
    _ = ∑ n ∈ Finset.Ioc (Nat.floor N) (Nat.floor z),
          globalMobiusWeightedCoefficient χ n :=
      globalMobiusPrefix_cutoff_eq_Ioc (Nat.floor N) (Nat.floor z)
        (globalMobiusWeightedCoefficient χ)

/-- The interval estimate at fixed `MUF` parameters and witnesses. -/
def MobiusUniformityAt (α A B D Cμ Xμ : ℝ) : Prop :=
  ∀ {q : ℕ} [NeZero q] {X L : ℝ}
    (hXμ : Xμ ≤ X) (hXL : X ^ α ≤ L) (hLX : L ≤ X)
    (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
    (r : ℕ) (hr : 1 ≤ r) (hrX : (r : ℝ) ≤ (Real.log X) ^ B)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ X ^ A)
    {u v : ℝ} (huL : L ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * L),
    ‖∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        twistedMobiusRectangleCoefficient r χ t n *
          inverseSqrtWeight (n : ℝ)‖ ≤
      Cμ * Real.sqrt L * (Real.log X) ^ (-D)

/-- Lean form of the scalar Möbius uniformity premise `MUF`, with real
endpoints encoding every half-open interval `(u,v] ⊆ (L,2L]`. -/
def MobiusUniformity : Prop :=
  ∀ {α A B D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
      (hA : 0 < A) (hB : 0 < B) (hD : 0 < D),
    ∃ Cμ Xμ : ℝ, 0 < Cμ ∧ 3 ≤ Xμ ∧
      (∀ {X : ℝ}, Xμ ≤ X → (Real.log X) ^ B ≤ X) ∧
      MobiusUniformityAt α A B D Cμ Xμ

/-- Square-root cancellation identity for positive arguments. -/
private theorem sqrt_mul_inverse_sqrt {y : ℝ} (hy : 0 < y) :
    Real.sqrt y * y ^ (-1 / 2 : ℝ) = 1 := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_add hy]
  have hpow : (1 / 2 : ℝ) + (-1 / 2 : ℝ) = 0 := by ring
  rw [hpow, Real.rpow_zero]

private theorem globalMobiusWeightedPrefix_bound
    {B E c Xμ x N : ℝ} {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hMUF : MobiusUniformityAt (1 / 3) 1 B E c Xμ)
    (hXμ3 : 3 ≤ Xμ) (hXμ : Xμ ≤ x)
    (hNlow : x ^ (1 / 3 : ℝ) ≤ N) (hNx : N ≤ x)
    (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log x) ^ B)
    (hwone : 1 ≤ Real.log x) (hB : 0 < B) (hE : 0 < E)
    {z : ℝ} (hz : z ∈ Set.Icc N (2 * N)) :
    ‖∑ n ∈ Finset.Icc 0 (Nat.floor z), globalMobiusCutoffSequence N χ n‖ ≤
      c * Real.sqrt N * (Real.log x) ^ (-E) := by
  have hNpos : 0 < N := by
    have hxpos : 0 < x := by linarith [hXμ3, hXμ]
    have hpow : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hxpos _
    linarith
  have hlogpow : 1 ≤ (Real.log x) ^ B := by
    exact Real.one_le_rpow hwone hB.le
  have hxpos : 0 < x := by linarith [hXμ3, hXμ]
  have hMuf := hMUF (X := x) (L := N) hXμ hNlow hNx hq hqX
    (r := 1)
    (by norm_num) (by exact_mod_cast hlogpow) χ 0
    (by simpa [Real.rpow_one] using (le_of_lt hxpos))
    (u := N) (v := z) le_rfl hz.1 hz.2
  have hcutoff := globalMobiusCutoffPrefix_eq_Ioc (N := N) (z := z)
    (le_of_lt hNpos) (χ := χ)
  rw [hcutoff]
  simpa [globalMobiusWeightedCoefficient, globalMobiusCharacterCoefficient] using hMuf

private theorem globalMobiusBlock_bound
    {B E c Xμ x N : ℝ} {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hMUF : MobiusUniformityAt (1 / 3) 1 B E c Xμ)
    (hc : 0 < c) (hXμ3 : 3 ≤ Xμ) (hXμ : Xμ ≤ x)
    (hNlow : x ^ (1 / 3 : ℝ) ≤ N) (hNx : N ≤ x)
    (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log x) ^ B)
    (hwone : 1 ≤ Real.log x) (hB : 0 < B) (hE : 0 < E) :
    ‖∑ n ∈ Finset.Ioc (Nat.floor N) (Nat.floor (2 * N)),
        globalMobiusCharacterCoefficient χ n‖ ≤
      3 * c * N * (Real.log x) ^ (-E) := by
  have hxpos : 0 < x := by linarith [hXμ3, hXμ]
  have hNpos : 0 < N := by
    have hpow : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hxpos _
    linarith
  have h2Npos : 0 < 2 * N := by positivity
  have h2Nle : N ≤ 2 * N := by nlinarith
  let f : ℝ → ℂ := fun t => (Real.sqrt t : ℂ)
  have hf' (t : ℝ) (ht : t ≠ 0) :
      HasDerivAt f (((1 / (2 * Real.sqrt t) : ℝ) : ℂ)) t := by
    simpa [f] using (Real.hasDerivAt_sqrt ht).ofReal_comp
  have hf_diff : ∀ t ∈ Set.Icc N (2 * N), DifferentiableAt ℝ f t := by
    intro t ht
    exact (hf' t (ne_of_gt (lt_of_lt_of_le hNpos ht.1))).differentiableAt
  have hfderiv_cont : ContinuousOn (fun t : ℝ =>
      ((1 / (2 * Real.sqrt t) : ℝ) : ℂ)) (Set.Icc N (2 * N)) := by
    have hreal : ContinuousOn (fun t : ℝ => (1 : ℝ) / (2 * Real.sqrt t))
        (Set.Icc N (2 * N)) := by
      refine continuousOn_const.div₀ ?_ ?_
      · fun_prop
      · intro t ht
        have htpos : 0 < t := lt_of_lt_of_le hNpos ht.1
        positivity
    exact Complex.continuous_ofReal.comp_continuousOn hreal
  have hf_int : IntegrableOn (deriv f) (Set.Icc N (2 * N)) := by
    have hcont : ContinuousOn (deriv f) (Set.Icc N (2 * N)) := by
      apply hfderiv_cont.congr
      intro t ht
      exact (hf' t (ne_of_gt (lt_of_lt_of_le hNpos ht.1))).deriv
    exact hcont.integrableOn_compact isCompact_Icc

  have hprefix (z : ℝ) (hz : z ∈ Set.Icc N (2 * N)) :
      ‖∑ n ∈ Finset.Icc 0 (Nat.floor z), globalMobiusCutoffSequence N χ n‖ ≤
        c * Real.sqrt N * (Real.log x) ^ (-E) :=
    globalMobiusWeightedPrefix_bound χ hMUF hXμ3 hXμ hNlow hNx hq hqX hwone hB hE hz
  let M : ℝ := c * Real.sqrt N * (Real.log x) ^ (-E)
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  let a : ℕ → ℂ := globalMobiusCutoffSequence N χ
  have hprefixN : (∑ n ∈ Finset.Icc 0 (Nat.floor N), a n) = 0 := by
    rw [globalMobiusCutoffPrefix_eq_Ioc (le_of_lt hNpos) χ]
    simp
  have habel := sum_mul_eq_sub_sub_integral_mul a (le_of_lt hNpos) h2Nle hf_diff hf_int
  have hterms :
      (∑ n ∈ Finset.Ioc (Nat.floor N) (Nat.floor (2 * N)),
        f (n : ℝ) * a n) =
      ∑ n ∈ Finset.Ioc (Nat.floor N) (Nat.floor (2 * N)),
        globalMobiusCharacterCoefficient χ n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnN : N < (n : ℝ) := (Nat.floor_lt (le_of_lt hNpos)).1
      (Finset.mem_Ioc.mp hn).1
    have hroot : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) = 1 :=
      sqrt_mul_inverse_sqrt (lt_trans hNpos hnN)
    have hrootC : ((Real.sqrt (n : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hroot
    calc
      f (n : ℝ) * a n =
          globalMobiusCharacterCoefficient χ n *
            ((Real.sqrt (n : ℝ) * (n : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
        simp [a, globalMobiusCutoffSequence, globalMobiusWeightedCoefficient,
          inverseSqrtWeight, f, hnN]
        ring
      _ = globalMobiusCharacterCoefficient χ n := by rw [hrootC, mul_one]
  rw [hterms] at habel
  have hprefix2N :
      ‖∑ n ∈ Finset.Icc 0 (Nat.floor (2 * N)), a n‖ ≤ M := by
    simpa [a, M] using hprefix (2 * N) ⟨h2Nle, le_rfl⟩
  have hprefixIcc (t : ℝ) (ht : t ∈ Set.Icc N (2 * N)) :
      ‖∑ n ∈ Finset.Icc 0 (Nat.floor t), a n‖ ≤ M := by
    simpa [a, M] using hprefix t ht
  have hderiv_value (t : ℝ) (ht : t ∈ Set.Icc N (2 * N)) :
      deriv f t = (((1 / (2 * Real.sqrt t) : ℝ) : ℂ)) :=
    (hf' t (ne_of_gt (lt_of_lt_of_le hNpos ht.1))).deriv
  have hderiv_norm_bound (t : ℝ) (ht : t ∈ Set.Icc N (2 * N)) :
      ‖deriv f t‖ ≤ 1 / (2 * Real.sqrt N) := by
    rw [hderiv_value t ht, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ (1 : ℝ) / (2 * Real.sqrt t) by positivity)]
    have hsqrt : Real.sqrt N ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
    have hdenpos : 0 < 2 * Real.sqrt N := by positivity
    have hdenle : 2 * Real.sqrt N ≤ 2 * Real.sqrt t := by nlinarith
    exact (one_div_le_one_div_of_le hdenpos hdenle)
  have hIntBound :
      ‖∫ t in N..(2 * N), deriv f t *
          (∑ n ∈ Finset.Icc 0 (Nat.floor t), a n)‖ ≤ M * Real.sqrt N / 2 := by
    have hpoint (t : ℝ) (ht : t ∈ Set.uIoc N (2 * N)) :
        ‖deriv f t * (∑ n ∈ Finset.Icc 0 (Nat.floor t), a n)‖ ≤
          M / (2 * Real.sqrt N) := by
      have ht' : t ∈ Set.Icc N (2 * N) := by
        rw [Set.uIoc_of_le h2Nle] at ht
        exact ⟨le_of_lt ht.1, ht.2⟩
      rw [norm_mul]
      have h1 := hderiv_norm_bound t ht'
      have h2 := hprefixIcc t ht'
      calc
        ‖deriv f t‖ * ‖∑ n ∈ Finset.Icc 0 (Nat.floor t), a n‖ ≤
            (1 / (2 * Real.sqrt N)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = M / (2 * Real.sqrt N) := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := N) (b := 2 * N) (f := fun t => deriv f t *
        (∑ n ∈ Finset.Icc 0 (Nat.floor t), a n)) hpoint
    have hlen : |2 * N - N| = N := by rw [show 2 * N - N = N by ring, abs_of_pos hNpos]
    calc
      _ ≤ (M / (2 * Real.sqrt N)) * |2 * N - N| := h
      _ = M * Real.sqrt N / 2 := by
        rw [hlen]
        have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
        field_simp [ne_of_gt hNpos]
        nlinarith [hsq]

  have hsumNorm :
      ‖∑ n ∈ Finset.Ioc (Nat.floor N) (Nat.floor (2 * N)),
          globalMobiusCharacterCoefficient χ n‖ ≤
        Real.sqrt (2 * N) * M + M * Real.sqrt N / 2 := by
    rw [habel]
    have htermN : ∑ n ∈ Finset.Icc 0 (Nat.floor N), a n = 0 := hprefixN
    rw [htermN]
    calc
      _ ≤ ‖f (2 * N) * (∑ n ∈ Finset.Icc 0 (Nat.floor (2 * N)), a n)‖ +
          ‖∫ t in Set.Ioc N (2 * N), deriv f t *
            (∑ n ∈ Finset.Icc 0 (Nat.floor t), a n)‖ := by
              simpa only [mul_zero, sub_zero] using norm_sub_le _ _
      _ ≤ Real.sqrt (2 * N) * M + M * Real.sqrt N / 2 := by
            have hterm :
                ‖f (2 * N) * (∑ n ∈ Finset.Icc 0 (Nat.floor (2 * N)), a n)‖ ≤
                  Real.sqrt (2 * N) * M := by
              have hfendpoint : ‖f (2 * N)‖ = Real.sqrt (2 * N) := by
                simp [f, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]
              rw [norm_mul, hfendpoint]
              exact mul_le_mul_of_nonneg_left hprefix2N (Real.sqrt_nonneg _)
            have hintset :
                ‖∫ t in Set.Ioc N (2 * N), deriv f t *
                  (∑ n ∈ Finset.Icc 0 (Nat.floor t), a n)‖ =
                ‖∫ t in N..(2 * N), deriv f t *
                  (∑ n ∈ Finset.Icc 0 (Nat.floor t), a n)‖ := by
              rw [← intervalIntegral.integral_of_le (by linarith : N ≤ 2 * N)]
            rw [hintset]
            exact add_le_add hterm hIntBound
  have hsqrtn : Real.sqrt (2 * N) ≤ 2 * Real.sqrt N := by
    have hsq : 2 * N ≤ (2 * Real.sqrt N) ^ 2 := by
      nlinarith [Real.sq_sqrt hNpos.le]
    calc
      Real.sqrt (2 * N) ≤ Real.sqrt ((2 * Real.sqrt N) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt N := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.sqrt (2 * N) * M + M * Real.sqrt N / 2 := hsumNorm
    _ ≤ 3 * Real.sqrt N * M := by
      calc
        Real.sqrt (2 * N) * M + M * Real.sqrt N / 2 ≤
            (2 * Real.sqrt N) * M + M * Real.sqrt N / 2 := by
              exact add_le_add (mul_le_mul_of_nonneg_right hsqrtn hMnonneg) le_rfl
        _ ≤ 3 * Real.sqrt N * M := by
          have hprod : 0 ≤ Real.sqrt N * M := mul_nonneg (Real.sqrt_nonneg N) hMnonneg
          calc
            (2 * Real.sqrt N) * M + M * Real.sqrt N / 2 =
                (5 / 2 : ℝ) * (Real.sqrt N * M) := by ring
            _ ≤ 3 * (Real.sqrt N * M) := by nlinarith [hprod]
            _ = 3 * Real.sqrt N * M := by ring
    _ = 3 * c * N * (Real.log x) ^ (-E) := by
      dsimp [M]
      calc
        3 * Real.sqrt N * (c * Real.sqrt N * (Real.log x) ^ (-E)) =
            3 * c * (Real.sqrt N * Real.sqrt N) * (Real.log x) ^ (-E) := by ring
        _ = 3 * c * N * (Real.log x) ^ (-E) := by
          rw [Real.mul_self_sqrt hNpos.le]

private theorem globalMobiusCharacterSum_eq_zero_Icc
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    globalMobiusCharacterSum χ x =
      ∑ n ∈ Finset.Icc 0 (Nat.floor x), globalMobiusCharacterCoefficient χ n := by
  have hzero : globalMobiusCharacterCoefficient χ 0 = 0 := by
    simp [globalMobiusCharacterCoefficient, twistedMobiusRectangleCoefficient,
      shiftedCharacterMobiusCoefficient, mobiusMultiplierCoefficient]
  have hfin : Finset.Icc 0 (Nat.floor x) =
      insert 0 (Finset.Icc 1 (Nat.floor x)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [globalMobiusCharacterSum, hfin, Finset.sum_insert (by simp), hzero]
  simp

private theorem globalMobiusCharacterInterval_eq_sub
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        globalMobiusCharacterCoefficient χ n) =
      globalMobiusCharacterSum χ v - globalMobiusCharacterSum χ u := by
  rw [globalMobiusCharacterSum_eq_zero_Icc χ v,
    globalMobiusCharacterSum_eq_zero_Icc χ u]
  have hfloor : Nat.floor u ≤ Nat.floor v := Nat.floor_mono huv
  have hunion : Finset.Icc 0 (Nat.floor v) =
      Finset.Icc 0 (Nat.floor u) ∪ Finset.Ioc (Nat.floor u) (Nat.floor v) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 (Nat.floor u))
      (Finset.Ioc (Nat.floor u) (Nat.floor v)) := by
    apply Finset.disjoint_left.mpr
    intro n hn₁ hn₂
    simp only [Finset.mem_Icc] at hn₁
    simp only [Finset.mem_Ioc] at hn₂
    omega
  have hsum := congrArg (fun s : Finset ℕ =>
    ∑ n ∈ s, globalMobiusCharacterCoefficient χ n) hunion
  rw [Finset.sum_union hdisj] at hsum
  rw [hsum]
  abel

private def globalMobiusDyadicEndpoint (x : ℝ) (j : ℕ) : ℝ :=
  x / (2 : ℝ) ^ j

private theorem globalMobiusDyadicEndpoint_succ (x : ℝ) (j : ℕ) :
    globalMobiusDyadicEndpoint x (j + 1) =
      globalMobiusDyadicEndpoint x j / 2 := by
  rw [globalMobiusDyadicEndpoint, globalMobiusDyadicEndpoint, pow_succ]
  ring

private theorem globalMobiusDyadicScale_sum (x : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, globalMobiusDyadicEndpoint x (j + 1)) =
      x - globalMobiusDyadicEndpoint x J := by
  induction J with
  | zero => simp [globalMobiusDyadicEndpoint]
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have hrel : globalMobiusDyadicEndpoint x J =
          2 * globalMobiusDyadicEndpoint x (J + 1) := by
        rw [globalMobiusDyadicEndpoint_succ]
        ring
      rw [hrel]
      ring

private theorem globalMobiusDyadicDifference_sum
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      (globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x j) -
        globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x (j + 1)))) =
      globalMobiusCharacterSum χ x -
        globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x J) := by
  induction J with
  | zero => simp [globalMobiusDyadicEndpoint]
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [globalMobiusDyadicEndpoint]
      abel

private theorem globalMobiusCharacterSum_norm_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 ≤ x) :
    ‖globalMobiusCharacterSum χ x‖ ≤ x := by
  calc
    ‖globalMobiusCharacterSum χ x‖ ≤
        ∑ n ∈ Finset.Icc 1 (Nat.floor x),
          ‖globalMobiusCharacterCoefficient χ n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (Nat.floor x), (1 : ℝ) :=
      Finset.sum_le_sum fun n hn => globalMobiusCharacterCoefficient_norm_le_one χ n
    _ = Nat.floor x := by simp
    _ ≤ x := Nat.floor_le hx

private def globalMobiusDyadicIndex (x : ℝ) : ℕ :=
  Nat.log 2 (Nat.floor (Real.sqrt x))

private theorem globalMobiusDyadicIndex_eq_floor_logb
    {x : ℝ} (hx : 64 ≤ x) :
    globalMobiusDyadicIndex x = Nat.floor (Real.logb 2 (Real.sqrt x)) := by
  have hxpos : 0 < x := by linarith
  have hrootpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hroot8 : 8 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    norm_num at h ⊢
    exact h
  have hfloor8 : 8 ≤ Nat.floor (Real.sqrt x) := by
    rw [Nat.le_floor_iff' (by norm_num : (8 : ℕ) ≠ 0)]
    exact hroot8
  have hlog3 : 3 ≤ Nat.log 2 (Nat.floor (Real.sqrt x)) :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by norm_num at hfloor8 ⊢; exact hfloor8)
  have hlognonneg : 0 ≤ Real.logb 2 (Real.sqrt x) :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) hrootpos).2
      (by linarith [hroot8])
  have hpowLowerNat : (2 : ℕ) ^ Nat.log 2 (Nat.floor (Real.sqrt x)) ≤
      Nat.floor (Real.sqrt x) := by
    exact Nat.pow_log_le_self 2 (by omega : Nat.floor (Real.sqrt x) ≠ 0)
  have hpowLower :
      (2 : ℝ) ^ (Nat.log 2 (Nat.floor (Real.sqrt x)) : ℝ) ≤ Real.sqrt x := by
    have hfloor := Nat.floor_le (Real.sqrt_nonneg x)
    have hpowLowerCast :
        (2 : ℝ) ^ (Nat.log 2 (Nat.floor (Real.sqrt x)) : ℝ) ≤
          (Nat.floor (Real.sqrt x) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hpowLowerNat
    exact hpowLowerCast.trans hfloor
  have hlogLower :
      (Nat.log 2 (Nat.floor (Real.sqrt x)) : ℝ) ≤ Real.logb 2 (Real.sqrt x) := by
    exact (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hrootpos).2 hpowLower
  have hpowUpperNat : Nat.floor (Real.sqrt x) <
      2 ^ (Nat.log 2 (Nat.floor (Real.sqrt x)) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
  have hpowUpper :
      (Nat.floor (Real.sqrt x) : ℝ) + 1 ≤
        (2 : ℝ) ^ (Nat.log 2 (Nat.floor (Real.sqrt x)) + 1) := by
    exact_mod_cast Nat.succ_le_of_lt hpowUpperNat
  have hfloor_lt : Real.sqrt x < (Nat.floor (Real.sqrt x) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hroot_lt_pow :
      Real.sqrt x < (2 : ℝ) ^ (Nat.log 2 (Nat.floor (Real.sqrt x)) + 1) :=
    hfloor_lt.trans_le hpowUpper
  have hroot_lt_rpow :
      Real.sqrt x <
        (2 : ℝ) ^ ((Nat.log 2 (Nat.floor (Real.sqrt x)) + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact hroot_lt_pow
  have hlogUpper :
      Real.logb 2 (Real.sqrt x) <
        (Nat.log 2 (Nat.floor (Real.sqrt x)) : ℝ) + 1 := by
    convert (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hrootpos).2
      hroot_lt_rpow using 1 <;> norm_cast
  have hfloorEq := (Nat.floor_eq_iff hlognonneg).2 ⟨hlogLower, hlogUpper⟩
  exact hfloorEq.symm

private theorem globalMobiusDyadicIndex_bounds
    {x : ℝ} (hx : 64 ≤ x) :
    3 ≤ globalMobiusDyadicIndex x ∧
      (2 : ℝ) ^ globalMobiusDyadicIndex x ≤ Real.sqrt x ∧
      Real.sqrt x < (2 : ℝ) ^ (globalMobiusDyadicIndex x + 1) := by
  have hxpos : 0 < x := by linarith
  have hrootpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hroot8 : 8 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    norm_num at h ⊢
    exact h
  have hfloor8 : 8 ≤ Nat.floor (Real.sqrt x) := by
    rw [Nat.le_floor_iff' (by norm_num : (8 : ℕ) ≠ 0)]
    exact hroot8
  have hJ3 : 3 ≤ globalMobiusDyadicIndex x := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      (by norm_num at hfloor8 ⊢; exact hfloor8)
  have hnz : Nat.floor (Real.sqrt x) ≠ 0 := by omega
  have hpowJNat : (2 : ℕ) ^ globalMobiusDyadicIndex x ≤ Nat.floor (Real.sqrt x) := by
    exact Nat.pow_log_le_self 2 hnz
  have hpowJ : (2 : ℝ) ^ globalMobiusDyadicIndex x ≤ Real.sqrt x := by
    have hfloor := Nat.floor_le (Real.sqrt_nonneg x)
    have hpowJCast :
        ((2 : ℕ) ^ globalMobiusDyadicIndex x : ℝ) ≤
          (Nat.floor (Real.sqrt x) : ℝ) := by
      exact_mod_cast hpowJNat
    exact hpowJCast.trans hfloor
  have hpowUpperNat : Nat.floor (Real.sqrt x) <
      2 ^ (globalMobiusDyadicIndex x + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
  have hpowUpper : (Nat.floor (Real.sqrt x) : ℝ) + 1 ≤
      (2 : ℝ) ^ (globalMobiusDyadicIndex x + 1) := by
    exact_mod_cast Nat.succ_le_of_lt hpowUpperNat
  have hfloor_lt : Real.sqrt x < (Nat.floor (Real.sqrt x) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  exact ⟨hJ3, hpowJ, hfloor_lt.trans_le hpowUpper⟩

noncomputable def globalMobiusSqrtLogThreshold (E : ℝ) : ℝ :=
  Real.exp (8 * Real.log (2 * logAbsorptionM (1 / 4) E))

private theorem globalMobius_sqrtLog_bound {E x : ℝ}
    (hE : 0 < E) (hx64 : 64 ≤ x)
    (hthreshold : globalMobiusSqrtLogThreshold E ≤ x) :
    2 * (Real.log x) ^ E ≤ Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlarge : (2 / (1 / 4 : ℝ)) *
      Real.log (2 * logAbsorptionM (1 / 4) E) ≤ Real.log x := by
    rw [show (2 / (1 / 4 : ℝ)) = 8 by norm_num]
    calc
      8 * Real.log (2 * logAbsorptionM (1 / 4) E) =
          Real.log (globalMobiusSqrtLogThreshold E) := by
            simp [globalMobiusSqrtLogThreshold]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hthreshold
  have habs := log_absorption_bound (a := (1 / 4 : ℝ)) (b := E) (K := 2) (X := x)
    (by norm_num) hE.le (by norm_num) hxone hlarge
  have hpow : x ^ (1 / 4 : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  exact habs.trans hpow

noncomputable def globalMobiusLargeCutoff (E Xμ : ℝ) : ℝ :=
  max 64 (max Xμ (globalMobiusSqrtLogThreshold E))

noncomputable def globalMobiusExplicitConstant (E c x0 : ℝ) : ℝ :=
  max 1 (max (3 * c + 1) ((Real.log x0) ^ E))

private theorem globalMobiusDyadicScale_bounds {x : ℝ} (hx64 : 64 ≤ x)
    {j : ℕ} (hj : j < globalMobiusDyadicIndex x) :
    x ^ (1 / 3 : ℝ) ≤ globalMobiusDyadicEndpoint x (j + 1) ∧
      globalMobiusDyadicEndpoint x (j + 1) ≤ x ∧
      2 * globalMobiusDyadicEndpoint x (j + 1) =
        globalMobiusDyadicEndpoint x j := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hJ := globalMobiusDyadicIndex_bounds hx64
  have hj1 : j + 1 ≤ globalMobiusDyadicIndex x := Nat.succ_le_of_lt hj
  have hpowjNat : (2 : ℕ) ^ (j + 1) ≤
      (2 : ℕ) ^ globalMobiusDyadicIndex x :=
    pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hj1
  have hpowj : (2 : ℝ) ^ (j + 1) ≤ Real.sqrt x := by
    have hpowjReal : (2 : ℝ) ^ (j + 1) ≤
        (2 : ℝ) ^ globalMobiusDyadicIndex x := by exact_mod_cast hpowjNat
    exact hpowjReal.trans hJ.2.1
  have hdenpos : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hsqrt_le_scale : Real.sqrt x ≤ globalMobiusDyadicEndpoint x (j + 1) := by
    rw [globalMobiusDyadicEndpoint]
    apply (le_div_iff₀ hdenpos).2
    calc
      Real.sqrt x * (2 : ℝ) ^ (j + 1) ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hpowj (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hxpos.le
  have hcube : x ^ (1 / 3 : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  have hscale_le : globalMobiusDyadicEndpoint x (j + 1) ≤ x := by
    rw [globalMobiusDyadicEndpoint]
    exact div_le_self hxpos.le
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have htwice : 2 * globalMobiusDyadicEndpoint x (j + 1) =
      globalMobiusDyadicEndpoint x j := by
    rw [globalMobiusDyadicEndpoint_succ]
    ring
  exact ⟨hcube.trans hsqrt_le_scale, hscale_le, htwice⟩

private def globalMobiusDyadicBlockSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc (Nat.floor (globalMobiusDyadicEndpoint x (j + 1)))
      (Nat.floor (globalMobiusDyadicEndpoint x j)),
    globalMobiusCharacterCoefficient χ n

private theorem globalMobiusDyadicCharacterSum_decomposition
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx64 : 64 ≤ x) :
    globalMobiusCharacterSum χ x =
      globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x
          (globalMobiusDyadicIndex x)) +
        ∑ j ∈ Finset.range (globalMobiusDyadicIndex x),
          globalMobiusDyadicBlockSum χ x j := by
  let J := globalMobiusDyadicIndex x
  have hblock (j : ℕ) (hj : j ∈ Finset.range J) :
      globalMobiusDyadicBlockSum χ x j =
        globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x j) -
          globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x (j + 1)) := by
    have hscale := globalMobiusDyadicScale_bounds hx64 (Finset.mem_range.mp hj)
    have hu_nonneg : 0 ≤ globalMobiusDyadicEndpoint x (j + 1) := by
      dsimp [globalMobiusDyadicEndpoint]
      positivity
    have huv : globalMobiusDyadicEndpoint x (j + 1) ≤
        globalMobiusDyadicEndpoint x j := by
      rw [← hscale.2.2]
      nlinarith [hscale.1]
    exact globalMobiusCharacterInterval_eq_sub χ hu_nonneg huv
  have hsumblocks :
      (∑ j ∈ Finset.range J, globalMobiusDyadicBlockSum χ x j) =
        globalMobiusCharacterSum χ x -
          globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x J) := by
    calc
      _ = ∑ j ∈ Finset.range J,
            (globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x j) -
              globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x (j + 1))) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hblock j hj
      _ = _ := globalMobiusDyadicDifference_sum χ x J
  calc
    globalMobiusCharacterSum χ x =
        globalMobiusCharacterSum χ x -
          globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x J) +
          globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x J) := by abel
    _ = (∑ j ∈ Finset.range J, globalMobiusDyadicBlockSum χ x j) +
          globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x J) := by
      rw [← hsumblocks]
    _ = globalMobiusCharacterSum χ (globalMobiusDyadicEndpoint x J) +
          ∑ j ∈ Finset.range J, globalMobiusDyadicBlockSum χ x j := by abel

/-- Explicit witness form of blueprint item `lml:global-mobius`; the cutoff and
constant are the approved choices. -/
theorem globalCharacterMobius_certificate
    (hMUF : MobiusUniformity) {E B : ℝ} (hE : 0 < E) (hB : 0 < B) :
    ∃ c Xμ x0 C : ℝ,
      0 < c ∧ 3 ≤ Xμ ∧
      (∀ {X : ℝ}, Xμ ≤ X → (Real.log X) ^ B ≤ X) ∧
      MobiusUniformityAt (1 / 3) 1 B E c Xμ ∧
      x0 = globalMobiusLargeCutoff E Xμ ∧
      64 ≤ x0 ∧ Xμ ≤ x0 ∧
      (∀ {x : ℝ}, x0 ≤ x → 2 * (Real.log x) ^ E ≤ Real.sqrt x) ∧
      C = globalMobiusExplicitConstant E c x0 ∧ 1 ≤ C ∧
      (∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
        3 ≤ x → 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
          ‖globalMobiusCharacterSum χ x‖ ≤ C * x * (Real.log x) ^ (-E)) := by
  obtain ⟨c, Xμ, hc, hXμ3, hlogrange, hMuf⟩ :=
    hMUF (α := (1 / 3 : ℝ)) (A := (1 : ℝ)) (B := B) (D := E)
      (by norm_num) (by norm_num) (by norm_num) hB hE
  let x0 := globalMobiusLargeCutoff E Xμ
  let C := globalMobiusExplicitConstant E c x0
  have hx0_64 : 64 ≤ x0 := by
    dsimp [x0, globalMobiusLargeCutoff]
    exact le_max_left _ _
  have hx0inner : max Xμ (globalMobiusSqrtLogThreshold E) ≤ x0 := by
    dsimp [x0, globalMobiusLargeCutoff]
    exact le_max_right _ _
  have hXμx0 : Xμ ≤ x0 := le_trans (le_max_left _ _) hx0inner
  have hthresholdx0 : globalMobiusSqrtLogThreshold E ≤ x0 :=
    le_trans (le_max_right _ _) hx0inner
  have hx0growth {x : ℝ} (hx0x : x0 ≤ x) :
      2 * (Real.log x) ^ E ≤ Real.sqrt x :=
    globalMobius_sqrtLog_bound hE (le_trans hx0_64 hx0x)
      (le_trans hthresholdx0 hx0x)
  have hCone : 1 ≤ C := by
    dsimp [C, globalMobiusExplicitConstant]
    exact le_max_left _ _
  have hCblock : 3 * c + 1 ≤ C := by
    dsimp [C, globalMobiusExplicitConstant]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hClog : (Real.log x0) ^ E ≤ C := by
    dsimp [C, globalMobiusExplicitConstant]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨c, Xμ, x0, C, hc, hXμ3, hlogrange, hMuf, rfl, hx0_64,
    hXμx0, ?_, rfl, hCone, ?_⟩
  · intro x hx0x
    exact hx0growth hx0x
  · intro q inst χ x hx3 hq hqX
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    by_cases hx0x : x0 ≤ x
    · let J := globalMobiusDyadicIndex x
      let small := globalMobiusDyadicEndpoint x J
      have hx64 : 64 ≤ x := le_trans hx0_64 hx0x
      have hXμx : Xμ ≤ x := le_trans hXμx0 hx0x
      have hwone : 1 ≤ Real.log x := by
        have hexp1 : Real.exp 1 < 3 := by
          have h := Real.exp_one_lt_d9
          norm_num at h ⊢
          linarith
        apply (Real.le_log_iff_exp_le hxpos).2
        exact hexp1.le.trans hx3
      have hgrowth := hx0growth hx0x
      have hJbound := globalMobiusDyadicIndex_bounds hx64
      have hdenpos : 0 < (2 : ℝ) ^ J := by positivity
      have hpowSucc : (2 : ℝ) ^ (J + 1) = 2 * (2 : ℝ) ^ J := by
        rw [pow_succ]
        ring
      have hrootLtPow : Real.sqrt x < 2 * (2 : ℝ) ^ J := by
        rw [← hpowSucc]
        exact hJbound.2.2
      have hrootSq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
      have hsmalllt : small < 2 * Real.sqrt x := by
        dsimp [small, globalMobiusDyadicEndpoint]
        apply (div_lt_iff₀ hdenpos).2
        have hmul := mul_lt_mul_of_pos_right hrootLtPow (Real.sqrt_pos.2 hxpos)
        calc
          x = Real.sqrt x * Real.sqrt x := hrootSq.symm
          _ < (2 * (2 : ℝ) ^ J) * Real.sqrt x := hmul
          _ = 2 * Real.sqrt x * (2 : ℝ) ^ J := by ring
      have hrecip : (Real.log x) ^ E * (Real.log x) ^ (-E) = 1 := by
        calc
          (Real.log x) ^ E * (Real.log x) ^ (-E) =
              (Real.log x) ^ (E + (-E)) := by rw [← Real.rpow_add hlogpos]
          _ = 1 := by rw [show E + (-E) = 0 by ring, Real.rpow_zero]
      have hlargePrefix : 2 * Real.sqrt x ≤ x * (Real.log x) ^ (-E) := by
        have hscaled : 2 ≤ Real.sqrt x * (Real.log x) ^ (-E) := by
          calc
            2 = (2 * (Real.log x) ^ E) * (Real.log x) ^ (-E) := by
              calc
                2 = 2 * ((Real.log x) ^ E * (Real.log x) ^ (-E)) := by
                  rw [hrecip]
                  ring
                _ = (2 * (Real.log x) ^ E) * (Real.log x) ^ (-E) := by ring
            _ ≤ Real.sqrt x * (Real.log x) ^ (-E) :=
              mul_le_mul_of_nonneg_right hgrowth (Real.rpow_nonneg hlogpos.le _)
        have hmul := mul_le_mul_of_nonneg_right hscaled (Real.sqrt_nonneg x)
        calc
          2 * Real.sqrt x ≤
              (Real.sqrt x * (Real.log x) ^ (-E)) * Real.sqrt x := hmul
          _ = x * (Real.log x) ^ (-E) := by
            calc
              (Real.sqrt x * (Real.log x) ^ (-E)) * Real.sqrt x =
                  (Real.sqrt x * Real.sqrt x) * (Real.log x) ^ (-E) := by ring
              _ = x * (Real.log x) ^ (-E) := by rw [hrootSq]
      have hsmall_nonneg : 0 ≤ small := by
        dsimp [small, globalMobiusDyadicEndpoint]
        positivity
      have hsmallnorm : ‖globalMobiusCharacterSum χ small‖ ≤ small :=
        globalMobiusCharacterSum_norm_le χ hsmall_nonneg
      have hsmallbound : small ≤ x * (Real.log x) ^ (-E) :=
        hsmalllt.le.trans hlargePrefix
      have hsumScales :
          (∑ j ∈ Finset.range J, globalMobiusDyadicEndpoint x (j + 1)) ≤ x := by
        rw [globalMobiusDyadicScale_sum]
        exact sub_le_self x (div_nonneg hxpos.le (by positivity))
      have hcoef_nonneg : 0 ≤ 3 * c * (Real.log x) ^ (-E) := by positivity
      have hblockBound (j : ℕ) (hj : j ∈ Finset.range J) :
          ‖globalMobiusDyadicBlockSum χ x j‖ ≤
            3 * c * globalMobiusDyadicEndpoint x (j + 1) *
              (Real.log x) ^ (-E) := by
        have hs := globalMobiusDyadicScale_bounds hx64 (Finset.mem_range.mp hj)
        have hblock := globalMobiusBlock_bound
          (B := B) (E := E) (c := c) (Xμ := Xμ) (x := x)
          (N := globalMobiusDyadicEndpoint x (j + 1)) χ hMuf hc hXμ3 hXμx
          hs.1 hs.2.1 hq hqX hwone hB hE
        unfold globalMobiusDyadicBlockSum
        rw [← hs.2.2]
        exact hblock
      have hblocksNorm :
          ‖∑ j ∈ Finset.range J, globalMobiusDyadicBlockSum χ x j‖ ≤
            3 * c * x * (Real.log x) ^ (-E) := by
        calc
          _ ≤ ∑ j ∈ Finset.range J,
                ‖globalMobiusDyadicBlockSum χ x j‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range J,
                3 * c * globalMobiusDyadicEndpoint x (j + 1) *
                  (Real.log x) ^ (-E) :=
            Finset.sum_le_sum fun j hj => hblockBound j hj
          _ = (3 * c * (Real.log x) ^ (-E)) *
                ∑ j ∈ Finset.range J, globalMobiusDyadicEndpoint x (j + 1) := by
            calc
              _ = ∑ j ∈ Finset.range J,
                    (3 * c * (Real.log x) ^ (-E)) *
                      globalMobiusDyadicEndpoint x (j + 1) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
              _ = _ := by rw [Finset.mul_sum]
          _ ≤ (3 * c * (Real.log x) ^ (-E)) * x :=
            mul_le_mul_of_nonneg_left hsumScales hcoef_nonneg
          _ = 3 * c * x * (Real.log x) ^ (-E) := by ring
      have hdecomp := globalMobiusDyadicCharacterSum_decomposition χ hx64
      have hfac_nonneg : 0 ≤ x * (Real.log x) ^ (-E) := by positivity
      calc
        ‖globalMobiusCharacterSum χ x‖ =
            ‖globalMobiusCharacterSum χ small +
              ∑ j ∈ Finset.range J, globalMobiusDyadicBlockSum χ x j‖ := by
                rw [hdecomp]
        _ ≤ ‖globalMobiusCharacterSum χ small‖ +
              ‖∑ j ∈ Finset.range J, globalMobiusDyadicBlockSum χ x j‖ :=
            norm_add_le _ _
        _ ≤ small + 3 * c * x * (Real.log x) ^ (-E) :=
            add_le_add hsmallnorm hblocksNorm
        _ ≤ x * (Real.log x) ^ (-E) + 3 * c * x * (Real.log x) ^ (-E) :=
            add_le_add hsmallbound le_rfl
        _ = (3 * c + 1) * (x * (Real.log x) ^ (-E)) := by ring
        _ ≤ C * (x * (Real.log x) ^ (-E)) :=
            mul_le_mul_of_nonneg_right hCblock hfac_nonneg
        _ = C * x * (Real.log x) ^ (-E) := by ring
    · have hxltx0 : x < x0 := lt_of_not_ge hx0x
      have hlogle : Real.log x ≤ Real.log x0 :=
        Real.log_le_log hxpos (le_of_lt hxltx0)
      have hpowle : (Real.log x) ^ E ≤ (Real.log x0) ^ E :=
        Real.rpow_le_rpow hlogpos.le hlogle hE.le
      have hrecip : (Real.log x) ^ E * (Real.log x) ^ (-E) = 1 := by
        calc
          (Real.log x) ^ E * (Real.log x) ^ (-E) =
              (Real.log x) ^ (E + (-E)) := by rw [← Real.rpow_add hlogpos]
          _ = 1 := by rw [show E + (-E) = 0 by ring, Real.rpow_zero]
      have hfac : 1 ≤ C * (Real.log x) ^ (-E) := by
        calc
          1 = (Real.log x) ^ E * (Real.log x) ^ (-E) := hrecip.symm
          _ ≤ C * (Real.log x) ^ (-E) :=
            mul_le_mul_of_nonneg_right (hpowle.trans hClog)
              (Real.rpow_nonneg hlogpos.le _)
      calc
        ‖globalMobiusCharacterSum χ x‖ ≤ x :=
          globalMobiusCharacterSum_norm_le χ hxpos.le
        _ = 1 * x := by ring
        _ ≤ (C * (Real.log x) ^ (-E)) * x :=
          mul_le_mul_of_nonneg_right hfac hxpos.le
        _ = C * x * (Real.log x) ^ (-E) := by ring

/-- The conditional global Dirichlet-character Möbius estimate in
`lml:global-mobius`. -/
theorem globalCharacterMobius
    (hMUF : MobiusUniformity) {E B : ℝ} (hE : 0 < E) (hB : 0 < B) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
        3 ≤ x → 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
          ‖globalMobiusCharacterSum χ x‖ ≤ C * x * (Real.log x) ^ (-E)) := by
  obtain ⟨c, Xμ, x0, C, hc, hXμ3, hlogrange, hMuf, hx0, hx0_64, hXμx0,
    hx0growth, hC, hCone, hbound⟩ :=
      globalCharacterMobius_certificate hMUF hE hB
  exact ⟨C, hCone, hbound⟩

end FractionalPrimes.Literature.Reciprocal

end
