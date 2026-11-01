module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletSeriesIdentity
public import FractionalPrimes.Literature.Reciprocal.PrincipalContinuedDirichletSeriesIdentity
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped LSeries.notation
open Nat.Primes

namespace FractionalPrimes.Literature.Reciprocal

/-- The prime-power logarithm series from blueprint `lrc:euler-log`, written
as the Taylor series of `-log (1-z)` at each Euler factor. -/
def continuedDirichletEulerLog {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, ∑' k : ℕ,
    (χ p * (p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)

private theorem eulerFactor_norm_lt_one {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re)
    (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
  grw [norm_mul, χ.norm_le_one p, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re,
    one_mul]
  exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)

private def natEquivIciTwo : ℕ ≃ Set.Ici (2 : ℕ) where
  toFun n := ⟨n + 2, by simp⟩
  invFun n := n.1 - 2
  left_inv n := by simp
  right_inv n := by
    apply Subtype.ext
    have hn : 2 ≤ n.1 := by
      simpa only [Set.mem_Ici] using n.2
    exact Nat.sub_add_cancel hn

private theorem tsum_nat_rpow_tail_le_integral {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ σ)⁻¹ ≤ 1 / (σ - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici (↑(1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono (by
      intro x hx
      simp only [Set.mem_Ici] at hx
      have hx' : (1 : ℝ) ≤ x := by simpa using hx
      exact Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hx'))
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioi (↑(1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith)
      (by norm_num : 0 < (↑(1 : ℕ) : ℝ))
  have hnonneg : ∀ x ∈ Ioi (↑(1 : ℕ) : ℝ), 0 ≤ x ^ (-σ) := by
    intro x hx
    have hx' : (0 : ℝ) < x := by
      exact lt_trans (by norm_num : (0 : ℝ) < (↑(1 : ℕ) : ℝ)) (mem_Ioi.mp hx)
    exact Real.rpow_nonneg hx'.le _
  have hcmp := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x ^ (-σ)) (N := (1 : ℕ)) hanti hint hnonneg
  have hseries :
      (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ σ)⁻¹) =
        ∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ) ^ (-σ)) := by
    apply tsum_congr
    intro n
    rw [← Real.rpow_neg (by positivity : 0 ≤ ((n + 2 : ℕ) : ℝ))]
  calc
    _ = ∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ) ^ (-σ)) := hseries
    _ ≤ ∫ x : ℝ in Ioi (1 : ℝ), x ^ (-σ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hcmp
    _ = 1 / (σ - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one]
      rw [Real.one_rpow]
      rw [show σ - 1 = -(1 - σ) by ring]
      field_simp
      ring

private theorem tsum_nat_rpow_indicator_tail_le_integral {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (if 2 ≤ n then (n : ℝ) ^ (-σ) else 0) ≤ 1 / (σ - 1) := by
  have hsubtype :
      (∑' n : ℕ, (if 2 ≤ n then (n : ℝ) ^ (-σ) else 0)) =
        ∑' n : Set.Ici (2 : ℕ), (n.1 : ℝ) ^ (-σ) := by
    simpa only [Set.mem_Ici, Set.indicator] using
      (tsum_subtype (Set.Ici (2 : ℕ)) (fun n : ℕ => (n : ℝ) ^ (-σ))).symm
  calc
    _ = ∑' n : Set.Ici (2 : ℕ), (n.1 : ℝ) ^ (-σ) := hsubtype
    _ = ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ (-σ)) := by
      exact (Equiv.tsum_eq natEquivIciTwo
        (fun n : Set.Ici (2 : ℕ) => (n.1 : ℝ) ^ (-σ))).symm
    _ ≤ 1 / (σ - 1) := by
      calc
        _ = ∑' n : ℕ, ((((n + 2 : ℕ) : ℝ) ^ σ)⁻¹) := by
          apply tsum_congr
          intro n
          rw [Real.rpow_neg (by positivity : 0 ≤ ((n + 2 : ℕ) : ℝ))]
        _ ≤ 1 / (σ - 1) := tsum_nat_rpow_tail_le_integral hσ

private theorem tsum_isPrimePow_rpow_le_indicator_tail {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : {n : ℕ // IsPrimePow n}, (n.1 : ℝ) ^ (-σ) ≤
      ∑' n : ℕ, (if 2 ≤ n then (n : ℝ) ^ (-σ) else 0) := by
  let tail : ℕ → ℝ := fun n => if 2 ≤ n then (n : ℝ) ^ (-σ) else 0
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail : Summable tail := by
    apply Summable.of_nonneg_of_le
      (f := fun n : ℕ => (n : ℝ) ^ (-σ)) (g := tail)
    · intro n
      dsimp [tail]
      split_ifs <;> positivity
    · intro n
      dsimp [tail]
      split_ifs with h
      · exact le_rfl
      · positivity
    · exact hnat
  have hprime_eq_tail :
      (∑' n : {n : ℕ // IsPrimePow n}, (n.1 : ℝ) ^ (-σ)) =
        ∑' n : {n : ℕ // IsPrimePow n}, tail n.1 := by
    apply tsum_congr
    intro n
    have hn : 2 ≤ n.1 := by
      have hn' := n.property.one_lt
      omega
    simp [tail, hn]
  calc
    _ = ∑' n : {n : ℕ // IsPrimePow n}, tail n.1 := hprime_eq_tail
    _ ≤ ∑' n : ℕ, tail n :=
      Summable.tsum_subtype_le tail {n : ℕ | IsPrimePow n}
        (by
          intro n
          dsimp [tail]
          split_ifs <;> positivity)
        htail

private theorem tsum_primes_rpow_eq_isPrimePow {σ : ℝ}
    (hprime : Summable (fun n : {n : ℕ // IsPrimePow n} => (n.1 : ℝ) ^ (-σ))) :
    ∑' p : Nat.Primes, ∑' k : ℕ,
      (((p.1 ^ (k + 1) : ℕ) : ℝ) ^ (-σ)) =
        ∑' n : {n : ℕ // IsPrimePow n}, (n.1 : ℝ) ^ (-σ) := by
  simpa only using
    (tsum_primes_pow_eq (f := fun n : ℕ => (n : ℝ) ^ (-σ)) hprime)

private theorem tsum_primes_prime_power_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' p : Nat.Primes, ∑' k : ℕ,
      (((p.1 ^ (k + 1) : ℕ) : ℝ) ^ (-σ)) ≤ 1 / (σ - 1) := by
  have hprime :
      Summable (fun n : {n : ℕ // IsPrimePow n} => (n.1 : ℝ) ^ (-σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype _
  rw [tsum_primes_rpow_eq_isPrimePow hprime]
  exact (tsum_isPrimePow_rpow_le_indicator_tail hσ).trans
    (tsum_nat_rpow_indicator_tail_le_integral hσ)

private theorem summable_prime_power_majorant {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      (((pk.1.1 ^ (pk.2 + 1) : ℕ) : ℝ) ^ (-σ))) := by
  have hprime :
      Summable (fun n : {n : ℕ // IsPrimePow n} => (n.1 : ℝ) ^ (-σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype _
  convert hprime.comp_injective Nat.Primes.prodNatEquiv.injective using 1
  ext ⟨p, k⟩
  simp [Nat.Primes.prodNatEquiv_apply]

private theorem continuedDirichletEulerLog_term_norm_le_majorant
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (p : Nat.Primes) (k : ℕ) :
    ‖(χ p * (p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)‖ ≤
      (((p.1 ^ (k + 1) : ℕ) : ℝ) ^ (-s.re)) := by
  have hp : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
    calc
      ‖χ p * (p : ℂ) ^ (-s)‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ := norm_mul _ _
      _ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one p) (norm_nonneg _)
      _ = (p : ℝ) ^ (-s.re) := by
        rw [norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
  have hden : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    calc
      ‖((k : ℂ) + 1)‖ = ‖(↑(k + 1) : ℂ)‖ := by congr 1 <;> push_cast <;> ring
      _ = ((k + 1 : ℕ) : ℝ) := by rw [Complex.norm_natCast]
      _ = (k : ℝ) + 1 := by norm_cast
  have hpow :
      ‖(χ p * (p : ℂ) ^ (-s)) ^ (k + 1)‖ =
        ‖χ p * (p : ℂ) ^ (-s)‖ ^ (k + 1) := norm_pow _ _
  calc
    ‖(χ p * (p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)‖ =
        ‖χ p * (p : ℂ) ^ (-s)‖ ^ (k + 1) / ((k : ℝ) + 1) := by
      rw [norm_div, hpow, hden]
    _ ≤ ‖χ p * (p : ℂ) ^ (-s)‖ ^ (k + 1) := by
      apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2
      nlinarith [pow_nonneg (norm_nonneg (χ p * (p : ℂ) ^ (-s))) (k + 1)]
    _ ≤ ((p : ℝ) ^ (-s.re)) ^ (k + 1) := by
      gcongr
    _ = (((p.1 ^ (k + 1) : ℕ) : ℝ) ^ (-s.re)) := by
      rw [Nat.cast_pow]
      exact Real.rpow_pow_comm (by positivity : 0 ≤ (p : ℝ)) (-s.re) (k + 1)

/-- Absolute summability of the full double prime-power logarithm series on
`Re(s)>1`. The majorant is obtained by the injective prime-power
reindexing and the convergent `n^(-Re(s))` tail. -/
theorem continuedDirichletEulerLog_doubleSeries_absSummable
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖(χ pk.1 * (pk.1 : ℂ) ^ (-s)) ^ (pk.2 + 1) / ((pk.2 : ℂ) + 1)‖) := by
  have hmajorant : Summable (fun pk : Nat.Primes × ℕ =>
      (((pk.1.1 ^ (pk.2 + 1) : ℕ) : ℝ) ^ (-s.re))) :=
    summable_prime_power_majorant (by linarith)
  apply Summable.of_nonneg_of_le
  · intro pk
    exact norm_nonneg _
  · intro pk
    exact continuedDirichletEulerLog_term_norm_le_majorant χ pk.1 pk.2
  · exact hmajorant

/-- In particular, the sum over primes of the absolute inner power-series
sums is summable, which certifies the nested series used in the definition. -/
theorem continuedDirichletEulerLog_outer_absSummable
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ∑' k : ℕ,
      ‖(χ p * (p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)‖) := by
  have hdouble := continuedDirichletEulerLog_doubleSeries_absSummable χ hs
  have hparts :=
    (summable_prod_of_nonneg
      (f := fun pk : Nat.Primes × ℕ =>
        ‖(χ pk.1 * (pk.1 : ℂ) ^ (-s)) ^ (pk.2 + 1) / ((pk.2 : ℂ) + 1)‖)
      (fun pk => norm_nonneg _)).mp hdouble
  exact hparts.2

/-- The prime-power logarithm is exactly the sum of logarithms of the
Euler factors on the domain of absolute convergence. -/
theorem continuedDirichletEulerLog_eq_neg_tsum_log
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    continuedDirichletEulerLog χ s =
      ∑' p : Nat.Primes, -log (1 - χ p * (p : ℂ) ^ (-s)) := by
  unfold continuedDirichletEulerLog
  refine tsum_congr fun p => ?_
  exact (hasSum_taylorSeries_neg_log' (eulerFactor_norm_lt_one χ hs p)).tsum_eq

private def continuedDirichletLogCoeff {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n * ArithmeticFunction.vonMangoldt n / Real.log n

private theorem continuedDirichletLogCoeff_norm_le_one
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {n : ℕ}
    (hn : n ≠ 0) : ‖continuedDirichletLogCoeff χ n‖ ≤ 1 := by
  by_cases hn1 : n = 1
  · subst n
    simp [continuedDirichletLogCoeff, ArithmeticFunction.vonMangoldt_apply_one]
  have hn' : 1 < n := by omega
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn')
  have hΛnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hΛle : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  rw [continuedDirichletLogCoeff, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnonneg, abs_of_pos hlog]
  calc
    ‖χ n‖ * ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) ≤
        (1 * ArithmeticFunction.vonMangoldt n) / Real.log (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlog.le
      exact mul_le_mul_of_nonneg_right (χ.norm_le_one n) hΛnonneg
    _ = ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) := by ring
    _ ≤ 1 := div_le_one_of_le₀ hΛle hlog.le

private theorem continuedDirichletLogCoeff_term_norm_le_tail
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖LSeries.term (continuedDirichletLogCoeff χ) s n‖ ≤
      if 2 ≤ n then (n : ℝ) ^ (-s.re) else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn2 : 2 ≤ n
  · have hnpos : 0 < n := by omega
    have hpowpos : 0 < (n : ℝ) ^ s.re :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
    rw [LSeries.norm_term_eq, if_neg hn0, if_pos hn2]
    calc
      ‖continuedDirichletLogCoeff χ n‖ / (n : ℝ) ^ s.re ≤
          1 / (n : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (continuedDirichletLogCoeff_norm_le_one χ hn0)
          hpowpos.le
      _ = (n : ℝ) ^ (-s.re) := by
        simpa [one_div] using
          (Real.rpow_neg (Nat.cast_nonneg n) s.re).symm
  · have hn1 : n = 1 := by omega
    subst n
    have hcoeff : continuedDirichletLogCoeff χ 1 = 0 := by
      simp [continuedDirichletLogCoeff, ArithmeticFunction.vonMangoldt_apply_one]
    simp [LSeries.term, hcoeff]

private theorem continuedDirichletEulerLog_eq_LSeries
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    continuedDirichletEulerLog χ s = LSeries (continuedDirichletLogCoeff χ) s := by
  rw [continuedDirichletEulerLog_eq_neg_tsum_log χ hs]
  change (∑' p : Nat.Primes, -log (1 - χ p * (p : ℂ) ^ (-s))) =
    LSeries (fun n => χ n * ArithmeticFunction.vonMangoldt n / Real.log n) s
  exact _root_.DirichletCharacter.eulerProduct_log_eq_LSeries χ hs

/-- The prime-power logarithm has the blueprint's uniform bound on the
right half-plane `Re(s) ≥ 3/2`. -/
theorem continuedDirichletEulerLog_norm_le_two
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 3 / 2 ≤ s.re) : ‖continuedDirichletEulerLog χ s‖ ≤ 2 := by
  have hs' : 1 < s.re := by linarith
  rw [continuedDirichletEulerLog_eq_LSeries χ hs']
  have hcoeff : ∀ n ≠ 0, ‖continuedDirichletLogCoeff χ n‖ ≤ 1 := by
    intro n hn
    exact continuedDirichletLogCoeff_norm_le_one χ hn
  have hlsum : LSeriesSummable (continuedDirichletLogCoeff χ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re hcoeff hs'
  have hterms : Summable (fun n => LSeries.term (continuedDirichletLogCoeff χ) s n) := by
    simpa only [LSeriesSummable] using hlsum
  have hnorm : Summable (fun n => ‖LSeries.term (continuedDirichletLogCoeff χ) s n‖) :=
    hterms.norm
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  let tail : ℕ → ℝ := fun n => if 2 ≤ n then (n : ℝ) ^ (-s.re) else 0
  have htail : Summable tail := by
    apply Summable.of_nonneg_of_le
      (f := fun n : ℕ => (n : ℝ) ^ (-s.re)) (g := tail)
    · intro n
      dsimp [tail]
      split_ifs <;> positivity
    · intro n
      dsimp [tail]
      split_ifs with h
      · exact le_rfl
      · positivity
    · exact hnat
  have htermBound (n : ℕ) :
      ‖LSeries.term (continuedDirichletLogCoeff χ) s n‖ ≤ tail n := by
    simpa [tail] using continuedDirichletLogCoeff_term_norm_le_tail χ s n
  calc
    ‖LSeries (continuedDirichletLogCoeff χ) s‖ ≤
        ∑' n : ℕ, ‖LSeries.term (continuedDirichletLogCoeff χ) s n‖ :=
      norm_tsum_le_tsum_norm hterms.norm
    _ ≤ ∑' n : ℕ, tail n := hnorm.tsum_le_tsum htermBound htail
    _ ≤ 1 / (s.re - 1) := tsum_nat_rpow_indicator_tail_le_integral (by linarith)
    _ ≤ 2 := by
      apply (div_le_iff₀ (by linarith : 0 < s.re - 1)).2
      linarith

/-- The prime-power logarithm is holomorphic throughout its half-plane of
absolute convergence. The bounded von Mangoldt coefficients give an
abscissa of absolute convergence at most one. -/
theorem continuedDirichletEulerLog_analyticOnNhd
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (continuedDirichletEulerLog χ) {s | 1 < s.re} := by
  have hcoeff : ∃ C : ℝ, ∀ n ≠ 0, ‖continuedDirichletLogCoeff χ n‖ ≤ C :=
    ⟨1, fun n hn => continuedDirichletLogCoeff_norm_le_one χ hn⟩
  have habscissa : LSeries.abscissaOfAbsConv (continuedDirichletLogCoeff χ) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const hcoeff
  have hanalytic :
      AnalyticOnNhd ℂ (fun s => LSeries (continuedDirichletLogCoeff χ) s)
        {s | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    apply LSeries_analyticOnNhd
    exact lt_of_le_of_lt habscissa (EReal.coe_lt_coe_iff.mpr hs)
  apply AnalyticOnNhd.congr (isOpen_re_gt 1) hanalytic
  intro s hs
  exact (continuedDirichletEulerLog_eq_LSeries χ hs).symm

/-- Exponentiating the approved prime-power logarithm gives the Dirichlet
L-series, by Mathlib's Euler-product logarithm theorem. -/
theorem exp_continuedDirichletEulerLog_eq_LSeries
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    exp (continuedDirichletEulerLog χ s) = LSeries (χ ·) s := by
  rw [continuedDirichletEulerLog_eq_neg_tsum_log χ hs]
  exact _root_.DirichletCharacter.LSeries_eulerProduct_exp_log χ hs

/-- The constant-one specialization of the prime-power logarithm exponentiates
to the Riemann zeta function, as required for the principal regularization. -/
theorem exp_continuedDirichletEulerLog_one_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    exp (continuedDirichletEulerLog (1 : _root_.DirichletCharacter ℂ 1) s) =
      riemannZeta s := by
  rw [continuedDirichletEulerLog_eq_neg_tsum_log (1 : _root_.DirichletCharacter ℂ 1) hs]
  convert riemannZeta_eulerProduct_exp_log hs using 2
  apply tsum_congr
  intro p
  simp [MulChar.one_apply <| isUnit_of_subsingleton _]

/-- The constant-one logarithm inherits the same uniform right-half-plane
bound as every Dirichlet-character Euler logarithm. -/
theorem continuedDirichletEulerLog_one_norm_le_two {s : ℂ}
    (hs : 3 / 2 ≤ s.re) :
    ‖continuedDirichletEulerLog (1 : _root_.DirichletCharacter ℂ 1) s‖ ≤ 2 :=
  continuedDirichletEulerLog_norm_le_two (1 : _root_.DirichletCharacter ℂ 1) hs

/-- The constant-one logarithm is holomorphic on `Re(s) > 1`. -/
theorem continuedDirichletEulerLog_one_analyticOnNhd :
    AnalyticOnNhd ℂ
      (continuedDirichletEulerLog (1 : _root_.DirichletCharacter ℂ 1))
      {s | 1 < s.re} :=
  continuedDirichletEulerLog_analyticOnNhd (1 : _root_.DirichletCharacter ℂ 1)

open scoped ArithmeticFunction.Moebius in
/-- The twisted Möbius L-series is the reciprocal exponential of the
prime-power logarithm on `Re(s)>1`. -/
theorem LSeries_twistedMoebius_eq_exp_neg_continuedDirichletEulerLog
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (↗χ * ↗ArithmeticFunction.moebius) s =
      exp (-continuedDirichletEulerLog χ s) := by
  have hprod := _root_.DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hexp := exp_continuedDirichletEulerLog_eq_LSeries χ hs
  have h := (inv_eq_of_mul_eq_one_right hprod).symm
  rw [h, ← hexp]
  exact (Complex.exp_neg _).symm

#print axioms exp_continuedDirichletEulerLog_eq_LSeries
#print axioms continuedDirichletEulerLog_doubleSeries_absSummable
#print axioms continuedDirichletEulerLog_outer_absSummable
#print axioms continuedDirichletEulerLog_norm_le_two
#print axioms continuedDirichletEulerLog_analyticOnNhd
#print axioms exp_continuedDirichletEulerLog_one_eq_riemannZeta
#print axioms continuedDirichletEulerLog_one_norm_le_two
#print axioms continuedDirichletEulerLog_one_analyticOnNhd
#print axioms LSeries_twistedMoebius_eq_exp_neg_continuedDirichletEulerLog

end FractionalPrimes.Literature.Reciprocal

end
