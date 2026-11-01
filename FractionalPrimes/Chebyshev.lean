module

public import FractionalPrimes.Sieve
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Chebyshev bounds used by the elementary sieve

This file formalizes blueprint lemma `ls:chebyshev`. The definitions are the
finite prime sum and prime count with the paper's inclusive cutoff `p ≤ x`.
Mathlib's Chebyshev function is defined by the same finite sum up to
`⌊x⌋₊`, and `Nat.primeCounting ⌊x⌋₊` counts exactly those primes.
-/

@[expose] public section

open scoped Nat.Prime
open MeasureTheory

namespace FractionalPrimes

noncomputable section

def paperTheta (x : ℝ) : ℝ := Chebyshev.theta x

def paperPi (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- Integer-indexed von Mangoldt function, extended by zero to nonpositive
integers as in blueprint `def:arithmetic`. -/
def paperLambda (n : ℤ) : ℝ :=
  if 0 < n then vonMangoldtWeight n.toNat else 0

/-- Integer-indexed Möbius function, extended by zero to nonpositive integers
as in blueprint `def:arithmetic`. -/
def paperMu (n : ℤ) : ℤ :=
  if 0 < n then mobiusWeight n.toNat else 0

/-- The summatory von Mangoldt function on natural endpoints. -/
def paperPsi (N : ℕ) : ℝ := Chebyshev.psi (N : ℝ)

theorem paperPsi_eq_sum_vonMangoldt (N : ℕ) :
    paperPsi N = ∑ n ∈ Finset.Icc 1 N, vonMangoldtWeight n := by
  rw [paperPsi, Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have hset : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 N)]
  simp [vonMangoldtWeight]

/-- The product of primes strictly below the real cutoff. The strict cutoff is
the explicit convention of the expanded blueprint. -/
def paperPrimeProduct (w : ℝ) : ℕ := sievePrimeProduct w

/-- The Cramér density multiplier `W(w)/φ(W(w))`. -/
def paperCramerDensity (w : ℝ) : ℝ :=
  (paperPrimeProduct w : ℝ) / (Nat.totient (paperPrimeProduct w) : ℝ)

/-- The strict-cutoff Cramér weight on ambient integer indices. -/
def paperCramerWeight (w : ℝ) (n : ℤ) : ℝ :=
  paperCramerDensity w *
    (if Int.gcd n (paperPrimeProduct w : ℤ) = 1 then 1 else 0)

/-- Location-dependent short-interval sieve cutoff `exp((log X)^(1/10))`. -/
def paperShortBlockCutoff (X : ℝ) : ℝ :=
  Real.exp ((Real.log X) ^ (1 / 10 : ℝ))

/-- The blueprint's Cramér weight attached to a block starting at `X`. -/
def paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℝ :=
  paperCramerWeight (paperShortBlockCutoff X) n

/-- The arithmetic objects from blueprint `def:arithmetic`, collected in one
paper-facing package. The component functions retain the blueprint's natural
endpoints for summatory functions and strict real prime cutoff for the sieve. -/
structure ArithmeticData where
  vonMangoldt : ℤ → ℝ
  mobius : ℤ → ℤ
  primeCounting : ℕ → ℕ
  mangoldtSummatory : ℕ → ℝ
  primeLogSummatory : ℕ → ℝ
  primeProduct : ℝ → ℕ
  cramerDensity : ℝ → ℝ
  cramerWeight : ℝ → ℤ → ℝ
  shortBlockCutoff : ℝ → ℝ
  shortBlockWeight : ℝ → ℤ → ℝ

noncomputable def arithmeticData : ArithmeticData where
  vonMangoldt := paperLambda
  mobius := paperMu
  primeCounting := fun N => paperPi (N : ℝ)
  mangoldtSummatory := paperPsi
  primeLogSummatory := fun N => paperTheta (N : ℝ)
  primeProduct := paperPrimeProduct
  cramerDensity := paperCramerDensity
  cramerWeight := paperCramerWeight
  shortBlockCutoff := paperShortBlockCutoff
  shortBlockWeight := paperShortBlockCramerWeight

@[simp] theorem paperLambda_nonpos {n : ℤ} (hn : n ≤ 0) : paperLambda n = 0 := by
  simp [paperLambda, not_lt.mpr hn]

@[simp] theorem paperMu_nonpos {n : ℤ} (hn : n ≤ 0) : paperMu n = 0 := by
  simp [paperMu, not_lt.mpr hn]

/-- The von Mangoldt coefficient has the elementary nonnegative logarithmic
bound from `lem:elementary` for every positive integer. -/
theorem paperLambda_bounds {n : ℤ} (hn : 1 ≤ n) :
    0 ≤ paperLambda n ∧ paperLambda n ≤ Real.log (n : ℝ) := by
  have hnpos : 0 < n := by omega
  rw [paperLambda, if_pos hnpos]
  have hncast : (n.toNat : ℝ) = (n : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ n))
  constructor
  · exact vonMangoldtWeight_nonneg _
  · rw [← hncast]
    exact vonMangoldtWeight_le_log

/-- Mathlib's Möbius bound transferred to the paper's integer-indexed
positive-integer extension. -/
theorem paperMu_abs_le_one {n : ℤ} (hn : 1 ≤ n) :
    |paperMu n| ≤ 1 := by
  have hnpos : 0 < n := by omega
  simpa [paperMu, mobiusWeight, hnpos] using
    (ArithmeticFunction.abs_moebius_le_one (n := n.toNat))

theorem arithmeticData_lambda_eq (n : ℤ) :
    arithmeticData.vonMangoldt n = paperLambda n := rfl

theorem arithmeticData_mu_eq (n : ℤ) : arithmeticData.mobius n = paperMu n := rfl

theorem arithmeticData_strictPrimeProduct (w : ℝ) :
    arithmeticData.primeProduct w =
      ∏ p ∈ sievePrimesBelow w, p := by
  rfl

/-- The packaged von Mangoldt summatory function retains the paper's
positive-integer sum and its exact natural endpoint. -/
theorem arithmeticData_mangoldtSummatory_eq (N : ℕ) :
    arithmeticData.mangoldtSummatory N =
      ∑ n ∈ Finset.Icc 1 N, vonMangoldtWeight n := by
  simpa [arithmeticData] using paperPsi_eq_sum_vonMangoldt N

/-- The package's sieve product uses the expanded blueprint's strict
real cutoff `p < w`. -/
theorem arithmeticData_primeProduct_strictCutoff (w : ℝ) :
    arithmeticData.primeProduct w =
      ∏ p ∈ sievePrimesBelow w, p := by
  exact arithmeticData_strictPrimeProduct w

/-- The location-dependent cutoff is exactly `exp((log X)^(1/10))`. -/
theorem arithmeticData_shortBlockCutoff_eq (X : ℝ) :
    arithmeticData.shortBlockCutoff X =
      Real.exp ((Real.log X) ^ (1 / 10 : ℝ)) := rfl

theorem paperTheta_eq_sum_primes (x : ℝ) :
    paperTheta x = ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with Nat.Prime p,
      Real.log (p : ℝ) := by
  simpa [paperTheta] using Chebyshev.theta_eq_sum_Icc x

theorem paperPi_eq_card_primes (x : ℝ) :
    paperPi x = ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).card := by
  rw [paperPi, ← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_eq_filter_Icc_zero]

/-- For `x ≥ 4`, the logarithm is large enough that the Chebyshev
prime-power remainder bound has the blueprint's squared-log form. -/
theorem two_log_mul_log_two_le_log_sq {x : ℝ} (hx : 4 ≤ x) :
    2 * Real.log x ≤ (Real.log x) ^ 2 / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlarge : 2 * Real.log 2 ≤ Real.log x := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) hx
  apply (le_div_iff₀ hlog2).2
  nlinarith [mul_le_mul_of_nonneg_right hlarge (le_of_lt hlogx)]

/-- The contribution to `ψ N` from exponents at least two, written as the
finite sum of prime-log sums at the corresponding root cutoffs. By
`paperTheta_eq_sum_primes`, each summand is precisely the sum over primes
`p` with `p^k ≤ N`; this is Mathlib's canonical finite prime-power indexing. -/
def paperHigherPrimePowerThetaSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.log (N : ℝ) / Real.log 2⌋₊,
    paperTheta ((N : ℝ) ^ ((1 : ℝ) / (k : ℝ)))

/-- The root-cutoff condition in the finite theta sum is exactly the
prime-power cutoff `p^k ≤ N`. This is Mathlib's floor/rpow equivalence,
specialized to positive natural exponents. -/
theorem prime_le_floor_root_iff_pow_le {N p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    p ≤ ⌊(N : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ ↔ p ^ k ≤ N := by
  rw [Nat.le_floor_iff' (Nat.ne_of_gt hp)]
  rw [show (1 : ℝ) / (k : ℝ) = (k : ℝ)⁻¹ by field_simp]
  rw [Real.le_rpow_inv_iff_of_pos (by exact_mod_cast hp.le)
    (by positivity) (by exact_mod_cast hk)]
  exact_mod_cast (show (p : ℝ) ^ (k : ℝ) ≤ (N : ℝ) ↔ p ^ k ≤ N by
    norm_cast)

/-- The exact pair-indexed interpretation of the higher-prime-power sum.
The prime variable is restricted by the equivalent root cutoff, while its
membership condition explicitly records `p^k ≤ N`. -/
def paperHigherPrimePowerPairSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.log (N : ℝ) / Real.log 2⌋₊,
    ∑ p ∈ (Finset.Icc 0
        ⌊(N : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter
          (fun p => Nat.Prime p ∧ p ^ k ≤ N),
      Real.log (p : ℝ)

/-- The explicit prime/exponent sum agrees exactly with the exponent-root
theta sum; the cutoff equivalence uses `prime_le_floor_root_iff_pow_le`. -/
theorem paperHigherPrimePowerPairSum_eq_thetaSum (N : ℕ) :
    paperHigherPrimePowerPairSum N = paperHigherPrimePowerThetaSum N := by
  unfold paperHigherPrimePowerPairSum paperHigherPrimePowerThetaSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [paperTheta_eq_sum_primes]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp0, hpfloor⟩, hprime, hpow⟩
      exact ⟨⟨hp0, hpfloor⟩, hprime⟩
    · rintro ⟨⟨hp0, hpfloor⟩, hprime⟩
      have hkpos : 0 < k := by
        have := Finset.mem_Icc.mp hk
        omega
      have hpow := (prime_le_floor_root_iff_pow_le
        (N := N) (p := p) (k := k) hprime.pos hkpos).1 hpfloor
      exact ⟨⟨hp0, hpfloor⟩, hprime, hpow⟩
  · intro p hp
    rfl

/-- Mathlib's exact `ψ = θ + higher prime powers` identity, in the project's
paper-facing notation and with the blueprint's exponent endpoints. -/
theorem paperHigherPrimePowerThetaSum_eq_psi_sub_theta {N : ℕ}
    (hN : 2 ≤ N) :
    paperHigherPrimePowerThetaSum N =
      paperPsi N - paperTheta (N : ℝ) := by
  have hdecomp := Chebyshev.psi_eq_theta_add_sum_theta
    (x := (N : ℝ)) (by exact_mod_cast hN)
  simp only [paperHigherPrimePowerThetaSum, paperPsi, paperTheta] at hdecomp ⊢
  linarith

/-- The higher-prime-power contribution satisfies the square-log bound used
in `lem:elementary`. -/
theorem paperHigherPrimePowerThetaSum_le {N : ℕ} (hN : 4 ≤ N) :
    paperHigherPrimePowerThetaSum N ≤
      (Real.log (N : ℝ)) ^ 2 / Real.log 2 * Real.sqrt (N : ℝ) := by
  rw [paperHigherPrimePowerThetaSum_eq_psi_sub_theta (by omega)]
  have hrem := Chebyshev.psi_sub_theta_le
    (x := (N : ℝ)) (by exact_mod_cast (by omega : 1 ≤ N))
  have hscalar := two_log_mul_log_two_le_log_sq
    (x := (N : ℝ)) (by exact_mod_cast hN)
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    exact le_of_lt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  change Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hscalar hsqrt]

/-- The normalized higher-prime-power estimate from `lem:elementary` for
`N ≥ 4`, now stated for the exact pair-indexed sum. -/
theorem paperHigherPrimePowerPairSum_normalized_le {N : ℕ} (hN : 4 ≤ N) :
    (N : ℝ)⁻¹ * paperHigherPrimePowerPairSum N ≤
      (Real.log (N : ℝ)) ^ 2 /
        (Real.log 2 * Real.sqrt (N : ℝ)) := by
  rw [paperHigherPrimePowerPairSum_eq_thetaSum]
  have hbound := paperHigherPrimePowerThetaSum_le hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  calc
    (N : ℝ)⁻¹ * paperHigherPrimePowerThetaSum N ≤
        (N : ℝ)⁻¹ *
          ((Real.log (N : ℝ)) ^ 2 / Real.log 2 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hNpos.le)
    _ = (Real.log (N : ℝ)) ^ 2 /
          (Real.log 2 * Real.sqrt (N : ℝ)) := by
      field_simp [ne_of_gt hNpos, ne_of_gt hsqrtpos, ne_of_gt hlog2pos]
      nlinarith [hsqr]

/-- Below four there are no admissible exponents `k ≥ 2`, so the exact
prime/exponent sum vanishes. -/
theorem paperHigherPrimePowerPairSum_eq_zero_of_lt_four {N : ℕ}
    (hN : 2 ≤ N) (hNlt : N < 4) :
    paperHigherPrimePowerPairSum N = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNlt : Real.log (N : ℝ) < Real.log 4 :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < N))
      (by exact_mod_cast hNlt)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hquot : Real.log (N : ℝ) / Real.log 2 < 2 :=
    (div_lt_iff₀ hlog2).2 (hlogNlt.trans_eq hlog4)
  have hupper : ⌊Real.log (N : ℝ) / Real.log 2⌋₊ < 2 :=
    (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).2 hquot
  have hempty :
      Finset.Icc 2 ⌊Real.log (N : ℝ) / Real.log 2⌋₊ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    omega
  simp [paperHigherPrimePowerPairSum, hempty]

/-- The normalized higher-prime-power estimate in the exact form and for the
full endpoint range stated in `lem:elementary`. -/
theorem paperHigherPrimePowerPairSum_normalized_le_of_two_le
    {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ)⁻¹ * paperHigherPrimePowerPairSum N ≤
      (Real.log (N : ℝ)) ^ 2 /
        (Real.log 2 * Real.sqrt (N : ℝ)) := by
  by_cases h4 : 4 ≤ N
  · exact paperHigherPrimePowerPairSum_normalized_le h4
  · have hNlt : N < 4 := by omega
    rw [paperHigherPrimePowerPairSum_eq_zero_of_lt_four hN hNlt]
    have hden : 0 < Real.log 2 * Real.sqrt (N : ℝ) :=
      mul_pos (Real.log_pos (by norm_num))
        (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N)))
    simp only [mul_zero]
    exact div_nonneg (sq_nonneg _) hden.le

/-- The first asymptotic growth comparison in `lem:elementary`, directly from
Mathlib's real-exponent logarithm/power asymptotic. -/
theorem paper_log_rpow_isLittleO_rpow {a b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => Real.log x ^ a) =o[Filter.atTop] fun x => x ^ b :=
  isLittleO_log_rpow_rpow_atTop a hb

/-- Sublinear logarithmic exponentials are dominated by every positive power,
as required by the second growth comparison in `lem:elementary`. -/
theorem paper_exp_log_rpow_isLittleO_rpow {ρ b : ℝ}
    (hρ : 0 < ρ) (hρlt : ρ < 1) (hb : 0 < b) :
    (fun x : ℝ => Real.exp ((Real.log x) ^ ρ)) =o[Filter.atTop]
      fun x => x ^ b := by
  have hratio : Filter.Tendsto (fun t : ℝ => t ^ ρ / t) Filter.atTop
      (nhds 0) := by
    have hnegative : Filter.Tendsto (fun t : ℝ => t ^ (-(1 - ρ)))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    refine hnegative.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    calc
      t ^ (-(1 - ρ)) = t ^ (ρ - 1) := by congr 1 <;> ring
      _ = t ^ ρ / t := by rw [Real.rpow_sub ht ρ 1, Real.rpow_one]
  have hdiff : Filter.Tendsto (fun t : ℝ => b * t - t ^ ρ)
      Filter.atTop Filter.atTop := by
    have hsmall : ∀ᶠ t : ℝ in Filter.atTop, t ^ ρ / t < b / 2 :=
      hratio.eventually (Iio_mem_nhds (by linarith))
    have hlin : Filter.Tendsto (fun t : ℝ => (b / 2) * t)
        Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos (by linarith)).2
        (Filter.tendsto_id (α := ℝ))
    apply Filter.tendsto_atTop_mono' Filter.atTop ?_ hlin
    filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℝ)]
      with t ht htle
    have htpos : 0 < t := by linarith
    have hpow : t ^ ρ < (b / 2) * t := (div_lt_iff₀ htpos).1 ht
    linarith
  have hexp := (Real.isLittleO_exp_comp_exp_comp
    (f := fun t : ℝ => t ^ ρ) (g := fun t => b * t)).2 hdiff
  have hlog := hexp.comp_tendsto Real.tendsto_log_atTop
  have hright : (fun x : ℝ => Real.exp (b * Real.log x)) =ᶠ[Filter.atTop]
      fun x => x ^ b := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_def_of_pos hx]
    rw [mul_comm]
  exact hlog.trans_eventuallyEq hright

/-- The inverse-power/logarithm comparison in `lem:elementary`. The proof
uses the already checked stronger little-o estimate with exponent `a+D`. -/
theorem paper_inverse_power_log_isBigO {a b D : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hD : 0 < D) :
    (fun x : ℝ => x ^ (-b) * (Real.log x) ^ a) =O[Filter.atTop]
      fun x => (Real.log x) ^ (-D) := by
  have hlogpow := paper_log_rpow_isLittleO_rpow
    (a := a + D) (b := b) hb
  have hratio := hlogpow.tendsto_div_nhds_zero
  have heq :
      (fun x : ℝ => x ^ (-b) * (Real.log x) ^ a / (Real.log x) ^ (-D)) =ᶠ[
        Filter.atTop] fun x => (Real.log x) ^ (a + D) / x ^ b := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    rw [Real.rpow_neg (by linarith : 0 ≤ x), Real.rpow_neg (le_of_lt hlog)]
    field_simp
    rw [← Real.rpow_add hlog a D]
  have hzero : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ (-D) = 0 → x ^ (-b) * (Real.log x) ^ a = 0 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx h
    have hlog : 0 < Real.log x := Real.log_pos hx
    exact ((Real.rpow_pos_of_pos hlog (-D)).ne' h).elim
  have hlittle :
      (fun x : ℝ => x ^ (-b) * (Real.log x) ^ a) =o[Filter.atTop]
        fun x => (Real.log x) ^ (-D) := by
    refine (Asymptotics.isLittleO_iff_tendsto' hzero).2 ?_
    exact hratio.congr' heq.symm
  exact hlittle.isBigO

/-- The real exponential phase used in the prime sums is exactly the unit
frequency character at the same real argument. -/
theorem paper_realExponentialPhase_eq_unitFrequencyPhase (f : ℝ → ℝ) (n : ℤ) :
    realExponentialPhase f n = unitFrequencyPhase (f (n : ℝ)) := rfl

/-- The unit-frequency phase obeys the blueprint's chord/Lipschitz estimate. -/
theorem paper_unitFrequencyPhase_lipschitz (u v : ℝ) :
    ‖unitFrequencyPhase u - unitFrequencyPhase v‖ ≤
      2 * Real.pi * |u - v| := by
  simpa [unitFrequencyPhase] using
    (norm_unitFrequencyPhase_mul_sub_le 1 u v)

/-- The paper's real-power derivative formula, with the falling factorial
represented by the project's polynomial coefficient. -/
theorem paper_rpow_iterated_derivative_formula {c t : ℝ}
    (ht : 0 < t) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => s ^ c) t =
      (descPochhammer ℝ j).eval c * t ^ (c - (j : ℝ)) := by
  simpa using iteratedDeriv_real_rpow c t j

/-- The polynomial falling-factorial coefficient is exactly the displayed
finite product `(c)_j = ∏_{h<j}(c-h)`. -/
theorem paper_fallingFactorial_eq_product (c : ℝ) (j : ℕ) :
    (descPochhammer ℝ j).eval c =
      ∏ h ∈ Finset.range j, (c - (h : ℝ)) :=
  descPochhammer_eval_eq_prod c j

/-- For a nonintegral exponent, none of the real-power derivatives vanish
at a positive argument, matching the blueprint's `(c)_j ≠ 0` clause. -/
theorem paper_rpow_iterated_derivative_ne_zero {c t : ℝ}
    (hc : NonIntegral c) (ht : 0 < t) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => s ^ c) t ≠ 0 := by
  rw [paper_rpow_iterated_derivative_formula ht j]
  exact mul_ne_zero (descPochhammer_eval_ne_zero hc j)
    (Real.rpow_pos_of_pos ht _).ne'

/-- The package's prime-count field is Mathlib's exact count through `N`. -/
theorem arithmeticData_primeCounting_eq (N : ℕ) :
    arithmeticData.primeCounting N =
      ((Finset.Icc 0 N).filter Nat.Prime).card := by
  simpa [arithmeticData, paperPi, Nat.floor_natCast] using
    paperPi_eq_card_primes (N : ℝ)

/-- The packaged prime-log summatory function retains the inclusive prime
endpoint `p ≤ N`. -/
theorem arithmeticData_primeLogSummatory_eq (N : ℕ) :
    arithmeticData.primeLogSummatory N =
      ∑ p ∈ Finset.Icc 0 N with Nat.Prime p, Real.log (p : ℝ) := by
  simpa [arithmeticData, paperTheta, Nat.floor_natCast] using
    paperTheta_eq_sum_primes (N : ℝ)

theorem paperTheta_upper_bound {x : ℝ} (hx : 1 ≤ x) :
    paperTheta x ≤ 4 * Real.log 2 * x := by
  have hx0 : 0 ≤ x := by linarith
  have h := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at h
  change Chebyshev.theta x ≤ 4 * Real.log 2 * x
  nlinarith [sieveLogTwo_bounds.1]

private theorem log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hlog := Real.log_le_rpow_div (x := x) (ε := 1 / 2)
    (by linarith) (by norm_num)
  calc
    Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlog
    _ = x ^ (1 / 2 : ℝ) * 2 := by field_simp
    _ = 2 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]; ring

theorem paperPi_upper_bound {x : ℝ} (hx : 2 ≤ x) :
    (paperPi x : ℝ) ≤ 8 * x / Real.log x := by
  have hx1 : 1 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 :=
    Real.log_sqrt (by linarith)
  have hbase := Chebyshev.pi_le_log4_mul_div hx1
  change (paperPi x : ℝ) ≤ _ at hbase
  rw [hlogsqrt] at hbase
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hbase
  have hlog2 := sieveLogTwo_bounds.2
  have hlogx := log_le_two_sqrt (by linarith : 1 ≤ x)
  have hsqrtTerm : Real.sqrt x ≤ 2 * x / Real.log x := by
    rw [le_div_iff₀ hlogpos]
    calc
      Real.sqrt x * Real.log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlogx (Real.sqrt_nonneg x)
      _ = 2 * x := by
        calc
          Real.sqrt x * (2 * Real.sqrt x) = 2 * (Real.sqrt x ^ 2) := by ring
          _ = 2 * x := by rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
  
  have hterm : (2 * Real.log 2 * x) / (Real.log x / 2) =
      4 * Real.log 2 * (x / Real.log x) := by
    field_simp [ne_of_gt hlogpos]
    ring
  have hmain : (2 * Real.log 2 * x) / (Real.log x / 2) ≤
      3 * x / Real.log x := by
    rw [hterm]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hcoeff : 4 * Real.log 2 ≤ 3 := by nlinarith [hlog2]
    calc
      4 * Real.log 2 * (x / Real.log x) ≤ 3 * (x / Real.log x) :=
        mul_le_mul_of_nonneg_right hcoeff hfactor
      _ = 3 * x / Real.log x := by ring
  have hbase' : (paperPi x : ℝ) ≤ 5 * x / Real.log x := by
    calc
      (paperPi x : ℝ) ≤
          (2 * Real.log 2 * x) / (Real.log x / 2) + Real.sqrt x := hbase
      _ ≤ 3 * x / Real.log x + 2 * x / Real.log x := add_le_add hmain hsqrtTerm
      _ = 5 * x / Real.log x := by ring
  have hnonneg : 0 ≤ x / Real.log x := by positivity
  calc
    (paperPi x : ℝ) ≤ 5 * x / Real.log x := hbase'
    _ ≤ 8 * x / Real.log x := by
      have hcoeff : (5 : ℝ) ≤ 8 := by norm_num
      calc
        5 * x / Real.log x = 5 * (x / Real.log x) := by ring
        _ ≤ 8 * (x / Real.log x) := mul_le_mul_of_nonneg_right hcoeff hnonneg
        _ = 8 * x / Real.log x := by ring

theorem chebyshev_bounds :
    (∀ x : ℝ, 1 ≤ x → paperTheta x ≤ 4 * Real.log 2 * x) ∧
    (∀ x : ℝ, 2 ≤ x → (paperPi x : ℝ) ≤ 8 * x / Real.log x) := by
  exact ⟨fun x hx => paperTheta_upper_bound hx,
    fun x hx => paperPi_upper_bound hx⟩

private theorem reciprocal_difference_telescopes (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N,
      (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) = 1 - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : 2 ≤ N
    · rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih h]
      push_cast
      have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hN1pos : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hNpos, hN1pos]
      <;> ring_nf
    · interval_cases N <;> norm_num [Finset.sum_Icc_succ_top]

theorem sum_reciprocal_error_le_one {S : Finset ℕ} {N : ℕ}
    (hN : 2 ≤ N) (hSN : S ⊆ Finset.Icc 2 N) :
    (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  calc
    (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1))) =
        ∑ p ∈ S, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpN := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hpN
      have hpPos : (p : ℝ) ≠ 0 := by positivity
      have hpSubPos : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hpPos, hpSubPos]
      <;> ring_nf
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
          (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSN
      intro n hnIcc hnNotS
      have hn : 2 ≤ n := (Finset.mem_Icc.mp hnIcc).1
      have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
      have hnPos : (n : ℝ) ≠ 0 := by positivity
      have hnSubPos : (n : ℝ) - 1 ≠ 0 := by linarith
      have hident :
          1 / ((n : ℝ) * ((n : ℝ) - 1)) =
            1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
        field_simp [hnPos, hnSubPos]
        <;> ring_nf
      have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
        mul_pos (by linarith) (by linarith)
      rw [← hident]
      exact div_nonneg (by norm_num) hden.le
    _ = 1 - 1 / (N : ℝ) := reciprocal_difference_telescopes N hN
    _ ≤ 1 := by
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith

theorem sum_log_prime_ratio_le_reciprocals_add_one {S : Finset ℕ} {N : ℕ}
    (hN : 2 ≤ N) (hSN : S ⊆ Finset.Icc 2 N) :
    (∑ p ∈ S, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
      (∑ p ∈ S, 1 / (p : ℝ)) + 1 := by
  have hpoint : ∀ p ∈ S,
      Real.log ((p : ℝ) / ((p : ℝ) - 1)) ≤
        1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hpN := (Finset.mem_Icc.mp (hSN hp)).1
    have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hpN
    have hpPos : 0 < (p : ℝ) := by linarith
    have hpSubPos : 0 < (p : ℝ) - 1 := by linarith
    have hlog := Real.log_le_sub_one_of_pos (div_pos hpPos hpSubPos)
    have hratio : (p : ℝ) / ((p : ℝ) - 1) - 1 =
        1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp
      <;> ring_nf
    rw [hratio] at hlog
    exact hlog
  calc
    (∑ p ∈ S, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
        ∑ p ∈ S,
          (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
      Finset.sum_le_sum fun p hp => hpoint p hp
    _ = (∑ p ∈ S, 1 / (p : ℝ)) +
        ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by rw [Finset.sum_add_distrib]
    _ ≤ (∑ p ∈ S, 1 / (p : ℝ)) + 1 := by
      exact add_le_add_right (sum_reciprocal_error_le_one hN hSN) _

def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

def primeReciprocalSet (u v : ℝ) : Finset ℕ :=
  (sievePrimesBelow v).filter fun p => u ≤ (p : ℝ)

theorem primeIndicator_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, primeIndicator n) =
      (Nat.primeCounting N : ℝ) := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
  simp [primeIndicator, Finset.sum_boole]

theorem primeIndicator_weighted_sum_eq_filter (S : Finset ℕ) :
    (∑ p ∈ S, (p : ℝ)⁻¹ * primeIndicator p) =
      ∑ p ∈ S.filter Nat.Prime, (p : ℝ)⁻¹ := by
  simp [primeIndicator, Finset.sum_filter]

private theorem primeReciprocal_nonendpoint_subset {u v : ℝ} (hu : 0 ≤ u) :
    (primeReciprocalSet u v).filter (fun p => p ≠ ⌊u⌋₊) ⊆
      (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpS, hpne⟩
  change p ∈ (sievePrimesBelow v).filter (fun p : ℕ => u ≤ (p : ℝ)) at hpS
  rcases Finset.mem_filter.mp hpS with ⟨hpv, hpu⟩
  rcases Finset.mem_filter.mp hpv with ⟨_, ⟨hprime, hp_lt_v⟩⟩
  have hfloor_le : ⌊u⌋₊ ≤ p := by
    have hcast : (⌊u⌋₊ : ℝ) ≤ (p : ℝ) := (Nat.floor_le hu).trans hpu
    exact_mod_cast hcast
  have hfloor_lt : ⌊u⌋₊ < p := lt_of_le_of_ne hfloor_le hpne.symm
  have hp_le_v : (p : ℝ) ≤ v := hp_lt_v.le
  have hp_le_floor : p ≤ ⌊v⌋₊ := Nat.le_floor (by exact_mod_cast hp_le_v)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hfloor_lt, hp_le_floor⟩, hprime⟩

private theorem primeReciprocal_endpoint_le_count {u v : ℝ} (hu : 2 ≤ u)
    (hS : ⌊u⌋₊ ∈ primeReciprocalSet u v) :
    1 / u ≤ (paperPi u : ℝ) / u := by
  change ⌊u⌋₊ ∈ (sievePrimesBelow v).filter (fun p : ℕ => u ≤ (p : ℝ)) at hS
  rcases Finset.mem_filter.mp hS with ⟨hpv, hpu⟩
  rcases Finset.mem_filter.mp hpv with ⟨_, ⟨hprime, _⟩⟩
  have hu0 : 0 ≤ u := by linarith
  have hfloor : (⌊u⌋₊ : ℝ) = u := le_antisymm (Nat.floor_le hu0) hpu
  have hmem : ⌊u⌋₊ ∈ Nat.primesLE ⌊u⌋₊ :=
    Nat.mem_primesLE.mpr ⟨le_rfl, hprime⟩
  have hcountNat : 1 ≤ Nat.primeCounting ⌊u⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.one_le_card.mpr ⟨⌊u⌋₊, hmem⟩
  have hcount : (1 : ℝ) ≤ (paperPi u : ℝ) := by
    change (1 : ℝ) ≤ (Nat.primeCounting ⌊u⌋₊ : ℝ)
    exact_mod_cast hcountNat
  have huPos : 0 < u := by linarith
  exact div_le_div_of_nonneg_right hcount huPos.le

theorem primeReciprocalAbelFormula {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        (p : ℝ)⁻¹ * primeIndicator p) =
      v⁻¹ * (∑ p ∈ Finset.Icc 0 ⌊v⌋₊, primeIndicator p) -
        u⁻¹ * (∑ p ∈ Finset.Icc 0 ⌊u⌋₊, primeIndicator p) -
        ∫ t in Set.Ioc u v,
          deriv (fun t : ℝ => t⁻¹) t *
            (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, primeIndicator p) := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hf_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_trans hu ht.1)))
  have hf_int : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc u v) := by
    have hcont : ContinuousOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc u v) := by
      rw [deriv_inv']
      have hsquare : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc u v) := by
        fun_prop
      have hnonzero : ∀ t ∈ Set.Icc u v, t ^ 2 ≠ 0 := by
        intro t ht
        exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_trans hu ht.1)))
      exact (hsquare.inv₀ hnonzero).neg
    exact hcont.integrableOn_compact isCompact_Icc
  simpa [primeIndicator] using
    (sum_mul_eq_sub_sub_integral_mul
      (fun n : ℕ => if n.Prime then (1 : ℝ) else 0)
      hu0 huv hf_diff hf_int)

theorem primeReciprocalAbelFormula_explicit {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        (p : ℝ)⁻¹ * primeIndicator p) =
      v⁻¹ * (paperPi v : ℝ) - u⁻¹ * (paperPi u : ℝ) +
        ∫ t in Set.Ioc u v,
          (t ^ 2)⁻¹ * (paperPi t : ℝ) := by
  rw [primeReciprocalAbelFormula hu huv]
  simp_rw [primeIndicator_sum, paperPi]
  simp_rw [deriv_inv', neg_mul, integral_neg, sub_neg_eq_add]

theorem primeReciprocal_interval_le_partial_summation {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ primeReciprocalSet u v, 1 / (p : ℝ)) ≤
      v⁻¹ * (paperPi v : ℝ) +
        ∫ t in Set.Ioc u v, (t ^ 2)⁻¹ * (paperPi t : ℝ) := by
  let S := primeReciprocalSet u v
  let S₀ := S.filter fun p => p ≠ ⌊u⌋₊
  let S₁ := S.filter fun p => p = ⌊u⌋₊
  let T := (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  have hsplit : (∑ p ∈ S, 1 / (p : ℝ)) =
      (∑ p ∈ S₀, 1 / (p : ℝ)) + ∑ p ∈ S₁, 1 / (p : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := S)
      (p := fun p => p ≠ ⌊u⌋₊) (f := fun p => 1 / (p : ℝ))]
    simp [S₀, S₁]
  have hsubset : S₀ ⊆ T := by
    dsimp [S₀, T, S]
    exact primeReciprocal_nonendpoint_subset (by linarith)
  have hnonneg : ∀ p ∈ T, p ∉ S₀ → 0 ≤ 1 / (p : ℝ) := by
    intro p _ _
    positivity
  have hS₀ : (∑ p ∈ S₀, 1 / (p : ℝ)) ≤ ∑ p ∈ T, 1 / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hS₁ : (∑ p ∈ S₁, 1 / (p : ℝ)) ≤ (paperPi u : ℝ) / u := by
    by_cases hend : ⌊u⌋₊ ∈ S
    · have hS₁eq : S₁ = {⌊u⌋₊} := by
        ext p
        simp only [S₁, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact And.right
        · intro hp
          subst p
          exact ⟨hend, rfl⟩
      rw [hS₁eq]
      simp only [Finset.sum_singleton]
      rw [show (⌊u⌋₊ : ℝ) = u from
        le_antisymm (Nat.floor_le (by linarith)) (Finset.mem_filter.mp hend).2]
      exact primeReciprocal_endpoint_le_count hu hend
    · have hS₁empty : S₁ = ∅ := by
        ext p
        simp only [S₁, Finset.mem_filter]
        constructor
        · rintro ⟨hpS, rfl⟩
          exact (hend hpS).elim
        · intro h
          simpa using h
      rw [hS₁empty]
      simp
      positivity
  have hTsum : (∑ p ∈ T, 1 / (p : ℝ)) =
      v⁻¹ * (paperPi v : ℝ) - u⁻¹ * (paperPi u : ℝ) +
        ∫ t in Set.Ioc u v, (t ^ 2)⁻¹ * (paperPi t : ℝ) := by
    calc
      (∑ p ∈ T, 1 / (p : ℝ)) =
          ∑ p ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
            (p : ℝ)⁻¹ * primeIndicator p := by
        dsimp [T]
        simpa [one_div] using
          (primeIndicator_weighted_sum_eq_filter
            (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)).symm
      _ = v⁻¹ * (paperPi v : ℝ) - u⁻¹ * (paperPi u : ℝ) +
          ∫ t in Set.Ioc u v, (t ^ 2)⁻¹ * (paperPi t : ℝ) :=
        primeReciprocalAbelFormula_explicit hu huv
  calc
    (∑ p ∈ S, 1 / (p : ℝ)) =
        (∑ p ∈ S₀, 1 / (p : ℝ)) + ∑ p ∈ S₁, 1 / (p : ℝ) := hsplit
    _ ≤ (∑ p ∈ T, 1 / (p : ℝ)) + (paperPi u : ℝ) / u := add_le_add hS₀ hS₁
    _ = v⁻¹ * (paperPi v : ℝ) +
        ∫ t in Set.Ioc u v, (t ^ 2)⁻¹ * (paperPi t : ℝ) := by
      rw [hTsum]
      ring

private theorem paperPi_integrand_integrableOn {u v : ℝ} (hu : 2 ≤ u) :
    IntegrableOn (fun t : ℝ => (paperPi t : ℝ) / t ^ 2) (Set.Ioc u v) := by
  have hpi : Measurable fun t : ℝ => (paperPi t : ℝ) := by
    exact (measurable_of_countable fun n : ℕ => (Nat.primeCounting n : ℝ)).comp
      Nat.measurable_floor
  apply Measure.integrableOn_of_bounded (μ := volume) (s := Set.Ioc u v)
  · exact measure_Ioc_lt_top.ne
  · exact (hpi.div (measurable_id.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htu : 2 ≤ t := (lt_of_le_of_lt hu ht.1).le
    have htv : t ≤ v := ht.2
    have hpi_le : paperPi t ≤ paperPi v := by
      exact Nat.monotone_primeCounting (Nat.floor_mono htv)
    have hpi_nonneg : 0 ≤ (paperPi t : ℝ) := Nat.cast_nonneg _
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    have hratio : 0 ≤ (paperPi t : ℝ) / t ^ 2 := div_nonneg hpi_nonneg (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hratio]
    calc
      (paperPi t : ℝ) / t ^ 2 ≤ (paperPi t : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      _ ≤ (paperPi v : ℝ) := by exact_mod_cast hpi_le

theorem paperPi_integral_bound {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (∫ t in Set.Ioc u v, (paperPi t : ℝ) / t ^ 2) ≤
      8 * (Real.log (Real.log v) - Real.log (Real.log u)) := by
  let g : ℝ → ℝ := fun t => 8 * (t⁻¹ / Real.log t)
  have hg_cont : ContinuousOn g (Set.Icc u v) := by
    dsimp [g]
    have hlog : ContinuousOn Real.log (Set.Icc u v) := by
      refine ContinuousOn.mono Real.continuousOn_log ?_
      intro t ht
      exact ne_of_gt (by linarith [ht.1, hu])
    have hlogpos : ∀ t ∈ Set.Icc u v, 0 < Real.log t := by
      intro t ht
      apply Real.log_pos
      linarith [ht.1, hu]
    have htne : ∀ t ∈ Set.Icc u v, t ≠ 0 := by
      intro t ht
      linarith [ht.1, hu]
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc u v) :=
      continuousOn_id.inv₀ htne
    exact continuousOn_const.mul (hinv.div hlog (fun t ht => ne_of_gt (hlogpos t ht)))
  have hg_int : IntegrableOn g (Set.Ioc u v) :=
    (hg_cont.integrableOn_compact isCompact_Icc).mono_set (by
      intro t ht
      exact ⟨ht.1.le, ht.2⟩)
  have hpoint : ∀ t ∈ Set.Ioc u v,
      (paperPi t : ℝ) / t ^ 2 ≤ g t := by
    intro t ht
    have ht2 : 2 ≤ t := (lt_of_le_of_lt hu ht.1).le
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hpi := paperPi_upper_bound ht2
    rw [le_div_iff₀ hlogpos] at hpi
    dsimp [g]
    rw [div_le_iff₀ (by positivity : 0 < t ^ 2)]
    field_simp
    nlinarith [hpi]
  have hmono := setIntegral_mono_on (paperPi_integrand_integrableOn hu)
    hg_int measurableSet_Ioc hpoint
  conv_rhs at hmono => rw [← intervalIntegral.integral_of_le huv]
  rw [intervalIntegral.integral_const_mul, integral_inv_div_log
    (by linarith [hu]) (by linarith [huv, hu])] at hmono
  simpa [g] using hmono

theorem primeReciprocal_sum_bound {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ primeReciprocalSet u v, 1 / (p : ℝ)) ≤
      12 + 8 * Real.log (Real.log v / Real.log u) := by
  have hv : 2 ≤ v := le_trans hu huv
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith [hu])
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith [hv])
  have hlogv_ge : 2 / 3 ≤ Real.log v :=
    sieveLogTwo_bounds.1.trans (Real.log_le_log (by norm_num) hv)
  have hboundary : v⁻¹ * (paperPi v : ℝ) ≤ 8 / Real.log v := by
    calc
      v⁻¹ * (paperPi v : ℝ) ≤ v⁻¹ * (8 * v / Real.log v) :=
        mul_le_mul_of_nonneg_left (paperPi_upper_bound hv)
          (inv_nonneg.mpr (by linarith [hv]))
      _ = 8 / Real.log v := by field_simp
  have hboundary12 : v⁻¹ * (paperPi v : ℝ) ≤ 12 := by
    calc
      v⁻¹ * (paperPi v : ℝ) ≤ 8 / Real.log v := hboundary
      _ ≤ 12 := (div_le_iff₀ hlogv).2 (by nlinarith)
  have hlogratio :
      Real.log (Real.log v / Real.log u) =
        Real.log (Real.log v) - Real.log (Real.log u) := by
    rw [Real.log_div (ne_of_gt hlogv) (ne_of_gt hlogu)]
  have hsum := primeReciprocal_interval_le_partial_summation hu huv
  have hsum' :
      (∑ p ∈ primeReciprocalSet u v, 1 / (p : ℝ)) ≤
        v⁻¹ * (paperPi v : ℝ) +
          ∫ t in Set.Ioc u v, (paperPi t : ℝ) / t ^ 2 := by
    simpa [div_eq_mul_inv, mul_comm] using hsum
  have hint := paperPi_integral_bound hu huv
  calc
    (∑ p ∈ primeReciprocalSet u v, 1 / (p : ℝ)) ≤
        v⁻¹ * (paperPi v : ℝ) +
          ∫ t in Set.Ioc u v, (paperPi t : ℝ) / t ^ 2 := hsum'
    _ ≤ 12 + 8 * Real.log (Real.log v / Real.log u) := by
      rw [hlogratio]
      exact add_le_add hboundary12 hint

theorem primeProductIntervalDimensionBound {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    (∏ p ∈ primeReciprocalSet u v, (1 - 1 / (p : ℝ))⁻¹) ≤
      sieveConstantC * (Real.log v / Real.log u) ^ sieveK := by
  let S := primeReciprocalSet u v
  have hv : 2 ≤ v := le_trans hu huv
  have hN : 2 ≤ ⌊v⌋₊ := Nat.le_floor (by exact_mod_cast hv)
  have hSN : S ⊆ Finset.Icc 2 ⌊v⌋₊ := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpv, _⟩
    change p ∈ sievePrimesBelow v at hpv
    rcases Finset.mem_filter.mp hpv with ⟨_, ⟨hprime, hp_lt_v⟩⟩
    exact Finset.mem_Icc.mpr
      ⟨hprime.two_le, Nat.le_floor (by exact_mod_cast hp_lt_v.le)⟩
  have hprod_eq :
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) =
        ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
    have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
    field_simp
    <;> ring
  have hlogprod :
      Real.log (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) =
        ∑ p ∈ S, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    apply Real.log_prod
    intro p hp
    apply div_ne_zero
    · have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
      exact ne_of_gt (by linarith)
    · have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      exact sub_ne_zero.mpr (by
        have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
        linarith)
  have hlogsum :
      (∑ p ∈ S, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
        13 + 8 * Real.log (Real.log v / Real.log u) := by
    calc
      _ ≤ (∑ p ∈ S, 1 / (p : ℝ)) + 1 :=
        sum_log_prime_ratio_le_reciprocals_add_one hN hSN
      _ ≤ (12 + 8 * Real.log (Real.log v / Real.log u)) + 1 :=
        by linarith [primeReciprocal_sum_bound hu huv]
      _ = 13 + 8 * Real.log (Real.log v / Real.log u) := by ring
  have hratio : 0 < Real.log v / Real.log u :=
    div_pos (Real.log_pos (by linarith [hv])) (Real.log_pos (by linarith [hu]))
  have hprod_pos : 0 < ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_pos fun p hp => div_pos (by
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith) (by
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith)
  have hmain :
      (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) ≤
        Real.exp 13 * (Real.log v / Real.log u) ^ (8 : ℝ) := by
    have hlogprod_bound :
        Real.log (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) ≤
          13 + 8 * Real.log (Real.log v / Real.log u) := by
      rw [hlogprod]
      exact hlogsum
    have hpow :
        Real.exp (8 * Real.log (Real.log v / Real.log u)) =
          (Real.log v / Real.log u) ^ (8 : ℝ) := by
      calc
        Real.exp (8 * Real.log (Real.log v / Real.log u)) =
            Real.exp ((8 : ℕ) * Real.log (Real.log v / Real.log u)) := by
          congr 1
        _ = Real.exp (Real.log (Real.log v / Real.log u)) ^ 8 :=
          Real.exp_nat_mul _ _
        _ = (Real.log v / Real.log u) ^ (8 : ℝ) := by
          rw [Real.exp_log hratio]
          exact (Real.rpow_natCast _ _).symm
    calc
      (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) =
          Real.exp (Real.log (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1))) :=
        (Real.exp_log hprod_pos).symm
      _ ≤ Real.exp (13 + 8 * Real.log (Real.log v / Real.log u)) :=
        Real.exp_le_exp.mpr hlogprod_bound
      _ = Real.exp 13 * Real.exp (8 * Real.log (Real.log v / Real.log u)) := by
        rw [Real.exp_add]
      _ = Real.exp 13 * (Real.log v / Real.log u) ^ (8 : ℝ) := by rw [hpow]
  rw [hprod_eq, sieveConstantC, sieveK]
  exact hmain

theorem sievePrimesBelow_iff (z : ℝ) (p : ℕ) :
    p ∈ sievePrimesBelow z ↔ p.Prime ∧ (p : ℝ) < z := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨_, hp⟩
    exact hp
  · rintro ⟨hp, hpz⟩
    have hpfloor : p ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hpz.le)
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · exact ⟨hp, hpz⟩

private theorem sievePrimesBelow_subset {a z : ℝ} (haz : a ≤ z) :
    sievePrimesBelow a ⊆ sievePrimesBelow z := by
  intro p hp
  rw [sievePrimesBelow_iff] at hp ⊢
  exact ⟨hp.1, lt_of_lt_of_le hp.2 haz⟩

private theorem sievePrimesBelow_sdiff_eq {a z : ℝ} :
    sievePrimesBelow z \ sievePrimesBelow a = primeReciprocalSet a z := by
  ext p
  rw [Finset.mem_sdiff, sievePrimesBelow_iff, sievePrimesBelow_iff,
    primeReciprocalSet, Finset.mem_filter, sievePrimesBelow_iff]
  constructor
  · rintro ⟨⟨hp, hpz⟩, hnot⟩
    refine ⟨⟨hp, hpz⟩, ?_⟩
    by_contra hpa
    exact hnot ⟨hp, lt_of_not_ge hpa⟩
  · rintro ⟨⟨hp, hpz⟩, hap⟩
    refine ⟨⟨hp, hpz⟩, ?_⟩
    rintro ⟨_, hpa⟩
    exact (not_lt_of_ge hap) hpa

theorem sieveDensityProduct_pos {z : ℝ} : 0 < sieveDensityProduct z := by
  apply Finset.prod_pos
  intro p hp
  rw [sievePrimesBelow_iff] at hp
  have hp2 : 2 ≤ p := hp.1.two_le
  have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp2
  have hrecip : 1 / (p : ℝ) < 1 := by
    rw [div_lt_iff₀ (by linarith : 0 < (p : ℝ))]
    linarith
  linarith

theorem sieveDensityProduct_interval_bound {a z : ℝ}
    (ha : 2 ≤ a) (haz : a ≤ z) :
    sieveDensityProduct a / sieveDensityProduct z ≤
      sieveConstantC * (Real.log z / Real.log a) ^ sieveK := by
  have hsubset := sievePrimesBelow_subset haz
  have hratio :
      sieveDensityProduct a / sieveDensityProduct z =
        ∏ p ∈ primeReciprocalSet a z, (1 - 1 / (p : ℝ))⁻¹ := by
    have hdiff := sievePrimesBelow_sdiff_eq (a := a) (z := z)
    have hdecomp :
        (∏ p ∈ sievePrimesBelow z \ sievePrimesBelow a,
          (1 - 1 / (p : ℝ))) * sieveDensityProduct a =
          sieveDensityProduct z := by
      simpa [sieveDensityProduct] using
        (Finset.prod_sdiff (s₁ := sievePrimesBelow a)
          (s₂ := sievePrimesBelow z)
          (f := fun p => (1 - 1 / (p : ℝ))) hsubset)
    have hprod_sdiff :
        (∏ p ∈ sievePrimesBelow z \ sievePrimesBelow a,
          (1 - 1 / (p : ℝ))) =
          sieveDensityProduct z / sieveDensityProduct a := by
      calc
        _ = _ * sieveDensityProduct a / sieveDensityProduct a := by
          field_simp [ne_of_gt (sieveDensityProduct_pos (z := a))]
        _ = _ := by rw [hdecomp]
    have hprod :
        ∏ p ∈ primeReciprocalSet a z, (1 - 1 / (p : ℝ)) =
          sieveDensityProduct z / sieveDensityProduct a := by
      rw [← hdiff]
      simpa [sieveDensityProduct] using hprod_sdiff
    calc
      sieveDensityProduct a / sieveDensityProduct z =
          (sieveDensityProduct z / sieveDensityProduct a)⁻¹ := by
        field_simp [ne_of_gt (sieveDensityProduct_pos (z := a)),
          ne_of_gt (sieveDensityProduct_pos (z := z))]
      _ = (∏ p ∈ primeReciprocalSet a z, (1 - 1 / (p : ℝ)))⁻¹ := by rw [← hprod]
      _ = ∏ p ∈ primeReciprocalSet a z, (1 - 1 / (p : ℝ))⁻¹ := by
        rw [← Finset.prod_inv_distrib]
  rw [hratio]
  exact primeProductIntervalDimensionBound ha haz

private theorem sievePrimesBelow_empty_of_le_two {x : ℝ} (hx : x ≤ 2) :
    sievePrimesBelow x = ∅ := by
  ext p
  rw [sievePrimesBelow_iff]
  constructor
  · rintro ⟨hp, hpx⟩
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    exact False.elim (not_lt_of_ge hp2 (lt_of_lt_of_le hpx hx))
  · intro h
    simpa using h

theorem sieveDensityProduct_dimension_bound {a z : ℝ}
    (ha : 1 < a) (haz : a < z) (hz : 2 ≤ z) :
    sieveDensityProduct a / sieveDensityProduct z ≤
      sieveConstantC * (Real.log z / Real.log a) ^ sieveK := by
  by_cases ha2 : 2 ≤ a
  · exact sieveDensityProduct_interval_bound ha2 haz.le
  · have ha_lt_two : a < 2 := lt_of_not_ge ha2
    have hseta := sievePrimesBelow_empty_of_le_two ha_lt_two.le
    have hset2 := sievePrimesBelow_empty_of_le_two (x := (2 : ℝ)) le_rfl
    have hVa : sieveDensityProduct a = 1 := by
      simp [sieveDensityProduct, hseta]
    have hV2 : sieveDensityProduct 2 = 1 := by
      simp [sieveDensityProduct, hset2]
    have hbase := sieveDensityProduct_interval_bound (a := 2) (z := z)
      (by norm_num) hz
    have hbase' : 1 / sieveDensityProduct z ≤
        sieveConstantC * (Real.log z / Real.log 2) ^ sieveK := by
      simpa [hV2] using hbase
    have hloga : 0 < Real.log a := Real.log_pos ha
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith [hz])
    have hloga_le : Real.log a ≤ Real.log 2 :=
      Real.log_le_log (by linarith [ha]) ha_lt_two.le
    have hquot : Real.log z / Real.log 2 ≤ Real.log z / Real.log a := by
      rw [div_le_div_iff₀ hlog2 hloga]
      nlinarith [mul_le_mul_of_nonneg_left hloga_le hlogz.le]
    have hpow :
        (Real.log z / Real.log 2) ^ sieveK ≤
          (Real.log z / Real.log a) ^ sieveK := by
      apply Real.rpow_le_rpow (by positivity) hquot
      norm_num [sieveK]
    calc
      sieveDensityProduct a / sieveDensityProduct z =
          1 / sieveDensityProduct z := by rw [hVa]
      _ ≤ sieveConstantC * (Real.log z / Real.log 2) ^ sieveK := hbase'
      _ ≤ sieveConstantC * (Real.log z / Real.log a) ^ sieveK :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos 13).le

theorem primeReciprocal_sum_dimension_bound {a z : ℝ}
    (ha : 1 < a) (haz : a < z) (hz : 2 ≤ z) :
    (∑ p ∈ primeReciprocalSet a z, 1 / (p : ℝ)) ≤
      Real.log sieveConstantC + sieveK * Real.log (Real.log z / Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith [hz])
  by_cases ha2 : 2 ≤ a
  · have hsum := primeReciprocal_sum_bound ha2 haz.le
    rw [sieveConstantC, Real.log_exp, sieveK]
    linarith
  · have ha_lt_two : a < 2 := lt_of_not_ge ha2
    have hset : primeReciprocalSet a z = primeReciprocalSet 2 z := by
      ext p
      simp only [primeReciprocalSet, Finset.mem_filter, sievePrimesBelow_iff]
      constructor
      · rintro ⟨⟨hp, hpz⟩, hap⟩
        refine ⟨⟨hp, hpz⟩, ?_⟩
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        exact hp2
      · rintro ⟨⟨hp, hpz⟩, hp2⟩
        refine ⟨⟨hp, hpz⟩, ?_⟩
        exact le_trans (le_of_lt ha_lt_two) hp2
    have hloga_le : Real.log a ≤ Real.log 2 :=
      Real.log_le_log (by linarith [ha]) ha_lt_two.le
    have hquot : Real.log z / Real.log 2 ≤ Real.log z / Real.log a := by
      rw [div_le_div_iff₀ hlog2 hloga]
      nlinarith [mul_le_mul_of_nonneg_left hloga_le hlogz.le]
    have hlogquot :
        Real.log (Real.log z / Real.log 2) ≤
          Real.log (Real.log z / Real.log a) :=
      Real.log_le_log (div_pos hlogz hlog2) hquot
    have hsum := primeReciprocal_sum_bound (u := 2) (v := z) (by norm_num) hz
    rw [hset, sieveConstantC, Real.log_exp, sieveK]
    linarith


end

end FractionalPrimes

end
