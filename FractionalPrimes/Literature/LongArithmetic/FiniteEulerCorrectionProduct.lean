module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.EulerProduct.Basic

@[expose] public section

noncomputable section

open Complex Set
open scoped BigOperators

namespace FractionalPrimes.Literature.LongArithmetic

private theorem finiteEulerCorrectionDenominator_ne_zero
    (p : Nat.Primes) (z : ℂ) (hz : ‖z‖ ≤ 1) {s : ℂ}
    (hs : 0 < s.re) :
    1 - z * (p : ℂ) ^ (-s) ≠ 0 := by
  have hpow_norm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_natCast_cpow_of_pos (mod_cast p.prop.pos) (-s)
  have hpow_lt : (p : ℝ) ^ (-s.re) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  have hpow_norm_lt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hpow_norm]
    exact hpow_lt
  intro hzero
  have heq : (1 : ℂ) = z * (p : ℂ) ^ (-s) := sub_eq_zero.mp hzero
  have hnormeq := congrArg norm heq
  rw [norm_one, norm_mul] at hnormeq
  have hmul : ‖z‖ * ‖(p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
    calc
      ‖z‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
  have honele : (1 : ℝ) ≤ ‖(p : ℂ) ^ (-s)‖ := by linarith [hnormeq, hmul]
  exact (not_lt_of_ge honele) hpow_norm_lt

/-- A single corrected Euler factor is analytic wherever the real part of the
Dirichlet variable is positive. -/
theorem analyticOnNhd_finiteEulerCorrectionFactor
    (p : Nat.Primes) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    AnalyticOnNhd ℂ
      (fun s : ℂ => (1 - z * (p : ℂ) ^ (-s))⁻¹) {s : ℂ | 0 < s.re} := by
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => (p : ℂ) ^ (-s))
      {s : ℂ | 0 < s.re} := by
    apply AnalyticOnNhd.cpow (f := fun _ : ℂ => (p : ℂ))
      (g := fun s : ℂ => -s) analyticOnNhd_const analyticOnNhd_id.neg
    intro s hs
    exact Complex.natCast_mem_slitPlane.mpr p.prop.ne_zero
  have hden : AnalyticOnNhd ℂ
      (fun s : ℂ => 1 - z * (p : ℂ) ^ (-s)) {s : ℂ | 0 < s.re} := by
    exact analyticOnNhd_const.sub (analyticOnNhd_const.mul hpow)
  apply hden.inv
  intro s hs
  exact finiteEulerCorrectionDenominator_ne_zero p z hz hs

#print axioms finiteEulerCorrectionDenominator_ne_zero
#print axioms analyticOnNhd_finiteEulerCorrectionFactor

/-- The reciprocal correction for a finite set of distinct prime factors. The
coefficient `z p` is kept explicit so the same analytic result applies to the
principal-modulus factors and to the factors removed by the Möbius multiplier. -/
def finiteEulerCorrectionProduct (S : Finset Nat.Primes)
    (z : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - z p * (p : ℂ) ^ (-s))⁻¹

/-- The distinct prime divisors of a natural number, represented by the prime
subtype so that the local factor retains a prime proof. -/
def finitePrimeDivisors (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.attach.map
    ⟨fun p => (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes), by
      intro a b hab
      have hval : a.1 = b.1 := congrArg (fun x : Nat.Primes => (x : ℕ)) hab
      exact Subtype.ext hval⟩

theorem mem_finitePrimeDivisors {n : ℕ} {p : Nat.Primes} :
    p ∈ finitePrimeDivisors n ↔ (p : ℕ) ∈ n.primeFactors := by
  rw [finitePrimeDivisors, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hmap⟩
    have hval : a.1 = (p : ℕ) :=
      congrArg (fun x : Nat.Primes => (x : ℕ)) hmap
    exact hval ▸ a.2
  · intro hp
    refine ⟨⟨(p : ℕ), hp⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

/-- Analyticity of a finite Euler correction product on the positive
half-plane. -/
theorem analyticOnNhd_finiteEulerCorrectionProduct
    (S : Finset Nat.Primes) (z : Nat.Primes → ℂ)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ 1) :
    AnalyticOnNhd ℂ (finiteEulerCorrectionProduct S z)
      {s : ℂ | 0 < s.re} := by
  classical
  change AnalyticOnNhd ℂ
    (fun s : ℂ => ∏ p ∈ S, (1 - z p * (p : ℂ) ^ (-s))⁻¹)
      {s : ℂ | 0 < s.re}
  exact Finset.analyticOnNhd_fun_prod S (fun p hp =>
    analyticOnNhd_finiteEulerCorrectionFactor p (z p) (hz p hp))

/-- Every finite Euler correction product with coefficients of norm at most
one is nonzero on the positive half-plane. -/
theorem finiteEulerCorrectionProduct_ne_zero
    (S : Finset Nat.Primes) (z : Nat.Primes → ℂ)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    finiteEulerCorrectionProduct S z s ≠ 0 := by
  classical
  unfold finiteEulerCorrectionProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact inv_ne_zero
    (finiteEulerCorrectionDenominator_ne_zero p (z p) (hz p hp) hs)

/-- The principal-character correction from primes dividing its modulus. Its
coefficients are identically one. -/
def qPrimeEulerCorrectionProduct (q : ℕ) (s : ℂ) : ℂ :=
  finiteEulerCorrectionProduct (finitePrimeDivisors q) (fun _ => 1) s

/-- The Möbius-multiplier correction from primes dividing `r`. Its local
coefficients are supplied by the character. -/
def rPrimeEulerCorrectionProduct (r : ℕ)
    (χp : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  finiteEulerCorrectionProduct (finitePrimeDivisors r) χp s

theorem analyticOnNhd_qPrimeEulerCorrectionProduct
    (q : ℕ) :
    AnalyticOnNhd ℂ (qPrimeEulerCorrectionProduct q)
      {s : ℂ | 0 < s.re} := by
  exact analyticOnNhd_finiteEulerCorrectionProduct (finitePrimeDivisors q) (fun _ => 1)
    (by intro p hp; norm_num)

theorem qPrimeEulerCorrectionProduct_ne_zero
    (q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    qPrimeEulerCorrectionProduct q s ≠ 0 := by
  exact finiteEulerCorrectionProduct_ne_zero (finitePrimeDivisors q) (fun _ => 1)
    (by intro p hp; norm_num) hs

theorem analyticOnNhd_rPrimeEulerCorrectionProduct
    (r : ℕ) (χp : Nat.Primes → ℂ)
    (hχp : ∀ p ∈ finitePrimeDivisors r, ‖χp p‖ ≤ 1) :
    AnalyticOnNhd ℂ (rPrimeEulerCorrectionProduct r χp)
      {s : ℂ | 0 < s.re} :=
  analyticOnNhd_finiteEulerCorrectionProduct (finitePrimeDivisors r) χp hχp

theorem rPrimeEulerCorrectionProduct_ne_zero
    (r : ℕ) (χp : Nat.Primes → ℂ)
    (hχp : ∀ p ∈ finitePrimeDivisors r, ‖χp p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) :
    rPrimeEulerCorrectionProduct r χp s ≠ 0 :=
  finiteEulerCorrectionProduct_ne_zero (finitePrimeDivisors r) χp hχp hs

#print axioms analyticOnNhd_finiteEulerCorrectionProduct
#print axioms finiteEulerCorrectionProduct_ne_zero
#print axioms analyticOnNhd_qPrimeEulerCorrectionProduct
#print axioms qPrimeEulerCorrectionProduct_ne_zero
#print axioms analyticOnNhd_rPrimeEulerCorrectionProduct
#print axioms rPrimeEulerCorrectionProduct_ne_zero

end FractionalPrimes.Literature.LongArithmetic

end
