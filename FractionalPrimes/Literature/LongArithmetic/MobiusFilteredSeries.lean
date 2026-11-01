module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FractionalPrimes.Literature.LongArithmetic.MobiusMultiplierCoefficient
public import FractionalPrimes.Literature.LongArithmetic.TprodRemoval

@[expose] public section

noncomputable section

open scoped ArithmeticFunction.Moebius LSeries.notation

namespace FractionalPrimes.Literature.LongArithmetic

/-- The absolutely convergent Möbius-weighted Dirichlet series for a completely
multiplicative coefficient map. The map-to-zero type is the canonical extension
of the paper's function on positive integers. -/
def mobiusWeightedDirichletSeries (χ : ℕ →*₀ ℂ) (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * χ n) s

/-- The summand in the Euler-product form of the Möbius-weighted series. -/
def mobiusWeightedEulerTerm (χ : ℕ →*₀ ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * χ n * (n : ℂ) ^ (-s)

def mobiusWeightedCoeff (χ : ℕ →*₀ ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * χ n

/-- The local linear Euler factor associated to a prime. -/
def mobiusEulerFactor (χ : ℕ →*₀ ℂ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  1 - χ p * (p : ℂ) ^ (-s)

private theorem mobiusWeightedCoeff_norm_le_one (χ : ℕ →*₀ ℂ)
    (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ) * χ n‖ ≤ 1 := by
  rw [norm_mul]
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  by_cases hn : n = 0
  · simp [hn] at *
  · exact (mul_le_mul hμ (hχ n hn) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem mobiusWeightedDirichletSeries_absolutelyConvergent
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * χ n) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  exact mobiusWeightedCoeff_norm_le_one χ hχ n

private theorem mobiusWeightedEulerTerm_eq_LSeries_term
    (χ : ℕ →*₀ ℂ) (s : ℂ) (n : ℕ) :
    mobiusWeightedEulerTerm χ s n =
      LSeries.term (mobiusWeightedCoeff χ) s n := by
  rw [LSeries.term_def₀ (by simp [mobiusWeightedCoeff])]
  simp [mobiusWeightedEulerTerm, mobiusWeightedCoeff]

private theorem mobiusWeightedEulerTerm_norm_summable
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖mobiusWeightedEulerTerm χ s n‖) := by
  have hL := mobiusWeightedDirichletSeries_absolutelyConvergent χ hχ hs
  have hnorm : Summable (fun n => ‖LSeries.term (mobiusWeightedCoeff χ) s n‖) := hL.norm
  exact hnorm.congr fun n => by rw [mobiusWeightedEulerTerm_eq_LSeries_term]

private theorem mobiusWeightedEulerTerm_one (χ : ℕ →*₀ ℂ) (s : ℂ) :
    mobiusWeightedEulerTerm χ s 1 = 1 := by
  simp [mobiusWeightedEulerTerm]

private theorem mobiusWeightedEulerTerm_zero (χ : ℕ →*₀ ℂ) (s : ℂ) :
    mobiusWeightedEulerTerm χ s 0 = 0 := by
  simp [mobiusWeightedEulerTerm]

private theorem mobiusWeightedEulerTerm_mul_of_coprime
    (χ : ℕ →*₀ ℂ) (s : ℂ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    mobiusWeightedEulerTerm χ s (m * n) =
      mobiusWeightedEulerTerm χ s m * mobiusWeightedEulerTerm χ s n := by
  have hμ := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    ArithmeticFunction.isMultiplicative_moebius hmn
  simp only [mobiusWeightedEulerTerm, hμ, Int.cast_mul, χ.map_mul]
  simp only [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

private theorem mobiusWeightedEulerTerm_primePower_tsum
    (χ : ℕ →*₀ ℂ) (s : ℂ) (p : Nat.Primes) :
    (∑' e : ℕ, mobiusWeightedEulerTerm χ s ((p : ℕ) ^ e)) =
      mobiusEulerFactor χ s p := by
  have hterm : ∀ e : ℕ,
      mobiusWeightedEulerTerm χ s ((p : ℕ) ^ e) =
        if e = 0 then 1 else if e = 1 then -(χ (p : ℕ) * (p : ℂ) ^ (-s)) else 0 := by
    intro e
    by_cases he0 : e = 0
    · subst e
      simp [mobiusWeightedEulerTerm]
    by_cases he1 : e = 1
    · subst e
      simp [mobiusWeightedEulerTerm, ArithmeticFunction.moebius_apply_prime p.2]
    · have he : e ≠ 0 := he0
      simp [mobiusWeightedEulerTerm, ArithmeticFunction.moebius_apply_prime_pow p.2 he,
        he0, he1]
  rw [tsum_congr hterm]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [mobiusEulerFactor]
    ring
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    simp [he.1, he.2]

theorem mobiusWeightedEulerProduct_eq
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, mobiusEulerFactor χ s p) =
      mobiusWeightedDirichletSeries χ s := by
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      mobiusWeightedEulerTerm χ s (m * n) =
        mobiusWeightedEulerTerm χ s m * mobiusWeightedEulerTerm χ s n := by
    intro m n hmn
    exact mobiusWeightedEulerTerm_mul_of_coprime χ s hmn
  have hsum := mobiusWeightedEulerTerm_norm_summable χ hχ hs
  have hEuler := EulerProduct.eulerProduct_tprod
    (f := mobiusWeightedEulerTerm χ s)
    (mobiusWeightedEulerTerm_one χ s) hmul hsum (mobiusWeightedEulerTerm_zero χ s)
  have hLocalProd :
      (∏' p : Nat.Primes, mobiusEulerFactor χ s p) =
        (∏' p : Nat.Primes, ∑' e : ℕ,
          mobiusWeightedEulerTerm χ s ((p : ℕ) ^ e)) := by
    exact tprod_congr fun p : Nat.Primes =>
      (mobiusWeightedEulerTerm_primePower_tsum χ s p).symm
  calc
    (∏' p : Nat.Primes, mobiusEulerFactor χ s p) =
        (∏' p : Nat.Primes, ∑' e : ℕ,
          mobiusWeightedEulerTerm χ s ((p : ℕ) ^ e)) := hLocalProd
    _ = ∑' n : ℕ, mobiusWeightedEulerTerm χ s n := hEuler
    _ = mobiusWeightedDirichletSeries χ s := by
      rw [mobiusWeightedDirichletSeries, LSeries]
      exact tsum_congr fun n => by
        change mobiusWeightedEulerTerm χ s n =
          LSeries.term (mobiusWeightedCoeff χ) s n
        exact mobiusWeightedEulerTerm_eq_LSeries_term χ s n

/-- The finite set of distinct prime divisors of a natural number, expressed
as a finset of prime subtypes. -/
def mobiusPrimeDivisors (r : ℕ) : Finset Nat.Primes :=
  r.primeFactors.attach.image
    (fun p => (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))

theorem mem_mobiusPrimeDivisors {r : ℕ} {p : Nat.Primes} :
    p ∈ mobiusPrimeDivisors r ↔ (p : ℕ) ∈ r.primeFactors := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, heq⟩
    have hv : (q : ℕ) = (p : ℕ) :=
      congrArg (fun z : Nat.Primes => (z : ℕ)) heq
    simpa [hv] using q.property
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨⟨(p : ℕ), hp⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

def mobiusAvoidingCoeff (r : ℕ) (χ : ℕ →*₀ ℂ) (n : ℕ) : ℂ :=
  if Nat.Coprime n r then mobiusWeightedCoeff χ n else 0

/-- The Möbius series with the Euler factors for primes dividing `r` removed. -/
def mobiusAvoidingDirichletSeries (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) : ℂ :=
  LSeries (mobiusAvoidingCoeff r χ) s

private def mobiusAvoidingEulerTerm (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if Nat.Coprime n r then mobiusWeightedEulerTerm χ s n else 0

private theorem mobiusAvoidingCoeff_norm_le_one (r : ℕ) (χ : ℕ →*₀ ℂ)
    (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) (n : ℕ) : ‖mobiusAvoidingCoeff r χ n‖ ≤ 1 := by
  unfold mobiusAvoidingCoeff
  by_cases h : Nat.Coprime n r
  · rw [if_pos h]
    exact mobiusWeightedCoeff_norm_le_one χ hχ n
  · simp [h]

private theorem mobiusAvoidingEulerTerm_eq_LSeries_term
    (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) (n : ℕ) :
    mobiusAvoidingEulerTerm r χ s n = LSeries.term (mobiusAvoidingCoeff r χ) s n := by
  have hzero : mobiusAvoidingCoeff r χ 0 = 0 := by
    unfold mobiusAvoidingCoeff
    by_cases h : Nat.Coprime 0 r <;> simp [h, mobiusWeightedCoeff]
  rw [LSeries.term_def₀ hzero]
  by_cases h : Nat.Coprime n r
  · simp [mobiusAvoidingEulerTerm, mobiusAvoidingCoeff, h,
      mobiusWeightedEulerTerm, mobiusWeightedCoeff]
  · simp [mobiusAvoidingEulerTerm, mobiusAvoidingCoeff, h]

private theorem mobiusAvoidingEulerTerm_norm_summable
    (r : ℕ) (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖mobiusAvoidingEulerTerm r χ s n‖) := by
  have hL : LSeriesSummable (mobiusAvoidingCoeff r χ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn => mobiusAvoidingCoeff_norm_le_one r χ hχ n) hs
  have hnorm : Summable (fun n => ‖LSeries.term (mobiusAvoidingCoeff r χ) s n‖) := hL.norm
  exact hnorm.congr fun n => by rw [mobiusAvoidingEulerTerm_eq_LSeries_term]

private theorem mobiusAvoidingEulerTerm_one
    (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) : mobiusAvoidingEulerTerm r χ s 1 = 1 := by
  simp [mobiusAvoidingEulerTerm, mobiusWeightedEulerTerm]

private theorem mobiusAvoidingEulerTerm_zero
    (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) : mobiusAvoidingEulerTerm r χ s 0 = 0 := by
  simp [mobiusAvoidingEulerTerm, mobiusWeightedEulerTerm]

private theorem mobiusAvoidingEulerTerm_mul_of_coprime
    (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    mobiusAvoidingEulerTerm r χ s (m * n) =
      mobiusAvoidingEulerTerm r χ s m * mobiusAvoidingEulerTerm r χ s n := by
  have hbase := mobiusWeightedEulerTerm_mul_of_coprime χ s hmn
  have hcop : Nat.Coprime (m * n) r ↔ Nat.Coprime m r ∧ Nat.Coprime n r :=
    Nat.coprime_mul_iff_left
  simp only [mobiusAvoidingEulerTerm, hcop]
  by_cases hm : Nat.Coprime m r
  · by_cases hn : Nat.Coprime n r
    · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn, hbase]
    · have hnot : ¬(Nat.Coprime m r ∧ Nat.Coprime n r) := fun h => hn h.2
      rw [if_neg hnot, if_pos hm, if_neg hn]
      simp
  · by_cases hn : Nat.Coprime n r
    · have hnot : ¬(Nat.Coprime m r ∧ Nat.Coprime n r) := fun h => hm h.1
      rw [if_neg hnot, if_neg hm, if_pos hn]
      simp
    · have hnot : ¬(Nat.Coprime m r ∧ Nat.Coprime n r) := fun h => hm h.1
      rw [if_neg hnot, if_neg hm, if_neg hn]
      simp

private theorem mobiusAvoidingPrimePower_tsum
    (r : ℕ) (χ : ℕ →*₀ ℂ) (s : ℂ) (p : Nat.Primes) :
    (∑' e : ℕ, mobiusAvoidingEulerTerm r χ s ((p : ℕ) ^ e)) =
      if (p : ℕ) ∣ r then 1 else mobiusEulerFactor χ s p := by
  have hterm : ∀ e : ℕ,
      mobiusAvoidingEulerTerm r χ s ((p : ℕ) ^ e) =
        if e = 0 then 1 else if e = 1 then
          if (p : ℕ) ∣ r then 0 else -(χ p * (p : ℂ) ^ (-s)) else 0 := by
    intro e
    by_cases he0 : e = 0
    · subst e
      simp [mobiusAvoidingEulerTerm, mobiusWeightedEulerTerm]
    by_cases he1 : e = 1
    · subst e
      simp [mobiusAvoidingEulerTerm, mobiusWeightedEulerTerm,
        ArithmeticFunction.moebius_apply_prime p.2,
        Nat.Prime.coprime_iff_not_dvd p.2]
    · have he : e ≠ 0 := he0
      simp [mobiusAvoidingEulerTerm, mobiusWeightedEulerTerm,
        ArithmeticFunction.moebius_apply_prime_pow p.2 he, he0, he1]
  rw [tsum_congr hterm, tsum_eq_sum (s := {0, 1})]
  · by_cases hp : (p : ℕ) ∣ r <;> simp [mobiusEulerFactor, hp] <;> ring
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    simp [he.1, he.2]

theorem mobiusAvoidingEulerProduct_eq
    (r : ℕ) (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes,
      if (p : ℕ) ∣ r then 1 else mobiusEulerFactor χ s p) =
      mobiusAvoidingDirichletSeries r χ s := by
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      mobiusAvoidingEulerTerm r χ s (m * n) =
        mobiusAvoidingEulerTerm r χ s m * mobiusAvoidingEulerTerm r χ s n := by
    intro m n hmn
    exact mobiusAvoidingEulerTerm_mul_of_coprime r χ s hmn
  have hsum := mobiusAvoidingEulerTerm_norm_summable r χ hχ hs
  have hEuler := EulerProduct.eulerProduct_tprod
    (f := mobiusAvoidingEulerTerm r χ s)
    (mobiusAvoidingEulerTerm_one r χ s) hmul hsum
    (mobiusAvoidingEulerTerm_zero r χ s)
  have hLocalProd :
      (∏' p : Nat.Primes,
        if (p : ℕ) ∣ r then 1 else mobiusEulerFactor χ s p) =
      (∏' p : Nat.Primes, ∑' e : ℕ,
        mobiusAvoidingEulerTerm r χ s ((p : ℕ) ^ e)) := by
    exact tprod_congr fun p : Nat.Primes =>
      (mobiusAvoidingPrimePower_tsum r χ s p).symm
  calc
    (∏' p : Nat.Primes,
      if (p : ℕ) ∣ r then 1 else mobiusEulerFactor χ s p) =
        (∏' p : Nat.Primes, ∑' e : ℕ,
          mobiusAvoidingEulerTerm r χ s ((p : ℕ) ^ e)) := hLocalProd
    _ = ∑' n : ℕ, mobiusAvoidingEulerTerm r χ s n := hEuler
    _ = mobiusAvoidingDirichletSeries r χ s := by
      rw [mobiusAvoidingDirichletSeries, LSeries]
      exact tsum_congr fun n => by
        change mobiusAvoidingEulerTerm r χ s n =
          LSeries.term (mobiusAvoidingCoeff r χ) s n
        exact mobiusAvoidingEulerTerm_eq_LSeries_term r χ s n

theorem mobiusPrimeDivisor_mem_iff_dvd {r : ℕ} (hr : r ≠ 0)
    (p : Nat.Primes) : p ∈ mobiusPrimeDivisors r ↔ (p : ℕ) ∣ r := by
  rw [mem_mobiusPrimeDivisors, Nat.mem_primeFactors]
  simp [p.2, hr]

/-- Every local Möbius Euler factor is nonzero in the half-plane of absolute
convergence. -/
theorem mobiusEulerFactor_ne_zero
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    mobiusEulerFactor χ s p ≠ 0 := by
  have hnorm : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    grw [norm_mul, hχ (p : ℕ) p.2.ne_zero,
      Complex.norm_natCast_cpow_of_pos (mod_cast p.2.pos), Complex.neg_re, one_mul]
    exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.2.one_lt) (by linarith)
  have hneq : χ p * (p : ℂ) ^ (-s) ≠ 1 := by
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  simpa [mobiusEulerFactor] using (sub_ne_zero.mpr hneq.symm)

private theorem mobiusEulerFactor_multipliable
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Multipliable (mobiusEulerFactor χ s) := by
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      mobiusWeightedEulerTerm χ s (m * n) =
        mobiusWeightedEulerTerm χ s m * mobiusWeightedEulerTerm χ s n := by
    intro m n hmn
    exact mobiusWeightedEulerTerm_mul_of_coprime χ s hmn
  have hsum := mobiusWeightedEulerTerm_norm_summable χ hχ hs
  have hprod := EulerProduct.eulerProduct_hasProd
    (f := mobiusWeightedEulerTerm χ s)
    (mobiusWeightedEulerTerm_one χ s) hmul hsum (mobiusWeightedEulerTerm_zero χ s)
  have hprod' : HasProd (mobiusEulerFactor χ s)
      (∑' n : ℕ, mobiusWeightedEulerTerm χ s n) :=
    hprod.congr_fun fun p => (mobiusWeightedEulerTerm_primePower_tsum χ s p).symm
  have hseries : (∑' n : ℕ, mobiusWeightedEulerTerm χ s n) =
      mobiusWeightedDirichletSeries χ s := by
    rw [mobiusWeightedDirichletSeries, LSeries]
    exact tsum_congr fun n => by
      change mobiusWeightedEulerTerm χ s n = LSeries.term (mobiusWeightedCoeff χ) s n
      exact mobiusWeightedEulerTerm_eq_LSeries_term χ s n
  rw [hseries] at hprod'
  exact hprod'.multipliable

private theorem mobiusAvoidingSeries_eq_weightedSeries_mul_removedFactors
    (r : ℕ) (hr : r ≠ 0) (χ : ℕ →*₀ ℂ)
    (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    mobiusAvoidingDirichletSeries r χ s =
      mobiusWeightedDirichletSeries χ s *
        ∏ p ∈ mobiusPrimeDivisors r, (mobiusEulerFactor χ s p)⁻¹ := by
  let S := mobiusPrimeDivisors r
  let u := mobiusEulerFactor χ s
  have hmem (p : Nat.Primes) : p ∈ S ↔ (p : ℕ) ∣ r :=
    mobiusPrimeDivisor_mem_iff_dvd hr p
  have hu : Multipliable u := mobiusEulerFactor_multipliable χ hχ hs
  have hfnz : ∀ p ∈ S, u p ≠ 0 := by
    intro p hp
    exact mobiusEulerFactor_ne_zero χ hχ hs p
  have hremove := tprod_remove_finset u hu S hfnz
  have hweighted : (∏' p : Nat.Primes, u p) =
      mobiusWeightedDirichletSeries χ s := mobiusWeightedEulerProduct_eq χ hχ hs
  have hfactor : (∏' p : Nat.Primes, if (p : ℕ) ∣ r then 1 else u p) =
      (∏' p : Nat.Primes, if p ∈ S then 1 else u p) := by
    apply tprod_congr
    intro p
    exact if_congr (hmem p).symm rfl rfl
  calc
    mobiusAvoidingDirichletSeries r χ s =
        ∏' p : Nat.Primes, if (p : ℕ) ∣ r then 1 else u p :=
      (mobiusAvoidingEulerProduct_eq r χ hχ hs).symm
    _ = (∏' p : Nat.Primes, if p ∈ S then 1 else u p) := hfactor
    _ = (∏' p : Nat.Primes, u p) * ∏ p ∈ S, (u p)⁻¹ := hremove
    _ = mobiusWeightedDirichletSeries χ s * ∏ p ∈ S, (u p)⁻¹ := by rw [hweighted]

/-- Exact arbitrary-multiplier Möbius Dirichlet-series identity, with the
finite Euler factors at primes dividing `r` removed. -/
theorem mobiusMultiplierDirichletSeries_eq
    (r : ℕ) (hr : r ≠ 0) (χ : ℕ →*₀ ℂ)
    (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (mobiusMultiplierCoefficient r χ) s =
      (ArithmeticFunction.moebius r : ℂ) *
        mobiusWeightedDirichletSeries χ s *
          ∏ p ∈ mobiusPrimeDivisors r, (mobiusEulerFactor χ s p)⁻¹ := by
  have hcoeff : mobiusCoprimeFilteredCoefficient r χ = mobiusAvoidingCoeff r χ := by
    funext n
    simp [mobiusCoprimeFilteredCoefficient, mobiusAvoidingCoeff,
      mobiusWeightedCoeff, mobiusMultiplierCoefficient]
  calc
    LSeries (mobiusMultiplierCoefficient r χ) s =
        (ArithmeticFunction.moebius r : ℂ) *
          mobiusAvoidingDirichletSeries r χ s := by
      rw [mobiusMultiplierLSeries_eq, hcoeff, mobiusAvoidingDirichletSeries]
    _ = (ArithmeticFunction.moebius r : ℂ) *
        (mobiusWeightedDirichletSeries χ s *
          ∏ p ∈ mobiusPrimeDivisors r, (mobiusEulerFactor χ s p)⁻¹) := by
      rw [mobiusAvoidingSeries_eq_weightedSeries_mul_removedFactors r hr χ hχ hs]
    _ = (ArithmeticFunction.moebius r : ℂ) * mobiusWeightedDirichletSeries χ s *
        ∏ p ∈ mobiusPrimeDivisors r, (mobiusEulerFactor χ s p)⁻¹ := by ring

#print axioms mobiusMultiplierDirichletSeries_eq
#print axioms mobiusEulerFactor_ne_zero

#print axioms mobiusWeightedDirichletSeries_absolutelyConvergent
#print axioms mobiusWeightedEulerProduct_eq

