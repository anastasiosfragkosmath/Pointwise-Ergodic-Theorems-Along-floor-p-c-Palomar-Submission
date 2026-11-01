module

public import FractionalPrimes.Core
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeFactorizationInjectivity
public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimePrincipalCorrection
public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter
public import FractionalPrimes.Literature.LongArithmetic.ShiftedCharacterMobiusSeries
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.MobiusToLong

open FractionalPrimes.Literature.LongArithmetic
open FractionalPrimes.Literature.Twisted
open Finset

/-- The principal character's natural-number extension is the coprimality
indicator, including at modulus one. -/
theorem principalCharacterNatHom_eq_coprime_indicator
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ = principalCharacter q)
    {n : ℕ} (hn : n ≠ 0) :
    dirichletCharacterNatHom χ n = if Nat.Coprime n q then 1 else 0 := by
  rw [dirichletCharacterNatHom_apply_of_ne_zero χ hn, hχ]
  have h := principalCharacter_evalInt (q := q) (n := (n : ℤ))
  simpa [evalInt, Nat.coprime_comm] using h

/-- Exact finite principal-character correction: the omitted von Mangoldt
terms are precisely the prime powers that are not coprime to the modulus. -/
theorem principalCharacterMissingMass_eq_primePowerSupport
    {x : ℝ} {q : ℕ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) -
      (∑ n ∈ Finset.Icc 1 (Nat.floor x),
        vonMangoldtWeight n * (if Nat.Coprime n q then (1 : ℝ) else 0)) =
      ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter
          (fun n => IsPrimePow n ∧ ¬ Nat.Coprime n q),
        vonMangoldtWeight n := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ n ∈ Finset.Icc 1 (Nat.floor x),
        (vonMangoldtWeight n -
          vonMangoldtWeight n * (if Nat.Coprime n q then (1 : ℝ) else 0))) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor x),
        (if Nat.Coprime n q then 0 else vonMangoldtWeight n) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hcop : Nat.Coprime n q
      · rw [if_pos hcop, if_pos hcop]
        ring
      · rw [if_neg hcop, if_neg hcop]
        ring
    _ = ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter
          (fun n => IsPrimePow n ∧ ¬ Nat.Coprime n q),
          vonMangoldtWeight n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hcop : Nat.Coprime n q
      · simp [hcop]
      · by_cases hp : IsPrimePow n
        · simp [hcop, hp]
        · have hzero : vonMangoldtWeight n = 0 := by
            simpa [vonMangoldtWeight] using (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hp
          simpa [hcop, hp, vonMangoldtWeight] using hzero

/-- On the filtered support above, the unique prime base divides `q`; thus
the support is exactly prime powers `p^j` with `p ∣ q`. -/
theorem primePower_not_coprime_iff_minFac_mem_primeFactors
    {n q : ℕ} (hn : IsPrimePow n) (hq : 0 < q) :
    ¬ Nat.Coprime n q ↔ n.minFac ∈ q.primeFactors := by
  constructor
  · intro hnot
    have hgne : Nat.gcd n q ≠ 1 := by
      intro hg
      apply hnot
      exact Nat.coprime_iff_gcd_eq_one.mpr hg
    have hgpos : 1 < Nat.gcd n q := by
      have hnle : 2 ≤ n := IsPrimePow.two_le hn
      have hnpos : 0 < n := by omega
      have hge : 0 < Nat.gcd n q := Nat.gcd_pos_of_pos_left q hnpos
      omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgpos)
    have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_left n q)
    have hpq : p ∣ q := hpdvd.trans (Nat.gcd_dvd_right n q)
    obtain ⟨r, hr, huniq⟩ := (isPrimePow_iff_unique_prime_dvd).mp hn
    have hpeq : p = n.minFac := by
      calc
        p = r := huniq p ⟨hp, hpn⟩
        _ = n.minFac := (huniq n.minFac
          ⟨Nat.minFac_prime hn.ne_one, Nat.minFac_dvd n⟩).symm
    rw [← hpeq]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpq, Nat.ne_of_gt hq⟩
  · intro hmem
    have hprime := Nat.prime_of_mem_primeFactors hmem
    have hdivq := (Nat.mem_primeFactors.mp hmem).2.1
    intro hcop
    have hnle : 2 ≤ n := IsPrimePow.two_le hn
    have hnpos : 0 < n := by omega
    have hminfac_dvd_gcd : n.minFac ∣ Nat.gcd n q := Nat.dvd_gcd (Nat.minFac_dvd n) hdivq
    have hminfac_le_gcd : n.minFac ≤ Nat.gcd n q :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left q hnpos) hminfac_dvd_gcd
    have hminfacpos : 1 < n.minFac := by
      exact Nat.minFac_prime hn.ne_one |>.one_lt
    have : 1 < Nat.gcd n q := lt_of_lt_of_le hminfacpos hminfac_le_gcd
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at this
    omega

/-- The finite principal-character correction has the exact logarithmic
modulus bound in the blueprint. The proof reindexes the supported prime
powers by their unique prime base and exponent, then applies the checked
per-prime and prime-factor-count estimates. -/
theorem principalCharacterMissingMass_le
    {x : ℝ} {q : ℕ} (hx : 3 ≤ x) (hq : 1 ≤ q) :
    0 ≤
        (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) -
          (∑ n ∈ Finset.Icc 1 (Nat.floor x),
            vonMangoldtWeight n * (if Nat.Coprime n q then (1 : ℝ) else 0)) ∧
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) -
          (∑ n ∈ Finset.Icc 1 (Nat.floor x),
            vonMangoldtWeight n * (if Nat.Coprime n q then (1 : ℝ) else 0)) ≤
        (Real.log (q : ℝ) / Real.log 2) * Real.log x := by
  classical
  have hx1 : 1 ≤ x := by linarith
  have hqpos : 0 < q := by omega
  let S : Finset ℕ := (Finset.Icc 1 (Nat.floor x)).filter
    (fun n => IsPrimePow n ∧ ¬ Nat.Coprime n q)
  let f : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac)
  let K : ℕ := Nat.floor (Real.log x / Real.log 2)
  let U : Finset (ℕ × ℕ) := q.primeFactors ×ˢ Finset.Icc 1 K
  let T : Finset (ℕ × ℕ) := U.filter fun y =>
    y.2 ≤ Nat.floor (Real.log x / Real.log (y.1 : ℝ))
  have hExact := principalCharacterMissingMass_eq_primePowerSupport (x := x) (q := q) hx1
  have hmass :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) -
        (∑ n ∈ Finset.Icc 1 (Nat.floor x),
          vonMangoldtWeight n * (if Nat.Coprime n q then (1 : ℝ) else 0)) =
        ∑ n ∈ S, vonMangoldtWeight n := by
    simpa [S] using hExact
  have hpowerForm (n : ℕ) (hn : n ∈ S) :
      vonMangoldtWeight n = Real.log (n.minFac : ℝ) := by
    have hpow := (Finset.mem_filter.mp hn).2.1
    simp [vonMangoldtWeight_def, ArithmeticFunction.vonMangoldt_apply, hpow]
  have hf_injective : Set.InjOn f (S : Set ℕ) := by
    intro n hn m hm hnm
    have hnPow := (Finset.mem_filter.mp hn).2.1
    have hmPow := (Finset.mem_filter.mp hm).2.1
    have hbase : n.minFac = m.minFac := congrArg Prod.fst hnm
    have hexp : n.factorization n.minFac = m.factorization m.minFac :=
      congrArg Prod.snd hnm
    exact primePowerMinFacExponent_injective hnPow hmPow hbase hexp
  have hsubset : S.image f ⊆ T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨n, hnS, rfl⟩
    rcases Finset.mem_filter.mp hnS with ⟨hnIcc, hnPow, hnotcop⟩
    have hpMem : n.minFac ∈ q.primeFactors :=
      (primePower_not_coprime_iff_minFac_mem_primeFactors hnPow hqpos).mp hnotcop
    have hp : Nat.Prime n.minFac := Nat.prime_of_mem_primeFactors hpMem
    have hkpos : 0 < n.factorization n.minFac :=
      hp.factorization_pos_of_dvd hnPow.ne_zero (Nat.minFac_dvd n)
    have hnIcc' := Finset.mem_Icc.mp hnIcc
    have hpowEq : n.minFac ^ n.factorization n.minFac = n :=
      hnPow.minFac_pow_factorization_eq
    have hpowle : (n.minFac : ℝ) ^ n.factorization n.minFac ≤ x := by
      calc
        (n.minFac : ℝ) ^ n.factorization n.minFac =
            ((n.minFac ^ n.factorization n.minFac : ℕ) : ℝ) := by norm_cast
        _ = (n : ℝ) := by exact_mod_cast hpowEq
        _ ≤ (Nat.floor x : ℝ) := by exact_mod_cast hnIcc'.2
        _ ≤ x := Nat.floor_le (by linarith)
    have hpOne : 1 < (n.minFac : ℝ) := by exact_mod_cast hp.one_lt
    have hlogp : 0 < Real.log (n.minFac : ℝ) := Real.log_pos hpOne
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2lelogp : Real.log 2 ≤ Real.log (n.minFac : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hKp_le_K :
        Nat.floor (Real.log x / Real.log (n.minFac : ℝ)) ≤ K := by
      apply Nat.floor_mono
      exact div_le_div_of_nonneg_left (Real.log_nonneg hx1) hlog2 hlog2lelogp
    have hlogpow :
        (n.factorization n.minFac : ℝ) * Real.log (n.minFac : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (by positivity :
        0 < (n.minFac : ℝ) ^ n.factorization n.minFac) hpowle
      rwa [Real.log_pow] at h
    have hexpUpper : n.factorization n.minFac ≤
        Nat.floor (Real.log x / Real.log (n.minFac : ℝ)) := by
      apply Nat.le_floor
      exact (le_div_iff₀ hlogp).2 hlogpow
    change (n.minFac, n.factorization n.minFac) ∈ U.filter _
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨hpMem,
        Finset.mem_Icc.mpr ⟨hkpos, (hexpUpper.trans hKp_le_K)⟩⟩
    · exact hexpUpper
  have hsumImage :
      (∑ n ∈ S, vonMangoldtWeight n) =
        ∑ y ∈ S.image f, Real.log (y.1 : ℝ) := by
    calc
      _ = ∑ n ∈ S, Real.log ((f n).1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simpa [f] using hpowerForm n hn
      _ = ∑ y ∈ S.image f, Real.log (y.1 : ℝ) :=
        (Finset.sum_image (f := fun y : ℕ × ℕ => Real.log (y.1 : ℝ))
          hf_injective).symm
  have hsumSubset :
      (∑ y ∈ S.image f, Real.log (y.1 : ℝ)) ≤
        ∑ y ∈ T, Real.log (y.1 : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro y hy hnot
    have hpMem : y.1 ∈ q.primeFactors := (Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1
    exact Real.log_nonneg (by exact_mod_cast
      (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hpMem)))
  have hKp_le_K (p : ℕ) (hp : p ∈ q.primeFactors) :
      Nat.floor (Real.log x / Real.log (p : ℝ)) ≤ K := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2lelogp : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_left (Real.log_nonneg hx1) hlog2 hlog2lelogp
  have hsumT :
      (∑ y ∈ T, Real.log (y.1 : ℝ)) =
        ∑ p ∈ q.primeFactors,
          ∑ k ∈ Finset.Icc 1 (Nat.floor (Real.log x / Real.log (p : ℝ))),
            Real.log (p : ℝ) := by
    rw [show T = U.filter
      (fun y => y.2 ≤ Nat.floor (Real.log x / Real.log (y.1 : ℝ))) by rfl]
    rw [Finset.sum_filter, Finset.sum_product]
    simp only [Prod.fst, Prod.snd]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_filter]
    have hset :
        (Finset.Icc 1 K).filter
          (fun k => k ≤ Nat.floor (Real.log x / Real.log (p : ℝ))) =
          Finset.Icc 1 (Nat.floor (Real.log x / Real.log (p : ℝ))) := by
      have hKp := hKp_le_K p hp
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hklo, hkK⟩, hKp'⟩
        exact ⟨hklo, hKp'⟩
      · rintro ⟨hklo, hKp'⟩
        exact ⟨⟨hklo, hKp'.trans hKp⟩, hKp'⟩
    rw [hset]
  have hsumTle :
      (∑ p ∈ q.primeFactors,
        ∑ k ∈ Finset.Icc 1 (Nat.floor (Real.log x / Real.log (p : ℝ))),
          Real.log (p : ℝ)) ≤
        ∑ p ∈ q.primeFactors, Real.log x := by
    apply Finset.sum_le_sum
    intro p hp
    exact log_weight_prime_power_exponents_le hx1 (Nat.prime_of_mem_primeFactors hp)
  have hsumFactors := sum_log_x_primeFactors_le hx1 hqpos
  rw [hmass]
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    simpa [vonMangoldtWeight] using
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · calc
      (∑ n ∈ S, vonMangoldtWeight n) =
          ∑ y ∈ S.image f, Real.log (y.1 : ℝ) := hsumImage
      _ ≤ ∑ y ∈ T, Real.log (y.1 : ℝ) := hsumSubset
      _ = ∑ p ∈ q.primeFactors,
          ∑ k ∈ Finset.Icc 1 (Nat.floor (Real.log x / Real.log (p : ℝ))),
            Real.log (p : ℝ) := hsumT
      _ ≤ ∑ p ∈ q.primeFactors, Real.log x := hsumTle
      _ ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x := hsumFactors

end FractionalPrimes.Literature.MobiusToLong

end
