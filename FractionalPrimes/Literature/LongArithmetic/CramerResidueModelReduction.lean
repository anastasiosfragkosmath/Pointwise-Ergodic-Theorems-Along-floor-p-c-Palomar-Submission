module

public import FractionalPrimes.RosserWeights
public import FractionalPrimes.Literature.LongArithmetic.DeletedSieveStoppingIdentity
public import FractionalPrimes.Literature.LongArithmetic.CramerResidueIntervalCount

/-!
# Model reduction on a residue class

These are the first local reductions in the approved proof of
`lal:cramer-residue` (expanded blueprint, pp. 7628–7669; Astra
`long-arithmetic-closure.tex`, lines 74–99). The file keeps the paper's
strict prime cutoff and positive natural modulus convention.
-/

@[expose] public section

namespace FractionalPrimes.Literature.LongArithmetic

open Classical

/-- The sieve primes below `z` which do not divide the residue modulus. -/
noncomputable def cramerResidueSelectedPrimes (z : ℝ) (q : ℕ) : Finset ℕ :=
  (sievePrimesBelow z).filter (fun p => ¬ p ∣ q)

/-- If the residue is nonunit and every prime divisor of the modulus lies
strictly below the sieve cutoff, the Cramér model vanishes on the entire
residue class. -/
theorem paperCramerWeight_eq_zero_of_nonunitResidue
    (z : ℝ) (q : ℕ) (a n : ℤ)
    (ha : 1 < Int.gcd a (q : ℤ))
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) < z)
    (hmod : n ≡ a [ZMOD (q : ℤ)]) :
    paperCramerWeight z n = 0 := by
  have hNatGcd : 1 < Nat.gcd a.natAbs q := by
    have hcast := ha
    rw [Int.gcd_def] at hcast
    exact_mod_cast hcast
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hNatGcd)
  have hpaNat : p ∣ a.natAbs := hpgcd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ q := hpgcd.trans (Nat.gcd_dvd_right _ _)
  have hpz : (p : ℝ) < z := hsmall p hp hpq
  have hpMem : p ∈ sievePrimesBelow z := by
    rw [sievePrimesBelow_iff]
    exact ⟨hp, hpz⟩
  have hpa : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hpaNat
  have hpqZ : (p : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.mpr hpq
  have hdiff : (p : ℤ) ∣ a - n := hpqZ.trans (Int.modEq_iff_dvd.mp hmod)
  have hpn : (p : ℤ) ∣ n := by
    have h := dvd_sub hpa hdiff
    convert h using 1 <;> ring
  have hpWNat : p ∣ sievePrimeProduct z := by
    unfold sievePrimeProduct
    exact Finset.dvd_prod_of_mem (fun r => r) hpMem
  have hpW : (p : ℤ) ∣ (sievePrimeProduct z : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpWNat
  have hnot : Int.gcd n (sievePrimeProduct z : ℤ) ≠ 1 := by
    intro hg
    have hpDivGcd : p ∣ Int.gcd n (sievePrimeProduct z : ℤ) :=
      Int.dvd_gcd hpn hpW
    rw [hg] at hpDivGcd
    have hpOneNat : p ∣ 1 := hpDivGcd
    exact hp.ne_one (Nat.dvd_one.mp hpOneNat)
  simp [paperCramerWeight, paperPrimeProduct, hnot]

private theorem intGcd_one_iff_natCoprime
    (n : ℤ) (m : ℕ) :
    Int.gcd n (m : ℤ) = 1 ↔ Nat.Coprime n.natAbs m := by
  rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
  simp

private theorem natCoprime_finset_primeProduct_iff
    {z : ℝ} {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z) (n : ℕ) :
    Nat.Coprime n (S.prod id) ↔ ∀ p ∈ S, ¬ p ∣ n := by
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp hpn
    have hpPrime : p.Prime := by
      have hpz := hS hp
      unfold sievePrimesBelow at hpz
      exact (Finset.mem_filter.mp hpz).2.1
    exact (hpPrime.coprime_iff_not_dvd).mp
      (Nat.coprime_comm.mp (h p hp)) hpn
  · intro h p hp
    have hpPrime : p.Prime := by
      have hpz := hS hp
      unfold sievePrimesBelow at hpz
      exact (Finset.mem_filter.mp hpz).2.1
    exact Nat.coprime_comm.mp
      ((hpPrime.coprime_iff_not_dvd).2 (h p hp))

/-- Every divisor of the selected-prime product is coprime to the residue
modulus, since each selected prime is excluded from its prime divisors. -/
theorem natCoprime_dvd_cramerResidueSelectedPrimeProduct
    (z : ℝ) (q d : ℕ)
    (hd : d ∣ (cramerResidueSelectedPrimes z q).prod id) :
    Nat.Coprime q d := by
  let S := cramerResidueSelectedPrimes z q
  have hS : S ⊆ sievePrimesBelow z := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hproduct : Nat.Coprime q (S.prod id) := by
    apply (natCoprime_finset_primeProduct_iff hS q).2
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  exact Nat.Coprime.of_dvd_right hd hproduct

/-- On a coprime residue class, the global strict-cutoff Cramér coprimality
indicator is exactly the indicator for primes below `z` that do not divide
the modulus. The omitted primes cannot divide any integer in this class. -/
theorem cramerSieveIndicator_eq_selected_of_coprimeResidue
    (z : ℝ) (q : ℕ) (a n : ℤ)
    (ha : Nat.Coprime a.natAbs q)
    (hmod : n ≡ a [ZMOD (q : ℤ)]) :
    (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) =
      (if Int.gcd n
          (((cramerResidueSelectedPrimes z q).prod id : ℕ) : ℤ) = 1
        then (1 : ℝ) else 0) := by
  let S := cramerResidueSelectedPrimes z q
  have hS : S ⊆ sievePrimesBelow z := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hGlobal :
      Int.gcd n (sievePrimeProduct z : ℤ) = 1 ↔
        ∀ p ∈ sievePrimesBelow z, ¬ p ∣ n.natAbs := by
    rw [intGcd_one_iff_natCoprime]
    exact natCoprime_sievePrimeProduct_iff
  have hSelected :
      Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 ↔
        ∀ p ∈ S, ¬ p ∣ n.natAbs := by
    rw [intGcd_one_iff_natCoprime]
    exact natCoprime_finset_primeProduct_iff hS n.natAbs
  have hSelectedCast :
      Int.gcd n
          (∏ p ∈ cramerResidueSelectedPrimes z q, (p : ℤ)) = 1 ↔
        ∀ p ∈ S, ¬ p ∣ n.natAbs := by
    simpa only [S, Nat.cast_prod, id_eq] using hSelected
  have hPred :
      (∀ p ∈ sievePrimesBelow z, ¬ p ∣ n.natAbs) ↔
        (∀ p ∈ S, ¬ p ∣ n.natAbs) := by
    constructor
    · intro h p hp
      exact h p (hS hp)
    · intro h p hp
      by_cases hpq : p ∣ q
      · intro hpn
        have hpPrime : p.Prime := by
          unfold sievePrimesBelow at hp
          exact (Finset.mem_filter.mp hp).2.1
        have hpnZ : (p : ℤ) ∣ n := Int.natCast_dvd.mpr hpn
        have hpqZ : (p : ℤ) ∣ (q : ℤ) :=
          Int.natCast_dvd_natCast.mpr hpq
        have hdiff : (p : ℤ) ∣ a - n :=
          hpqZ.trans (Int.modEq_iff_dvd.mp hmod)
        have hpaZ : (p : ℤ) ∣ a := by
          have h := dvd_add hdiff hpnZ
          convert h using 1 <;> ring
        have hpa : p ∣ a.natAbs := Int.natCast_dvd.mp hpaZ
        have hcopP : Nat.Coprime p q := Nat.Coprime.of_dvd_left hpa ha
        exact (hpPrime.coprime_iff_not_dvd.mp hcopP) hpq
      · have hpS : p ∈ S := by
          exact Finset.mem_filter.mpr ⟨hp, hpq⟩
        exact h p hpS
  have hIndicators :
      Int.gcd n (sievePrimeProduct z : ℤ) = 1 ↔
        Int.gcd n
          (∏ p ∈ cramerResidueSelectedPrimes z q, (p : ℤ)) = 1 :=
    hGlobal.trans (hPred.trans hSelectedCast.symm)
  by_cases hg : Int.gcd n (sievePrimeProduct z : ℤ) = 1
  · have hgs : Int.gcd n
        (∏ p ∈ cramerResidueSelectedPrimes z q, (p : ℤ)) = 1 :=
      hIndicators.mp hg
    simp [hg, hgs]
  · have hgs : Int.gcd n
        (∏ p ∈ cramerResidueSelectedPrimes z q, (p : ℤ)) ≠ 1 :=
      fun hgs => hg (hIndicators.mpr hgs)
    simp [hg, hgs]

/-- Exact density cancellation after deleting the primes that divide the
residue modulus. The selected set keeps the strict `p < z` cutoff. -/
theorem cramerResidueDensity_selected_eq_totientRatio
    (z : ℝ) (q : ℕ) (hq : 0 < q)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) < z) :
    paperCramerDensity z *
        deletedPrimeSieveDensityProduct (cramerResidueSelectedPrimes z q) z =
      (q : ℝ) / (Nat.totient q : ℝ) := by
  let T := sievePrimesBelow z
  let S := cramerResidueSelectedPrimes z q
  let f : ℕ → ℝ := fun p => 1 - 1 / (p : ℝ)
  have hSsubset : S ⊆ sievePrimesBelow z := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hVS : deletedPrimeSieveDensityProduct S z = ∏ p ∈ S, f p := by
    unfold deletedPrimeSieveDensityProduct
    have hfilter : S.filter (fun p : ℕ => (p : ℝ) < z) = S := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · intro hp
        exact hp.1
      · intro hp
        exact ⟨hp, ((sievePrimesBelow_iff z p).mp (hSsubset hp)).2⟩
    rw [hfilter]
  have hqFactors : T.filter (fun p : ℕ => p ∣ q) = q.primeFactors := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpT, hpq⟩
      exact Nat.mem_primeFactors.mpr
        ⟨((sievePrimesBelow_iff z p).mp hpT).1, hpq, ne_of_gt hq⟩
    · intro hpqFactors
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpqFactors
      have hpq : p ∣ q := (Nat.mem_primeFactors.mp hpqFactors).2.1
      exact ⟨(sievePrimesBelow_iff z p).2 ⟨hpPrime, hsmall p hpPrime hpq⟩, hpq⟩
  have hSFactors : S = T.filter (fun p : ℕ => ¬ p ∣ q) := by
    rfl
  have hsplit :
      (∏ p ∈ q.primeFactors, f p) *
          deletedPrimeSieveDensityProduct S z =
        sieveDensityProduct z := by
    calc
      (∏ p ∈ q.primeFactors, f p) *
          deletedPrimeSieveDensityProduct S z =
        (∏ p ∈ T.filter (fun p : ℕ => p ∣ q), f p) *
          ∏ p ∈ T.filter (fun p : ℕ => ¬ p ∣ q), f p := by
            rw [← hqFactors, hVS, hSFactors]
      _ = ∏ p ∈ T, f p := by
        exact Finset.prod_filter_mul_prod_filter_not T
          (fun p : ℕ => p ∣ q) f
      _ = sieveDensityProduct z := by
        simp [sieveDensityProduct, T, f]
  have htotientQ :
      (Nat.totient q : ℚ) =
        (q : ℚ) * ∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹) := by
    simpa using Nat.totient_eq_mul_prod_factors q
  have htotientRealQ :
      ((Nat.totient q : ℚ) : ℝ) =
        ((q : ℚ) : ℝ) * ∏ p ∈ q.primeFactors,
          (1 - (((p : ℚ)⁻¹ : ℚ) : ℝ)) := by
    exact_mod_cast htotientQ
  have htotientReal :
      (Nat.totient q : ℝ) =
        (q : ℝ) * ∏ p ∈ q.primeFactors, f p := by
    simpa [f] using htotientRealQ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqFactorsProduct :
      (∏ p ∈ q.primeFactors, f p) =
        (Nat.totient q : ℝ) / (q : ℝ) := by
    calc
      (∏ p ∈ q.primeFactors, f p) =
          ((q : ℝ) * ∏ p ∈ q.primeFactors, f p) / (q : ℝ) := by
            field_simp [ne_of_gt hqR]
      _ = (Nat.totient q : ℝ) / (q : ℝ) := by
            rw [← htotientReal]
  have hfactorPos : ∀ p ∈ q.primeFactors, 0 < f p := by
    intro p hp
    dsimp [f]
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpRone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    have hrecip : 1 / (p : ℝ) < 1 :=
      (div_lt_iff₀ hpRpos).2 (by simpa using hpRone)
    linarith
  have hqFactorProductPos : 0 < ∏ p ∈ q.primeFactors, f p := by
    apply Finset.prod_pos
    intro p hp
    exact hfactorPos p hp
  have hselectedFactorPos : ∀ p ∈ S, 0 < f p := by
    intro p hp
    dsimp [f]
    have hpPrime : p.Prime := ((sievePrimesBelow_iff z p).mp (hSsubset hp)).1
    have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpRone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
    have hrecip : 1 / (p : ℝ) < 1 :=
      (div_lt_iff₀ hpRpos).2 (by simpa using hpRone)
    linarith
  have hVSpos : 0 < deletedPrimeSieveDensityProduct S z := by
    rw [hVS]
    apply Finset.prod_pos
    intro p hp
    exact hselectedFactorPos p hp
  have hphiR : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hq)
  have hR : paperCramerDensity z = (sieveDensityProduct z)⁻¹ := by
    change (sievePrimeProduct z : ℝ) /
      (Nat.totient (sievePrimeProduct z) : ℝ) = _
    exact sievePrimeRatio_eq_inv_density
  calc
    paperCramerDensity z * deletedPrimeSieveDensityProduct S z =
        (sieveDensityProduct z)⁻¹ * deletedPrimeSieveDensityProduct S z := by
          rw [hR]
    _ = (∏ p ∈ q.primeFactors, f p)⁻¹ := by
          rw [← hsplit]
          field_simp [ne_of_gt hqFactorProductPos, ne_of_gt hVSpos]
    _ = (q : ℝ) / (Nat.totient q : ℝ) := by
          rw [hqFactorsProduct]
          field_simp [ne_of_gt hqR, ne_of_gt hphiR]

/-- Rewrite the deleted-sieve divisor sum on an integer n as the finite
integer-divisibility sum over its nonzero coefficient support. -/
theorem deletedPrimeSieveCoefficientSum_eq_supportedIntDivisorSum
    {z y : ℝ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {S : Finset ℕ} (hS : S ⊆ sievePrimesBelow z)
    (nu : Fin 2) (n : ℤ) :
    (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      deletedPrimeSieveCoefficient z y nu S d) =
    (∑ d ∈ (rosserAllSModuli y).filter
        (fun d => deletedPrimeSieveCoefficient z y nu S d ≠ 0),
      if (d : ℤ) ∣ n then deletedPrimeSieveCoefficient z y nu S d else 0) := by
  classical
  let c : ℕ → ℝ := fun d => deletedPrimeSieveCoefficient z y nu S d
  let D : Finset ℕ := (rosserAllSModuli y).filter (fun d => c d ≠ 0)
  have hzero : ∀ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
      y ≤ (d : ℝ) → c d = 0 := by
    intro d hd hdy
    by_contra hne
    have hdlt := (deletedPrimeSieveCoefficient_support hz hzy hS hne).2.1
    exact (not_lt_of_ge hdy) hdlt
  have hmoduli := rosserPositiveDivisorSum_eq_moduliSum_int
    (y := y) n c hzero
  have hreduce :
      (∑ d ∈ rosserAllSModuli y,
        if (d : ℤ) ∣ n then c d else 0) =
      (∑ d ∈ D, if (d : ℤ) ∣ n then c d else 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hcoeffZero : c d = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hd, hne⟩)
    simp [hcoeffZero]
  simpa [c, D] using hmoduli.trans hreduce

/-- The weighted CRT rounding estimate on a real half-open interval. Each
positive supported divisor contributes at most one unit of rounding error;
the coefficient bounds and the number of supported divisors give the final
`y` bound. This is the finite arithmetic-progression estimate used in the
coprime branch of `lal:cramer-residue`. -/
theorem coprimeCRTWeightedDivisorSum_error
    {y : ℝ} (hy : 1 ≤ y)
    (X H : ℝ) (q : ℕ) (a : ℤ)
    (D : Finset ℕ) (lambda : ℕ → ℝ)
    (hH : 0 < H) (hq : 0 < q)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) < y)
    (hcop : ∀ d ∈ D, Nat.Coprime q d)
    (hlambda : ∀ d ∈ D, -1 ≤ lambda d ∧ lambda d ≤ 1) :
    |(∑ n ∈ (Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
          (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)]),
        ∑ d ∈ D, if (d : ℤ) ∣ n then lambda d else 0) -
      H / (q : ℝ) * ∑ d ∈ D, lambda d / (d : ℝ)| ≤ y := by
  let I : Finset ℤ := Finset.Ioc (Int.floor X) (Int.floor (X + H))
  let C : Finset ℤ := I.filter (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])
  have hH0 : 0 ≤ H := le_of_lt hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hDcard := finset_positive_moduli_card_le hy D hD
  have hcountSum := finite_interval_divisor_sum_eq_count_sum C D lambda
  have hfilter (d : ℕ) :
      C.filter (fun n : ℤ => (d : ℤ) ∣ n) =
        I.filter (fun n : ℤ =>
          n ≡ a [ZMOD (q : ℤ)] ∧ (d : ℤ) ∣ n) := by
    ext n
    simp [C, I, and_assoc, and_left_comm, and_comm]
  have hCRT (d : ℕ) (hd : d ∈ D) :
      |((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
        H / (Nat.lcm d q : ℝ)| ≤ 1 := by
    rw [hfilter d]
    exact coprimeCRTIntervalCount_error X H q d a hH0 hq (hD d hd).1
      (hcop d hd)
  have hmain :
      H / (q : ℝ) * (∑ d ∈ D, lambda d / (d : ℝ)) =
        ∑ d ∈ D, lambda d * (H / (Nat.lcm d q : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (hD d hd).1
    have hlcm : (Nat.lcm d q : ℝ) = (q : ℝ) * (d : ℝ) := by
      rw [Nat.Coprime.lcm_eq_mul (hcop d hd).symm]
      push_cast
      ring
    rw [hlcm]
    field_simp [ne_of_gt hqR, ne_of_gt hdR]
  have hidentity :
      (∑ n ∈ C, ∑ d ∈ D,
        if (d : ℤ) ∣ n then lambda d else 0) -
        H / (q : ℝ) * (∑ d ∈ D, lambda d / (d : ℝ)) =
      ∑ d ∈ D, lambda d *
        (((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
          H / (Nat.lcm d q : ℝ)) := by
    rw [hcountSum, hmain, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hterm : ∀ d ∈ D,
      |lambda d *
        (((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
          H / (Nat.lcm d q : ℝ))| ≤ 1 := by
    intro d hd
    have hAbsCoeff : |lambda d| ≤ 1 := abs_le.mpr (hlambda d hd)
    rw [abs_mul]
    calc
      |lambda d| *
          |((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
            H / (Nat.lcm d q : ℝ)| ≤ |lambda d| * 1 :=
        mul_le_mul_of_nonneg_left (hCRT d hd) (abs_nonneg _)
      _ ≤ 1 := by simpa using hAbsCoeff
  have hbound :
      |∑ d ∈ D, lambda d *
        (((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
          H / (Nat.lcm d q : ℝ))| ≤ y := by
    calc
      |∑ d ∈ D, lambda d *
          (((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
            H / (Nat.lcm d q : ℝ))| ≤
          ∑ d ∈ D, |lambda d *
            (((C.filter (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) -
              H / (Nat.lcm d q : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ D, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hterm d hd
      _ = (D.card : ℝ) := by simp
      _ ≤ y := hDcard
  rw [hidentity]
  exact hbound

/-- Blueprint aggregate `lal:cramer-residue`: the strict-cutoff Cramér model
vanishes on nonunit residue classes, and on a unit class has the stated
real-endpoint mean with the unchanged `sieveD` and `paperCramerDensity` error.
The floor `Ioc` is exactly the set of integers in `(X, X + H]`; since
`X ≥ 3`, all of its elements are positive. -/
theorem cramerResidueMean
    (X H y : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) (hH : 0 < H) (hq : 0 < q)
    (hzy : paperShortBlockCutoff X ≤ y)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ q →
      (p : ℝ) < paperShortBlockCutoff X) :
    (1 < Int.gcd a (q : ℤ) →
      ∀ n : ℤ, n ≡ a [ZMOD (q : ℤ)] →
        paperShortBlockCramerWeight X n = 0) ∧
    (Int.gcd a (q : ℤ) = 1 →
      |(∑ n ∈ (Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
            (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight X n) -
        H / (Nat.totient q : ℝ)| ≤
        sieveD * (H / (Nat.totient q : ℝ)) *
            Real.exp (-(Real.log y / Real.log (paperShortBlockCutoff X))) +
          paperCramerDensity (paperShortBlockCutoff X) * y) := by
  classical
  let z : ℝ := paperShortBlockCutoff X
  have hXpos : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans hX
  have hscale : 1 ≤ (Real.log X) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow hlogX (by norm_num)
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h
    exact h
  have hz : 2 ≤ z := by
    dsimp [z, paperShortBlockCutoff]
    exact htwoExp.trans (Real.exp_le_exp.mpr hscale)
  have hsmallZ : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) < z := by
    intro p hp hpq
    simpa [z] using hsmall p hp hpq
  have hRbounds := paperCramerDensity_bounds hz
  have hRpos : 0 < paperCramerDensity z :=
    lt_of_lt_of_le (by norm_num) hRbounds.1
  have hy : 1 ≤ y := by
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_trans hz hzy)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hphiR : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hq)
  constructor
  · intro hnonunit n hmod
    simpa [paperShortBlockCramerWeight, z] using
      (paperCramerWeight_eq_zero_of_nonunitResidue
        z q a n hnonunit hsmallZ hmod)
  · intro hgcd
    have ha : Nat.Coprime a.natAbs q :=
      (intGcd_one_iff_natCoprime a q).mp hgcd
    let S : Finset ℕ := cramerResidueSelectedPrimes z q
    let C : Finset ℤ := (Finset.Ioc (Int.floor X) (Int.floor (X + H))).filter
      (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])
    let lo : ℕ → ℝ := fun d => deletedPrimeSieveLowerCoefficient z y S d
    let up : ℕ → ℝ := fun d => deletedPrimeSieveUpperCoefficient z y S d
    let Dlo : Finset ℕ := (rosserAllSModuli y).filter (fun d => lo d ≠ 0)
    let Dup : Finset ℕ := (rosserAllSModuli y).filter (fun d => up d ≠ 0)
    let loDivisorSum : ℤ → ℝ := fun n =>
      ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs, lo d
    let upDivisorSum : ℤ → ℝ := fun n =>
      ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs, up d
    let loTotal : ℝ := ∑ n ∈ C, loDivisorSum n
    let upTotal : ℝ := ∑ n ∈ C, upDivisorSum n
    let loMean : ℝ := ∑ d ∈ Finset.range (⌊y⌋₊ + 1), lo d / (d : ℝ)
    let upMean : ℝ := ∑ d ∈ Finset.range (⌊y⌋₊ + 1), up d / (d : ℝ)
    let V : ℝ := deletedPrimeSieveDensityProduct S z
    let E : ℝ := Real.exp (-(Real.log y / Real.log z))
    let b : ℝ := H / (q : ℝ)
    let m : ℝ := H / (Nat.totient q : ℝ)
    let R : ℝ := paperCramerDensity z
    let densityError : ℝ := sieveD * V * E
    let finalError : ℝ := sieveD * m * E + R * y
    let modelIndicator : ℤ → ℝ := fun n =>
      if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then 1 else 0
    let modelIndicatorSum : ℝ := ∑ n ∈ C, modelIndicator n
    let modelSum : ℝ := ∑ n ∈ C, paperShortBlockCramerWeight X n
    have hS : S ⊆ sievePrimesBelow z := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hdeleted := deletedPrimeSieve (z := z) (y := y) hz hzy hS
    have hdeletedBounds := hdeleted.1
    have hdeletedSupport := hdeleted.2.1
    have hdeletedPointwise := hdeleted.2.2.1
    have hdeletedDensity := hdeleted.2.2.2
    have hLowerSupport (d : ℕ) (hd : d ∈ Dlo) :
        0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id := by
      have hcoeff : lo d ≠ 0 := (Finset.mem_filter.mp hd).2
      exact hdeletedSupport d |>.1 (by simpa [lo] using hcoeff)
    have hUpperSupport (d : ℕ) (hd : d ∈ Dup) :
        0 < d ∧ (d : ℝ) < y ∧ Squarefree d ∧ d ∣ S.prod id := by
      have hcoeff : up d ≠ 0 := (Finset.mem_filter.mp hd).2
      exact hdeletedSupport d |>.2 (by simpa [up] using hcoeff)
    have hDloBounds : ∀ d ∈ Dlo, -1 ≤ lo d ∧ lo d ≤ 1 := by
      intro d hd
      have hb := hdeletedBounds d
      exact ⟨by simpa [lo] using hb.1,
        by simpa [lo] using hb.2.1⟩
    have hDupBounds : ∀ d ∈ Dup, -1 ≤ up d ∧ up d ≤ 1 := by
      intro d hd
      have hb := hdeletedBounds d
      exact ⟨by simpa [up] using hb.2.2.1,
        by simpa [up] using hb.2.2.2⟩
    have hDloCoprime : ∀ d ∈ Dlo, Nat.Coprime q d := by
      intro d hd
      exact natCoprime_dvd_cramerResidueSelectedPrimeProduct z q d
        (by simpa [S] using (hLowerSupport d hd).2.2.2)
    have hDupCoprime : ∀ d ∈ Dup, Nat.Coprime q d := by
      intro d hd
      exact natCoprime_dvd_cramerResidueSelectedPrimeProduct z q d
        (by simpa [S] using (hUpperSupport d hd).2.2.2)
    have hDloRange : Dlo ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro d hd
      change d ∈ (rosserAllSModuli y).filter (fun d => lo d ≠ 0) at hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
    have hDupRange : Dup ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro d hd
      change d ∈ (rosserAllSModuli y).filter (fun d => up d ≠ 0) at hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
    have hLoRangeMean :
        (∑ d ∈ Dlo, lo d / (d : ℝ)) = loMean := by
      dsimp [loMean]
      apply Finset.sum_subset hDloRange
      intro d hd hnot
      have hcoeffZero : lo d = 0 := by
        by_contra hne
        have hsupp := hdeletedSupport d
        have hdsupp := hsupp.1 (by simpa [lo] using hne)
        rcases hdsupp with ⟨hdpos, hdlt, _, _⟩
        have hdmod : d ∈ rosserAllSModuli y :=
          Finset.mem_filter.mpr ⟨hd, hdpos, hdlt⟩
        exact hnot (Finset.mem_filter.mpr
          ⟨hdmod, by simpa [lo] using hne⟩)
      simp [hcoeffZero]
    have hUpRangeMean :
        (∑ d ∈ Dup, up d / (d : ℝ)) = upMean := by
      dsimp [upMean]
      apply Finset.sum_subset hDupRange
      intro d hd hnot
      have hcoeffZero : up d = 0 := by
        by_contra hne
        have hsupp := hdeletedSupport d
        have hdsupp := hsupp.2 (by simpa [up] using hne)
        rcases hdsupp with ⟨hdpos, hdlt, _, _⟩
        have hdmod : d ∈ rosserAllSModuli y :=
          Finset.mem_filter.mpr ⟨hd, hdpos, hdlt⟩
        exact hnot (Finset.mem_filter.mpr
          ⟨hdmod, by simpa [up] using hne⟩)
      simp [hcoeffZero]
    have hLoBridge (n : ℤ) :
        loDivisorSum n =
          ∑ d ∈ Dlo, if (d : ℤ) ∣ n then lo d else 0 := by
      by_cases hs : Real.log y / Real.log z < 2
      · have hzero : ∀ d : ℕ, lo d = 0 := by
          intro d
          simp [lo, deletedPrimeSieveLowerCoefficient, hs]
        have hDempty : Dlo = ∅ := by
          ext d
          simp [Dlo, hzero]
        simp [loDivisorSum, hzero, hDempty]
      · simpa [loDivisorSum, Dlo, lo,
          deletedPrimeSieveLowerCoefficient, hs] using
            (deletedPrimeSieveCoefficientSum_eq_supportedIntDivisorSum
              hz hzy hS (0 : Fin 2) n)
    have hUpBridge (n : ℤ) :
        upDivisorSum n =
          ∑ d ∈ Dup, if (d : ℤ) ∣ n then up d else 0 := by
      change
        (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          deletedPrimeSieveUpperCoefficient z y S d) =
        (∑ d ∈ (rosserAllSModuli y).filter
            (fun d => deletedPrimeSieveUpperCoefficient z y S d ≠ 0),
          if (d : ℤ) ∣ n then deletedPrimeSieveUpperCoefficient z y S d else 0)
      exact deletedPrimeSieveCoefficientSum_eq_supportedIntDivisorSum
        hz hzy hS (1 : Fin 2) n
    have hLoIntervalBridge :
        loTotal = ∑ n ∈ C,
          ∑ d ∈ Dlo, if (d : ℤ) ∣ n then lo d else 0 := by
      dsimp [loTotal]
      apply Finset.sum_congr rfl
      intro n hn
      exact hLoBridge n
    have hUpIntervalBridge :
        upTotal = ∑ n ∈ C,
          ∑ d ∈ Dup, if (d : ℤ) ∣ n then up d else 0 := by
      dsimp [upTotal]
      apply Finset.sum_congr rfl
      intro n hn
      exact hUpBridge n
    have hCRTloRaw := coprimeCRTWeightedDivisorSum_error
      (y := y) hy X H q a Dlo lo hH hq
      (fun d hd => ⟨(hLowerSupport d hd).1, (hLowerSupport d hd).2.1⟩)
      hDloCoprime hDloBounds
    have hCRTupRaw := coprimeCRTWeightedDivisorSum_error
      (y := y) hy X H q a Dup up hH hq
      (fun d hd => ⟨(hUpperSupport d hd).1, (hUpperSupport d hd).2.1⟩)
      hDupCoprime hDupBounds
    have hCRTlo : |loTotal - b * (∑ d ∈ Dlo, lo d / (d : ℝ))| ≤ y := by
      rw [hLoIntervalBridge]
      simpa [C, b] using hCRTloRaw
    have hCRTup : |upTotal - b * (∑ d ∈ Dup, up d / (d : ℝ))| ≤ y := by
      rw [hUpIntervalBridge]
      simpa [C, b] using hCRTupRaw
    have hLoCRTlower : b * loMean - y ≤ loTotal := by
      have h := (abs_le.mp hCRTlo).1
      rw [hLoRangeMean] at h
      linarith
    have hUpCRTupper : upTotal ≤ b * upMean + y := by
      have h := (abs_le.mp hCRTup).2
      rw [hUpRangeMean] at h
      linarith
    have hLoTotalLe : loTotal ≤ modelIndicatorSum := by
      dsimp [loTotal, modelIndicatorSum, modelIndicator]
      apply Finset.sum_le_sum
      intro n hn
      have hmod : n ≡ a [ZMOD (q : ℤ)] := (Finset.mem_filter.mp hn).2
      have hindicator := cramerSieveIndicator_eq_selected_of_coprimeResidue
        z q a n ha hmod
      rw [show
        (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) =
          (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) by
            simpa [S] using hindicator]
      simpa [loDivisorSum, lo] using (hdeletedPointwise n).1
    have hUpTotalGe : modelIndicatorSum ≤ upTotal := by
      dsimp [upTotal, modelIndicatorSum, modelIndicator]
      apply Finset.sum_le_sum
      intro n hn
      have hmod : n ≡ a [ZMOD (q : ℤ)] := (Finset.mem_filter.mp hn).2
      have hindicator := cramerSieveIndicator_eq_selected_of_coprimeResidue
        z q a n ha hmod
      rw [show
        (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then (1 : ℝ) else 0) =
          (if Int.gcd n ((S.prod id : ℕ) : ℤ) = 1 then (1 : ℝ) else 0) by
            simpa [S] using hindicator]
      simpa [upDivisorSum, up] using (hdeletedPointwise n).2
    have hModelIndicator : modelSum = R * modelIndicatorSum := by
      dsimp [modelSum, modelIndicatorSum, modelIndicator, R]
      calc
        (∑ n ∈ C, paperShortBlockCramerWeight X n) =
            ∑ n ∈ C, paperCramerDensity z *
              (if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then
                (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hg : Int.gcd n (sievePrimeProduct z : ℤ) = 1
          · simp [paperShortBlockCramerWeight, paperCramerWeight,
              paperPrimeProduct, z, hg]
          · simp [paperShortBlockCramerWeight, paperCramerWeight,
              paperPrimeProduct, z, hg]
        _ = paperCramerDensity z *
            (∑ n ∈ C,
              if Int.gcd n (sievePrimeProduct z : ℤ) = 1 then
                (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
    have hCancel := cramerResidueDensity_selected_eq_totientRatio
      z q hq hsmallZ
    have hBase : R * (b * V) = m := by
      dsimp [R, b, m, V]
      calc
        paperCramerDensity z * (H / (q : ℝ) *
            deletedPrimeSieveDensityProduct S z) =
          H / (q : ℝ) *
            (paperCramerDensity z * deletedPrimeSieveDensityProduct S z) := by
              ring
        _ = H / (Nat.totient q : ℝ) := by
          rw [hCancel]
          field_simp [ne_of_gt hqR, ne_of_gt hphiR]
    have hDensityLo : |loMean - V| ≤ densityError := by
      simpa [loMean, lo, V, E, densityError] using hdeletedDensity.1
    have hDensityUp : |upMean - V| ≤ densityError := by
      simpa [upMean, up, V, E, densityError] using hdeletedDensity.2
    have hLoMeanLower : V - densityError ≤ loMean := by
      have h := (abs_le.mp hDensityLo).1
      linarith
    have hUpMeanUpper : upMean ≤ V + densityError := by
      have h := (abs_le.mp hDensityUp).2
      linarith
    have hbpos : 0 < b := by
      dsimp [b]
      exact div_pos hH hqR
    have hLoScaled : R * (b * (V - densityError)) ≤ R * (b * loMean) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLoMeanLower hbpos.le) hRpos.le
    have hUpScaled : R * (b * upMean) ≤
        R * (b * (V + densityError)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUpMeanUpper hbpos.le) hRpos.le
    have hErrorCancel : R * (b * densityError) = sieveD * m * E := by
      calc
        R * (b * densityError) = sieveD * E * (R * (b * V)) := by
          dsimp [densityError]
          ring
        _ = sieveD * E * m := by rw [hBase]
        _ = sieveD * m * E := by ring
    have hLoMainCancel :
        R * (b * (V - densityError)) = m - sieveD * m * E := by
      calc
        R * (b * (V - densityError)) = R * (b * V) - R * (b * densityError) := by
          ring
        _ = m - sieveD * m * E := by rw [hBase, hErrorCancel]
    have hUpMainCancel :
        R * (b * (V + densityError)) = m + sieveD * m * E := by
      calc
        R * (b * (V + densityError)) = R * (b * V) + R * (b * densityError) := by
          ring
        _ = m + sieveD * m * E := by rw [hBase, hErrorCancel]
    have hModelLower :
        m - sieveD * m * E - R * y ≤ modelSum := by
      calc
        m - sieveD * m * E - R * y ≤ R * (b * loMean) - R * y := by
          linarith [hLoMainCancel, hLoScaled]
        _ = R * (b * loMean - y) := by ring
        _ ≤ R * loTotal :=
          mul_le_mul_of_nonneg_left hLoCRTlower hRpos.le
        _ ≤ R * modelIndicatorSum :=
          mul_le_mul_of_nonneg_left hLoTotalLe hRpos.le
        _ = modelSum := hModelIndicator.symm
    have hModelUpper :
        modelSum ≤ m + sieveD * m * E + R * y := by
      calc
        modelSum = R * modelIndicatorSum := hModelIndicator
        _ ≤ R * upTotal :=
          mul_le_mul_of_nonneg_left hUpTotalGe hRpos.le
        _ ≤ R * (b * upMean + y) :=
          mul_le_mul_of_nonneg_left hUpCRTupper hRpos.le
        _ = R * (b * upMean) + R * y := by ring
        _ ≤ R * (b * (V + densityError)) + R * y := by
          simpa [add_comm] using add_le_add_right hUpScaled (R * y)
        _ = m + sieveD * m * E + R * y := by
          rw [hUpMainCancel]
    have hfinal : |modelSum - m| ≤ finalError := by
      apply abs_le.mpr
      constructor
      · dsimp [finalError]
        linarith [hModelLower]
      · dsimp [finalError]
        linarith [hModelUpper]
    simpa [modelSum, m, finalError, R, E, z, C] using hfinal

end FractionalPrimes.Literature.LongArithmetic

end
