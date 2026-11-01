module
public import FractionalPrimes.Final.ForwardAverageFacts

public import FractionalPrimes.Literature.Ergodic.PrimeNormalizedConvergence
public import FractionalPrimes.Final.PrimePartsDecomposition


@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Final
noncomputable section

theorem primes_Icc_zero_eq_primes_Icc_one (N : ℕ) :
    (Finset.Icc 0 N).filter Nat.Prime = (Finset.Icc 1 N).filter Nat.Prime := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
  constructor
  · rintro ⟨hN, hn⟩
    exact ⟨⟨hn.one_lt.le, hN⟩, hn⟩
  · rintro ⟨⟨_, hN⟩, hn⟩
    exact ⟨hN, hn⟩

theorem primeLogPartialSum_eq_prime_filter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → E) (N : ℕ) :
    primeLogPartialSum g N =
      ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (n : ℝ) • g n := by
  rw [primeLogPartialSum, ← Finset.sum_filter, primes_Icc_zero_eq_primes_Icc_one]

theorem primePartialSum_eq_prime_filter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → E) (N : ℕ) :
    primePartialSum g N = ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, g n := by
  rw [primePartialSum, ← Finset.sum_filter, primes_Icc_zero_eq_primes_Icc_one]

theorem primeLogMean_orbit_eq
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (N : Scale) (x : X) :
    (N.val : ℝ)⁻¹ • primeLogPartialSum
        (fun n => f (S.forwardTime (floorPower c n) x)) N.val =
      paperPrimeOnlyPart S c f N x := by
  rw [primeLogPartialSum_eq_prime_filter]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, paperPrimeOnlyPart]

theorem primeMean_orbit_eq
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) (f : X → ℂ) (N : ℕ) (hN : 2 ≤ N) (x : X) :
    (Nat.primeCounting N : ℝ)⁻¹ • primePartialSum
        (fun n => f (S.forwardTime (floorPower c n) x)) N =
      primeCutoffAverage S c f N hN x := by
  rw [primePartialSum_eq_prime_filter]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    primeCutoffAverage, primeAverage, System.shift, System.forwardTime, floorTime, Function.comp_apply, Pi.smul_apply, smul_eq_mul]

#print axioms primeLogMean_orbit_eq
#print axioms primeMean_orbit_eq
end
end FractionalPrimes.Final
