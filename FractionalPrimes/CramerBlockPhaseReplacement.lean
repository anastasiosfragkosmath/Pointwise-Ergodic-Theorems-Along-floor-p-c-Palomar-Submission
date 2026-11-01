module

public import FractionalPrimes.RosserWeights
public import FractionalPrimes.CramerBlockWeightedProgression

/-! The oscillatory phase replacement step in the approved proof of
`ar:cramer-block`, using the checked strict-cutoff Rosser sieve contract. -/

@[expose] public section

namespace FractionalPrimes

/-- Finite divisor/interval sum interchange for the Rosser support.
This is the exact rearrangement used before applying the progression
estimate modulus by modulus in `ar:cramer-block`. -/
theorem rosserDivisorPhase_sum_swap
    (S : Finset ℤ) (y : ℝ) (coeff : ℕ → ℂ) (phase : ℤ → ℂ) :
    (∑ n ∈ S,
      ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        coeff d * phase n) =
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        coeff d *
          ∑ n ∈ S.filter (fun n : ℤ => 0 < d ∧ d ∣ n.natAbs), phase n := by
  simp_rw [rosserPositiveDivisorsBelow, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

/-- Exact progression reindexing on a real-endpoint integer interval.
The positive-divisor filter is the one used by the Rosser weights. -/
theorem sum_realIntegerInterval_filter_dvd_eq_scaled
    (X H : ℝ) (d : ℕ) (hd : 0 < d) (f : ℤ → ℂ) :
    (∑ n ∈ (realIntegerInterval X H).filter
        (fun n : ℤ => 0 < d ∧ d ∣ n.natAbs), f n) =
      ∑ m ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
        f ((d : ℤ) * m) := by
  symm
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  apply Finset.sum_bij (fun m _hm => (d : ℤ) * m)
  · intro m hm
    have hbounds := (mem_realIntegerInterval_iff _ _ m).mp hm
    have hlow : X < (d : ℝ) * (m : ℝ) := by
      have h := (div_lt_iff₀ hdR).mp hbounds.1
      nlinarith
    have hhigh : (d : ℝ) * (m : ℝ) ≤ X + H := by
      have hright : (m : ℝ) ≤ (X + H) / (d : ℝ) := by
        calc
          (m : ℝ) ≤ X / (d : ℝ) + H / (d : ℝ) := hbounds.2
          _ = (X + H) / (d : ℝ) := by ring
      have h := (le_div_iff₀ hdR).mp hright
      nlinarith
    simp only [Finset.mem_filter]
    constructor
    · apply (mem_realIntegerInterval_iff X H _).mpr
      constructor
      · simpa only [Int.cast_mul, Int.cast_natCast] using hlow
      · simpa only [Int.cast_mul, Int.cast_natCast] using hhigh
    · exact ⟨hd, (Int.natCast_dvd).mp ⟨m, rfl⟩⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    exact mul_left_cancel₀ (ne_of_gt hdZ) heq
  · intro n hn
    have hfilter := Finset.mem_filter.mp hn
    have hdiv : (d : ℤ) ∣ n := (Int.natCast_dvd).mpr hfilter.2.2
    obtain ⟨m, hm⟩ := hdiv
    refine ⟨m, ?_, hm.symm⟩
    have hbounds := (mem_realIntegerInterval_iff X H n).mp hfilter.1
    apply (mem_realIntegerInterval_iff _ _ m).mpr
    constructor
    · apply (div_lt_iff₀ hdR).mpr
      have hcast : (n : ℝ) = (d : ℝ) * (m : ℝ) := by
        exact_mod_cast hm
      nlinarith
    · have hcast : (n : ℝ) = (d : ℝ) * (m : ℝ) := by
        exact_mod_cast hm
      have hupper : (m : ℝ) ≤ (X + H) / (d : ℝ) :=
        (le_div_iff₀ hdR).mpr (by nlinarith [hbounds.2])
      simpa only [add_div] using hupper
  · intro m hm
    rfl

/-- The Rosser divisor phase sum equals the weighted sum of exact
progression phase sums, including the zero-modulus term (which vanishes). -/
theorem rosserDivisorPhase_sum_scaled
    (X H y : ℝ) (coeff : ℕ → ℂ) (phase : ℤ → ℂ) :
    (∑ n ∈ realIntegerInterval X H,
      (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs, coeff d) * phase n) =
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        coeff d *
          ∑ m ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            phase ((d : ℤ) * m) := by
  calc
    _ = ∑ n ∈ realIntegerInterval X H,
        ∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          coeff d * phase n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_mul]
    _ = ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        coeff d *
          ∑ n ∈ (realIntegerInterval X H).filter
              (fun n : ℤ => 0 < d ∧ d ∣ n.natAbs), phase n :=
      rosserDivisorPhase_sum_swap _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hd0 : d = 0
      · subst d
        simp [realIntegerInterval]
      · exact congrArg (coeff d * ·)
          (sum_realIntegerInterval_filter_dvd_eq_scaled X H d
            (Nat.pos_of_ne_zero hd0) phase)

/-- Real sieve coefficients embedded in the complex phase identity. -/
theorem rosserRealDivisorPhase_sum_scaled
    (X H y : ℝ) (coeff : ℕ → ℝ) (phase : ℤ → ℂ) :
    (∑ n ∈ realIntegerInterval X H,
      ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs, coeff d : ℝ) : ℂ) *
        phase n) =
      ∑ d ∈ Finset.range (⌊y⌋₊ + 1),
        (coeff d : ℂ) *
          ∑ m ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            phase ((d : ℤ) * m) := by
  simpa only [Complex.ofReal_sum] using
    rosserDivisorPhase_sum_scaled X H y (fun d => (coeff d : ℂ)) phase

/-- A finite family of positive divisor moduli reindexes directly into
the exact scaled progression intervals. -/
theorem positiveDivisorPhase_sum_scaled
    (X H : ℝ) (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (coeff : ℕ → ℂ) (phase : ℤ → ℂ) :
    (∑ n ∈ realIntegerInterval X H,
      (∑ d ∈ D, if (d : ℤ) ∣ n then coeff d else 0) * phase n) =
      ∑ d ∈ D, coeff d *
        ∑ m ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
          phase ((d : ℤ) * m) := by
  calc
    _ = ∑ n ∈ realIntegerInterval X H,
        ∑ d ∈ D, if (d : ℤ) ∣ n then coeff d * phase n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ = ∑ d ∈ D, ∑ n ∈ realIntegerInterval X H,
        if (d : ℤ) ∣ n then coeff d * phase n else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ D, coeff d *
        ∑ n ∈ (realIntegerInterval X H).filter
          (fun n : ℤ => (d : ℤ) ∣ n), phase n := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hfilter :
          (realIntegerInterval X H).filter (fun n : ℤ => (d : ℤ) ∣ n) =
            (realIntegerInterval X H).filter
              (fun n : ℤ => 0 < d ∧ d ∣ n.natAbs) := by
        ext n
        simp only [Finset.mem_filter, Int.natCast_dvd, hD d hd, true_and]
      rw [hfilter, sum_realIntegerInterval_filter_dvd_eq_scaled X H d (hD d hd) phase]

/-- The upper Rosser divisor model is exactly the finite weighted family
of progression phase sums over its true nonzero modulus support. -/
theorem rosserUpperDivisorPhase_sum_scaled
    (X H w y : ℝ) (hw : 2 ≤ w) (hwy : w ≤ y)
    (phase : ℤ → ℂ) :
    (∑ n ∈ realIntegerInterval X H,
      ((∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
          rosserAllSUpperCoefficient w y d : ℝ) : ℂ) * phase n) =
      ∑ d ∈ rosserAllSModuli y,
        (rosserAllSUpperCoefficient w y d : ℂ) *
          ∑ m ∈ realIntegerInterval (X / (d : ℝ)) (H / (d : ℝ)),
            phase ((d : ℤ) * m) := by
  have hD : ∀ d ∈ rosserAllSModuli y, 0 < d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2.1
  calc
    _ = ∑ n ∈ realIntegerInterval X H,
        (∑ d ∈ rosserAllSModuli y,
          if (d : ℤ) ∣ n then (rosserAllSUpperCoefficient w y d : ℂ) else 0) *
          phase n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [(rosserAllSDivisorSum_eq_moduli_int hw hwy n).2]
      rw [Complex.ofReal_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ = _ := positiveDivisorPhase_sum_scaled X H _ hD _ phase

/-- On a finite integer interval, the upper Rosser sieve approximant
replaces the strict-cutoff Cramér model in every unit-bounded phase sum
with the exact interval `L¹` loss from the sieve contract. -/
theorem rosserUpperCramerPhaseReplacement {J : Set ℝ} (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ (n : ℝ) ∈ J)
    (hJconv : ∀ x ∈ J, ∀ y ∈ J, ∀ t : ℝ,
      x ≤ t → t ≤ y → t ∈ J)
    {L : ℕ} (hcard : S.card = L) (hL : 1 ≤ L) {w y : ℝ}
    (hw : 2 ≤ w) (hwy : w ≤ y)
    (hyL : y ≤ (L : ℝ) ^ (1 / 10 : ℝ))
    (phase : ℤ → ℂ) (hphase : ∀ n ∈ S, ‖phase n‖ ≤ 1) :
    ‖(∑ n ∈ S,
        (((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) : ℂ) *
          phase n) -
      (∑ n ∈ S,
        (((sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ)) *
          (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
            rosserAllSUpperCoefficient w y d) : ℂ) * phase n)‖ ≤
      (L : ℝ) * sieveConstant * Real.exp (-Real.log y / Real.log w) := by
  have hfund := rosserFundamentalInterval S hS hJconv hcard hL hw hwy hyL
  have hupper := hfund.2.2.2.2.2
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum := (div_le_iff₀ hLpos).mp hupper
  have hphaseBound := norm_phase_weight_replacement_le_L1 S
    (fun n => ((sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ)) *
      (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0))
    (fun n => ((sievePrimeProduct w : ℝ) /
      (Nat.totient (sievePrimeProduct w) : ℝ)) *
      (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
        rosserAllSUpperCoefficient w y d)) phase hphase
  calc
    _ ≤ ∑ n ∈ S,
        |((sievePrimeProduct w : ℝ) /
            (Nat.totient (sievePrimeProduct w) : ℝ)) *
            (if Int.gcd n (sievePrimeProduct w : ℤ) = 1 then (1 : ℝ) else 0) -
          ((sievePrimeProduct w : ℝ) /
            (Nat.totient (sievePrimeProduct w) : ℝ)) *
            (∑ d ∈ rosserPositiveDivisorsBelow y n.natAbs,
              rosserAllSUpperCoefficient w y d)| := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_natCast] using hphaseBound
    _ ≤ (L : ℝ) * sieveConstant * Real.exp (-Real.log y / Real.log w) := by
      convert hsum using 1 <;> ring

end FractionalPrimes

#print axioms FractionalPrimes.rosserUpperCramerPhaseReplacement
#print axioms FractionalPrimes.rosserDivisorPhase_sum_swap
#print axioms FractionalPrimes.sum_realIntegerInterval_filter_dvd_eq_scaled
#print axioms FractionalPrimes.rosserDivisorPhase_sum_scaled
#print axioms FractionalPrimes.rosserRealDivisorPhase_sum_scaled
#print axioms FractionalPrimes.positiveDivisorPhase_sum_scaled
#print axioms FractionalPrimes.rosserUpperDivisorPhase_sum_scaled
