module

public import FractionalPrimes.Literature.Twisted.SmallDivisorDomination
public import FractionalPrimes.Literature.Twisted.HarmonicDivisorMoment
public import FractionalPrimes.Literature.Uniformity.DivisorMomentBound
public import FractionalPrimes.ArithmeticBasicsCore

/-!
# Local divisor moments

The first standalone step is the exact count of multiples in the
paper's real half-open interval, including negative endpoints and
zero length. It is the counting input to `ltw:local-divisor-moment`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

/-- Multiples of a positive integer in `(x,x+h]` number at most
`h/d+1`, even for negative `x` and `h=0`. -/
theorem realIntegerInterval_multiples_card_le
    (x h : ℝ) (hh : 0 ≤ h) (d : ℕ) (hd : 0 < d) :
    (((FractionalPrimes.realIntegerInterval x h).filter
      (fun n : ℤ => (d : ℤ) ∣ n)).card : ℝ) ≤ h / d + 1 := by
  let s := (FractionalPrimes.realIntegerInterval x h).filter
    (fun n : ℤ => (d : ℤ) ∣ n)
  let t := FractionalPrimes.realIntegerInterval (x / d) (h / d)
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hmap : Set.MapsTo (fun n : ℤ => n / (d : ℤ)) s t := by
    intro n hn
    have hnInt : n ∈ FractionalPrimes.realIntegerInterval x h :=
      (Finset.mem_filter.mp hn).1
    have hdiv : (d : ℤ) ∣ n := (Finset.mem_filter.mp hn).2
    obtain ⟨hnlo, hnhi⟩ := (FractionalPrimes.mem_realIntegerInterval_iff x h n).mp hnInt
    have hq : n = (d : ℤ) * (n / d) := by
      simpa [mul_comm] using (Int.ediv_mul_cancel hdiv).symm
    have hqReal : (n : ℝ) = (d : ℝ) * ((n / (d : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hq
    apply (FractionalPrimes.mem_realIntegerInterval_iff (x / d) (h / d) _).mpr
    constructor
    · apply (div_lt_iff₀ hdReal).mpr
      nlinarith [hnlo]
    · rw [← add_div]
      apply (le_div_iff₀ hdReal).mpr
      nlinarith [hnhi]
  have hinj : Set.InjOn (fun n : ℤ => n / (d : ℤ)) s := by
    intro a ha b hb hab
    have had : (d : ℤ) ∣ a := (Finset.mem_filter.mp ha).2
    have hbd : (d : ℤ) ∣ b := (Finset.mem_filter.mp hb).2
    have haeq : a = (d : ℤ) * (a / d) := by
      simpa [mul_comm] using (Int.ediv_mul_cancel had).symm
    have hbeq : b = (d : ℤ) * (b / d) := by
      simpa [mul_comm] using (Int.ediv_mul_cancel hbd).symm
    change a / (d : ℤ) = b / (d : ℤ) at hab
    rw [haeq, hbeq, hab]
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn _ hmap hinj
  have hlen : 0 ≤ h / (d : ℝ) := div_nonneg hh hdReal.le
  calc
    (s.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast hcard
    _ ≤ h / d + 1 :=
      FractionalPrimes.realIntegerInterval_card_le_of_nonneg (x / d) (h / d) hlen

/-- The same count after restricting to positive integers up to `Z`.
The cutoff only removes possible multiples. -/
theorem positiveInterval_multiples_card_le
    (x h Z : ℝ) (hh : 0 ≤ h) (d : ℕ) (hd : 0 < d) :
    ((((Finset.Icc 1 (Nat.floor Z)).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)).filter
      (fun n : ℕ => d ∣ n)).card : ℝ) ≤ h / d + 1 := by
  let s := ((Finset.Icc 1 (Nat.floor Z)).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)).filter
      (fun n : ℕ => d ∣ n)
  let t := (FractionalPrimes.realIntegerInterval x h).filter
    (fun n : ℤ => (d : ℤ) ∣ n)
  have hmap : Set.MapsTo (fun n : ℕ => (n : ℤ)) s t := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hx := (Finset.mem_filter.mp hn'.1).2
    apply Finset.mem_filter.mpr
    constructor
    · exact (FractionalPrimes.mem_realIntegerInterval_iff x h (n : ℤ)).mpr
        ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
    · change (d : ℤ) ∣ (n : ℤ)
      exact_mod_cast hn'.2
  have hinj : Set.InjOn (fun n : ℕ => (n : ℤ)) s := by
    intro a ha b hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn _ hmap hinj
  calc
    (s.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast hcard
    _ ≤ h / d + 1 := realIntegerInterval_multiples_card_le x h hh d hd

/-- Every small divisor of `n≤Z` lies in the common divisor range
`[1, floor (Z^(1/m))]`. -/
theorem eligibleSmallDivisors_subset_cutoff
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (Z : ℝ) (hnZ : (n : ℝ) ≤ Z) :
    eligibleSmallDivisors n m ⊆
      Finset.Icc 1 (Nat.floor (Z ^ (1 / (m : ℝ) : ℝ))) := by
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  have hdiv : d ∣ n := (Nat.mem_divisors.mp hd'.1).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv hn
  have hexp : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hpow : (n : ℝ) ^ (1 / (m : ℝ) : ℝ) ≤
      Z ^ (1 / (m : ℝ) : ℝ) :=
    Real.rpow_le_rpow hnnonneg hnZ hexp
  apply Finset.mem_Icc.mpr
  constructor
  · exact hdpos
  · apply Nat.le_floor
    exact hd'.2.trans hpow

/-- Finite Fubini identity for the small-divisor sum under a common
real cutoff. -/
theorem localSmallDivisor_sum_rearrange
    (m : ℕ) (hm : 0 < m) (Z : ℝ)
    (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ Z)
    (w : ℕ → ℝ) :
    (∑ n ∈ s, ∑ d ∈ eligibleSmallDivisors n m, w d) =
      ∑ d ∈ Finset.Icc 1 (Nat.floor (Z ^ (1 / (m : ℝ) : ℝ))),
        (((s.filter (fun n => d ∈ eligibleSmallDivisors n m)).card : ℝ) * w d) := by
  let t := Finset.Icc 1 (Nat.floor (Z ^ (1 / (m : ℝ) : ℝ)))
  have heq (n : ℕ) (hn : n ∈ s) :
      eligibleSmallDivisors n m =
        t.filter (fun d => d ∈ eligibleSmallDivisors n m) := by
    ext d
    constructor
    · intro hd
      exact Finset.mem_filter.mpr
        ⟨eligibleSmallDivisors_subset_cutoff m n hm (hs n hn).1 Z
          (hs n hn).2 hd, hd⟩
    · exact fun hd => (Finset.mem_filter.mp hd).2
  calc
    (∑ n ∈ s, ∑ d ∈ eligibleSmallDivisors n m, w d) =
        ∑ n ∈ s, ∑ d ∈ t,
          if d ∈ eligibleSmallDivisors n m then w d else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [heq n hn]
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro d hd
            simp only [Finset.mem_filter, hd, true_and]
    _ = ∑ d ∈ t, ∑ n ∈ s,
          if d ∈ eligibleSmallDivisors n m then w d else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ t,
          (((s.filter (fun n => d ∈ eligibleSmallDivisors n m)).card : ℝ) * w d) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [← Finset.sum_filter]
            simp [mul_comm]

/-- The exact small-divisor reduction before applying the harmonic and
ordinary moment estimates. -/
theorem localDivisorMoment_raw_bound
    (m C : ℕ) (hm : 0 < m) (hC : 0 < C)
    (Z x h : ℝ) (hZ : 1 ≤ Z) (hh : 0 ≤ h) :
    (∑ n ∈ (Finset.Icc 1 (Nat.floor Z)).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h),
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
      (2 ^ (m * C) : ℝ) *
        ∑ d ∈ Finset.Icc 1
          (Nat.floor (Z ^ (1 / (m : ℝ) : ℝ))),
          (h / d + 1) *
            (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 d : ℝ) ^
              ((2 * m + 1) * C) := by
  let s := (Finset.Icc 1 (Nat.floor Z)).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)
  let t := Finset.Icc 1 (Nat.floor (Z ^ (1 / (m : ℝ) : ℝ)))
  let R := (2 * m + 1) * C
  let w : ℕ → ℝ := fun d =>
    (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 d : ℝ) ^ R
  have hs (n : ℕ) (hn : n ∈ s) : 0 < n ∧ (n : ℝ) ≤ Z := by
    have hnI := (Finset.mem_filter.mp hn).1
    have hnlo := (Finset.mem_Icc.mp hnI).1
    have hnhi := (Finset.mem_Icc.mp hnI).2
    refine ⟨by omega, ?_⟩
    exact (by exact_mod_cast hnhi : (n : ℝ) ≤ Nat.floor Z).trans
      (Nat.floor_le (by linarith))
  have hw (d : ℕ) : 0 ≤ w d := by
    dsimp [w]
    positivity
  have hsmall (n : ℕ) (hn : n ∈ s) :
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C ≤
        (2 ^ (m * C) : ℝ) * ∑ d ∈ eligibleSmallDivisors n m, w d := by
    have hnat := smallDivisorDomination m C n hm hC (hs n hn).1
    have hreal :
        ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n ^ C : ℕ) : ℝ) ≤
          ((2 ^ (m * C) * ∑ d ∈ eligibleSmallDivisors n m,
            FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 d ^ R : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, w, R]
      using hreal
  calc
    (∑ n ∈ s,
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
        ∑ n ∈ s, (2 ^ (m * C) : ℝ) *
          ∑ d ∈ eligibleSmallDivisors n m, w d := by
            apply Finset.sum_le_sum
            intro n hn
            exact hsmall n hn
    _ = (2 ^ (m * C) : ℝ) *
          ∑ d ∈ t,
            (((s.filter (fun n => d ∈ eligibleSmallDivisors n m)).card : ℝ) * w d) := by
              rw [← Finset.mul_sum]
              congr 1
              exact localSmallDivisor_sum_rearrange m hm Z s hs w
    _ ≤ (2 ^ (m * C) : ℝ) *
          ∑ d ∈ t, (h / d + 1) * w d := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro d hd
            have hsubset : s.filter (fun n => d ∈ eligibleSmallDivisors n m) ⊆
                s.filter (fun n => d ∣ n) := by
              intro n hn
              have hn' := Finset.mem_filter.mp hn
              exact Finset.mem_filter.mpr
                ⟨hn'.1, (Nat.mem_divisors.mp (Finset.mem_filter.mp hn'.2).1).1⟩
            have hcount :
                (((s.filter (fun n => d ∈ eligibleSmallDivisors n m)).card : ℝ)) ≤
                  h / d + 1 := by
              have hc := Finset.card_le_card hsubset
              exact (by exact_mod_cast hc :
                ((s.filter (fun n => d ∈ eligibleSmallDivisors n m)).card : ℝ) ≤
                  (s.filter (fun n => d ∣ n)).card).trans
                (positiveInterval_multiples_card_le x h Z hh d
                  (Finset.mem_Icc.mp hd).1)
            exact mul_le_mul_of_nonneg_right hcount (hw d)

/-- `ltw:local-divisor-moment`, with the exact coefficient and logarithmic
exponent in the approved blueprint. -/
theorem localDivisorMoment
    (m C : ℕ) (hm : 0 < m) (hC : 0 < C)
    (Z x h : ℝ) (hZ : 1 ≤ Z) (hh : 0 ≤ h) :
    (∑ n ∈ (Finset.Icc 1 (Nat.floor Z)).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h),
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
      (2 ^ (m * C) : ℝ) *
        (h + Z ^ (1 / (m : ℝ) : ℝ)) *
          (1 + Real.log (Z ^ (1 / (m : ℝ) : ℝ))) ^
            (2 ^ ((2 * m + 1) * C)) := by
  let D : ℝ := Z ^ (1 / (m : ℝ) : ℝ)
  let R : ℕ := (2 * m + 1) * C
  let H : ℝ := 1 + Real.log D
  let E : ℕ := 2 ^ R
  let t := Finset.Icc 1 (Nat.floor D)
  let w : ℕ → ℝ := fun d =>
    (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 d : ℝ) ^ R
  have hD : 1 ≤ D := by
    dsimp [D]
    exact Real.one_le_rpow hZ (by positivity)
  have hH : 1 ≤ H := by
    dsimp [H]
    have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
    linarith
  have hR : 1 ≤ R := by
    dsimp [R]
    have hpos : 0 < (2 * m + 1) * C :=
      Nat.mul_pos (by omega) hC
    omega
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hHpow : H ^ (E - 1) ≤ H ^ E :=
    pow_le_pow_right₀ hH (Nat.sub_le E 1)
  have hcoeff : 0 ≤ (2 ^ (m * C) : ℝ) := by positivity
  have hraw := localDivisorMoment_raw_bound m C hm hC Z x h hZ hh
  have hharm :
      (∑ d ∈ t, w d / (d : ℝ)) ≤ H ^ E := by
    simpa only [t, w, R, D, H, E] using
      harmonicDivisorMoment 2 R (by omega) hR D hD
  have hord :
      (∑ d ∈ t, w d) ≤ D * H ^ (E - 1) := by
    simpa only [t, w, R, D, H, E] using
      FractionalPrimes.Literature.Uniformity.divisorMomentBound
        2 R (by omega) hR D hD
  have hsum :
      (∑ d ∈ t, (h / d + 1) * w d) ≤ (h + D) * H ^ E := by
    have hsplit :
        (∑ d ∈ t, (h / d + 1) * w d) =
          h * (∑ d ∈ t, w d / (d : ℝ)) + ∑ d ∈ t, w d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rw [hsplit]
    calc
      h * (∑ d ∈ t, w d / (d : ℝ)) + ∑ d ∈ t, w d ≤
          h * H ^ E + D * H ^ (E - 1) := by
        gcongr
      _ ≤ h * H ^ E + D * H ^ E := by
        gcongr
      _ = (h + D) * H ^ E := by ring
  calc
    (∑ n ∈ (Finset.Icc 1 (Nat.floor Z)).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h),
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
        (2 ^ (m * C) : ℝ) * ∑ d ∈ t, (h / d + 1) * w d := by
          simpa only [t, w, D, R] using hraw
    _ ≤ (2 ^ (m * C) : ℝ) * ((h + D) * H ^ E) :=
      mul_le_mul_of_nonneg_left hsum hcoeff
    _ = (2 ^ (m * C) : ℝ) *
        (h + Z ^ (1 / (m : ℝ) : ℝ)) *
          (1 + Real.log (Z ^ (1 / (m : ℝ) : ℝ))) ^
            (2 ^ ((2 * m + 1) * C)) := by
      simp only [D, H, E, R]
      ring

/-- Restricting to a residue class only removes nonnegative summands. -/
theorem localDivisorMoment_residue
    (m C : ℕ) (hm : 0 < m) (hC : 0 < C)
    (Z x h : ℝ) (hZ : 1 ≤ Z) (hh : 0 ≤ h)
    (q a : ℕ) :
    (∑ n ∈ ((Finset.Icc 1 (Nat.floor Z)).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)).filter
          (fun n : ℕ => n % q = a),
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
      (2 ^ (m * C) : ℝ) *
        (h + Z ^ (1 / (m : ℝ) : ℝ)) *
          (1 + Real.log (Z ^ (1 / (m : ℝ) : ℝ))) ^
            (2 ^ ((2 * m + 1) * C)) := by
  calc
    (∑ n ∈ ((Finset.Icc 1 (Nat.floor Z)).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)).filter
          (fun n : ℕ => n % q = a),
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ≤
        ∑ n ∈ (Finset.Icc 1 (Nat.floor Z)).filter
          (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h),
            (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
              intro n hn _
              positivity
    _ ≤ _ := localDivisorMoment m C hm hC Z x h hZ hh

#print axioms realIntegerInterval_multiples_card_le
#print axioms positiveInterval_multiples_card_le
#print axioms eligibleSmallDivisors_subset_cutoff
#print axioms localSmallDivisor_sum_rearrange
#print axioms localDivisorMoment_raw_bound
#print axioms localDivisorMoment
#print axioms localDivisorMoment_residue

end FractionalPrimes.Literature.Twisted

end
