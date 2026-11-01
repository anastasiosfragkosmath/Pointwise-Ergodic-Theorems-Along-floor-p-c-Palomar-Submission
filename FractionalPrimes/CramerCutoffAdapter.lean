module

public import FractionalPrimes.RosserWeights

/-!
# Paper-to-blueprint Cramér cutoff adapter

The paper includes a prime at the endpoint of its Cramér product, while the
approved blueprint uses a strict prime cutoff.  This file records the exact
correction at a prime endpoint without changing either existing definition.
-/

@[expose] public section

open scoped Nat.Prime
open Classical

namespace FractionalPrimes

noncomputable section

/-- The prime set for the paper's inclusive real cutoff `p ≤ w`. -/
def paperInclusivePrimeSet (w : ℝ) : Finset ℕ :=
  if h : (⌊w⌋₊ : ℝ) = w ∧ (⌊w⌋₊).Prime then
    insert ⌊w⌋₊ (sievePrimesBelow w)
  else sievePrimesBelow w

/-- The literal finite-filter presentation of the paper's `p ≤ w` prime set. -/
def paperInclusivePrimeSetFilter (w : ℝ) : Finset ℕ :=
  (Finset.range (⌊w⌋₊ + 1)).filter fun p => p.Prime ∧ (p : ℝ) ≤ w

/-- The compact endpoint-insertion definition is exactly the literal paper
finite filter, including for nonintegral and composite integer cutoffs. -/
theorem paperInclusivePrimeSet_eq_filter (w : ℝ) :
    paperInclusivePrimeSet w = paperInclusivePrimeSetFilter w := by
  ext q
  have hfilter : q ∈ paperInclusivePrimeSetFilter w ↔
      q.Prime ∧ (q : ℝ) ≤ w := by
    simp only [paperInclusivePrimeSetFilter, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hqprime, hqle⟩
      exact ⟨hqprime, hqle⟩
    · rintro ⟨hqprime, hqle⟩
      have hqfloor : q ≤ ⌊w⌋₊ := Nat.le_floor hqle
      exact ⟨by omega, hqprime, hqle⟩
  rw [hfilter]
  by_cases hb : (⌊w⌋₊ : ℝ) = w ∧ (⌊w⌋₊).Prime
  · simp only [paperInclusivePrimeSet, dif_pos hb, Finset.mem_insert,
      sievePrimesBelow_iff]
    constructor
    · rintro (hq | ⟨hqprime, hqlt⟩)
      · subst q
        exact ⟨hb.2, hb.1.le⟩
      · exact ⟨hqprime, hqlt.le⟩
    · rintro ⟨hqprime, hqle⟩
      by_cases hqfloor : q = ⌊w⌋₊
      · exact Or.inl hqfloor
      · right
        refine ⟨hqprime, ?_⟩
        have hneq : (q : ℝ) ≠ w := by
          intro hqw
          have hfloor : Nat.floor (q : ℝ) = Nat.floor w := congrArg Nat.floor hqw
          have hqfloor' : q = ⌊w⌋₊ := by simpa using hfloor
          exact hqfloor hqfloor'
        exact lt_of_le_of_ne hqle hneq
  · simp only [paperInclusivePrimeSet, dif_neg hb, sievePrimesBelow_iff]
    constructor
    · rintro ⟨hqprime, hqlt⟩
      exact ⟨hqprime, hqlt.le⟩
    · rintro ⟨hqprime, hqle⟩
      by_cases hqlt : (q : ℝ) < w
      · exact ⟨hqprime, hqlt⟩
      · have hqw : (q : ℝ) = w := le_antisymm hqle (le_of_not_gt hqlt)
        have hfloor : Nat.floor (q : ℝ) = Nat.floor w := congrArg Nat.floor hqw
        have hqeq : q = ⌊w⌋₊ := by simpa using hfloor
        exact False.elim (hb ⟨by simpa [hqeq] using hqw, by simpa [hqeq] using hqprime⟩)

/-- The paper's prime product with its inclusive endpoint convention. -/
def paperInclusivePrimeProduct (w : ℝ) : ℕ :=
  ∏ p ∈ paperInclusivePrimeSet w, p

/-- The inclusive product is the literal product over all primes `p ≤ w`. -/
theorem paperInclusivePrimeProduct_eq_filter (w : ℝ) :
    paperInclusivePrimeProduct w =
      ∏ p ∈ paperInclusivePrimeSetFilter w, p := by
  rw [paperInclusivePrimeProduct, paperInclusivePrimeSet_eq_filter]

/-- The paper's inclusive Cramér weight with its original integer-indexed
gcd convention. -/
def paperInclusiveCramerWeight (w : ℝ) (n : ℤ) : ℝ :=
  ((paperInclusivePrimeProduct w : ℝ) /
      (Nat.totient (paperInclusivePrimeProduct w) : ℝ)) *
    (if Int.gcd n (paperInclusivePrimeProduct w : ℤ) = 1 then 1 else 0)

/-- Away from an integer prime endpoint, the manuscript's inclusive
Cramér model agrees exactly with the blueprint's strict model. -/
theorem paperInclusiveCramerWeight_eq_strict_of_no_endpoint
    (w : ℝ) (n : ℤ)
    (h : ¬ ((⌊w⌋₊ : ℝ) = w ∧ (⌊w⌋₊).Prime)) :
    paperInclusiveCramerWeight w n = paperCramerWeight w n := by
  have hprod : paperInclusivePrimeProduct w = paperPrimeProduct w := by
    simp [paperInclusivePrimeProduct, paperInclusivePrimeSet, h,
      paperPrimeProduct, sievePrimeProduct]
  simp [paperInclusiveCramerWeight, paperCramerWeight,
    paperCramerDensity, hprod, paperPrimeProduct]
  split_ifs <;> simp_all

/-- The paper's inclusive prime product at a prime endpoint. -/
def paperInclusivePrimeProductAtPrime (p : ℕ) : ℕ :=
  p * paperPrimeProduct (p : ℝ)

/-- The paper's inclusive Cramér weight at a prime endpoint, on positive
natural indices. -/
def paperInclusiveCramerWeightAtPrime (p n : ℕ) : ℝ :=
  ((paperInclusivePrimeProductAtPrime p : ℝ) /
      (Nat.totient (paperInclusivePrimeProductAtPrime p) : ℝ)) *
    (if Nat.gcd n (paperInclusivePrimeProductAtPrime p) = 1 then 1 else 0)

/-- At a prime endpoint, adjoining the endpoint prime to the strict product
multiplies that product by the endpoint prime. -/
theorem paperInclusivePrimeProductAtPrime_eq (p : ℕ) :
    paperInclusivePrimeProductAtPrime p =
      p * paperPrimeProduct (p : ℝ) := rfl

/-- At an integer prime endpoint, the inclusive prime set is the strict set
with precisely that endpoint inserted. -/
theorem paperInclusivePrimeSet_atPrime {p : ℕ} (hp : p.Prime) :
    paperInclusivePrimeSet (p : ℝ) = insert p (sievePrimesBelow (p : ℝ)) := by
  simp [paperInclusivePrimeSet, hp]

/-- The inclusive finite product at a prime endpoint is exactly the strict
product times the endpoint prime. -/
theorem paperInclusivePrimeProduct_atPrime {p : ℕ} (hp : p.Prime) :
    paperInclusivePrimeProduct (p : ℝ) =
      paperInclusivePrimeProductAtPrime p := by
  rw [paperInclusivePrimeProduct, paperInclusivePrimeSet_atPrime hp,
    Finset.prod_insert]
  · simp [paperInclusivePrimeProductAtPrime, paperPrimeProduct, sievePrimeProduct,
      mul_comm]
  · rw [sievePrimesBelow_iff]
    exact fun h => (not_lt_of_ge (le_rfl : (p : ℝ) ≤ p)) h.2

/-- The endpoint prime does not divide the strict product below it. -/
theorem prime_not_dvd_paperPrimeProduct_at_self {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ paperPrimeProduct (p : ℝ) := by
  rw [paperPrimeProduct, sievePrimeProduct]
  refine Prime.not_dvd_finsetProd hp.prime ?_
  intro q hq
  rw [sievePrimesBelow_iff] at hq
  intro hdiv
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.1).mp hdiv
  subst q
  exact (not_lt_of_ge (le_rfl : (p : ℝ) ≤ p)) hq.2

/-- Exact totient-ratio change when the endpoint prime is adjoined. -/
theorem paperInclusiveCramerDensityAtPrime_eq {p : ℕ} (hp : p.Prime) :
    (paperInclusivePrimeProductAtPrime p : ℝ) /
        (Nat.totient (paperInclusivePrimeProductAtPrime p) : ℝ) =
      paperCramerDensity (p : ℝ) * ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hpnot := prime_not_dvd_paperPrimeProduct_at_self hp
  have hφ := Nat.totient_mul_of_prime_of_not_dvd hp hpnot
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpSub : (p : ℝ) - 1 ≠ 0 := by linarith
  have hWpos : 0 < paperPrimeProduct (p : ℝ) := by
    dsimp [paperPrimeProduct, sievePrimeProduct]
    apply Finset.prod_pos
    intro q hq
    rw [sievePrimesBelow_iff] at hq
    exact hq.1.pos
  have hWreal : (0 : ℝ) < paperPrimeProduct (p : ℝ) := by
    exact_mod_cast hWpos
  have hφWpos : (0 : ℝ) < Nat.totient (paperPrimeProduct (p : ℝ)) := by
    exact_mod_cast (Nat.totient_pos.mpr hWpos)
  rw [paperInclusivePrimeProductAtPrime_eq, hφ]
  unfold paperCramerDensity paperPrimeProduct
  push_cast
  field_simp [ne_of_gt hWreal, ne_of_gt hφWpos, hpSub]
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  ring

/-- On natural inputs, the direct inclusive model agrees with the prime-endpoint
natural-index helper. -/
theorem paperInclusiveCramerWeight_atPrime {p n : ℕ} (hp : p.Prime) :
    paperInclusiveCramerWeight (p : ℝ) (n : ℤ) =
      paperInclusiveCramerWeightAtPrime p n := by
  unfold paperInclusiveCramerWeight paperInclusiveCramerWeightAtPrime
  rw [paperInclusivePrimeProduct_atPrime hp, Int.gcd_natCast_natCast]

/-- Coprimality with the product including the boundary prime splits into
strict-cutoff coprimality and avoidance of that one prime. -/
theorem nat_gcd_eq_one_mul_prime_iff {p n W : ℕ} (hp : p.Prime) :
    Nat.gcd n (p * W) = 1 ↔ Nat.gcd n W = 1 ∧ ¬ p ∣ n := by
  change Nat.Coprime n (p * W) ↔ Nat.Coprime n W ∧ ¬ p ∣ n
  rw [Nat.coprime_comm, Nat.coprime_mul_iff_left]
  simp [Nat.coprime_comm, hp.coprime_iff_not_dvd, and_comm]

/-- The strict paper weight on a natural index is the original integer-indexed
weight from `paperCramerWeight`. -/
theorem paperCramerWeight_natCast (w : ℝ) (n : ℕ) :
    paperCramerWeight w (n : ℤ) =
      paperCramerDensity w *
        (if Nat.gcd n (paperPrimeProduct w) = 1 then 1 else 0) := by
  unfold paperCramerWeight
  rw [Int.gcd_natCast_natCast]

/-- The inclusive paper model at a prime endpoint is exactly the strict model
with the boundary-prime density and divisibility correction. -/
theorem paperInclusiveCramerWeightAtPrime_sub_strict {p n : ℕ}
    (hp : p.Prime) :
    paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
        paperCramerWeight (p : ℝ) (n : ℤ) =
      paperCramerDensity (p : ℝ) *
        (if Nat.gcd n (paperPrimeProduct (p : ℝ)) = 1 then
          if p ∣ n then -1 else 1 / ((p : ℝ) - 1)
        else 0) := by
  unfold paperInclusiveCramerWeight
  rw [paperInclusivePrimeProduct_atPrime hp]
  rw [paperInclusiveCramerDensityAtPrime_eq hp]
  rw [paperCramerWeight_natCast]
  rw [paperInclusivePrimeProductAtPrime_eq]
  rw [Int.gcd_natCast_natCast]
  simp only [nat_gcd_eq_one_mul_prime_iff hp]
  have hpSubPos : 0 < (p : ℝ) - 1 := by
    have hp2 : 2 ≤ p := hp.two_le
    have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  by_cases hg : Nat.gcd n (paperPrimeProduct (p : ℝ)) = 1 <;>
    by_cases hpn : p ∣ n
  · simp [hg, hpn]
    <;> ring
  · simp [hg, hpn]
    <;> field_simp [ne_of_gt hpSubPos]
    <;> ring
  · simp [hg]
  · simp [hg]

/-- Pointwise absolute error, with the divisibility case separated from the
small nonmultiple correction. -/
theorem paperInclusiveCramerWeightAtPrime_abs_sub_strict_le {p n : ℕ}
    (hp : p.Prime) :
    |paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
        paperCramerWeight (p : ℝ) (n : ℤ)| ≤
      paperCramerDensity (p : ℝ) *
        ((if p ∣ n then (1 : ℝ) else 0) + 1 / ((p : ℝ) - 1)) := by
  rw [paperInclusiveCramerWeightAtPrime_sub_strict hp]
  have hR : 0 ≤ paperCramerDensity (p : ℝ) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h := (paperCramerDensity_bounds (w := (p : ℝ)) hp2).1
    linarith
  have hpSubPos : 0 < (p : ℝ) - 1 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  by_cases hg : Nat.gcd n (paperPrimeProduct (p : ℝ)) = 1
  · by_cases hpn : p ∣ n
    · simp [hg, hpn, abs_mul, abs_of_nonneg hR]
      nlinarith [mul_nonneg hR (le_of_lt (inv_pos.mpr hpSubPos))]
    · simp [hg, hpn, abs_of_nonneg hR, abs_of_pos hpSubPos]
  · simp [hg, abs_mul, abs_of_nonneg hR]
    positivity

/-- In an integer interval, the number of multiples of `p` is at most its
length divided by `p`, plus one. This uses Mathlib's exact interval residue
count and requires only `0 < p` and `a ≤ b`. -/
theorem card_multiples_Ioc_le_div_add_one {p a b : ℕ} (hp : 0 < p)
    (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun n => p ∣ n)).card ≤ (b - a) / p + 1 := by
  have hfilter :
      (Finset.Ioc a b).filter (fun n => p ∣ n) =
        {n ∈ Finset.Ioc a b | n ≡ 0 [MOD p]} := by
    ext n
    simp [Nat.modEq_zero_iff_dvd]
  have hcount := Nat.Ioc_filter_modEq_card (a := a) (b := b) (r := p) (v := 0) hp
  rw [← hfilter] at hcount
  have hdiv : a / p ≤ b / p := Nat.div_le_div_right hab
  have hcountCast :
      ((((Finset.Ioc a b).filter (fun n => p ∣ n)).card : ℕ) : ℤ) =
        ((b / p - a / p : ℕ) : ℤ) := by
    rw [hcount]
    simp only [Nat.cast_zero, sub_zero, Rat.floor_natCast_div_natCast]
    rw [Nat.cast_sub hdiv]
    rw [max_eq_left]
    · rfl
    · have hdivZ : (a / p : ℤ) ≤ b / p := by exact_mod_cast hdiv
      linarith
  have hNat : b / p - a / p ≤ (b - a) / p + 1 := by
    apply Nat.sub_le_iff_le_add.mpr
    calc
      b / p = (a + (b - a)) / p := by rw [Nat.add_sub_cancel' hab]
      _ ≤ a / p + (b - a) / p + 1 :=
        Nat.add_div_le_div_add_div_add_one a (b - a) p
      _ = ((b - a) / p + 1) + a / p := by ac_rfl
  have hboundCast :
      ((((Finset.Ioc a b).filter (fun n => p ∣ n)).card : ℕ) : ℤ) ≤
        ((((b - a) / p + 1 : ℕ) : ℤ)) := by
    rw [hcountCast]
    exact_mod_cast hNat
  exact_mod_cast hboundCast

/-- The exact pointwise correction sums to an interval error bounded by the
length-over-prime term plus one endpoint term. No assumption `H ≥ p` is used. -/
theorem paperInclusiveCramerIntervalL1Error {p a b : ℕ} (hp : p.Prime)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b,
      |paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
        paperCramerWeight (p : ℝ) (n : ℤ)|) ≤
      paperCramerDensity (p : ℝ) *
        (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1) +
          ((((b - a) / p : ℕ) : ℝ) + 1)) := by
  have hpoint {n : ℕ} (hn : n ∈ Finset.Ioc a b) :
      |paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
          paperCramerWeight (p : ℝ) (n : ℤ)| ≤
        paperCramerDensity (p : ℝ) *
          ((if p ∣ n then (1 : ℝ) else 0) + 1 / ((p : ℝ) - 1)) :=
    paperInclusiveCramerWeightAtPrime_abs_sub_strict_le hp
  have hcount := card_multiples_Ioc_le_div_add_one hp.pos hab
  have hpSubPos : 0 < (p : ℝ) - 1 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hR : 0 ≤ paperCramerDensity (p : ℝ) := by
    have h := (paperCramerDensity_bounds (w := (p : ℝ))
      (by exact_mod_cast hp.two_le)).1
    linarith
  calc
    _ ≤ ∑ n ∈ Finset.Ioc a b,
        paperCramerDensity (p : ℝ) *
          ((if p ∣ n then (1 : ℝ) else 0) + 1 / ((p : ℝ) - 1)) :=
      Finset.sum_le_sum fun n hn => hpoint hn
    _ = paperCramerDensity (p : ℝ) *
        (((((Finset.Ioc a b).filter (fun n => p ∣ n)).card : ℕ) : ℝ) +
          (((Finset.Ioc a b).card : ℕ) : ℝ) / ((p : ℝ) - 1)) := by
      have hInd :
          (∑ n ∈ Finset.Ioc a b, (if p ∣ n then (1 : ℝ) else 0)) =
            (((Finset.Ioc a b).filter (fun n => p ∣ n)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp
      have hConst :
          (∑ _n ∈ Finset.Ioc a b, (1 : ℝ) / ((p : ℝ) - 1)) =
            (((Finset.Ioc a b).card : ℕ) : ℝ) / ((p : ℝ) - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hInd, hConst]
    _ ≤ paperCramerDensity (p : ℝ) *
        (((((b - a) / p : ℕ) : ℝ) + 1) +
          (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1))) := by
      gcongr
      · exact_mod_cast hcount
      · simp
    _ = _ := by ring

/-- Uniform real-cutoff endpoint correction. Off a prime endpoint it is
exactly zero; at a prime endpoint it is the proved interval count bound. -/
theorem paperInclusiveCramerIntervalL1Error_general (w : ℝ) (a b : ℕ)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b,
      |paperInclusiveCramerWeight w (n : ℤ) -
        paperCramerWeight w (n : ℤ)|) ≤
      if h : (⌊w⌋₊ : ℝ) = w ∧ (⌊w⌋₊).Prime then
        paperCramerDensity w *
          (((b - a : ℕ) : ℝ) / ((⌊w⌋₊ : ℝ) - 1) +
            ((((b - a) / ⌊w⌋₊ : ℕ) : ℝ) + 1))
      else 0 := by
  by_cases h : (⌊w⌋₊ : ℝ) = w ∧ (⌊w⌋₊).Prime
  · simp only [dif_pos h]
    have hprime := paperInclusiveCramerIntervalL1Error
      (p := ⌊w⌋₊) (a := a) (b := b) h.2 hab
    simpa only [h.1] using hprime
  · simp only [dif_neg h]
    simp [paperInclusiveCramerWeight_eq_strict_of_no_endpoint _ _ h]

/-- Any unit-bounded complex phase has the same endpoint-cutoff error bound;
in particular this applies uniformly to polynomial phases. -/
theorem paperInclusiveCramerIntervalCorrelationError {p a b : ℕ}
    (hp : p.Prime) (hab : a ≤ b) (phase : ℕ → ℂ)
    (hphase : ∀ n ∈ Finset.Ioc a b, ‖phase n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Ioc a b,
        ((paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
          paperCramerWeight (p : ℝ) (n : ℤ) : ℝ) : ℂ) * phase n‖ ≤
      paperCramerDensity (p : ℝ) *
        (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1) +
          ((((b - a) / p : ℕ) : ℝ) + 1)) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc a b,
        ‖((paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
          paperCramerWeight (p : ℝ) (n : ℤ) : ℝ) : ℂ) * phase n‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc a b,
        |paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
          paperCramerWeight (p : ℝ) (n : ℤ)| * ‖phase n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ n ∈ Finset.Ioc a b,
        |paperInclusiveCramerWeight (p : ℝ) (n : ℤ) -
          paperCramerWeight (p : ℝ) (n : ℤ)| := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_of_le_one_right (abs_nonneg _) (hphase n hn)
    _ ≤ paperCramerDensity (p : ℝ) *
        (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1) +
          ((((b - a) / p : ℕ) : ℝ) + 1)) :=
      paperInclusiveCramerIntervalL1Error hp hab

end

end FractionalPrimes

#print axioms FractionalPrimes.paperInclusiveCramerWeight_eq_strict_of_no_endpoint
#print axioms FractionalPrimes.paperInclusiveCramerIntervalL1Error_general

end
