module

public import FractionalPrimes.ArithmeticBasicsCore
public import FractionalPrimes.Chebyshev
public import FractionalPrimes.CramerCutoffAdapter
public import FractionalPrimes.CramerDensityAtScale
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Floor endpoints for changing a short-interval centre

This file isolates the exact finite-set and length bookkeeping at the start
of blueprint `lc:model-difference`.  It does not compare the two Cramér
models; that estimate is the next analytic step.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

private theorem shortBlockCutoff_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun y : ℝ => FractionalPrimes.paperShortBlockCutoff y)
      (Real.exp ((Real.log t) ^ (1 / 10 : ℝ)) *
        (1 / 10 : ℝ) * (Real.log t) ^ (1 / 10 - 1 : ℝ) * t⁻¹) t := by
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htpos.ne'
  have hpow : HasDerivAt (fun y : ℝ => (Real.log y) ^ (1 / 10 : ℝ))
      (t⁻¹ * (1 / 10 : ℝ) * (Real.log t) ^ (1 / 10 - 1 : ℝ)) t :=
    hlog.rpow_const (Or.inl hlogpos.ne')
  have hexp := (Real.hasDerivAt_exp _).comp t hpow
  simpa [FractionalPrimes.paperShortBlockCutoff, mul_assoc, mul_left_comm,
    mul_comm, Function.comp_def] using hexp

private theorem shortBlockCutoff_deriv_abs_le_tenth {t : ℝ} (ht : 3 ≤ t) :
    |deriv FractionalPrimes.paperShortBlockCutoff t| ≤ 1 / 10 := by
  have ht1 : 1 < t := by linarith
  have htpos : 0 < t := by linarith
  have hderiv := (shortBlockCutoff_hasDerivAt ht1).deriv
  have hlog : 1 ≤ Real.log t := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < t)).2
    exact (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ t))
  have hpowbase : (Real.log t) ^ (1 / 10 : ℝ) ≤ Real.log t :=
    Real.rpow_le_self_of_one_le hlog (by norm_num)
  have hexp : Real.exp ((Real.log t) ^ (1 / 10 : ℝ)) ≤ t := by
    calc
      Real.exp ((Real.log t) ^ (1 / 10 : ℝ)) ≤ Real.exp (Real.log t) :=
        Real.exp_le_exp.mpr hpowbase
      _ = t := Real.exp_log htpos
  have hnegativePower :
      (Real.log t) ^ (1 / 10 - 1 : ℝ) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hlog
    norm_num
  have hpositive :
      0 ≤ Real.exp ((Real.log t) ^ (1 / 10 : ℝ)) *
        (1 / 10 : ℝ) * (Real.log t) ^ (1 / 10 - 1 : ℝ) * t⁻¹ := by
    positivity
  rw [hderiv, abs_of_nonneg hpositive]
  calc
    Real.exp ((Real.log t) ^ (1 / 10 : ℝ)) *
        (1 / 10 : ℝ) * (Real.log t) ^ (1 / 10 - 1 : ℝ) * t⁻¹ ≤
      t * (1 / 10 : ℝ) * 1 * t⁻¹ := by
        gcongr
    _ = 1 / 10 := by field_simp

/-- The cutoff increases by less than one when the real centre is replaced
by its integer part. This gives the one-prime gap used in `lc:model-difference`.
-/
theorem paperShortBlockCutoff_floor_gap {x : ℝ} (hx : 4 ≤ x) :
    0 ≤ FractionalPrimes.paperShortBlockCutoff x -
        FractionalPrimes.paperShortBlockCutoff (Int.floor x) ∧
      FractionalPrimes.paperShortBlockCutoff x -
        FractionalPrimes.paperShortBlockCutoff (Int.floor x) < 1 := by
  let m : ℝ := (Int.floor x : ℤ)
  have hmle : m ≤ x := by
    dsimp [m]
    exact Int.floor_le x
  have hmlt : x < m + 1 := by
    dsimp [m]
    exact Int.lt_floor_add_one x
  have hmge : 3 ≤ m := by
    dsimp [m]
    have h := Int.le_floor.mpr (by linarith : (3 : ℝ) ≤ x)
    exact_mod_cast h
  have hmonolog : Real.log m ≤ Real.log x :=
    Real.log_le_log (by linarith : 0 < m) hmle
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith : 1 ≤ m)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith : 1 ≤ x)
  have hmonopow : (Real.log m) ^ (1 / 10 : ℝ) ≤
      (Real.log x) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow hlogm hmonolog (by norm_num)
  have hmono : FractionalPrimes.paperShortBlockCutoff m ≤
      FractionalPrimes.paperShortBlockCutoff x := by
    dsimp [FractionalPrimes.paperShortBlockCutoff]
    exact Real.exp_le_exp.mpr hmonopow
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc m x) :
      DifferentiableAt ℝ FractionalPrimes.paperShortBlockCutoff t := by
    have ht3 : 3 ≤ t := le_trans hmge ht.1
    exact (shortBlockCutoff_hasDerivAt (by linarith [ht3])).differentiableAt
  have hderivbound (t : ℝ) (ht : t ∈ Set.Icc m x) :
      ‖deriv FractionalPrimes.paperShortBlockCutoff t‖ ≤ 1 / 10 := by
    rw [Real.norm_eq_abs]
    exact shortBlockCutoff_deriv_abs_le_tenth (t := t) (le_trans hmge ht.1)
  have hmean : ‖FractionalPrimes.paperShortBlockCutoff x -
      FractionalPrimes.paperShortBlockCutoff m‖ ≤
      (1 / 10 : ℝ) * ‖x - m‖ := by
    exact (convex_Icc m x).norm_image_sub_le_of_norm_deriv_le
      hderiv hderivbound (x := m) (y := x)
      ⟨le_rfl, hmle⟩ ⟨hmle, le_rfl⟩
  have hdist : |x - m| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmle)]
    linarith
  have hgapnonneg : 0 ≤
      FractionalPrimes.paperShortBlockCutoff x -
        FractionalPrimes.paperShortBlockCutoff m := sub_nonneg.mpr hmono
  have hgapabs : |FractionalPrimes.paperShortBlockCutoff x -
      FractionalPrimes.paperShortBlockCutoff m| < 1 := by
    have hbound : |FractionalPrimes.paperShortBlockCutoff x -
        FractionalPrimes.paperShortBlockCutoff m| ≤
        (1 / 10 : ℝ) * |x - m| := by
      simpa [Real.norm_eq_abs] using hmean
    calc
      _ ≤ (1 / 10 : ℝ) * |x - m| := hbound
      _ < 1 := by nlinarith
  exact ⟨hgapnonneg,
    (abs_of_nonneg hgapnonneg ▸ hgapabs)⟩

/-- If two real cutoffs differ by less than one, at most one prime enters the
strict prime set when the cutoff increases. -/
theorem sievePrimesBelow_sdiff_card_le_one {a b : ℝ}
    (hgap : b - a < 1) :
    (FractionalPrimes.sievePrimesBelow b \
      FractionalPrimes.sievePrimesBelow a).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rw [Finset.mem_sdiff, FractionalPrimes.sievePrimesBelow_iff,
    FractionalPrimes.sievePrimesBelow_iff] at hp hq
  have hpa : a ≤ (p : ℝ) := by
    by_contra h
    exact hp.2 ⟨hp.1.1, lt_of_not_ge h⟩
  have hqa : a ≤ (q : ℝ) := by
    by_contra h
    exact hq.2 ⟨hq.1.1, lt_of_not_ge h⟩
  by_contra hpq
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
    have hstep : (p : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt hpq
    nlinarith [hp.1.2, hq.1.2]
  · have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
    have hstep : (q : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hqp
    nlinarith [hp.1.2, hq.1.2]

/-- The strict prime product changes by either no factor or exactly the sole
prime lying between two cutoffs less than one apart. -/
theorem sievePrimeProduct_change_under_gap {a b : ℝ}
    (hab : a ≤ b) (hgap : b - a < 1) :
    FractionalPrimes.sievePrimeProduct b =
        FractionalPrimes.sievePrimeProduct a ∨
      ∃ p : ℕ, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b ∧
        FractionalPrimes.sievePrimeProduct b =
          p * FractionalPrimes.sievePrimeProduct a := by
  let D := FractionalPrimes.sievePrimesBelow b \
    FractionalPrimes.sievePrimesBelow a
  have hcard : D.card ≤ 1 := by
    dsimp [D]
    exact sievePrimesBelow_sdiff_card_le_one hgap
  have hsubset : FractionalPrimes.sievePrimesBelow a ⊆
      FractionalPrimes.sievePrimesBelow b := by
    intro p hp
    rw [FractionalPrimes.sievePrimesBelow_iff] at hp ⊢
    exact ⟨hp.1, lt_of_lt_of_le hp.2 hab⟩
  have hdecomp :
      (∏ p ∈ D, p) * FractionalPrimes.sievePrimeProduct a =
        FractionalPrimes.sievePrimeProduct b := by
    dsimp [D, FractionalPrimes.sievePrimeProduct]
    simpa using (Finset.prod_sdiff
      (s₁ := FractionalPrimes.sievePrimesBelow a)
      (s₂ := FractionalPrimes.sievePrimesBelow b)
      (f := fun p : ℕ => p) hsubset)
  by_cases hD : D.Nonempty
  · obtain ⟨p, hpD⟩ := hD
    have hDsingleton : D = {p} := by
      ext q
      simp only [Finset.mem_singleton]
      constructor
      · intro hqD
        exact ((Finset.card_le_one.mp hcard) p hpD q hqD).symm
      · intro hqp
        subst q
        exact hpD
    have hpPrime : p.Prime := by
      have hp := (Finset.mem_sdiff.mp hpD).1
      rw [FractionalPrimes.sievePrimesBelow_iff] at hp
      exact hp.1
    have hpb : (p : ℝ) < b := by
      have hp := (Finset.mem_sdiff.mp hpD).1
      rw [FractionalPrimes.sievePrimesBelow_iff] at hp
      exact hp.2
    have hpa : a ≤ (p : ℝ) := by
      have hpnot := (Finset.mem_sdiff.mp hpD).2
      rw [FractionalPrimes.sievePrimesBelow_iff] at hpnot
      by_contra h
      exact hpnot ⟨hpPrime, lt_of_not_ge h⟩
    rw [hDsingleton, Finset.prod_singleton] at hdecomp
    right
    exact ⟨p, hpPrime, hpa, hpb, hdecomp.symm⟩
  · have hDempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    left
    simpa [hDempty] using hdecomp.symm

/-- For the short-block cutoff, replacing a real centre by its integer part
adds either no prime or exactly one prime to the strict product. -/
theorem paperShortBlockPrimeProduct_floor_change {x : ℝ} (hx : 4 ≤ x) :
    FractionalPrimes.sievePrimeProduct
        (FractionalPrimes.paperShortBlockCutoff x) =
        FractionalPrimes.sievePrimeProduct
          (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) ∨
      ∃ p : ℕ, p.Prime ∧
        FractionalPrimes.paperShortBlockCutoff (Int.floor x) ≤ (p : ℝ) ∧
        (p : ℝ) < FractionalPrimes.paperShortBlockCutoff x ∧
        FractionalPrimes.sievePrimeProduct
            (FractionalPrimes.paperShortBlockCutoff x) =
          p * FractionalPrimes.sievePrimeProduct
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) := by
  have hgap := paperShortBlockCutoff_floor_gap hx
  exact sievePrimeProduct_change_under_gap (sub_nonneg.mp hgap.1) hgap.2

private theorem sievePrimesBelow_transition_eq {a b : ℝ} {p : ℕ}
    (hp : p.Prime) (hpa : a ≤ (p : ℝ)) (hpb : (p : ℝ) < b)
    (hgap : b - a < 1) :
    FractionalPrimes.sievePrimesBelow a =
        FractionalPrimes.sievePrimesBelow (p : ℝ) ∧
      FractionalPrimes.sievePrimesBelow b =
        insert p (FractionalPrimes.sievePrimesBelow (p : ℝ)) := by
  let D := FractionalPrimes.sievePrimesBelow b \
    FractionalPrimes.sievePrimesBelow a
  have hcard : D.card ≤ 1 := by
    dsimp [D]
    exact sievePrimesBelow_sdiff_card_le_one hgap
  have hpD : p ∈ D := by
    change p ∈ FractionalPrimes.sievePrimesBelow b \
      FractionalPrimes.sievePrimesBelow a
    rw [Finset.mem_sdiff, FractionalPrimes.sievePrimesBelow_iff,
      FractionalPrimes.sievePrimesBelow_iff]
    exact ⟨⟨hp, hpb⟩, fun h => (not_lt_of_ge hpa) h.2⟩
  constructor
  · ext q
    rw [FractionalPrimes.sievePrimesBelow_iff,
      FractionalPrimes.sievePrimesBelow_iff]
    constructor
    · rintro ⟨hq, hqa⟩
      exact ⟨hq, lt_of_lt_of_le hqa hpa⟩
    · rintro ⟨hq, hqp⟩
      by_cases hqa : (q : ℝ) < a
      · exact ⟨hq, hqa⟩
      · have hqD : q ∈ D := by
          change q ∈ FractionalPrimes.sievePrimesBelow b \
            FractionalPrimes.sievePrimesBelow a
          rw [Finset.mem_sdiff, FractionalPrimes.sievePrimesBelow_iff,
            FractionalPrimes.sievePrimesBelow_iff]
          exact ⟨⟨hq, lt_trans hqp hpb⟩, fun h => hqa h.2⟩
        have hqp' : q = p := (Finset.card_le_one.mp hcard) q hqD p hpD
        subst q
        exact False.elim (lt_irrefl (p : ℝ) hqp)
  · ext q
    rw [Finset.mem_insert, FractionalPrimes.sievePrimesBelow_iff,
      FractionalPrimes.sievePrimesBelow_iff]
    constructor
    · rintro ⟨hq, hqb⟩
      by_cases hqp : (q : ℝ) < p
      · exact Or.inr ⟨hq, hqp⟩
      · by_cases heq : q = p
        · exact Or.inl heq
        · have hpq : (p : ℝ) < q := by
            exact lt_of_le_of_ne (le_of_not_gt hqp) (by
              intro h
              exact heq (by exact_mod_cast h.symm))
          have hqD : q ∈ D := by
            change q ∈ FractionalPrimes.sievePrimesBelow b \
              FractionalPrimes.sievePrimesBelow a
            rw [Finset.mem_sdiff, FractionalPrimes.sievePrimesBelow_iff,
              FractionalPrimes.sievePrimesBelow_iff]
            exact ⟨⟨hq, hqb⟩, fun h => (not_lt_of_ge (le_trans hpa hpq.le)) h.2⟩
          have hqp' : q = p := (Finset.card_le_one.mp hcard) q hqD p hpD
          exact False.elim (heq hqp')
    · rintro (hqp | ⟨hq, hqp⟩)
      · subst q
        exact ⟨hp, hpb⟩
      · exact ⟨hq, lt_trans hqp hpb⟩

private theorem sievePrimeProduct_transition_eq {a b : ℝ} {p : ℕ}
    (hp : p.Prime) (hpa : a ≤ (p : ℝ)) (hpb : (p : ℝ) < b)
    (hgap : b - a < 1) :
    FractionalPrimes.sievePrimeProduct a =
        FractionalPrimes.sievePrimeProduct (p : ℝ) ∧
      FractionalPrimes.sievePrimeProduct b =
        p * FractionalPrimes.sievePrimeProduct (p : ℝ) := by
  have hsets := sievePrimesBelow_transition_eq hp hpa hpb hgap
  constructor
  · unfold FractionalPrimes.sievePrimeProduct
    rw [hsets.1]
  · unfold FractionalPrimes.sievePrimeProduct
    rw [hsets.2]
    have hpbelow : p ∉ FractionalPrimes.sievePrimesBelow (p : ℝ) := by
      rw [FractionalPrimes.sievePrimesBelow_iff]
      exact fun h => (lt_irrefl (p : ℝ)) h.2
    rw [Finset.prod_insert hpbelow]

/-- At the unique crossing prime, the real-centred strict Cramér weight is
the inclusive endpoint model, while the integer-centred weight is the strict
model at that prime. The resulting pointwise error is exactly the one-prime
totient correction. -/
theorem paperShortBlockCramerWeight_change_le_of_crossing_prime
    {x : ℝ} (hx : 4 ≤ x) {p n : ℕ} (hp : p.Prime)
    (hpa : FractionalPrimes.paperShortBlockCutoff (Int.floor x) ≤ (p : ℝ))
    (hpb : (p : ℝ) < FractionalPrimes.paperShortBlockCutoff x) :
    |FractionalPrimes.paperCramerWeight
          (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
        FractionalPrimes.paperCramerWeight
          (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)| ≤
      FractionalPrimes.paperCramerDensity (p : ℝ) *
        ((if p ∣ n then (1 : ℝ) else 0) + 1 / ((p : ℝ) - 1)) := by
  have hgap := paperShortBlockCutoff_floor_gap hx
  have htrans := sievePrimeProduct_transition_eq hp hpa hpb hgap.2
  have holdProduct :
      FractionalPrimes.paperPrimeProduct
        (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) =
        FractionalPrimes.paperPrimeProduct (p : ℝ) := by
    simpa [FractionalPrimes.paperPrimeProduct] using htrans.1
  have hnewProduct :
      FractionalPrimes.paperPrimeProduct
        (FractionalPrimes.paperShortBlockCutoff x) =
        FractionalPrimes.paperInclusivePrimeProduct (p : ℝ) := by
    rw [FractionalPrimes.paperInclusivePrimeProduct_atPrime hp]
    simpa [FractionalPrimes.paperPrimeProduct,
      FractionalPrimes.paperInclusivePrimeProductAtPrime] using htrans.2
  have holdWeight :
      FractionalPrimes.paperCramerWeight
          (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ) =
        FractionalPrimes.paperCramerWeight (p : ℝ) (n : ℤ) := by
    simp [FractionalPrimes.paperCramerWeight,
      FractionalPrimes.paperCramerDensity, holdProduct]
  have hnewWeight :
      FractionalPrimes.paperCramerWeight
          (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) =
        FractionalPrimes.paperInclusiveCramerWeight (p : ℝ) (n : ℤ) := by
    simp [FractionalPrimes.paperCramerWeight,
      FractionalPrimes.paperCramerDensity,
      FractionalPrimes.paperInclusiveCramerWeight, hnewProduct]
  rw [hnewWeight, holdWeight]
  exact FractionalPrimes.paperInclusiveCramerWeightAtPrime_abs_sub_strict_le hp

/-- The one-prime pointwise correction sums over any integer interval to the
usual length-over-prime term plus the exact endpoint-count remainder. -/
theorem paperShortBlockCramerIntervalL1Error_of_crossing_prime
    {x : ℝ} {p a b : ℕ} (hx : 4 ≤ x) (hp : p.Prime)
    (hpa : FractionalPrimes.paperShortBlockCutoff (Int.floor x) ≤ (p : ℝ))
    (hpb : (p : ℝ) < FractionalPrimes.paperShortBlockCutoff x)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b,
      |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) ≤
      FractionalPrimes.paperCramerDensity (p : ℝ) *
        (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1) +
          ((((b - a) / p : ℕ) : ℝ) + 1)) := by
  have hpoint {n : ℕ} (hn : n ∈ Finset.Ioc a b) :
      |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)| ≤
        FractionalPrimes.paperCramerDensity (p : ℝ) *
          ((if p ∣ n then (1 : ℝ) else 0) + 1 / ((p : ℝ) - 1)) :=
    paperShortBlockCramerWeight_change_le_of_crossing_prime hx hp hpa hpb
  have hpSubPos : 0 < (p : ℝ) - 1 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hR : 0 ≤ FractionalPrimes.paperCramerDensity (p : ℝ) := by
    have h := (FractionalPrimes.paperCramerDensity_bounds
      (w := (p : ℝ)) (by exact_mod_cast hp.two_le)).1
    linarith
  calc
    _ ≤ ∑ n ∈ Finset.Ioc a b,
        FractionalPrimes.paperCramerDensity (p : ℝ) *
          ((if p ∣ n then (1 : ℝ) else 0) + 1 / ((p : ℝ) - 1)) :=
      Finset.sum_le_sum fun n hn => hpoint hn
    _ = FractionalPrimes.paperCramerDensity (p : ℝ) *
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
    _ ≤ FractionalPrimes.paperCramerDensity (p : ℝ) *
        (((((b - a) / p : ℕ) : ℝ) + 1) +
          (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1))) := by
      gcongr
      · exact_mod_cast (FractionalPrimes.card_multiples_Ioc_le_div_add_one
          hp.pos hab)
      · simp
    _ = _ := by ring

/-- Exact source case split for changing the real centre to its integer part:
either the two strict products (and hence the models) agree, or one crossing
prime gives the explicit interval-L1 correction. -/
theorem paperShortBlockCramerInterval_floor_change_cases
    {x : ℝ} {a b : ℕ} (hx : 4 ≤ x) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b,
      |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) = 0 ∨
      ∃ p : ℕ, p.Prime ∧
        FractionalPrimes.paperShortBlockCutoff (Int.floor x) ≤ (p : ℝ) ∧
        (p : ℝ) < FractionalPrimes.paperShortBlockCutoff x ∧
        (∑ n ∈ Finset.Ioc a b,
          |FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
              FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) ≤
          FractionalPrimes.paperCramerDensity (p : ℝ) *
            (((b - a : ℕ) : ℝ) / ((p : ℝ) - 1) +
              ((((b - a) / p : ℕ) : ℝ) + 1)) := by
  rcases paperShortBlockPrimeProduct_floor_change hx with hsame | ⟨p, hp, hpa, hpb, _⟩
  · left
    simp [FractionalPrimes.paperCramerWeight,
      FractionalPrimes.paperCramerDensity,
      FractionalPrimes.paperPrimeProduct, hsame]
  · exact Or.inr ⟨p, hp, hpa, hpb,
      paperShortBlockCramerIntervalL1Error_of_crossing_prime hx hp hpa hpb hab⟩

private theorem rpow_mul_exp_neg_le_sharp_max {a d t : ℝ}
    (ha : 0 < a) (hd : 0 < d) (ht : 0 ≤ t) :
    t ^ d * Real.exp (-(a * t)) ≤ (d / (a * Real.exp 1)) ^ d := by
  by_cases ht0 : t = 0
  · subst t
    simp [Real.zero_rpow hd.ne']
    positivity
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let u : ℝ := a * t / d
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos (mul_pos ha htpos) hd
  have hlog := Real.log_le_sub_one_of_pos hu
  have hcore : u ^ d * Real.exp (-(d * u)) ≤ Real.exp (-d) := by
    rw [Real.rpow_def_of_pos hu, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      Real.log u * d - d * u ≤ (u - 1) * d - d * u := by
        exact sub_le_sub_right (mul_le_mul_of_nonneg_right hlog hd.le) _
      _ = -d := by ring
  have htEq : t = (d / a) * u := by
    dsimp [u]
    field_simp [ha.ne', hd.ne']
  have hscale : a * t = d * u := by
    dsimp [u]
    field_simp [hd.ne']
  have hscale' : a * ((d / a) * u) = d * u := by
    rw [← htEq]
    exact hscale
  have hexppow : Real.exp (-1) ^ d = Real.exp (-d) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos (-1)), Real.log_exp]
    congr 1
    ring
  have hconstant : d / (a * Real.exp 1) = (d / a) * Real.exp (-1) := by
    rw [Real.exp_neg]
    field_simp [ha.ne', ne_of_gt (Real.exp_pos 1)]
  calc
    t ^ d * Real.exp (-(a * t)) =
        (d / a) ^ d * (u ^ d * Real.exp (-(d * u))) := by
      rw [htEq, Real.mul_rpow (by positivity) (by positivity), hscale']
      ring
    _ ≤ (d / a) ^ d * Real.exp (-d) :=
      mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg (by positivity) _)
    _ = (d / (a * Real.exp 1)) ^ d := by
      rw [hconstant, Real.mul_rpow (by positivity) (by positivity), hexppow]

/-- Explicit two-term logarithmic absorption used after the one-prime
interval estimate in `lc:model-difference`. The constants are the source's
sharp maxima with the stated outer slack factors 8 and 4. -/
theorem paperShortBlockLogDecay_bound {A t : ℝ}
    (hA : 0 < A) (ht : 0 ≤ t) :
    6 * t ^ (A + 2 / 5 : ℝ) *
        Real.exp (-(t ^ (1 / 10 : ℝ))) +
      t ^ (A + 2 / 5 : ℝ) * Real.exp (-((5 / 8 : ℝ) * t)) ≤
    8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
      4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5) := by
  let B : ℝ := A + 2 / 5
  have hB : 0 < B := by dsimp [B]; linarith
  let s : ℝ := t ^ (1 / 10 : ℝ)
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Real.rpow_nonneg ht _
  have hpow : s ^ (10 * B) = t ^ B := by
    dsimp [s]
    rw [← Real.rpow_mul ht (1 / 10 : ℝ) (10 * B)]
    congr 1
    ring
  have hfirst := rpow_mul_exp_neg_le_sharp_max
    (a := (1 : ℝ)) (d := 10 * B) (t := s) (by norm_num) (by positivity) hs
  have hsecond := rpow_mul_exp_neg_le_sharp_max
    (a := (5 / 8 : ℝ)) (d := B) (t := t) (by norm_num) hB ht
  have hfirst' : t ^ B * Real.exp (-s) ≤ (10 * B / Real.exp 1) ^ (10 * B) := by
    calc
      t ^ B * Real.exp (-s) = s ^ (10 * B) * Real.exp (-(1 * s)) := by
        rw [← hpow]
        congr 1 <;> ring_nf
      _ ≤ (10 * B / (1 * Real.exp 1)) ^ (10 * B) := hfirst
      _ = (10 * B / Real.exp 1) ^ (10 * B) := by congr 1 <;> ring
  have hsecond' :
      t ^ B * Real.exp (-((5 / 8 : ℝ) * t)) ≤
        (8 * B / (5 * Real.exp 1)) ^ B := by
    calc
      _ ≤ (B / ((5 / 8 : ℝ) * Real.exp 1)) ^ B := hsecond
      _ = (8 * B / (5 * Real.exp 1)) ^ B := by congr 1 <;> ring
  have hM1 : 0 ≤ (10 * B / Real.exp 1) ^ (10 * B) := by positivity
  have hM2 : 0 ≤ (8 * B / (5 * Real.exp 1)) ^ B := by positivity
  have hfirstWeighted :
      6 * t ^ B * Real.exp (-s) ≤ 6 * (10 * B / Real.exp 1) ^ (10 * B) := by
    calc
      6 * t ^ B * Real.exp (-s) = 6 * (t ^ B * Real.exp (-s)) := by ring
      _ ≤ 6 * (10 * B / Real.exp 1) ^ (10 * B) :=
        mul_le_mul_of_nonneg_left hfirst' (by norm_num)
  calc
    _ ≤ 6 * (10 * B / Real.exp 1) ^ (10 * B) +
        (8 * B / (5 * Real.exp 1)) ^ B := by
      exact add_le_add hfirstWeighted hsecond'
    _ ≤ 8 * (10 * B / Real.exp 1) ^ (10 * B) +
        4 * (8 * B / (5 * Real.exp 1)) ^ B := by nlinarith
    _ = _ := by dsimp [B]

/-- Exact `lc:model-difference` Cramér-model estimate on the integer samples
of the real interval `(x,x+h]`. Its constant is the blueprint's stated
`K_A = exp(13) 2^A [8(10b/e)^(10b)+4(8b/(5e))^b]`, with `b=A+2/5`. -/
theorem paperCramerChangeCentre_floor_bound {A x h : ℝ}
    (hA : 0 < A) (hx : 4 ≤ x) (hh : x ^ (5 / 8 : ℝ) ≤ h) :
    (∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor (x + h)),
      |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) ≤
      Real.exp 13 * 2 ^ A *
        (8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
          4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5)) *
        h * (Real.log x) ^ (-A : ℝ) := by
  let a : ℕ := Nat.floor x
  let b : ℕ := Nat.floor (x + h)
  let L : ℕ := b - a
  let m : ℝ := (a : ℝ)
  let t : ℝ := Real.log m
  let B : ℝ := A + 2 / 5
  let D : ℝ :=
    8 * (10 * B / Real.exp 1) ^ (10 * B) +
      4 * (8 * B / (5 * Real.exp 1)) ^ B
  have hxpos : 0 < x := by linarith
  have hHpos : 0 < h := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hh
  have hHge1 : 1 ≤ h := by
    have hxge1 : 1 ≤ x := by linarith
    have hxpow : 1 ≤ x ^ (5 / 8 : ℝ) :=
      Real.one_le_rpow hxge1 (by norm_num)
    exact hxpow.trans hh
  have ha4 : 4 ≤ a := by
    dsimp [a]
    exact Nat.le_floor hx
  have hm4 : (4 : ℝ) ≤ m := by
    dsimp [m]
    exact_mod_cast ha4
  have hmpos : 0 < m := by linarith
  have hfloorCast : (Int.floor x : ℝ) = m := by
    dsimp [m, a]
    exact_mod_cast (Int.natCast_floor_eq_floor hxpos.le).symm
  have hmle : m ≤ x := by
    dsimp [m, a]
    exact Nat.floor_le hxpos.le
  have hxFloor : x < m + 1 := by
    dsimp [m, a]
    exact Nat.lt_floor_add_one x
  have hMge3 : 3 ≤ m := by linarith
  have hMge2 : 2 ≤ m := by linarith
  have hmgt1 : 1 < m := by linarith
  have htpos : 0 < t := by
    dsimp [t]
    exact Real.log_pos hmgt1
  have ht : 0 ≤ t := htpos.le
  have htge1 : 1 ≤ t := by
    apply (Real.le_log_iff_exp_le hmpos).2
    exact (Real.exp_one_lt_three.le).trans (by linarith : (3 : ℝ) ≤ m)
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith : 1 < x)
  have hlog2le : Real.log 2 ≤ t := by
    dsimp [t]
    exact Real.log_le_log (by norm_num) hMge2
  have hxlt2m : x < 2 * m := by nlinarith [hxFloor, hm4]
  have hlogxle : Real.log x ≤ 2 * t := by
    have hlog := Real.log_le_log hxpos hxlt2m.le
    have hlogmul : Real.log (2 * m) = Real.log 2 + Real.log m := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hmpos)]
    calc
      Real.log x ≤ Real.log (2 * m) := hlog
      _ = Real.log 2 + t := by rw [hlogmul]
      _ ≤ t + t := add_le_add hlog2le le_rfl
      _ = 2 * t := by ring
  have hlogPow : (Real.log x) ^ A ≤ (2 : ℝ) ^ A * t ^ A := by
    calc
      (Real.log x) ^ A ≤ (2 * t) ^ A :=
        Real.rpow_le_rpow hlogxpos.le hlogxle hA.le
      _ = (2 : ℝ) ^ A * t ^ A := by
        rw [Real.mul_rpow (by norm_num) ht]
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hpowSum : t ^ A * t ^ (2 / 5 : ℝ) = t ^ B := by
    calc
      t ^ A * t ^ (2 / 5 : ℝ) = t ^ (A + 2 / 5) :=
        (Real.rpow_add htpos A (2 / 5 : ℝ)).symm
      _ = t ^ B := by dsimp [B]
  have hmPow : m ^ (5 / 8 : ℝ) = Real.exp ((5 / 8 : ℝ) * t) := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    dsimp [t]
    ring
  have hMpow_le_xpow : m ^ (5 / 8 : ℝ) ≤ x ^ (5 / 8 : ℝ) :=
    Real.rpow_le_rpow hmpos.le hmle (by norm_num)
  have hMexp_le_h : Real.exp ((5 / 8 : ℝ) * t) ≤ h := by
    calc
      Real.exp ((5 / 8 : ℝ) * t) = m ^ (5 / 8 : ℝ) := hmPow.symm
      _ ≤ x ^ (5 / 8 : ℝ) := hMpow_le_xpow
      _ ≤ h := hh
  have hrecipH : 1 / h ≤ Real.exp (-((5 / 8 : ℝ) * t)) := by
    have hinv := one_div_le_one_div_of_le (Real.exp_pos ((5 / 8 : ℝ) * t)) hMexp_le_h
    simpa [Real.exp_neg] using hinv
  have hQge2 : 2 ≤ Real.exp (t ^ (1 / 10 : ℝ)) := by
    have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h
      exact h
    have hsone : 1 ≤ t ^ (1 / 10 : ℝ) :=
      Real.one_le_rpow htge1 (by norm_num)
    exact htwoExp.trans (Real.exp_le_exp.mpr hsone)
  have hRlower :
      1 ≤ FractionalPrimes.paperCramerDensity
        (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) := by
    rw [hfloorCast]
    simpa [FractionalPrimes.paperShortBlockCutoff, t] using
      (FractionalPrimes.paperCramerDensity_lc_product hQge2).1
  have hRupper :
      FractionalPrimes.paperCramerDensity
          (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) ≤
        Real.exp 13 * t ^ (2 / 5 : ℝ) := by
    rw [hfloorCast]
    simpa [FractionalPrimes.paperShortBlockCutoff, t] using
      FractionalPrimes.paperCramerDensity_at_cutoff_scale hMge3
  have hab : a ≤ b := by
    dsimp [a, b]
    apply Nat.floor_mono
    linarith
  have hLcast : (L : ℝ) = (b : ℝ) - (a : ℝ) := by
    dsimp [L]
    exact Nat.cast_sub hab
  have hfloorRight : (b : ℝ) ≤ x + h := by
    dsimp [b]
    exact Nat.floor_le (by linarith)
  have hxFloorLeft : x < (a : ℝ) + 1 := by
    dsimp [a]
    exact Nat.lt_floor_add_one x
  have hLle : (L : ℝ) ≤ 2 * h := by
    rw [hLcast]
    nlinarith [hfloorRight, hxFloorLeft, hHge1]
  have hfloorGap := paperShortBlockCutoff_floor_gap hx
  have hCases := paperShortBlockCramerInterval_floor_change_cases
    (x := x) (a := a) (b := b) hx hab
  rcases hCases with hzero | ⟨p, hp, hpa, hpb, hL1⟩
  · rw [hzero]
    positivity
  · have htrans := sievePrimeProduct_transition_eq hp hpa hpb hfloorGap.2
    have hDensityEq :
        FractionalPrimes.paperCramerDensity (p : ℝ) =
          FractionalPrimes.paperCramerDensity
            (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) := by
      simp [FractionalPrimes.paperCramerDensity,
        FractionalPrimes.paperPrimeProduct, htrans.1]
    have hRlowerP :
        1 ≤ FractionalPrimes.paperCramerDensity (p : ℝ) := by
      rw [hDensityEq]
      exact hRlower
    have hRupperP :
        FractionalPrimes.paperCramerDensity (p : ℝ) ≤ Real.exp 13 * t ^ (2 / 5 : ℝ) := by
      rw [hDensityEq]
      exact hRupper
    have hQLower :
        Real.exp (t ^ (1 / 10 : ℝ)) ≤ (p : ℝ) := by
      have hpa' : FractionalPrimes.paperShortBlockCutoff m ≤ (p : ℝ) := by
        simpa [hfloorCast] using hpa
      simpa [FractionalPrimes.paperShortBlockCutoff, t] using hpa'
    have hrecipP : (p : ℝ)⁻¹ ≤ Real.exp (-(t ^ (1 / 10 : ℝ))) := by
      have hinv := one_div_le_one_div_of_le
        (Real.exp_pos (t ^ (1 / 10 : ℝ))) hQLower
      simpa [Real.exp_neg] using hinv
    have hdivCast :
        ((L / p : ℕ) : ℝ) ≤ (L : ℝ) / (p : ℝ) :=
      Nat.cast_div_le (α := ℝ) (m := L) (n := p)
    have hpR2 : (2 : ℝ) ≤ p := by
      have hQ' : 2 ≤ FractionalPrimes.paperShortBlockCutoff (Int.floor x) := by
        rw [hfloorCast]
        simpa [FractionalPrimes.paperShortBlockCutoff, t] using hQge2
      exact le_trans hQ' hpa
    have hpSubPos : 0 < (p : ℝ) - 1 := by linarith
    have hpPos : 0 < (p : ℝ) := by linarith
    have hrecipPrime : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpSubPos hpPos).2
      nlinarith
    have hLdiv : (L : ℝ) / (p : ℝ) ≤ (2 * h) / (p : ℝ) :=
      div_le_div_of_nonneg_right hLle (by positivity)
    have hterm1 : (L : ℝ) / ((p : ℝ) - 1) ≤ 2 * (L : ℝ) / (p : ℝ) := by
      calc
        (L : ℝ) / ((p : ℝ) - 1) = (L : ℝ) * (1 / ((p : ℝ) - 1)) := by ring
        _ ≤ (L : ℝ) * (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hrecipPrime (by positivity)
        _ = 2 * (L : ℝ) / (p : ℝ) := by ring
    have hdivPlus : ((L / p : ℕ) : ℝ) + 1 ≤
        (L : ℝ) / (p : ℝ) + 1 := by
      have h := add_le_add_right hdivCast 1
      simpa [add_comm] using h
    have hLdiv3Plus : 3 * ((L : ℝ) / (p : ℝ)) + 1 ≤
        3 * ((2 * h) / (p : ℝ)) + 1 := by
      have hdiv3 := mul_le_mul_of_nonneg_left hLdiv
        (by norm_num : (0 : ℝ) ≤ 3)
      have h := add_le_add_right hdiv3 1
      simpa [add_comm] using h
    have hbracket :
        (L : ℝ) / ((p : ℝ) - 1) +
            (((L / p : ℕ) : ℝ) + 1) ≤ 6 * h / (p : ℝ) + 1 := by
      calc
        _ ≤ 2 * (L : ℝ) / (p : ℝ) + ((L : ℝ) / (p : ℝ) + 1) := by
          exact add_le_add hterm1 hdivPlus
        _ = 3 * ((L : ℝ) / (p : ℝ)) + 1 := by ring
        _ ≤ 3 * ((2 * h) / (p : ℝ)) + 1 := hLdiv3Plus
        _ = 6 * h / (p : ℝ) + 1 := by ring
    have hbracketDecay :
        6 * h / (p : ℝ) + 1 ≤
          6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 := by
      calc
        6 * h / (p : ℝ) + 1 = 6 * h * (1 / (p : ℝ)) + 1 := by ring
        _ ≤ 6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 := by
          have hrecipP' : 1 / (p : ℝ) ≤ Real.exp (-(t ^ (1 / 10 : ℝ))) := by
            simpa [one_div] using hrecipP
          have hweighted : 6 * h * (1 / (p : ℝ)) ≤
              6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) :=
            mul_le_mul_of_nonneg_left hrecipP' (by positivity : 0 ≤ 6 * h)
          have h := add_le_add_right hweighted 1
          simpa [add_comm] using h
    have hRnonnegP : 0 ≤ FractionalPrimes.paperCramerDensity (p : ℝ) :=
      le_trans (by norm_num) hRlowerP
    have hErrorUpper :
        (∑ n ∈ Finset.Ioc a b,
          |FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
              FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) ≤
          Real.exp 13 * t ^ (2 / 5 : ℝ) *
            (6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1) := by
      calc
        _ ≤ FractionalPrimes.paperCramerDensity (p : ℝ) *
            ((L : ℝ) / ((p : ℝ) - 1) + (((L / p : ℕ) : ℝ) + 1)) := hL1
        _ ≤ FractionalPrimes.paperCramerDensity (p : ℝ) *
            (6 * h / (p : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hbracket hRnonnegP
        _ ≤ FractionalPrimes.paperCramerDensity (p : ℝ) *
            (6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1) :=
          mul_le_mul_of_nonneg_left hbracketDecay hRnonnegP
        _ ≤ Real.exp 13 * t ^ (2 / 5 : ℝ) *
            (6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1) := by
          exact mul_le_mul_of_nonneg_right hRupperP (by positivity)
    have htail : t ^ B / h ≤ t ^ B * Real.exp (-((5 / 8 : ℝ) * t)) := by
      have hpownonneg : 0 ≤ t ^ B := Real.rpow_nonneg ht B
      calc
        t ^ B / h = t ^ B * (1 / h) := by ring
        _ ≤ t ^ B * Real.exp (-((5 / 8 : ℝ) * t)) :=
          mul_le_mul_of_nonneg_left hrecipH hpownonneg
    have hdecay :
        t ^ B * (6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h) ≤ D := by
      calc
        t ^ B * (6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h) =
            6 * t ^ B * Real.exp (-(t ^ (1 / 10 : ℝ))) + t ^ B / h := by ring
        _ ≤ 6 * t ^ B * Real.exp (-(t ^ (1 / 10 : ℝ))) +
            t ^ B * Real.exp (-((5 / 8 : ℝ) * t)) := by
          have hadd := add_le_add_left htail
            (6 * t ^ B * Real.exp (-(t ^ (1 / 10 : ℝ))))
          simpa [add_comm] using hadd
        _ ≤ D := by
          simpa [B, D] using paperShortBlockLogDecay_bound hA ht
    have hFpos : 0 < (Real.log x) ^ A / h :=
      div_pos (Real.rpow_pos_of_pos hlogxpos A) hHpos
    have hscaled :
        (Real.exp 13 * t ^ (2 / 5 : ℝ) *
          (6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1)) *
            ((Real.log x) ^ A / h) ≤ Real.exp 13 * 2 ^ A * D := by
      have hYnonneg :
          0 ≤ 6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h := by positivity
      have hcoef :
          (Real.log x) ^ A * t ^ (2 / 5 : ℝ) ≤
            (2 ^ A * t ^ A) * t ^ (2 / 5 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hlogPow (Real.rpow_nonneg ht _)
      calc
        _ = Real.exp 13 * ((Real.log x) ^ A * t ^ (2 / 5 : ℝ)) *
              (6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h) := by
          field_simp [ne_of_gt hHpos]
        _ ≤ Real.exp 13 * ((2 ^ A * t ^ A) * t ^ (2 / 5 : ℝ)) *
              (6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h) := by
          apply mul_le_mul_of_nonneg_right _ hYnonneg
          exact mul_le_mul_of_nonneg_left hcoef (Real.exp_pos 13).le
        _ = Real.exp 13 * 2 ^ A *
              (t ^ B *
                (6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h)) := by
          calc
            _ = Real.exp 13 * 2 ^ A *
                ((t ^ A * t ^ (2 / 5 : ℝ)) *
                  (6 * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1 / h)) := by ring
            _ = _ := by rw [hpowSum]
        _ ≤ Real.exp 13 * 2 ^ A * D :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)
    have htargetFactor :
        (Real.exp 13 * 2 ^ A * D * h * (Real.log x) ^ (-A : ℝ)) *
          ((Real.log x) ^ A / h) = Real.exp 13 * 2 ^ A * D := by
      have hpowCancel : (Real.log x) ^ (-A : ℝ) * (Real.log x) ^ A = 1 := by
        rw [← Real.rpow_add hlogxpos (-A : ℝ) A]
        simp
      field_simp [ne_of_gt hHpos]
      calc
        D * (Real.log x) ^ (-A : ℝ) * (Real.log x) ^ A =
            D * ((Real.log x) ^ (-A : ℝ) * (Real.log x) ^ A) := by ring
        _ = D := by rw [hpowCancel]; ring
    have hErrorScaled :
        (∑ n ∈ Finset.Ioc a b,
          |FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
              FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) *
            ((Real.log x) ^ A / h) ≤ Real.exp 13 * 2 ^ A * D := by
      calc
        _ ≤ (Real.exp 13 * t ^ (2 / 5 : ℝ) *
            (6 * h * Real.exp (-(t ^ (1 / 10 : ℝ))) + 1)) *
              ((Real.log x) ^ A / h) :=
          mul_le_mul_of_nonneg_right hErrorUpper (le_of_lt hFpos)
        _ ≤ Real.exp 13 * 2 ^ A * D := hscaled
    have hErrorFinal :
        (∑ n ∈ Finset.Ioc a b,
          |FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff x) (n : ℤ) -
              FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff (Int.floor x)) (n : ℤ)|) ≤
          Real.exp 13 * 2 ^ A * D * h * (Real.log x) ^ (-A : ℝ) := by
      apply (mul_le_mul_iff_of_pos_right hFpos).mp
      calc
        _ ≤ Real.exp 13 * 2 ^ A * D := hErrorScaled
        _ = (Real.exp 13 * 2 ^ A * D * h * (Real.log x) ^ (-A : ℝ)) *
              ((Real.log x) ^ A / h) := htargetFactor.symm
    simpa [D] using hErrorFinal

/-- The integers in `(x,x+h]` are exactly the integer half-open interval
between the two floor endpoints. -/
theorem realIntegerInterval_eq_floor_Ioc (x h : ℝ) :
    FractionalPrimes.realIntegerInterval x h =
      Finset.Ioc (Int.floor x) (Int.floor (x + h)) := by
  ext n
  simp [FractionalPrimes.realIntegerInterval]

/-- Rounding both endpoints of a real interval changes its length by
strictly less than one. -/
theorem floorEndpointLength_error_abs_lt_one (x h : ℝ) :
    |((Int.floor (x + h) - Int.floor x : ℤ) : ℝ) - h| < 1 := by
  have hrightLo : (Int.floor (x + h) : ℝ) ≤ x + h := Int.floor_le (x + h)
  have hrightHi : x + h < (Int.floor (x + h) : ℝ) + 1 :=
    Int.lt_floor_add_one (x + h)
  have hleftLo : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hleftHi : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  have hcast : ((Int.floor (x + h) - Int.floor x : ℤ) : ℝ) - h =
      ((Int.floor (x + h) : ℝ) - (x + h)) -
        ((Int.floor x : ℝ) - x) := by
    push_cast
    ring
  rw [hcast]
  have hrightLower : -1 < (Int.floor (x + h) : ℝ) - (x + h) := by
    linarith
  have hleftLower : -1 < (Int.floor x : ℝ) - x := by
    linarith
  have hrightUpper : (Int.floor (x + h) : ℝ) - (x + h) ≤ 0 := by
    linarith
  have hleftUpper : (Int.floor x : ℝ) - x ≤ 0 := by
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- Cardinality version matching the short-interval notation: the number of
integer samples differs from `h` by less than one. -/
theorem realIntegerInterval_card_sub_length_abs_lt_one
    (x h : ℝ) (hh : 0 < h) :
    |((FractionalPrimes.realIntegerInterval x h).card : ℝ) - h| < 1 := by
  have hcard :
      ((FractionalPrimes.realIntegerInterval x h).card : ℤ) =
        Int.floor (x + h) - Int.floor x :=
    FractionalPrimes.realIntegerInterval_card x h hh
  have hcast :
      ((FractionalPrimes.realIntegerInterval x h).card : ℝ) =
        ((Int.floor (x + h) - Int.floor x : ℤ) : ℝ) := by
    exact_mod_cast hcard
  rw [hcast]
  exact floorEndpointLength_error_abs_lt_one x h

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.realIntegerInterval_eq_floor_Ioc
#print axioms FractionalPrimes.Literature.Polynomial.paperShortBlockCutoff_floor_gap
#print axioms FractionalPrimes.Literature.Polynomial.sievePrimesBelow_sdiff_card_le_one
#print axioms FractionalPrimes.Literature.Polynomial.sievePrimeProduct_change_under_gap
#print axioms FractionalPrimes.Literature.Polynomial.paperShortBlockPrimeProduct_floor_change
#print axioms FractionalPrimes.Literature.Polynomial.paperShortBlockCramerWeight_change_le_of_crossing_prime
#print axioms FractionalPrimes.Literature.Polynomial.paperShortBlockCramerIntervalL1Error_of_crossing_prime
#print axioms FractionalPrimes.Literature.Polynomial.paperShortBlockCramerInterval_floor_change_cases
#print axioms FractionalPrimes.Literature.Polynomial.paperShortBlockLogDecay_bound
#print axioms FractionalPrimes.Literature.Polynomial.paperCramerChangeCentre_floor_bound
#print axioms FractionalPrimes.Literature.Polynomial.floorEndpointLength_error_abs_lt_one
#print axioms FractionalPrimes.Literature.Polynomial.realIntegerInterval_card_sub_length_abs_lt_one

end
