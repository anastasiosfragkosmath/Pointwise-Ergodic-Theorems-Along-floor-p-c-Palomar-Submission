module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Finset.Card
public import FractionalPrimes.Literature.Uniformity.DivisorSummatoryBound

/-!
# Elementary divisor tools for `ltw:small-divisors`

The blueprint's small-divisor domination uses the submultiplicativity
of the number of divisors. We isolate the exact arithmetic injection
before formalizing the finite prime-factor grouping.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

/-- If `d ∣ a*b`, the part of `d` left after removing its gcd with
`a` divides `b`. -/
theorem divisorQuotientGcd_dvd_right {d a b : ℕ} (hd : d ∣ a * b)
    (hdpos : 0 < d) : d / Nat.gcd d a ∣ b := by
  let g := Nat.gcd d a
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left a hdpos
  have hda : g ∣ d := Nat.gcd_dvd_left d a
  have haa : g ∣ a := Nat.gcd_dvd_right d a
  have hcop : Nat.Coprime (d / g) (a / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hEqA : (a / g) * g = a := Nat.div_mul_cancel haa
  have hraw : (d / g) * g ∣ ((a / g) * b) * g := by
    calc
      (d / g) * g = d := Nat.div_mul_cancel hda
      _ ∣ a * b := hd
      _ = ((a / g) * b) * g := by
        calc
          a * b = ((a / g) * g) * b := by rw [hEqA]
          _ = ((a / g) * b) * g := by ac_rfl
  have hquot : d / g ∣ (a / g) * b :=
    (mul_dvd_mul_iff_right hgpos.ne').mp hraw
  exact hcop.dvd_of_dvd_mul_left hquot

/-- The divisor-count function is submultiplicative, with no
coprimality hypothesis. -/
theorem cardDivisors_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  let φ : ℕ → ℕ × ℕ := fun d => (Nat.gcd d a, d / Nat.gcd d a)
  have hmap : Set.MapsTo φ ((a * b).divisors : Set ℕ)
      ((a.divisors.product b.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro d hd
    have hmem := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d a, ha⟩
    · exact Nat.mem_divisors.mpr
        ⟨divisorQuotientGcd_dvd_right hmem.1 hdpos, hb⟩
  have hinj : Set.InjOn φ ((a * b).divisors : Set ℕ) := by
    intro d _ e _ h
    have hfst : Nat.gcd d a = Nat.gcd e a := congrArg Prod.fst h
    have hsnd : d / Nat.gcd d a = e / Nat.gcd e a := congrArg Prod.snd h
    calc
      d = Nat.gcd d a * (d / Nat.gcd d a) := by
        simpa [mul_comm] using (Nat.div_mul_cancel (Nat.gcd_dvd_left d a)).symm
      _ = Nat.gcd e a * (e / Nat.gcd e a) :=
        congrArg₂ (· * ·) hfst hsnd
      _ = e := by
        simpa [mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_left e a)
  have hcard := Finset.card_le_card_of_injOn φ hmap hinj
  calc
    (a * b).divisors.card ≤ (a.divisors.product b.divisors).card := hcard
    _ = a.divisors.card * b.divisors.card := Finset.card_product _ _

/-- The blueprint notation `τ=d₂` agrees with Mathlib's finite
divisor count at every natural input, including zero. -/
theorem divisorCoefficient_two_eq_cardDivisors (n : ℕ) :
    FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n =
      n.divisors.card := by
  change (ArithmeticFunction.zeta ^ 2) n = n.divisors.card
  calc
    (ArithmeticFunction.zeta ^ 2) n =
        (ArithmeticFunction.zeta * ArithmeticFunction.pow 0) n := by
          rw [pow_two, ArithmeticFunction.pow_zero_eq_zeta]
    _ = (ArithmeticFunction.sigma 0) n := by
      rw [ArithmeticFunction.zeta_mul_pow_eq_sigma]
    _ = n.divisors.card := ArithmeticFunction.sigma_zero_apply n

/-- The exact `τ(uv) ≤ τ(u)τ(v)` form used by the blueprint. -/
theorem divisorCoefficient_two_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 (a * b) ≤
      FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 a *
        FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 b := by
  simpa only [divisorCoefficient_two_eq_cardDivisors] using
    cardDivisors_mul_le a b (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)

/-- The submultiplicative bound iterated over a finite list of
positive factors. -/
theorem cardDivisors_list_prod_le (xs : List ℕ)
    (hpos : ∀ x ∈ xs, 0 < x) :
    xs.prod.divisors.card ≤ (xs.map fun x => x.divisors.card).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 < x := hpos x (by simp)
      have hxs : ∀ y ∈ xs, 0 < y := by
        intro y hy
        exact hpos y (by simp [hy])
      have hxsp : 0 < xs.prod := List.prod_pos hxs
      simp only [List.prod_cons, List.map_cons]
      calc
        (x * xs.prod).divisors.card ≤
            x.divisors.card * xs.prod.divisors.card :=
          cardDivisors_mul_le x xs.prod (Nat.ne_of_gt hx) (Nat.ne_of_gt hxsp)
        _ ≤ x.divisors.card * (xs.map fun y => y.divisors.card).prod :=
          Nat.mul_le_mul_left _ (ih hxs)

/-- A finite list whose entries are all at least `T` has product at
least `T` raised to its length. This is the counting step behind
both large-prime and closed-block bounds in `ltw:small-divisors`. -/
theorem threshold_pow_length_le_prod (xs : List ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hx : ∀ x ∈ xs, T ≤ (x : ℝ)) :
    T ^ xs.length ≤ (xs.prod : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hhead : T ≤ (x : ℝ) := hx x (by simp)
      have htail : ∀ y ∈ xs, T ≤ (y : ℝ) := by
        intro y hy
        exact hx y (by simp [hy])
      have hpow : 0 ≤ T ^ xs.length := pow_nonneg hT _
      have hprod : 0 ≤ (xs.prod : ℝ) := Nat.cast_nonneg _
      simpa [List.prod_cons, pow_succ, mul_comm] using
        (mul_le_mul hhead (ih htail) hpow (by positivity : 0 ≤ (x : ℝ)))

/-- If the whole product is bounded by `T^k` and every factor is
at least `T > 1`, there are at most `k` factors. -/
theorem threshold_factor_count_le (xs : List ℕ) (T : ℝ) (k : ℕ)
    (hT : 1 < T) (hx : ∀ x ∈ xs, T ≤ (x : ℝ))
    (hbound : (xs.prod : ℝ) ≤ T ^ k) : xs.length ≤ k := by
  apply (pow_le_pow_iff_right₀ hT).mp
  exact (threshold_pow_length_le_prod xs T (le_of_lt (by positivity)) hx).trans hbound

/-- The large-factor counting step of the blueprint, independent of
primality: among factors of a positive product at most `(T²)^k`,
there are at most `k` factors larger than `T²`. -/
theorem largeFactors_card_le (xs : List ℕ) (hprod : 0 < xs.prod)
    (T : ℝ) (hT : 1 < T) (k : ℕ)
    (hbound : (xs.prod : ℝ) ≤ (T ^ 2) ^ k) :
    (xs.filter (fun x : ℕ => decide (T ^ 2 < (x : ℝ)))).length ≤ k := by
  let ys : List ℕ := xs.filter (fun x : ℕ => decide (T ^ 2 < (x : ℝ)))
  have hsub : List.Sublist ys xs := by
    dsimp [ys]
    exact List.filter_sublist
  have hdiv : ys.prod ∣ xs.prod := hsub.prod_dvd_prod
  have hle : ys.prod ≤ xs.prod := Nat.le_of_dvd hprod hdiv
  apply threshold_factor_count_le ys (T ^ 2) k (by nlinarith) ?_
    ((Nat.cast_le.mpr hle).trans hbound)
  intro x hx
  have hlarge : T ^ 2 < (x : ℝ) := by
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  exact le_of_lt hlarge

/-- Greedy packing of factors at most `T`: a completed block is
emitted as soon as the running product reaches `T`. The first
coordinate is the final incomplete block. -/
noncomputable def greedySmallFactorBlocks (T : ℝ) (a : ℕ) :
    List ℕ → ℕ × List ℕ
  | [] => (a, [])
  | x :: xs =>
    if T ≤ ((a * x : ℕ) : ℝ) then
      let q := greedySmallFactorBlocks T 1 xs
      (q.1, (a * x) :: q.2)
    else
      greedySmallFactorBlocks T (a * x) xs

/-- Greedy packing preserves the full factor product exactly. -/
theorem greedySmallFactorBlocks_prod (T : ℝ) (a : ℕ) (xs : List ℕ) :
    a * xs.prod =
      (greedySmallFactorBlocks T a xs).1 *
        (greedySmallFactorBlocks T a xs).2.prod := by
  induction xs generalizing a with
  | nil => simp [greedySmallFactorBlocks]
  | cons x xs ih =>
      by_cases h : T ≤ ((a * x : ℕ) : ℝ)
      · simp only [greedySmallFactorBlocks, h, ↓reduceIte,
          List.prod_cons]
        have hrec := ih 1
        simp only [one_mul] at hrec
        calc
          a * (x * xs.prod) = (a * x) * xs.prod := by ac_rfl
          _ = (a * x) * ((greedySmallFactorBlocks T 1 xs).1 *
                (greedySmallFactorBlocks T 1 xs).2.prod) := by rw [hrec]
          _ = (greedySmallFactorBlocks T 1 xs).1 *
                ((a * x) * (greedySmallFactorBlocks T 1 xs).2.prod) := by ac_rfl
      · simpa only [greedySmallFactorBlocks, h, ↓reduceIte,
          List.prod_cons, mul_assoc] using ih (a * x)

/-- The running product remains below `T`; completed blocks lie
between `T` and `T²`. -/
theorem greedySmallFactorBlocks_bounds (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hx : ∀ x ∈ xs, 0 < x ∧ (x : ℝ) ≤ T)
    (a : ℕ) (ha : 0 < a) (haT : (a : ℝ) < T) :
    let q := greedySmallFactorBlocks T a xs
    0 < q.1 ∧ (q.1 : ℝ) < T ∧
      ∀ b ∈ q.2, T ≤ (b : ℝ) ∧ (b : ℝ) ≤ T ^ 2 := by
  induction xs generalizing a with
  | nil => simpa [greedySmallFactorBlocks] using
      (show 0 < a ∧ (a : ℝ) < T ∧
        (∀ b ∈ ([] : List ℕ), T ≤ (b : ℝ) ∧ (b : ℝ) ≤ T ^ 2) from
        ⟨ha, haT, by simp⟩)
  | cons x xs ih =>
      have hxp : 0 < x := (hx x (by simp)).1
      have hxT : (x : ℝ) ≤ T := (hx x (by simp)).2
      have htail : ∀ y ∈ xs, 0 < y ∧ (y : ℝ) ≤ T := by
        intro y hy
        exact hx y (by simp [hy])
      have haxp : 0 < a * x := Nat.mul_pos ha hxp
      by_cases h : T ≤ ((a * x : ℕ) : ℝ)
      · have hrec := ih htail 1 (by omega) (by exact_mod_cast hT)
        have haxT : ((a * x : ℕ) : ℝ) ≤ T ^ 2 := by
          have hmul : (a : ℝ) * (x : ℝ) ≤ T * T :=
            mul_le_mul (le_of_lt haT) hxT (Nat.cast_nonneg _) (by linarith)
          simpa [pow_two] using hmul
        simp only [greedySmallFactorBlocks, h, ↓reduceIte,
          List.mem_cons]
        refine ⟨hrec.1, hrec.2.1, ?_⟩
        intro b hb
        rcases hb with rfl | hb
        · exact ⟨h, haxT⟩
        · exact hrec.2.2 b hb
      · have haxT : ((a * x : ℕ) : ℝ) < T := lt_of_not_ge h
        simpa only [greedySmallFactorBlocks, h, ↓reduceIte] using
          ih htail (a * x) haxp haxT

/-- The number of completed greedy blocks is bounded by the
exponent of any power-of-`T` bound for the full factor product. -/
theorem greedySmallFactorBlocks_closed_count (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hx : ∀ x ∈ xs, 0 < x ∧ (x : ℝ) ≤ T)
    (k : ℕ) (hbound : (xs.prod : ℝ) ≤ T ^ k) :
    (greedySmallFactorBlocks T 1 xs).2.length ≤ k := by
  let q := greedySmallFactorBlocks T 1 xs
  have hq := greedySmallFactorBlocks_bounds T hT xs hx 1 (by omega)
    (by exact_mod_cast hT)
  have hprod := greedySmallFactorBlocks_prod T 1 xs
  simp only [one_mul] at hprod
  have hxspos : 0 < xs.prod := List.prod_pos (by
    intro x hmem
    exact (hx x hmem).1)
  have hdiv : q.2.prod ∣ xs.prod := by
    refine ⟨q.1, ?_⟩
    simpa only [q, mul_comm] using hprod
  have hle : q.2.prod ≤ xs.prod := Nat.le_of_dvd hxspos hdiv
  apply threshold_factor_count_le q.2 T k hT ?_
    ((Nat.cast_le.mpr hle).trans hbound)
  intro b hb
  exact (hq.2.2 b hb).1

/-- The final short pending product is included only when nontrivial.
Every entry of this list is a divisor-sized block. -/
noncomputable def smallFactorBlocks (T : ℝ) (xs : List ℕ) : List ℕ :=
  let q := greedySmallFactorBlocks T 1 xs
  if q.1 = 1 then q.2 else q.1 :: q.2

theorem smallFactorBlocks_prod (T : ℝ) (xs : List ℕ) :
    (smallFactorBlocks T xs).prod = xs.prod := by
  let q := greedySmallFactorBlocks T 1 xs
  have hp := greedySmallFactorBlocks_prod T 1 xs
  simp only [one_mul] at hp
  by_cases h : q.1 = 1
  · simpa [smallFactorBlocks, q, h] using hp.symm
  · simpa [smallFactorBlocks, q, h, List.prod_cons] using hp.symm

theorem smallFactorBlocks_bounds (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hx : ∀ x ∈ xs, 0 < x ∧ (x : ℝ) ≤ T) :
    ∀ b ∈ smallFactorBlocks T xs,
      0 < b ∧ (b : ℝ) ≤ T ^ 2 := by
  let q := greedySmallFactorBlocks T 1 xs
  have hq := greedySmallFactorBlocks_bounds T hT xs hx 1 (by omega)
    (by exact_mod_cast hT)
  intro b hb
  by_cases h : q.1 = 1
  · have hbq : b ∈ q.2 := by simpa [smallFactorBlocks, q, h] using hb
    have hbound := hq.2.2 b hbq
    constructor
    · exact_mod_cast lt_of_lt_of_le (by linarith : (0:ℝ) < T) hbound.1
    · exact hbound.2
  · have hbq : b = q.1 ∨ b ∈ q.2 := by
      simpa [smallFactorBlocks, q, h] using hb
    rcases hbq with rfl | hbq
    · exact ⟨hq.1, le_trans (le_of_lt hq.2.1) (by nlinarith)⟩
    · have hbound := hq.2.2 b hbq
      constructor
      · exact_mod_cast lt_of_lt_of_le (by linarith : (0:ℝ) < T) hbound.1
      · exact hbound.2

theorem smallFactorBlocks_length_le (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hx : ∀ x ∈ xs, 0 < x ∧ (x : ℝ) ≤ T)
    (k : ℕ) (hbound : (xs.prod : ℝ) ≤ T ^ k) :
    (smallFactorBlocks T xs).length ≤ k + 1 := by
  let q := greedySmallFactorBlocks T 1 xs
  have hc := greedySmallFactorBlocks_closed_count T hT xs hx k hbound
  by_cases h : q.1 = 1
  · simpa [smallFactorBlocks, q, h] using hc.trans (Nat.le_succ k)
  · simpa [smallFactorBlocks, q, h] using Nat.succ_le_succ hc

/-- Prime factors greater than the upper block threshold. -/
noncomputable def largeFactors (T : ℝ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun x : ℕ => decide (T ^ 2 < (x : ℝ)))

/-- Individual medium factors, already within the block-size bound. -/
noncomputable def mediumFactors (T : ℝ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun x : ℕ => decide (T < (x : ℝ) ∧ (x : ℝ) ≤ T ^ 2))

/-- Factors small enough for greedy packing. -/
noncomputable def smallFactors (T : ℝ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun x : ℕ => decide ((x : ℝ) ≤ T))

/-- The three threshold classes partition the original factor
product exactly, including equality at either threshold. -/
theorem factorClasses_prod (T : ℝ) (hT : 1 < T) (xs : List ℕ) :
    (largeFactors T xs).prod * (mediumFactors T xs).prod *
      (smallFactors T xs).prod = xs.prod := by
  have hT2 : T ≤ T ^ 2 := by nlinarith
  induction xs with
  | nil => simp [largeFactors, mediumFactors, smallFactors]
  | cons x xs ih =>
      by_cases hs : (x : ℝ) ≤ T
      · have hl : ¬ T ^ 2 < (x : ℝ) := by linarith
        have hm : ¬ (T < (x : ℝ) ∧ (x : ℝ) ≤ T ^ 2) := by
          intro h
          exact (not_lt_of_ge hs) h.1
        simp [largeFactors, mediumFactors, smallFactors, hs, hl, hm,
          List.filter_cons, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] at ih ⊢
        exact Or.inl ih
      · by_cases hl : T ^ 2 < (x : ℝ)
        · have hm : ¬ (T < (x : ℝ) ∧ (x : ℝ) ≤ T ^ 2) := by
            intro h
            exact (not_le_of_gt hl) h.2
          simp [largeFactors, mediumFactors, smallFactors, hs, hl, hm,
            List.filter_cons, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] at ih ⊢
          exact Or.inl ih
        · have hm : T < (x : ℝ) ∧ (x : ℝ) ≤ T ^ 2 := by
            constructor <;> linarith
          simp [largeFactors, mediumFactors, smallFactors, hs, hl, hm,
            List.filter_cons, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] at ih ⊢
          exact Or.inl ih

/-- All medium factors and all completed small-factor blocks have
size at least `T`. The only possible smaller block is the final
pending product. -/
noncomputable def fullThresholdBlocks (T : ℝ) (xs : List ℕ) : List ℕ :=
  mediumFactors T xs ++ (greedySmallFactorBlocks T 1 (smallFactors T xs)).2

theorem fullThresholdBlocks_count_le (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hxs : ∀ x ∈ xs, 0 < x)
    (k : ℕ) (hbound : (xs.prod : ℝ) ≤ T ^ k) :
    (fullThresholdBlocks T xs).length ≤ k := by
  let sm := smallFactors T xs
  let q := greedySmallFactorBlocks T 1 sm
  have hsm : ∀ x ∈ sm, 0 < x ∧ (x : ℝ) ≤ T := by
    intro x hx
    have hxorig : x ∈ xs := (List.mem_filter.mp hx).1
    have hxT : (x : ℝ) ≤ T := of_decide_eq_true (List.mem_filter.mp hx).2
    exact ⟨hxs x hxorig, hxT⟩
  have hq := greedySmallFactorBlocks_bounds T hT sm hsm 1 (by omega)
    (by exact_mod_cast hT)
  have hqprod := greedySmallFactorBlocks_prod T 1 sm
  simp only [one_mul] at hqprod
  have hclasses := factorClasses_prod T hT xs
  have hdiv : (fullThresholdBlocks T xs).prod ∣ xs.prod := by
    refine ⟨(largeFactors T xs).prod * q.1, ?_⟩
    calc
      xs.prod = (largeFactors T xs).prod *
          (mediumFactors T xs).prod * sm.prod := hclasses.symm
      _ = (mediumFactors T xs).prod * q.2.prod *
          ((largeFactors T xs).prod * q.1) := by
        rw [hqprod]
        ac_rfl
      _ = (fullThresholdBlocks T xs).prod *
          ((largeFactors T xs).prod * q.1) := by
        simp [fullThresholdBlocks, q, sm, List.prod_append]
  have hxspos : 0 < xs.prod := List.prod_pos hxs
  have hle : (fullThresholdBlocks T xs).prod ≤ xs.prod :=
    Nat.le_of_dvd hxspos hdiv
  apply threshold_factor_count_le (fullThresholdBlocks T xs) T k hT ?_
    ((Nat.cast_le.mpr hle).trans hbound)
  intro b hb
  have hmem : b ∈ mediumFactors T xs ∨ b ∈ q.2 := by
    simpa [fullThresholdBlocks, q, sm] using hb
  rcases hmem with hmed | hclosed
  · have hpred : T < (b : ℝ) ∧ (b : ℝ) ≤ T ^ 2 :=
      of_decide_eq_true (List.mem_filter.mp hmed).2
    exact le_of_lt hpred.1
  · exact (hq.2.2 b hclosed).1

/-- The medium singleton factors and greedy small-factor blocks;
every element has size at most `T²`. -/
noncomputable def boundedFactorBlocks (T : ℝ) (xs : List ℕ) : List ℕ :=
  mediumFactors T xs ++ smallFactorBlocks T (smallFactors T xs)

theorem boundedFactorBlocks_prod (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) :
    (largeFactors T xs).prod * (boundedFactorBlocks T xs).prod =
      xs.prod := by
  simpa [boundedFactorBlocks, List.prod_append,
    smallFactorBlocks_prod, mul_assoc] using factorClasses_prod T hT xs

theorem boundedFactorBlocks_bounds (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hxs : ∀ x ∈ xs, 0 < x) :
    ∀ b ∈ boundedFactorBlocks T xs,
      0 < b ∧ (b : ℝ) ≤ T ^ 2 := by
  have hsm : ∀ x ∈ smallFactors T xs,
      0 < x ∧ (x : ℝ) ≤ T := by
    intro x hx
    exact ⟨hxs x (List.mem_filter.mp hx).1,
      of_decide_eq_true (List.mem_filter.mp hx).2⟩
  intro b hb
  have hb' : b ∈ mediumFactors T xs ∨
      b ∈ smallFactorBlocks T (smallFactors T xs) := by
    simpa [boundedFactorBlocks] using hb
  rcases hb' with hm | hs
  · have hmed : T < (b : ℝ) ∧ (b : ℝ) ≤ T ^ 2 :=
      of_decide_eq_true (List.mem_filter.mp hm).2
    exact ⟨by exact_mod_cast (lt_trans (by linarith : (0:ℝ) < T) hmed.1),
      hmed.2⟩
  · exact smallFactorBlocks_bounds T hT (smallFactors T xs) hsm b hs

theorem boundedFactorBlocks_length_le (T : ℝ) (hT : 1 < T)
    (xs : List ℕ) (hxs : ∀ x ∈ xs, 0 < x)
    (k : ℕ) (hbound : (xs.prod : ℝ) ≤ T ^ k) :
    (boundedFactorBlocks T xs).length ≤ k + 1 := by
  let sm := smallFactors T xs
  let q := greedySmallFactorBlocks T 1 sm
  have hc := fullThresholdBlocks_count_le T hT xs hxs k hbound
  by_cases h : q.1 = 1
  · have heq : boundedFactorBlocks T xs = fullThresholdBlocks T xs := by
      simp [boundedFactorBlocks, fullThresholdBlocks,
        smallFactorBlocks, q, sm, h]
    rw [heq]
    omega
  · have hlen : (boundedFactorBlocks T xs).length =
        (fullThresholdBlocks T xs).length + 1 := by
      simp [boundedFactorBlocks, fullThresholdBlocks,
        smallFactorBlocks, q, sm, h, List.length_append]
      omega
    omega

/-- The real threshold chosen in the blueprint has exactly the two
required powers; no approximation of the cutoff is used. -/
theorem divisorThresholdProperties (n m : ℕ) (hn : 1 < n) (hm : 0 < m) :
    let T : ℝ := (n : ℝ) ^ (1 / ((2 * m : ℕ) : ℝ) : ℝ)
    1 < T ∧ T ^ (2 * m) = (n : ℝ) ∧
      T ^ 2 = (n : ℝ) ^ (1 / (m : ℝ) : ℝ) := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have h2mne : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
  have hmainexp : (1 / (((2 * m : ℕ) : ℝ)) : ℝ) *
      ((2 * m : ℕ) : ℝ) = 1 := by field_simp
  have htwoexp : (1 / (((2 * m : ℕ) : ℝ)) : ℝ) * 2 =
      1 / (m : ℝ) := by
    push_cast
    field_simp
  dsimp
  constructor
  · exact Real.one_lt_rpow hnreal (by positivity)
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hnnonneg, hmainexp,
      Real.rpow_one]
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hnnonneg]
    congr 1

/-- The exact factor grouping asserted in the blueprint proof:
large prime entries number at most `m`, and the other entries form
at most `2m+1` divisors below the stated real cutoff. -/
theorem primeFactorBlockFacts (n m : ℕ) (hn : 1 < n) (hm : 0 < m) :
    let T : ℝ := (n : ℝ) ^ (1 / ((2 * m : ℕ) : ℝ) : ℝ)
    (largeFactors T n.primeFactorsList).length ≤ m ∧
    (boundedFactorBlocks T n.primeFactorsList).length ≤ 2 * m + 1 ∧
    (largeFactors T n.primeFactorsList).prod *
      (boundedFactorBlocks T n.primeFactorsList).prod = n ∧
    ∀ b ∈ boundedFactorBlocks T n.primeFactorsList,
      b ∣ n ∧ (b : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ) : ℝ) := by
  let T : ℝ := (n : ℝ) ^ (1 / ((2 * m : ℕ) : ℝ) : ℝ)
  have hprops := divisorThresholdProperties n m hn hm
  change 1 < T ∧ T ^ (2 * m) = (n : ℝ) ∧
    T ^ 2 = (n : ℝ) ^ (1 / (m : ℝ) : ℝ) at hprops
  rcases hprops with ⟨hT, hpower, hcut⟩
  let xs := n.primeFactorsList
  have hxs : ∀ p ∈ xs, 0 < p := by
    intro p hp
    exact Nat.pos_of_mem_primeFactorsList hp
  have hnzero : n ≠ 0 := by omega
  have hprod : xs.prod = n := Nat.prod_primeFactorsList hnzero
  have hreal : (xs.prod : ℝ) ≤ T ^ (2 * m) := by
    rw [hprod, hpower]
  have hpow2 : (T ^ 2) ^ m = T ^ (2 * m) := by rw [pow_mul]
  have hlarge : (largeFactors T xs).length ≤ m :=
    largeFactors_card_le xs (by rw [hprod]; omega) T hT m
      (by rw [hpow2]; exact hreal)
  have hblocks : (boundedFactorBlocks T xs).length ≤ 2 * m + 1 :=
    boundedFactorBlocks_length_le T hT xs hxs (2 * m) hreal
  have hpartition : (largeFactors T xs).prod *
      (boundedFactorBlocks T xs).prod = n := by
    rw [boundedFactorBlocks_prod T hT xs, hprod]
  dsimp only
  refine ⟨hlarge, hblocks, hpartition, ?_⟩
  intro b hb
  have hblockDiv : b ∣ (boundedFactorBlocks T xs).prod := List.dvd_prod hb
  have hpartDiv : (boundedFactorBlocks T xs).prod ∣ n := by
    refine ⟨(largeFactors T xs).prod, ?_⟩
    simpa only [mul_comm] using hpartition.symm
  have hbound := boundedFactorBlocks_bounds T hT xs hxs b hb
  exact ⟨hblockDiv.trans hpartDiv, by rw [← hcut]; exact hbound.2⟩

/-- Each prime factor contributes exactly two divisors to the
submultiplicative product bound. -/
theorem primeList_cardDivisors_prod (xs : List ℕ)
    (hprime : ∀ p ∈ xs, p.Prime) :
    (xs.map fun p => p.divisors.card).prod = 2 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      have hp : p.Prime := hprime p (by simp)
      have htail : ∀ q ∈ xs, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hcard : p.divisors.card = 2 := by
        rw [hp.divisors]
        exact Finset.card_pair hp.ne_one.symm
      simp only [List.map_cons, List.prod_cons, List.length_cons,
        pow_succ, hcard, ih htail]
      ac_rfl

/-- The divisor-count consequence of an abstract large-prime/small-block
factorization. The finite maximum argument is kept separate. -/
theorem cardDivisors_factorPartition_le (large blocks : List ℕ)
    (hprime : ∀ p ∈ large, p.Prime)
    (hblocks : ∀ b ∈ blocks, 0 < b)
    (M m : ℕ) (hM : 1 ≤ M)
    (hblockM : ∀ b ∈ blocks, b.divisors.card ≤ M)
    (hlarge : large.length ≤ m)
    (hsmall : blocks.length ≤ 2 * m + 1) :
    (large.prod * blocks.prod).divisors.card ≤
      2 ^ m * M ^ (2 * m + 1) := by
  have hlargePos : 0 < large.prod := List.prod_pos (by
    intro p hp
    exact (hprime p hp).pos)
  have hblocksPos : 0 < blocks.prod := List.prod_pos hblocks
  have hprimeProd := cardDivisors_list_prod_le large (by
    intro p hp
    exact (hprime p hp).pos)
  have hblockProd := cardDivisors_list_prod_le blocks hblocks
  have hprimeEq := primeList_cardDivisors_prod large hprime
  have hblocksM : (blocks.map fun b => b.divisors.card).prod ≤
      M ^ blocks.length := by
    calc
      (blocks.map fun b => b.divisors.card).prod ≤
          (blocks.map fun _ => M).prod := by
            apply List.prod_le_prod
            intro b hb
            exact hblockM b hb
      _ = M ^ blocks.length := by simp
  have hlargePow : 2 ^ large.length ≤ 2 ^ m :=
    pow_le_pow_right₀ (by norm_num) hlarge
  have hblockPow : M ^ blocks.length ≤ M ^ (2 * m + 1) :=
    pow_le_pow_right₀ hM hsmall
  calc
    (large.prod * blocks.prod).divisors.card ≤
        large.prod.divisors.card * blocks.prod.divisors.card :=
      cardDivisors_mul_le large.prod blocks.prod
        (Nat.ne_of_gt hlargePos) (Nat.ne_of_gt hblocksPos)
    _ ≤ (large.map fun p => p.divisors.card).prod *
        (blocks.map fun b => b.divisors.card).prod :=
      Nat.mul_le_mul hprimeProd hblockProd
    _ ≤ 2 ^ m * M ^ (2 * m + 1) := by
      rw [hprimeEq]
      exact Nat.mul_le_mul hlargePow (hblocksM.trans hblockPow)

/-- The finite family of divisors under the blueprint's real cutoff. -/
noncomputable def eligibleSmallDivisors (n m : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => (d : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ) : ℝ))

theorem one_mem_eligibleSmallDivisors (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    1 ∈ eligibleSmallDivisors n m := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmreal : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hcut : (1 : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ) : ℝ) :=
    Real.one_le_rpow hnreal hmreal
  change 1 ∈ n.divisors.filter
    (fun d : ℕ => (d : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ) : ℝ))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨one_dvd n, Nat.ne_of_gt hn⟩,
      by simpa only [Nat.cast_one] using hcut⟩

theorem eligibleSmallDivisors_nonempty (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    (eligibleSmallDivisors n m).Nonempty :=
  ⟨1, one_mem_eligibleSmallDivisors n m hn hm⟩

/-- A finite maximum of nonnegative divisor powers is bounded by
their sum, with the maximizing divisor still in the cutoff set. -/
theorem eligibleSmallDivisors_sup_pow_le_sum (n m e : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    (eligibleSmallDivisors n m).sup (fun d => d.divisors.card) ^ e ≤
      ∑ d ∈ eligibleSmallDivisors n m, d.divisors.card ^ e := by
  obtain ⟨d, hd, hmax⟩ :=
    Finset.exists_mem_eq_sup (eligibleSmallDivisors n m)
      (eligibleSmallDivisors_nonempty n m hn hm)
      (fun d => d.divisors.card)
  rw [hmax]
  exact Finset.single_le_sum
    (f := fun d : ℕ => d.divisors.card ^ e)
    (fun _ _ => Nat.zero_le _) hd

/-- The exact small-divisor inequality in cardinal-divisor notation. -/
theorem smallDivisorDomination_card (m C n : ℕ)
    (hm : 0 < m) (hC : 0 < C) (hn : 0 < n) :
    n.divisors.card ^ C ≤ 2 ^ (m * C) *
      ∑ d ∈ eligibleSmallDivisors n m,
        d.divisors.card ^ ((2 * m + 1) * C) := by
  by_cases hn1 : n = 1
  · subst n
    have hone := one_mem_eligibleSmallDivisors 1 m (by omega) hm
    have hsum : 1 ≤
        ∑ d ∈ eligibleSmallDivisors 1 m,
          d.divisors.card ^ ((2 * m + 1) * C) := by
      simpa using (Finset.single_le_sum
        (f := fun d : ℕ => d.divisors.card ^ ((2 * m + 1) * C))
        (fun _ _ => Nat.zero_le _) hone)
    have hpow : 1 ≤ 2 ^ (m * C) := by
      have hp : 0 < 2 ^ (m * C) := pow_pos (by omega) _
      omega
    have hmul : 1 ≤ 2 ^ (m * C) *
        (∑ d ∈ eligibleSmallDivisors 1 m,
          d.divisors.card ^ ((2 * m + 1) * C)) := by
      simpa using Nat.mul_le_mul hpow hsum
    simpa using hmul
  · have hnlarge : 1 < n := by omega
    let T : ℝ := (n : ℝ) ^ (1 / ((2 * m : ℕ) : ℝ) : ℝ)
    let xs := n.primeFactorsList
    let large := largeFactors T xs
    let blocks := boundedFactorBlocks T xs
    let E := eligibleSmallDivisors n m
    let M := E.sup (fun d => d.divisors.card)
    have hT : 1 < T := (divisorThresholdProperties n m hnlarge hm).1
    have hfacts := primeFactorBlockFacts n m hnlarge hm
    change large.length ≤ m ∧ blocks.length ≤ 2 * m + 1 ∧
      large.prod * blocks.prod = n ∧
      (∀ b ∈ blocks,
        b ∣ n ∧ (b : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ) : ℝ)) at hfacts
    rcases hfacts with ⟨hlargeCount, hblockCount, hpartition, hblockFacts⟩
    have hxs : ∀ p ∈ xs, 0 < p := by
      intro p hp
      exact Nat.pos_of_mem_primeFactorsList hp
    have hlargePrime : ∀ p ∈ large, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1
    have hblocksPos : ∀ b ∈ blocks, 0 < b := by
      intro b hb
      exact (boundedFactorBlocks_bounds T hT xs hxs b hb).1
    have hMone : 1 ≤ M := by
      have hmem : 1 ∈ E := one_mem_eligibleSmallDivisors n m hn hm
      have hle : (1 : ℕ).divisors.card ≤ M :=
        Finset.le_sup (f := fun d : ℕ => d.divisors.card) hmem
      simpa using hle
    have hblocksM : ∀ b ∈ blocks, b.divisors.card ≤ M := by
      intro b hb
      have hbf := hblockFacts b hb
      have hbE : b ∈ E := by
        change b ∈ n.divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (n : ℝ) ^ (1 / (m : ℝ) : ℝ))
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨hbf.1, Nat.ne_of_gt hn⟩, hbf.2⟩
      exact Finset.le_sup (f := fun d : ℕ => d.divisors.card) hbE
    have hτ : n.divisors.card ≤ 2 ^ m * M ^ (2 * m + 1) := by
      calc
        n.divisors.card = (large.prod * blocks.prod).divisors.card := by
          rw [hpartition]
        _ ≤ 2 ^ m * M ^ (2 * m + 1) :=
          cardDivisors_factorPartition_le large blocks
            hlargePrime hblocksPos M m hMone hblocksM
            hlargeCount hblockCount
    have hsum := eligibleSmallDivisors_sup_pow_le_sum n m
      ((2 * m + 1) * C) hn hm
    calc
      n.divisors.card ^ C ≤ (2 ^ m * M ^ (2 * m + 1)) ^ C :=
        pow_le_pow_left₀ (by omega) hτ C
      _ = 2 ^ (m * C) * M ^ ((2 * m + 1) * C) := by
        simp only [mul_pow, pow_mul]
      _ ≤ 2 ^ (m * C) *
          (∑ d ∈ eligibleSmallDivisors n m,
            d.divisors.card ^ ((2 * m + 1) * C)) :=
        Nat.mul_le_mul_left _ hsum

/-- The blueprint's `ltw:small-divisors` statement with `τ=d₂` and
the exact real cutoff `n^(1/m)`. -/
theorem smallDivisorDomination (m C n : ℕ)
    (hm : 0 < m) (hC : 0 < C) (hn : 0 < n) :
    FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n ^ C ≤
      2 ^ (m * C) *
        ∑ d ∈ eligibleSmallDivisors n m,
          FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 d ^
            ((2 * m + 1) * C) := by
  simpa only [divisorCoefficient_two_eq_cardDivisors] using
    smallDivisorDomination_card m C n hm hC hn

#print axioms divisorQuotientGcd_dvd_right
#print axioms cardDivisors_mul_le
#print axioms divisorCoefficient_two_eq_cardDivisors
#print axioms divisorCoefficient_two_mul_le
#print axioms cardDivisors_list_prod_le
#print axioms threshold_pow_length_le_prod
#print axioms threshold_factor_count_le
#print axioms largeFactors_card_le
#print axioms greedySmallFactorBlocks_prod
#print axioms greedySmallFactorBlocks_bounds
#print axioms greedySmallFactorBlocks_closed_count
#print axioms smallFactorBlocks_prod
#print axioms smallFactorBlocks_bounds
#print axioms smallFactorBlocks_length_le
#print axioms factorClasses_prod
#print axioms fullThresholdBlocks_count_le
#print axioms boundedFactorBlocks_prod
#print axioms boundedFactorBlocks_bounds
#print axioms boundedFactorBlocks_length_le
#print axioms divisorThresholdProperties
#print axioms primeFactorBlockFacts
#print axioms primeList_cardDivisors_prod
#print axioms cardDivisors_factorPartition_le
#print axioms eligibleSmallDivisors_nonempty
#print axioms one_mem_eligibleSmallDivisors
#print axioms eligibleSmallDivisors_sup_pow_le_sum
#print axioms smallDivisorDomination_card
#print axioms smallDivisorDomination

end FractionalPrimes.Literature.Twisted

end
