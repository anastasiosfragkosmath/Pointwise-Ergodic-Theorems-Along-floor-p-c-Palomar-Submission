module

public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter
public import FractionalPrimes.Literature.Twisted.CharacterOrthogonalityAdapter
public import FractionalPrimes.Literature.Twisted.FlatGcdAllocation
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.EuclideanDomain

/-!
# Finite triple character factorization

The algebraic step behind `ltw:triple-character-factorization`: an exact
residue-class constraint on a product of three positive integers is expanded
by character orthogonality, and the three finite sums separate without a
loss in the character normalization.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- Complex powers split over products of positive natural bases, with no
restriction on the complex exponent. -/
theorem positiveNatCpow_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (z : ℂ) :
    ((m * n : ℕ) : ℂ) ^ z = (m : ℂ) ^ z * (n : ℂ) ^ z := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmnC : ((m * n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)
  have hbase : ((m * n : ℕ) : ℂ) = ((m : ℝ) : ℂ) * (n : ℂ) := by
    push_cast
    ring
  calc
    ((m * n : ℕ) : ℂ) ^ z = (((m : ℝ) : ℂ) * (n : ℂ)) ^ z := by rw [hbase]
    _ = (m : ℂ) ^ z * (n : ℂ) ^ z := by
      rw [Complex.cpow_def_of_ne_zero (by simpa [hbase] using hmnC),
        Complex.cpow_def_of_ne_zero hmC, Complex.cpow_def_of_ne_zero hnC,
        Complex.log_ofReal_mul hmR hnC]
      rw [add_mul, Complex.exp_add]
      rw [Complex.ofReal_log hmR.le]
      rfl

/-- Dividing an integer and a positive modulus by their common gcd gives
coprime residual data. This is the quotient-coprimality step used for the
residue `a'` and modulus `Q` in `ltw:triple-character-factorization`. -/
theorem residueGcdQuotientsCoprime {a : ℤ} {q : ℕ} (hq : 0 < q) :
    IsCoprime (a / (Nat.gcd a.natAbs q : ℤ))
      ((q / Nat.gcd a.natAbs q : ℕ) : ℤ) := by
  let d : ℕ := Nat.gcd a.natAbs q
  have hdq : (d : ℤ) = GCDMonoid.gcd a (q : ℤ) := by
    dsimp [d]
    rw [← Int.coe_gcd]
    simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  have hqInt : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hcop := isCoprime_div_gcd_div_gcd (p := a) (q := (q : ℤ)) hqInt
  rw [← hdq] at hcop
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right _ hq
  have hdiv : d ∣ q := by
    dsimp [d]
    exact Nat.gcd_dvd_right _ _
  have hcastdiv : ((q / d : ℕ) : ℤ) = (q : ℤ) / (d : ℤ) := by
    exact Int.natCast_div q d
  rw [hcastdiv]
  exact hcop

/-- The natural gcd factorization of the modulus used in the nonunit residue
decomposition. -/
theorem residueGcd_modulus_factor {a : ℤ} {q : ℕ} (hq : 0 < q) :
    Nat.gcd a.natAbs q * (q / Nat.gcd a.natAbs q) = q := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a.natAbs q)

/-- The corresponding signed integer factorization of the residue. -/
theorem residueGcd_residue_factor {a : ℤ} {q : ℕ} :
    (Nat.gcd a.natAbs q : ℤ) *
      (a / (Nat.gcd a.natAbs q : ℤ)) = a := by
  have hdq : (Nat.gcd a.natAbs q : ℤ) = GCDMonoid.gcd a (q : ℤ) := by
    rw [← Int.coe_gcd]
    simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  have hgcd : GCDMonoid.gcd a (q : ℤ) ∣ a := GCDMonoid.gcd_dvd_left _ _
  calc
    (Nat.gcd a.natAbs q : ℤ) * (a / (Nat.gcd a.natAbs q : ℤ)) =
        GCDMonoid.gcd a (q : ℤ) * (a / GCDMonoid.gcd a (q : ℤ)) := by
          rw [hdq]
    _ = a := by
          calc
            GCDMonoid.gcd a (q : ℤ) * (a / GCDMonoid.gcd a (q : ℤ)) =
                (a / GCDMonoid.gcd a (q : ℤ)) * GCDMonoid.gcd a (q : ℤ) := by ring
            _ = a := Int.ediv_mul_cancel hgcd

/-- Cancelling the common gcd from a residue congruence is exact, including
the modulus-one case. -/
theorem residueGcd_congruence_quotient_iff {a : ℤ} {q n : ℕ}
    (hq : 0 < q) (hndvd : Nat.gcd a.natAbs q ∣ n) :
    ((n : ZMod q) = (a : ZMod q)) ↔
      (((n / Nat.gcd a.natAbs q : ℕ) : ℤ) : ZMod (q / Nat.gcd a.natAbs q)) =
        ((a / (Nat.gcd a.natAbs q : ℤ)) : ZMod
          (q / Nat.gcd a.natAbs q)) := by
  let d : ℕ := Nat.gcd a.natAbs q
  let Q : ℕ := q / d
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right _ hq
  have hdcast : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdpos)
  have hqfactorNat : d * Q = q := by
    dsimp [Q]
    exact Nat.mul_div_cancel' (by dsimp [d]; exact Nat.gcd_dvd_right _ _)
  have hqfactor : (q : ℤ) = (d : ℤ) * (Q : ℤ) := by
    exact_mod_cast hqfactorNat.symm
  have hnfactorNat : d * (n / d) = n := Nat.mul_div_cancel' (by simpa [d] using hndvd)
  have hnfactor : (n : ℤ) = (d : ℤ) * ((n / d : ℕ) : ℤ) := by
    exact_mod_cast hnfactorNat.symm
  have hafactor : a = (d : ℤ) * (a / (d : ℤ)) := by
    simpa [d] using (residueGcd_residue_factor (a := a) (q := q)).symm
  have hmodFull :
      ((n : ℤ) ≡ a [ZMOD (q : ℤ)]) ↔
        ((d : ℤ) * ((n / d : ℕ) : ℤ) ≡
          (d : ℤ) * (a / (d : ℤ)) [ZMOD (d : ℤ) * (Q : ℤ)]) := by
    rw [← hnfactor, ← hafactor, ← hqfactor]
  have hmodQuot := Int.ModEq.mul_left_cancel_iff' hdcast
    (m := (Q : ℤ)) (a := ((n / d : ℕ) : ℤ)) (b := a / (d : ℤ))
  calc
    ((n : ZMod q) = (a : ZMod q)) ↔
        ((n : ℤ) ≡ a [ZMOD (q : ℤ)]) :=
          (by simpa only [Int.cast_natCast] using
            (ZMod.intCast_eq_intCast_iff (n : ℤ) a q))
    _ ↔ ((d : ℤ) * ((n / d : ℕ) : ℤ) ≡
          (d : ℤ) * (a / (d : ℤ)) [ZMOD (d : ℤ) * (Q : ℤ)]) := hmodFull
    _ ↔ (((n / d : ℕ) : ℤ) ≡ a / (d : ℤ) [ZMOD (Q : ℤ)]) := hmodQuot
    _ ↔ (((n / d : ℕ) : ℤ) : ZMod Q) = ((a / (d : ℤ)) : ZMod Q) :=
          (ZMod.intCast_eq_intCast_iff _ _ Q).symm

/-- A residue congruence fixes the gcd with its modulus, even when the residue
is represented by a negative integer. -/
theorem residueGcd_eq_of_congruent {a : ℤ} {q n : ℕ}
    (hcongr : (n : ZMod q) = (a : ZMod q)) :
    Nat.gcd n q = Nat.gcd a.natAbs q := by
  have hmod : (n : ℤ) ≡ a [ZMOD (q : ℤ)] := by
    have h := ZMod.intCast_eq_intCast_iff (n : ℤ) a q
    exact h.mp (by simpa only [Int.cast_natCast] using hcongr)
  have hqdiv : (q : ℤ) ∣ (n : ℤ) - a := hmod.symm.dvd
  have hgcd : GCDMonoid.gcd (n : ℤ) (q : ℤ) =
      GCDMonoid.gcd a (q : ℤ) :=
    gcd_eq_of_dvd_sub_left hqdiv
  have habs := congrArg Int.natAbs hgcd
  simpa only [Int.natAbs_gcd, Int.gcd_eq_natAbs, Int.natAbs_natCast] using habs

/-- The product of the allocated factors through label `i`. -/
def orderedAllocationPrefix {k : ℕ} (r : Fin k → PositiveInteger)
    (i : Fin k) : ℕ :=
  ∏ j ∈ Finset.Iic i, (r j).1

private theorem orderedAllocationPrefix_dvd
    {k d : ℕ} (r : divisorFactorTuples k d) (i : Fin k) :
    orderedAllocationPrefix r.1 i ∣ d := by
  have hp := Finset.prod_dvd_prod_of_subset
    (Finset.Iic i) Finset.univ (fun j : Fin k => (r.1 j).1)
    (Finset.subset_univ _)
  simpa [orderedAllocationPrefix, r.2] using hp

/-- On a residue class, the flat gcd-allocation cutoffs are exactly the
source cutoffs modulo the residual moduli `q_i`. The product of the residual
variables is coprime to `Q`, which supplies the extra `Q` factor in each
source cutoff. -/
theorem flatAllocationCutoffs_iff_source
    {k : ℕ} {a : ℤ} {q n : ℕ} (hq : 0 < q)
    (hcongr : (n : ZMod q) = (a : ZMod q))
    {d t : ℕ} (hd : d = Nat.gcd a.natAbs q)
    (ht : t = n / d)
    (r : divisorFactorTuples k d) (m : divisorFactorTuples k t) :
    (∀ i : Fin k, Nat.Coprime (m.1 i).1
      (d / orderedAllocationPrefix r.1 i)) ↔
    (∀ i : Fin k, Nat.Coprime (m.1 i).1
      (q / orderedAllocationPrefix r.1 i)) := by
  have hgc : Nat.gcd n q = d := by
    rw [hd]
    exact residueGcd_eq_of_congruent hcongr
  have hqDiv : d ∣ q := by
    rw [hd]
    exact Nat.gcd_dvd_right _ _
  have hqposD : 0 < d := by
    rw [hd]
    exact Nat.gcd_pos_of_pos_right _ hq
  have hqfac : d * (q / d) = q := Nat.mul_div_cancel' hqDiv
  have hcopResidual : Nat.Coprime t (q / d) := by
    have hc := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_right n hq)
    simpa [hgc, ht, hqfac, Nat.mul_comm] using hc
  have hfactorDiv (i : Fin k) :
      orderedAllocationPrefix r.1 i ∣ d := orderedAllocationPrefix_dvd r i
  have hqfactor' : q = (q / d) * d := by
    calc
      q = d * (q / d) := hqfac.symm
      _ = (q / d) * d := Nat.mul_comm _ _
  have hqiFactor (i : Fin k) :
      q / orderedAllocationPrefix r.1 i =
        (d / orderedAllocationPrefix r.1 i) * (q / d) := by
    calc
      q / orderedAllocationPrefix r.1 i =
          ((q / d) * d) / orderedAllocationPrefix r.1 i :=
            congrArg (fun x : ℕ => x / orderedAllocationPrefix r.1 i) hqfactor'
      _ = (q / d) * (d / orderedAllocationPrefix r.1 i) := by
          exact Nat.mul_div_assoc (q / d) (hfactorDiv i)
      _ = (d / orderedAllocationPrefix r.1 i) * (q / d) := by ac_rfl
  have hmiCopResidual (i : Fin k) : Nat.Coprime (m.1 i).1 (q / d) := by
    have hdvd : (m.1 i).1 ∣ t := by
      calc
        (m.1 i).1 ∣ ∏ j : Fin k, (m.1 j).1 :=
          Finset.dvd_prod_of_mem (fun j : Fin k => (m.1 j).1)
            (Finset.mem_univ i)
        _ = t := m.2
    exact Nat.Coprime.of_dvd_left hdvd hcopResidual
  constructor
  · intro hflat i
    rw [hqiFactor i, Nat.coprime_mul_iff_right]
    exact ⟨hflat i, hmiCopResidual i⟩
  · intro hsource i
    have hi := hsource i
    rw [hqiFactor i, Nat.coprime_mul_iff_right] at hi
    exact hi.1

/-- The labeled partial-gcd allocation at a fixed residue-class integer. -/
noncomputable def residueClassGcdAllocatedConvolution
    (fs : List (ArithmeticFunction ℂ)) (q d t : ℕ) : ℂ :=
  ∑ r : divisorFactorTuples fs.length d,
    ∑ m : divisorFactorTuples fs.length t,
      if ∀ i : Fin fs.length,
        Nat.Coprime (m.1 i).1 (q / orderedAllocationPrefix r.1 i) then
        ∏ i : Fin fs.length,
          (fs.get i) ((r.1 i).1 * (m.1 i).1)
      else 0

/-- The flat gcd-allocation theorem specializes to the source's partial
allocation for a product in the residue class `a mod q`. -/
theorem residueClassFlatGcdAllocation
    (fs : List (ArithmeticFunction ℂ)) {a : ℤ} {q n : ℕ}
    (hq : 0 < q) (hn : 0 < n)
    (hcongr : (n : ZMod q) = (a : ZMod q)) :
    (fs.prod) n = residueClassGcdAllocatedConvolution fs q
      (Nat.gcd a.natAbs q) (n / Nat.gcd a.natAbs q) := by
  classical
  let d : ℕ := Nat.gcd a.natAbs q
  let t : ℕ := n / d
  have hgc : Nat.gcd n q = d := by
    dsimp [d]
    exact residueGcd_eq_of_congruent hcongr
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right _ hq
  have hndvd : d ∣ n := by
    rw [← hgc]
    exact Nat.gcd_dvd_left _ _
  have htpos : 0 < t := by
    dsimp [t]
    exact Nat.div_pos (Nat.le_of_dvd hn hndvd) hdpos
  have hdt : d * t = n := by
    dsimp [t]
    exact Nat.mul_div_cancel' hndvd
  have hflat := flatGcdAllocation fs hdpos htpos
  calc
    (fs.prod) n = (fs.prod) (d * t) := by rw [hdt]
    _ = flatGcdAllocatedConvolution fs d t := hflat
    _ = residueClassGcdAllocatedConvolution fs q d t := by
      unfold flatGcdAllocatedConvolution residueClassGcdAllocatedConvolution
      simp only [orderedAllocationPrefix]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro m hm
      have hiff := flatAllocationCutoffs_iff_source
        (k := fs.length) (a := a) (q := q) (n := n) hq hcongr
        (d := d) (t := t) rfl rfl r m
      exact if_congr hiff rfl rfl

/-- Finite support bounds on the three factors give the corresponding bound
on their Dirichlet convolution product. -/
theorem tripleConvolution_support_bound
    (a₁ a₂ a₃ : ArithmeticFunction ℂ) {N₁ N₂ N₃ n : ℕ}
    (h₁ : ∀ m, a₁ m ≠ 0 → m ≤ N₁)
    (h₂ : ∀ m, a₂ m ≠ 0 → m ≤ N₂)
    (h₃ : ∀ m, a₃ m ≠ 0 → m ≤ N₃)
    (hn : 0 < n) (hconv : (a₁ * a₂ * a₃) n ≠ 0) :
    n ≤ N₁ * N₂ * N₃ := by
  classical
  let fs : List (ArithmeticFunction ℂ) := [a₁, a₂, a₃]
  have hprod : fs.prod = a₁ * a₂ * a₃ := by
    simp [fs]
    exact (mul_assoc a₁ a₂ a₃).symm
  have hflat := flatGcdAllocation fs (r := 1) (by norm_num) hn
  have hflat' : (a₁ * a₂ * a₃) n = flatGcdAllocatedConvolution fs 1 n := by
    simpa [hprod] using hflat
  have hsum : flatGcdAllocatedConvolution fs 1 n ≠ 0 := by
    rw [← hflat']
    exact hconv
  unfold flatGcdAllocatedConvolution at hsum
  obtain ⟨r, hr, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨m, hm, hmne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrne
  have hcoeff :
      (∏ i : Fin 3, (fs.get i) ((r.1 i).1 * (m.1 i).1)) ≠ 0 := by
    have hterm := hmne
    by_cases hc : ∀ i : Fin fs.length,
        Nat.Coprime (m.1 i).1 (1 / ∏ j ∈ Finset.Iic i, (r.1 j).1)
    · rw [if_pos hc] at hterm
      exact hterm
    · rw [if_neg hc] at hterm
      exact (hterm rfl).elim
  have hrone (i : Fin 3) : (r.1 i).1 = 1 := by
    apply Nat.dvd_one.mp
    calc
      (r.1 i).1 ∣ ∏ j : Fin 3, (r.1 j).1 :=
        Finset.dvd_prod_of_mem (fun j : Fin 3 => (r.1 j).1) (Finset.mem_univ i)
      _ = 1 := r.2
  have hfac (i : Fin 3) :
      (fs.get i) ((r.1 i).1 * (m.1 i).1) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hcoeff) i (Finset.mem_univ i)
  have ha₁ : a₁ (m.1 0).1 ≠ 0 := by
    have h := hfac 0
    rw [hrone 0] at h
    simpa [fs] using h
  have ha₂ : a₂ (m.1 1).1 ≠ 0 := by
    have h := hfac 1
    rw [hrone 1] at h
    simpa [fs] using h
  have ha₃ : a₃ (m.1 2).1 ≠ 0 := by
    have h := hfac 2
    rw [hrone 2] at h
    simpa [fs] using h
  have hm₁ : (m.1 0).1 ≤ N₁ := h₁ _ ha₁
  have hm₂ : (m.1 1).1 ≤ N₂ := h₂ _ ha₂
  have hm₃ : (m.1 2).1 ≤ N₃ := h₃ _ ha₃
  have htuple :
      (m.1 0).1 * ((m.1 1).1 * (m.1 2).1) = n := by
    have hmprod := m.2
    change (∏ i : Fin 3, (m.1 i).1) = n at hmprod
    rw [Fin.prod_univ_three] at hmprod
    simpa [Nat.mul_assoc] using hmprod
  calc
    n = (m.1 0).1 * ((m.1 1).1 * (m.1 2).1) := htuple.symm
    _ ≤ N₁ * (N₂ * N₃) := Nat.mul_le_mul hm₁ (Nat.mul_le_mul hm₂ hm₃)
    _ = N₁ * N₂ * N₃ := by ring

/-- Reindex the finite sum over a nonunit residue by cancelling its common
gcd with the modulus. -/
theorem finiteResidueMellin_gcd_reindex
    (f : ℕ → ℂ) {a : ℤ} {q P : ℕ} (hq : 0 < q) (s : ℂ) :
    (∑ n ∈ Finset.Icc 1 (Nat.gcd a.natAbs q * P),
      if (n : ZMod q) = (a : ZMod q) then
        f n * (n : ℂ) ^ (-s) else 0) =
    ∑ t ∈ Finset.Icc 1 P,
      if (t : ZMod (q / Nat.gcd a.natAbs q)) =
          ((a / (Nat.gcd a.natAbs q : ℤ)) : ZMod
            (q / Nat.gcd a.natAbs q)) then
        f (Nat.gcd a.natAbs q * t) *
          ((Nat.gcd a.natAbs q * t : ℕ) : ℂ) ^ (-s)
      else 0 := by
  classical
  let d : ℕ := Nat.gcd a.natAbs q
  let Q : ℕ := q / d
  let a' : ℤ := a / (d : ℤ)
  let A : Finset ℕ := (Finset.Icc 1 (d * P)).filter
    (fun n => (n : ZMod q) = (a : ZMod q))
  let B : Finset ℕ := (Finset.Icc 1 P).filter
    (fun t => (t : ZMod Q) = (a' : ZMod Q))
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right _ hq
  have hqposD : 0 < Q := by
    dsimp [Q, d]
    exact Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right _ _)) hdpos
  have hleft :
      (∑ n ∈ Finset.Icc 1 (d * P),
        if (n : ZMod q) = (a : ZMod q) then
          f n * (n : ℂ) ^ (-s) else 0) =
      ∑ n ∈ A, f n * (n : ℂ) ^ (-s) := by
    simp [A, Finset.sum_filter]
  have hright :
      (∑ t ∈ Finset.Icc 1 P,
        if (t : ZMod Q) = (a' : ZMod Q) then
          f (d * t) * ((d * t : ℕ) : ℂ) ^ (-s) else 0) =
      ∑ t ∈ B, f (d * t) * ((d * t : ℕ) : ℂ) ^ (-s) := by
    simp [B, Finset.sum_filter]
  rw [hleft, hright]
  apply Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hnCongr⟩
    rcases Finset.mem_Icc.mp hnI with ⟨hnLower, hnUpper⟩
    have hgc : Nat.gcd n q = d := by
      dsimp [d]
      exact residueGcd_eq_of_congruent hnCongr
    have hndvd : d ∣ n := by rw [← hgc]; exact Nat.gcd_dvd_left _ _
    have hntpos : 0 < n / d := Nat.div_pos
      (Nat.le_of_dvd (by omega) hndvd) hdpos
    have hfactor : d * (n / d) = n := Nat.mul_div_cancel' hndvd
    have hnquot : (n / d) ≤ P := by
      have hmul : d * (n / d) ≤ d * P := by simpa [hfactor] using hnUpper
      exact le_of_mul_le_mul_left hmul hdpos
    have hquotCongr :=
      (residueGcd_congruence_quotient_iff hq hndvd).mp hnCongr
    simp only [B, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hntpos, hnquot⟩,
      by simpa only [Q, a', d, Int.cast_natCast] using hquotCongr⟩
  · intro n hn m hm hnm
    have hndvd : d ∣ n := by
      rcases Finset.mem_filter.mp hn with ⟨_, hnCongr⟩
      change Nat.gcd a.natAbs q ∣ n
      rw [← residueGcd_eq_of_congruent hnCongr]
      exact Nat.gcd_dvd_left _ _
    have hmdvd : d ∣ m := by
      rcases Finset.mem_filter.mp hm with ⟨_, hmCongr⟩
      change Nat.gcd a.natAbs q ∣ m
      rw [← residueGcd_eq_of_congruent hmCongr]
      exact Nat.gcd_dvd_left _ _
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' hndvd).symm
      _ = d * (m / d) := congrArg (fun t => d * t) hnm
      _ = m := Nat.mul_div_cancel' hmdvd
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨htI, htCongr⟩
    rcases Finset.mem_Icc.mp htI with ⟨htLower, htUpper⟩
    have hdt : d ∣ d * t := ⟨t, rfl⟩
    have hquot : (d * t) / d = t := Nat.mul_div_right t hdpos
    have hresCongr :=
      (residueGcd_congruence_quotient_iff hq hdt).mpr
        (by simpa [Q, a', d, hquot] using htCongr)
    have hnLower : 1 ≤ d * t := by
      exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left t hdpos)
    have hnUpper : d * t ≤ d * P := Nat.mul_le_mul_left d htUpper
    refine ⟨d * t, Finset.mem_filter.mpr ?_, ?_⟩
    · refine ⟨Finset.mem_Icc.mpr ⟨hnLower, hnUpper⟩, ?_⟩
      simpa [hquot] using hresCongr
    · simpa [hquot]
  · intro n hn
    have hndvd : d ∣ n := by
      rcases Finset.mem_filter.mp hn with ⟨_, hnCongr⟩
      change Nat.gcd a.natAbs q ∣ n
      rw [← residueGcd_eq_of_congruent hnCongr]
      exact Nat.gcd_dvd_left _ _
    have hfactor : d * (n / d) = n := Nat.mul_div_cancel' hndvd
    rw [hfactor]

/-- Positive triples whose product is at most `P`, used to flatten the
dependent sum over a product bound and its ordered factor tuples. -/
def boundedPositiveTriple (P : ℕ) :=
  {m : Fin 3 → PositiveInteger // ∏ i : Fin 3, (m i).1 ≤ P}

theorem boundedPositiveTriple_finite (P : ℕ) :
    Finite (boundedPositiveTriple P) := by
  classical
  apply Finite.of_injective
    (fun m : boundedPositiveTriple P => fun i : Fin 3 =>
      (⟨(m.1 i).1, by
        have hle : (m.1 i).1 ≤ ∏ j : Fin 3, (m.1 j).1 := by
          simpa using
            (Finset.single_le_prod (s := Finset.univ)
              (f := fun j : Fin 3 => (m.1 j).1)
              (fun j hj => Nat.one_le_iff_ne_zero.mpr
                (Nat.ne_of_gt (m.1 j).2)) (Finset.mem_univ i))
        exact Nat.lt_succ_of_le (le_trans hle m.2)⟩ : Fin (P + 1)))
  intro m n h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg Fin.val (congrFun h i)

noncomputable instance boundedPositiveTriple_fintype (P : ℕ) :
    Fintype (boundedPositiveTriple P) := by
  haveI : Finite (boundedPositiveTriple P) := boundedPositiveTriple_finite P
  exact Fintype.ofFinite _

private noncomputable def flattenBoundedPositiveTriple (P : ℕ) :
    (Σ t : {t : ℕ // t ∈ Finset.Icc 1 P}, divisorFactorTuples 3 t.1) ≃
      boundedPositiveTriple P := by
  classical
  refine
    { toFun := fun x => ⟨x.2.1, ?_⟩
      invFun := fun m => ?_
      left_inv := ?_
      right_inv := ?_ }
  · calc
      ∏ i : Fin 3, (x.2.1 i).1 = x.1.1 := x.2.2
      _ ≤ P := (Finset.mem_Icc.mp x.1.2).2
  · let t : ℕ := ∏ i : Fin 3, (m.1 i).1
    have htpos : 0 < t := by
      dsimp [t]
      exact Finset.prod_pos fun i hi => (m.1 i).2
    refine ⟨⟨t, Finset.mem_Icc.mpr ⟨htpos, m.2⟩⟩,
      ⟨m.1, ?_⟩⟩
    rfl
  · rintro ⟨⟨t, ht⟩, m⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact m.2
    · rfl
  · intro m
    apply Subtype.ext
    rfl

private theorem finiteFactorTupleSigmaReindex (P : ℕ)
    (F : ∀ t : ℕ, divisorFactorTuples 3 t → ℂ) :
    (∑ t ∈ Finset.Icc 1 P,
      ∑ m : divisorFactorTuples 3 t, F t m) =
      ∑ m : boundedPositiveTriple P,
        F (((flattenBoundedPositiveTriple P).symm m).1.1)
          ((flattenBoundedPositiveTriple P).symm m).2 := by
  classical
  let T : Finset ℕ := Finset.Icc 1 P
  have hsubtype :
      (∑ t : {t : ℕ // t ∈ T},
        ∑ m : divisorFactorTuples 3 t.1, F t.1 m) =
      ∑ t ∈ T, ∑ m : divisorFactorTuples 3 t, F t m := by
    let f : ℕ → ℂ := fun t => ∑ m : divisorFactorTuples 3 t, F t m
    calc
      (∑ t : {t : ℕ // t ∈ T}, f t.1) =
          ∑ t ∈ T.attach, f t.1 := by
            rw [← Finset.attach_eq_univ]
      _ = ∑ t ∈ T, f t := Finset.sum_attach T f
      _ = _ := rfl
  rw [← hsubtype]
  let G : (Σ t : {t : ℕ // t ∈ T}, divisorFactorTuples 3 t.1) → ℂ :=
    fun x => F x.1.1 x.2
  have hsigma :
      (∑ t : {t : ℕ // t ∈ T},
        ∑ m : divisorFactorTuples 3 t.1, F t.1 m) =
        ∑ x : Σ t : {t : ℕ // t ∈ T}, divisorFactorTuples 3 t.1, G x := by
    simpa [G] using (Fintype.sum_sigma G).symm
  rw [hsigma]
  exact Fintype.sum_equiv (flattenBoundedPositiveTriple P)
    G
    (fun m => F ((flattenBoundedPositiveTriple P).symm m).1.1
      ((flattenBoundedPositiveTriple P).symm m).2)
    (by
      intro x
      simpa [G] using
        (congrArg (fun y => F y.1.1 y.2)
          (Equiv.symm_apply_apply (flattenBoundedPositiveTriple P) x).symm))

abbrev positiveIntervalIndex (P : ℕ) :=
  {m : ℕ // m ∈ Finset.Icc 1 P}

theorem positiveIntervalIndex_finite (P : ℕ) :
    Finite (positiveIntervalIndex P) := by
  apply Finite.of_injective
    (fun m : positiveIntervalIndex P =>
      (⟨m.1, by
        have hm := Finset.mem_Icc.mp m.2
        omega⟩ : Fin (P + 1)))
  intro m n h
  apply Subtype.ext
  exact congrArg Fin.val h

noncomputable instance positiveIntervalIndex_fintype (P : ℕ) :
    Fintype (positiveIntervalIndex P) := by
  haveI : Finite (positiveIntervalIndex P) := positiveIntervalIndex_finite P
  exact Fintype.ofFinite _

def boundedIntervalTriple (P : ℕ) :=
  {m : Fin 3 → positiveIntervalIndex P //
    ∏ i : Fin 3, (m i).1 ≤ P}

noncomputable instance boundedIntervalTriple_fintype (P : ℕ) :
    Fintype (boundedIntervalTriple P) := by
  classical
  exact Subtype.fintype _

private noncomputable def boundedPositiveIntervalEquiv (P : ℕ) :
    boundedPositiveTriple P ≃ boundedIntervalTriple P where
  toFun m := by
    refine ⟨fun i => ⟨(m.1 i).1, Finset.mem_Icc.mpr ?_⟩, ?_⟩
    · have hcoord : (m.1 i).1 ≤ ∏ j : Fin 3, (m.1 j).1 :=
        Finset.single_le_prod (s := Finset.univ)
          (f := fun j : Fin 3 => (m.1 j).1)
          (fun j hj => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (m.1 j).2)) (Finset.mem_univ i)
      exact ⟨(m.1 i).2, hcoord.trans m.2⟩
    · simpa using m.2
  invFun m := by
    refine ⟨fun i => ⟨(m.1 i).1, ?_⟩, m.2⟩
    have hlow := (Finset.mem_Icc.mp (m.1 i).2).1
    omega
  left_inv m := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv m := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl

private def intervalIndexToPositive (P : ℕ) (m : positiveIntervalIndex P) :
    PositiveInteger :=
  ⟨m.1, by have hm := (Finset.mem_Icc.mp m.2).1; omega⟩

private def intervalBoxToPositive (P : ℕ)
    (m : Fin 3 → positiveIntervalIndex P) : Fin 3 → PositiveInteger :=
  fun i => intervalIndexToPositive P (m i)

private theorem boundedPositiveTriple_sum_eq_intervalBox
    (P : ℕ) (G : (Fin 3 → PositiveInteger) → ℂ)
    (hzero : ∀ m, P < ∏ i : Fin 3, (m i).1 → G m = 0) :
    (∑ m : boundedPositiveTriple P, G m.1) =
      ∑ m : Fin 3 → positiveIntervalIndex P,
        G (intervalBoxToPositive P m) := by
  classical
  let e := boundedPositiveIntervalEquiv P
  have hreindex :
      (∑ m : boundedPositiveTriple P, G m.1) =
        ∑ m : boundedIntervalTriple P,
          G (intervalBoxToPositive P m.1) := by
    exact Fintype.sum_equiv e
      (fun m => G m.1)
      (fun m => G (intervalBoxToPositive P m.1))
      (by
        intro m
        apply congrArg G
        funext i
        apply Subtype.ext
        rfl)
  have hfiltered :
      (∑ m : boundedIntervalTriple P,
        G (intervalBoxToPositive P m.1)) =
      ∑ m : Fin 3 → positiveIntervalIndex P,
        if ∏ i : Fin 3, (m i).1 ≤ P then
          G (intervalBoxToPositive P m) else 0 := by
    simpa [boundedIntervalTriple, Finset.sum_filter] using
      (Finset.sum_subtype_eq_sum_filter
        (s := Finset.univ)
        (p := fun m : Fin 3 → positiveIntervalIndex P =>
          ∏ i : Fin 3, (m i).1 ≤ P)
        (fun m => G (intervalBoxToPositive P m)))
  calc
    (∑ m : boundedPositiveTriple P, G m.1) =
        ∑ m : boundedIntervalTriple P,
          G (intervalBoxToPositive P m.1) := hreindex
    _ = ∑ m : Fin 3 → positiveIntervalIndex P,
          if ∏ i : Fin 3, (m i).1 ≤ P then
            G (intervalBoxToPositive P m) else 0 := hfiltered
    _ = ∑ m : Fin 3 → positiveIntervalIndex P,
          G (intervalBoxToPositive P m) := by
            apply Fintype.sum_congr
            intro m
            by_cases hm : ∏ i : Fin 3, (m i).1 ≤ P
            · simp [hm]
            · have hlt : P < ∏ i : Fin 3, (m i).1 := Nat.lt_of_not_ge hm
              simp [hm, hzero (intervalBoxToPositive P m) hlt]

private theorem sum_positiveIntervalIndex_eq_sum_Icc (P : ℕ)
    (f : positiveIntervalIndex P → ℂ) :
    (∑ m : positiveIntervalIndex P, f m) =
      ∑ m ∈ Finset.Icc 1 P,
        (if h : m ∈ Finset.Icc 1 P then f ⟨m, h⟩ else 0) := by
  classical
  let g : ℕ → ℂ := fun m =>
    if h : m ∈ Finset.Icc 1 P then f ⟨m, h⟩ else 0
  calc
    (∑ m : positiveIntervalIndex P, f m) =
        ∑ m ∈ (Finset.Icc 1 P).attach, f m := by
          have hset :
              (Finset.univ : Finset (positiveIntervalIndex P)) =
                (Finset.Icc 1 P).attach := by
            ext m
            simp
          exact congrArg (fun s : Finset (positiveIntervalIndex P) => s.sum f) hset
    _ = ∑ m ∈ (Finset.Icc 1 P).attach, g m.1 := by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [g, dif_pos m.2]
    _ = ∑ m ∈ Finset.Icc 1 P, g m := Finset.sum_attach _ _
    _ = _ := by rfl

private noncomputable def fin3PiEquiv (α : Type*) :
    (Fin 3 → α) ≃ α × α × α where
  toFun m := (m 0, m 1, m 2)
  invFun p := Fin.cons p.1 (Fin.cons p.2.1 (Fin.cons p.2.2 Fin.elim0))
  left_inv m := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    rfl


/-- The finite Dirichlet polynomial for one allocated factor. The cutoff is
large enough to contain every nonzero term when the original coefficient is
supported below `P`. -/
noncomputable def finiteAllocatedDirichletPolynomial
    (a : ArithmeticFunction ℂ) (r q : ℕ) (S : Finset ℕ)
    {Q : ℕ} (χ : BlueprintCharacter Q) (s : ℂ) : ℂ :=
  ∑ m ∈ S,
    a (r * m) * (if Nat.Coprime m q then 1 else 0) *
      evalInt χ (m : ℤ) * (m : ℂ) ^ (-s)

/-- The three coefficient functions with their labels preserved. -/
def threeArithmeticFactors (a₁ a₂ a₃ : ArithmeticFunction ℂ) :
    Fin 3 → ArithmeticFunction ℂ :=
  Fin.cases a₁ (Fin.cases a₂ (Fin.cases a₃ Fin.elim0))

@[simp] theorem threeArithmeticFactors_zero (a₁ a₂ a₃ : ArithmeticFunction ℂ) :
    threeArithmeticFactors a₁ a₂ a₃ 0 = a₁ := rfl

@[simp] theorem threeArithmeticFactors_one (a₁ a₂ a₃ : ArithmeticFunction ℂ) :
    threeArithmeticFactors a₁ a₂ a₃ 1 = a₂ := rfl

@[simp] theorem threeArithmeticFactors_two (a₁ a₂ a₃ : ArithmeticFunction ℂ) :
    threeArithmeticFactors a₁ a₂ a₃ 2 = a₃ := rfl

private theorem sum_triple_product_separates
    {S₁ S₂ S₃ : Finset ℕ} (f₁ f₂ f₃ : ℕ → ℂ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
      f₁ m₁ * f₂ m₂ * f₃ m₃) =
      (∑ m₁ ∈ S₁, f₁ m₁) *
        (∑ m₂ ∈ S₂, f₂ m₂) *
        (∑ m₃ ∈ S₃, f₃ m₃) := by
  classical
  calc
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        f₁ m₁ * f₂ m₂ * f₃ m₃) =
        ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
          (f₁ m₁ * f₂ m₂) * (∑ m₃ ∈ S₃, f₃ m₃) := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            apply Finset.sum_congr rfl
            intro m₂ hm₂
            rw [← Finset.mul_sum]
    _ = ∑ m₁ ∈ S₁,
          (f₁ m₁ * (∑ m₂ ∈ S₂, f₂ m₂)) *
            (∑ m₃ ∈ S₃, f₃ m₃) := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            calc
              (∑ m₂ ∈ S₂,
                  f₁ m₁ * f₂ m₂ * (∑ m₃ ∈ S₃, f₃ m₃)) =
                  ∑ m₂ ∈ S₂,
                    f₁ m₁ * (f₂ m₂ * (∑ m₃ ∈ S₃, f₃ m₃)) := by
                      apply Finset.sum_congr rfl
                      intro m₂ hm₂
                      ring
              _ = f₁ m₁ *
                    ∑ m₂ ∈ S₂, f₂ m₂ * (∑ m₃ ∈ S₃, f₃ m₃) := by
                      rw [← Finset.mul_sum]
              _ = f₁ m₁ *
                    ((∑ m₂ ∈ S₂, f₂ m₂) *
                      (∑ m₃ ∈ S₃, f₃ m₃)) := by
                      rw [Finset.sum_mul]
              _ = (f₁ m₁ * (∑ m₂ ∈ S₂, f₂ m₂)) *
                    (∑ m₃ ∈ S₃, f₃ m₃) := by ring
    _ = (∑ m₁ ∈ S₁, f₁ m₁) *
          (∑ m₂ ∈ S₂, f₂ m₂) *
          (∑ m₃ ∈ S₃, f₃ m₃) := by
            calc
              (∑ m₁ ∈ S₁,
                  (f₁ m₁ * (∑ m₂ ∈ S₂, f₂ m₂)) *
                    (∑ m₃ ∈ S₃, f₃ m₃)) =
                  ∑ m₁ ∈ S₁,
                    f₁ m₁ * ((∑ m₂ ∈ S₂, f₂ m₂) *
                      (∑ m₃ ∈ S₃, f₃ m₃)) := by
                      apply Finset.sum_congr rfl
                      intro m₁ hm₁
                      ring
              _ = (∑ m₁ ∈ S₁, f₁ m₁) *
                    ((∑ m₂ ∈ S₂, f₂ m₂) *
                      (∑ m₃ ∈ S₃, f₃ m₃)) := by
                      exact (Finset.sum_mul S₁ f₁
                        ((∑ m₂ ∈ S₂, f₂ m₂) *
                          (∑ m₃ ∈ S₃, f₃ m₃))).symm
              _ = (∑ m₁ ∈ S₁, f₁ m₁) *
                    (∑ m₂ ∈ S₂, f₂ m₂) *
                    (∑ m₃ ∈ S₃, f₃ m₃) := by ring

private theorem sum_triple_div
    {S₁ S₂ S₃ : Finset ℕ} (f : ℕ → ℕ → ℕ → ℂ) (z : ℂ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
      f m₁ m₂ m₃ / z) =
      (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        f m₁ m₂ m₃) / z := by
  classical
  calc
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        f m₁ m₂ m₃ / z) =
        ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
          (∑ m₃ ∈ S₃, f m₁ m₂ m₃) / z := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            apply Finset.sum_congr rfl
            intro m₂ hm₂
            symm
            rw [Finset.sum_div]
    _ = ∑ m₁ ∈ S₁,
          (∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃, f m₁ m₂ m₃) / z := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            symm
            rw [Finset.sum_div]
    _ = (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
          f m₁ m₂ m₃) / z := by
            symm
            rw [Finset.sum_div]

private theorem sum_triple_mul_right
    {S₁ S₂ S₃ : Finset ℕ} (f : ℕ → ℕ → ℕ → ℂ) (z : ℂ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
      f m₁ m₂ m₃ * z) =
      (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        f m₁ m₂ m₃) * z := by
  classical
  calc
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        f m₁ m₂ m₃ * z) =
        ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
          (∑ m₃ ∈ S₃, f m₁ m₂ m₃) * z := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            apply Finset.sum_congr rfl
            intro m₂ hm₂
            exact (Finset.sum_mul S₃ (fun m₃ => f m₁ m₂ m₃) z).symm
    _ = ∑ m₁ ∈ S₁,
          (∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃, f m₁ m₂ m₃) * z := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            exact (Finset.sum_mul S₂
              (fun m₂ => ∑ m₃ ∈ S₃, f m₁ m₂ m₃) z).symm
    _ = (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
          f m₁ m₂ m₃) * z := by
            exact (Finset.sum_mul S₁
              (fun m₁ => ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃, f m₁ m₂ m₃) z).symm

private theorem sum_triple_character_comm
    {Q : ℕ} [NeZero Q] {S₁ S₂ S₃ : Finset ℕ}
    (F : BlueprintCharacter Q → ℕ → ℕ → ℕ → ℂ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
      ∑ χ : BlueprintCharacter Q, F χ m₁ m₂ m₃) =
      ∑ χ : BlueprintCharacter Q,
        ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
          F χ m₁ m₂ m₃ := by
  classical
  calc
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        ∑ χ : BlueprintCharacter Q, F χ m₁ m₂ m₃) =
        ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
          ∑ χ : BlueprintCharacter Q, ∑ m₃ ∈ S₃, F χ m₁ m₂ m₃ := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            apply Finset.sum_congr rfl
            intro m₂ hm₂
            rw [Finset.sum_comm]
    _ = ∑ m₁ ∈ S₁, ∑ χ : BlueprintCharacter Q,
          ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃, F χ m₁ m₂ m₃ := by
            apply Finset.sum_congr rfl
            intro m₁ hm₁
            rw [Finset.sum_comm]
    _ = ∑ χ : BlueprintCharacter Q,
          ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
            F χ m₁ m₂ m₃ := by
            rw [Finset.sum_comm]

/-- Exact finite residue-class factorization into three character sums.
The coefficients `cᵢ` may include any allocated coefficient, coprimality
cutoff, and complex power. -/
theorem finiteTripleCharacterFactorization
    {Q : ℕ} (hQ : 0 < Q) (a' : ℤ)
    (ha' : IsCoprime a' (Q : ℤ))
    (S₁ S₂ S₃ : Finset ℕ) (c₁ c₂ c₃ : ℕ → ℂ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
      (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
        then 1 else 0) * c₁ m₁ * c₂ m₂ * c₃ m₃) =
      (∑ χ : BlueprintCharacter Q,
        star (evalInt χ a') *
          (∑ m₁ ∈ S₁, c₁ m₁ * evalInt χ (m₁ : ℤ)) *
          (∑ m₂ ∈ S₂, c₂ m₂ * evalInt χ (m₂ : ℤ)) *
          (∑ m₃ ∈ S₃, c₃ m₃ * evalInt χ (m₃ : ℤ))) /
        (Q.totient : ℂ) := by
  classical
  haveI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hchar (χ : BlueprintCharacter Q) (m₁ m₂ m₃ : ℕ) :
      evalInt χ ((m₁ * m₂ * m₃ : ℕ) : ℤ) =
        evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) * evalInt χ (m₃ : ℤ) := by
    simp [evalInt, Nat.cast_mul, map_mul, mul_assoc]
  have horthTriple (m₁ m₂ m₃ : ℕ) :
      (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
        then (1 : ℂ) else 0) =
        (∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') *
            (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
              evalInt χ (m₃ : ℤ))) / (Q.totient : ℂ) := by
    have horth := integer_character_orthogonality_indicator hQ a'
      ((m₁ * m₂ * m₃ : ℕ) : ℤ) ha'
    calc
      (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
          then (1 : ℂ) else 0) =
          (∑ χ : BlueprintCharacter Q,
            star (evalInt χ a') *
              evalInt χ ((m₁ * m₂ * m₃ : ℕ) : ℤ)) /
            (Q.totient : ℂ) := by
              simpa only [Int.cast_natCast] using horth
      _ = _ := by
            congr 1
            apply Finset.sum_congr rfl
            intro χ hχ
            rw [hchar]
  have hsumDivMul (t : Finset (BlueprintCharacter Q))
      (F : BlueprintCharacter Q → ℂ) (w : ℂ) :
      ((∑ χ ∈ t, F χ) / (Q.totient : ℂ)) * w =
        ∑ χ ∈ t, (F χ * w) / (Q.totient : ℂ) := by
    rw [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  calc
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
        (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
          then 1 else 0) * c₁ m₁ * c₂ m₂ * c₃ m₃) =
        ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
          ∑ χ : BlueprintCharacter Q,
            (star (evalInt χ a') *
              (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                evalInt χ (m₃ : ℤ)) *
              (c₁ m₁ * c₂ m₂ * c₃ m₃)) / (Q.totient : ℂ) := by
          apply Finset.sum_congr rfl
          intro m₁ hm₁
          apply Finset.sum_congr rfl
          intro m₂ hm₂
          apply Finset.sum_congr rfl
          intro m₃ hm₃
          rw [horthTriple]
          simpa [mul_assoc] using
            (hsumDivMul Finset.univ
              (fun χ => star (evalInt χ a') *
                (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                  evalInt χ (m₃ : ℤ)))
              (c₁ m₁ * c₂ m₂ * c₃ m₃))
    _ = ∑ χ : BlueprintCharacter Q,
          ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
            (star (evalInt χ a') *
              (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                evalInt χ (m₃ : ℤ)) *
              (c₁ m₁ * c₂ m₂ * c₃ m₃)) / (Q.totient : ℂ) := by
          exact sum_triple_character_comm (Q := Q)
            (fun χ m₁ m₂ m₃ =>
              (star (evalInt χ a') *
                (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                  evalInt χ (m₃ : ℤ)) *
                (c₁ m₁ * c₂ m₂ * c₃ m₃)) / (Q.totient : ℂ))
    _ = ∑ χ : BlueprintCharacter Q,
          (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
            (star (evalInt χ a') *
              (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                evalInt χ (m₃ : ℤ)) *
              (c₁ m₁ * c₂ m₂ * c₃ m₃))) / (Q.totient : ℂ) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          exact sum_triple_div
            (fun m₁ m₂ m₃ =>
              star (evalInt χ a') *
                (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                  evalInt χ (m₃ : ℤ)) *
                (c₁ m₁ * c₂ m₂ * c₃ m₃)) (Q.totient : ℂ)
    _ = ∑ χ : BlueprintCharacter Q,
          (star (evalInt χ a') *
            (∑ m₁ ∈ S₁, c₁ m₁ * evalInt χ (m₁ : ℤ)) *
            (∑ m₂ ∈ S₂, c₂ m₂ * evalInt χ (m₂ : ℤ)) *
            (∑ m₃ ∈ S₃, c₃ m₃ * evalInt χ (m₃ : ℤ))) /
            (Q.totient : ℂ) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          congr 1
          calc
            (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
                star (evalInt χ a') *
                  (evalInt χ (m₁ : ℤ) * evalInt χ (m₂ : ℤ) *
                    evalInt χ (m₃ : ℤ)) *
                  (c₁ m₁ * c₂ m₂ * c₃ m₃)) =
                ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
                  ((c₁ m₁ * evalInt χ (m₁ : ℤ)) *
                    (c₂ m₂ * evalInt χ (m₂ : ℤ)) *
                    (c₃ m₃ * evalInt χ (m₃ : ℤ))) *
                    star (evalInt χ a') := by
                      apply Finset.sum_congr rfl
                      intro m₁ hm₁
                      apply Finset.sum_congr rfl
                      intro m₂ hm₂
                      apply Finset.sum_congr rfl
                      intro m₃ hm₃
                      ring
            _ = (∑ m₁ ∈ S₁, c₁ m₁ * evalInt χ (m₁ : ℤ)) *
                  (∑ m₂ ∈ S₂, c₂ m₂ * evalInt χ (m₂ : ℤ)) *
                  (∑ m₃ ∈ S₃, c₃ m₃ * evalInt χ (m₃ : ℤ)) *
                  star (evalInt χ a') := by
                    calc
                      (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
                          ((c₁ m₁ * evalInt χ (m₁ : ℤ)) *
                            (c₂ m₂ * evalInt χ (m₂ : ℤ)) *
                            (c₃ m₃ * evalInt χ (m₃ : ℤ))) *
                            star (evalInt χ a')) =
                          (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
                            (c₁ m₁ * evalInt χ (m₁ : ℤ)) *
                              (c₂ m₂ * evalInt χ (m₂ : ℤ)) *
                              (c₃ m₃ * evalInt χ (m₃ : ℤ))) *
                            star (evalInt χ a') := by
                              exact sum_triple_mul_right _ _
                      _ = (∑ m₁ ∈ S₁, c₁ m₁ * evalInt χ (m₁ : ℤ)) *
                            (∑ m₂ ∈ S₂, c₂ m₂ * evalInt χ (m₂ : ℤ)) *
                            (∑ m₃ ∈ S₃, c₃ m₃ * evalInt χ (m₃ : ℤ)) *
                            star (evalInt χ a') := by
                              rw [sum_triple_product_separates]
            _ = star (evalInt χ a') *
                  (∑ m₁ ∈ S₁, c₁ m₁ * evalInt χ (m₁ : ℤ)) *
                  (∑ m₂ ∈ S₂, c₂ m₂ * evalInt χ (m₂ : ℤ)) *
                  (∑ m₃ ∈ S₃, c₃ m₃ * evalInt χ (m₃ : ℤ)) := by ring
    _ = (∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') *
            (∑ m₁ ∈ S₁, c₁ m₁ * evalInt χ (m₁ : ℤ)) *
            (∑ m₂ ∈ S₂, c₂ m₂ * evalInt χ (m₂ : ℤ)) *
            (∑ m₃ ∈ S₃, c₃ m₃ * evalInt χ (m₃ : ℤ))) /
            (Q.totient : ℂ) := by
          symm
          rw [Finset.sum_div]

/-- The finite character expansion after a fixed gcd allocation, with the
Dirichlet monomial split into its three labeled factors. -/
theorem finiteAllocatedTripleCharacterFactorization
    {Q : ℕ} (hQ : 0 < Q) (a' : ℤ)
    (ha' : IsCoprime a' (Q : ℤ))
    (S₁ S₂ S₃ : Finset ℕ)
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    (r₁ q₁ r₂ q₂ r₃ q₃ d : ℕ)
    (s : ℂ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
      (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
        then (1 : ℂ) else 0) *
        ((d : ℂ) ^ (-s) *
          (a₁ (r₁ * m₁) * (if Nat.Coprime m₁ q₁ then 1 else 0) *
            (m₁ : ℂ) ^ (-s)) *
          (a₂ (r₂ * m₂) * (if Nat.Coprime m₂ q₂ then 1 else 0) *
            (m₂ : ℂ) ^ (-s)) *
          (a₃ (r₃ * m₃) * (if Nat.Coprime m₃ q₃ then 1 else 0) *
            (m₃ : ℂ) ^ (-s)))) =
      ((d : ℂ) ^ (-s) / (Q.totient : ℂ)) *
        ∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') *
            finiteAllocatedDirichletPolynomial a₁ r₁ q₁ S₁ χ s *
            finiteAllocatedDirichletPolynomial a₂ r₂ q₂ S₂ χ s *
            finiteAllocatedDirichletPolynomial a₃ r₃ q₃ S₃ χ s := by
  classical
  let c₁ : ℕ → ℂ := fun m =>
    a₁ (r₁ * m) * (if Nat.Coprime m q₁ then 1 else 0) * (m : ℂ) ^ (-s)
  let c₂ : ℕ → ℂ := fun m =>
    a₂ (r₂ * m) * (if Nat.Coprime m q₂ then 1 else 0) * (m : ℂ) ^ (-s)
  let c₃ : ℕ → ℂ := fun m =>
    a₃ (r₃ * m) * (if Nat.Coprime m q₃ then 1 else 0) * (m : ℂ) ^ (-s)
  have hsep := finiteTripleCharacterFactorization hQ a' ha'
    S₁ S₂ S₃ c₁ c₂ c₃
  have hpoly₁ (χ : BlueprintCharacter Q) :
      (∑ m ∈ S₁, c₁ m * evalInt χ (m : ℤ)) =
        finiteAllocatedDirichletPolynomial a₁ r₁ q₁ S₁ χ s := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [c₁, finiteAllocatedDirichletPolynomial]
    ring
  have hpoly₂ (χ : BlueprintCharacter Q) :
      (∑ m ∈ S₂, c₂ m * evalInt χ (m : ℤ)) =
        finiteAllocatedDirichletPolynomial a₂ r₂ q₂ S₂ χ s := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [c₂, finiteAllocatedDirichletPolynomial]
    ring
  have hpoly₃ (χ : BlueprintCharacter Q) :
      (∑ m ∈ S₃, c₃ m * evalInt χ (m : ℤ)) =
        finiteAllocatedDirichletPolynomial a₃ r₃ q₃ S₃ χ s := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [c₃, finiteAllocatedDirichletPolynomial]
    ring
  calc
    _ = (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
          (if (a' : ZMod Q) = ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
            then 1 else 0) * c₁ m₁ * c₂ m₂ * c₃ m₃) * (d : ℂ) ^ (-s) := by
            calc
              _ = (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∑ m₃ ∈ S₃,
                    ((if (a' : ZMod Q) =
                        ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
                      then 1 else 0) * c₁ m₁ * c₂ m₂ * c₃ m₃) *
                      (d : ℂ) ^ (-s)) := by
                    apply Finset.sum_congr rfl
                    intro m₁ hm₁
                    apply Finset.sum_congr rfl
                    intro m₂ hm₂
                    apply Finset.sum_congr rfl
                    intro m₃ hm₃
                    simp only [c₁, c₂, c₃]
                    ring
              _ = _ := sum_triple_mul_right
                    (fun m₁ m₂ m₃ =>
                      (if (a' : ZMod Q) =
                        ((m₁ * m₂ * m₃ : ℕ) : ZMod Q)
                       then 1 else 0) * c₁ m₁ * c₂ m₂ * c₃ m₃)
                    ((d : ℂ) ^ (-s))
    _ = _ := by
      rw [hsep]
      simp_rw [hpoly₁, hpoly₂, hpoly₃]
      ring

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.finiteTripleCharacterFactorization
#print axioms FractionalPrimes.Literature.Twisted.positiveNatCpow_mul
