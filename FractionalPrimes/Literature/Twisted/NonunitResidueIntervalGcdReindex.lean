module

public import FractionalPrimes.Literature.Twisted.NonunitTripleCharacterFactorization

/-!
# Gcd reindexing for a nonunit residue in a real interval

The source's scalar nonunit-residue reduction needs the same gcd cancellation
as the triple-polynomial identity, but on an arbitrary half-open real
interval.  The existing finite Mellin reindexing uses a product cutoff; this
lemma keeps the two real endpoints and their floor conventions explicit.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Twisted

/-- Reindex a residue-class sum by its common gcd with the modulus.  The
half-open interval `(u,v]` is represented by `Ioc (floor u) (floor v)` on
positive integers, and the reduced interval has endpoints divided by the
same gcd. -/
theorem finiteResidueInterval_gcd_reindex
    (F : ℕ → ℂ) {q b : ℕ} (hq : 0 < q) (hb : b < q)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
      if n % q = b then F n else 0) =
    ∑ m ∈ Finset.Ioc
        (Nat.floor (u / (Nat.gcd b q : ℝ)))
        (Nat.floor (v / (Nat.gcd b q : ℝ))),
      if m % (q / Nat.gcd b q) = b / Nat.gcd b q then
        F (Nat.gcd b q * m) else 0 := by
  classical
  let d := Nat.gcd b q
  let Q := q / d
  let b' := b / d
  let A := (Finset.Ioc (Nat.floor u) (Nat.floor v)).filter
    (fun n => n % q = b)
  let B := (Finset.Ioc (Nat.floor (u / (d : ℝ)))
      (Nat.floor (v / (d : ℝ)))).filter (fun m => m % Q = b')
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_right b hq
  have hdq : d ∣ q := by dsimp [d]; exact Nat.gcd_dvd_right b q
  have hdb : d ∣ b := by dsimp [d]; exact Nat.gcd_dvd_left b q
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos
  have hqFactor : d * Q = q := by
    dsimp [Q]
    exact Nat.mul_div_cancel' hdq
  have hbFactor : d * b' = b := by
    dsimp [b']
    exact Nat.mul_div_cancel' hdb
  have hb'lt : b' < Q := by
    dsimp [b', Q]
    have hmul : (b / Nat.gcd b q) * Nat.gcd b q <
        (q / Nat.gcd b q) * Nat.gcd b q := by
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left b q),
        Nat.div_mul_cancel (Nat.gcd_dvd_right b q)]
      exact hb
    exact (Nat.mul_lt_mul_right hdpos).mp hmul
  have hleft :
      (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        if n % q = b then F n else 0) = ∑ n ∈ A, F n := by
    dsimp [A]
    rw [← Finset.sum_filter]
  have hright :
      (∑ m ∈ Finset.Ioc (Nat.floor (u / (d : ℝ)))
          (Nat.floor (v / (d : ℝ))),
        if m % Q = b' then F (d * m) else 0) =
        ∑ m ∈ B, F (d * m) := by
    dsimp [B]
    rw [← Finset.sum_filter]
  rw [hleft, hright]
  apply Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hnres⟩
    have hnI' := Finset.mem_Ioc.mp hnI
    have hmod : n ≡ b [MOD q] := by
      change n % q = b % q
      rw [Nat.mod_eq_of_lt hb]
      exact hnres
    have hmodD : n ≡ b [MOD d] := Nat.ModEq.of_dvd hdq hmod
    have hnmodD : n % d = 0 := by
      change n % d = b % d at hmodD
      rw [Nat.mod_eq_zero_of_dvd hdb] at hmodD
      exact hmodD
    have hndvd : d ∣ n := Nat.dvd_of_mod_eq_zero hnmodD
    have hnFactor : n = d * (n / d) :=
      (Nat.mul_div_cancel' hndvd).symm
    have hmodMul : d * (n / d) ≡ d * b' [MOD d * Q] := by
      change (d * (n / d)) % (d * Q) = (d * b') % (d * Q)
      have hmod' : n % (d * Q) = (d * b') % (d * Q) := by
        rw [hqFactor, hbFactor]
        exact hmod
      calc
        (d * (n / d)) % (d * Q) = n % (d * Q) :=
          (congrArg (fun k : ℕ => k % (d * Q)) hnFactor).symm
        _ = (d * b') % (d * Q) := hmod'
    have hquotMod : n / d ≡ b' [MOD Q] := by
      exact (Nat.ModEq.mul_left_cancel_iff' (Nat.ne_of_gt hdpos)).mp
        (by simpa [Nat.mul_assoc] using hmodMul)
    have hnquotRes : n / d % Q = b' := by
      have hquotMod' : n / d % Q = b' % Q := hquotMod
      rw [Nat.mod_eq_of_lt hb'lt] at hquotMod'
      exact hquotMod'
    have huDiv : 0 ≤ u / (d : ℝ) := div_nonneg hu (Nat.cast_nonneg d)
    have hvNonneg : 0 ≤ v := le_trans hu huv
    have hvDiv : 0 ≤ v / (d : ℝ) := div_nonneg hvNonneg (Nat.cast_nonneg d)
    have huReal : u < (n : ℝ) := (Nat.floor_lt hu).1 hnI'.1
    have hvReal : (n : ℝ) ≤ v := (Nat.le_floor_iff hvNonneg).1 hnI'.2
    have hcastFactor : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      calc
        (n : ℝ) = ((d * (n / d) : ℕ) : ℝ) := by exact_mod_cast hnFactor
        _ = (d : ℝ) * ((n / d : ℕ) : ℝ) := by push_cast; ring
    have hlowReal : u / (d : ℝ) < ((n / d : ℕ) : ℝ) := by
      apply (div_lt_iff₀ (by exact_mod_cast hdpos)).2
      nlinarith [huReal, hcastFactor]
    have hhighReal : ((n / d : ℕ) : ℝ) ≤ v / (d : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hdpos)).2
      nlinarith [hvReal, hcastFactor]
    have hlowNat : Nat.floor (u / (d : ℝ)) < n / d :=
      (Nat.floor_lt huDiv).2 hlowReal
    have hhighNat : n / d ≤ Nat.floor (v / (d : ℝ)) :=
      (Nat.le_floor_iff hvDiv).2 hhighReal
    change n / d ∈ B
    dsimp [B]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hlowNat, hhighNat⟩, hnquotRes⟩
  · intro n hn m hm hEq
    have hnres : n % q = b := (Finset.mem_filter.mp hn).2
    have hmod : n ≡ b [MOD q] := by
      change n % q = b % q
      rw [Nat.mod_eq_of_lt hb]
      exact hnres
    have hmodD : n ≡ b [MOD d] := Nat.ModEq.of_dvd hdq hmod
    have hnmodD : n % d = 0 := by
      change n % d = b % d at hmodD
      rw [Nat.mod_eq_zero_of_dvd hdb] at hmodD
      exact hmodD
    have hndvd : d ∣ n := Nat.dvd_of_mod_eq_zero hnmodD
    have hmres : m % q = b := (Finset.mem_filter.mp hm).2
    have hmodm : m ≡ b [MOD q] := by
      change m % q = b % q
      rw [Nat.mod_eq_of_lt hb]
      exact hmres
    have hmodmD : m ≡ b [MOD d] := Nat.ModEq.of_dvd hdq hmodm
    have hmmodD : m % d = 0 := by
      change m % d = b % d at hmodmD
      rw [Nat.mod_eq_zero_of_dvd hdb] at hmodmD
      exact hmodmD
    have hmdvd : d ∣ m := Nat.dvd_of_mod_eq_zero hmmodD
    have hnFactor : n = d * (n / d) :=
      (Nat.mul_div_cancel' hndvd).symm
    have hquo : n / d = m / d := hEq
    calc
      n = d * (n / d) := hnFactor
      _ = d * (m / d) := congrArg (fun x : ℕ => d * x) hquo
      _ = m := Nat.mul_div_cancel' hmdvd
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmI, hmres⟩
    have hmI' := Finset.mem_Ioc.mp hmI
    let n := d * m
    have hmquot : n / d = m := by
      dsimp [n]
      exact Nat.mul_div_cancel_left m hdpos
    have hmodReduced : m ≡ b' [MOD Q] := by
      change m % Q = b' % Q
      rw [Nat.mod_eq_of_lt hb'lt]
      exact hmres
    have hmodFull : n ≡ b [MOD q] := by
      have hmul := Nat.ModEq.mul_left' d hmodReduced
      simpa [n, hqFactor, hbFactor, Nat.mul_assoc] using hmul
    have hnres : n % q = b := by
      change n % q = b % q at hmodFull
      rw [Nat.mod_eq_of_lt hb] at hmodFull
      exact hmodFull
    have huDiv : 0 ≤ u / (d : ℝ) := div_nonneg hu (Nat.cast_nonneg d)
    have hvNonneg : 0 ≤ v := le_trans hu huv
    have hvDiv : 0 ≤ v / (d : ℝ) := div_nonneg hvNonneg (Nat.cast_nonneg d)
    have hlowDivReal : u / (d : ℝ) < (m : ℝ) :=
      (Nat.floor_lt huDiv).1 hmI'.1
    have hhighDivReal : (m : ℝ) ≤ v / (d : ℝ) :=
      (Nat.le_floor_iff hvDiv).1 hmI'.2
    have hcastFactor : (n : ℝ) = (d : ℝ) * (m : ℝ) := by
      dsimp [n]
      push_cast
      ring
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
    have hlowReal : u < (n : ℝ) := by
      apply (div_lt_iff₀ hdR).1 at hlowDivReal
      nlinarith [hlowDivReal, hcastFactor]
    have hhighReal : (n : ℝ) ≤ v := by
      apply (le_div_iff₀ hdR).1 at hhighDivReal
      nlinarith [hhighDivReal, hcastFactor]
    have hlowNat : Nat.floor u < n := (Nat.floor_lt hu).2 hlowReal
    have hhighNat : n ≤ Nat.floor v := (Nat.le_floor_iff hvNonneg).2 hhighReal
    have hnA : n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v) :=
      Finset.mem_Ioc.mpr ⟨hlowNat, hhighNat⟩
    refine ⟨n, Finset.mem_filter.mpr ⟨hnA, hnres⟩, ?_⟩
    exact hmquot
  · intro n hn
    have hnres : n % q = b := (Finset.mem_filter.mp hn).2
    have hmod : n ≡ b [MOD q] := by
      change n % q = b % q
      rw [Nat.mod_eq_of_lt hb]
      exact hnres
    have hmodD : n ≡ b [MOD d] := Nat.ModEq.of_dvd hdq hmod
    have hnmodD : n % d = 0 := by
      change n % d = b % d at hmodD
      rw [Nat.mod_eq_zero_of_dvd hdb] at hmodD
      exact hmodD
    have hndvd : d ∣ n := Nat.dvd_of_mod_eq_zero hnmodD
    have hnFactor : n = d * (n / d) :=
      (Nat.mul_div_cancel' hndvd).symm
    exact congrArg F hnFactor

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.finiteResidueInterval_gcd_reindex
