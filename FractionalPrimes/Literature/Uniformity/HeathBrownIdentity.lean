module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

/-!
# Exact truncated convolution identities

This file formalizes the exact Möbius and von Mangoldt identities in
blueprint item `lu:hb-identity`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open Finset

noncomputable section

/-- The Möbius function truncated at the real cutoff `z`. -/
def truncatedMobius (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ z then (ArithmeticFunction.moebius n : ℝ) else 0, by
    simp [ArithmeticFunction.moebius]
  ⟩

@[simp]
theorem truncatedMobius_apply_of_le {z : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ z) :
    truncatedMobius z n = (ArithmeticFunction.moebius n : ℝ) := by
  simp [truncatedMobius, hn]

@[simp]
theorem truncatedMobius_apply_of_not_le {z : ℝ} {n : ℕ} (hn : ¬ (n : ℝ) ≤ z) :
    truncatedMobius z n = 0 := by
  simp [truncatedMobius, hn]

/-- The error factor `1 - 1 * μ_z` in the finite geometric identity. -/
def heathBrownError (z : ℝ) : ArithmeticFunction ℝ :=
  1 - (ArithmeticFunction.zeta * truncatedMobius z)

private theorem sum_Icc_one_sub_eq_range {R : Type*} [AddCommMonoid R]
    (L : ℕ) (f : ℕ → R) :
    (∑ r ∈ Finset.Icc 1 L, f (r - 1)) = ∑ k ∈ Finset.range L, f k := by
  classical
  apply Finset.sum_bij (fun r _ => r - 1)
  · intro r hr
    simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
    omega
  · intro r hr s hs hrs
    simp only [Finset.mem_Icc] at hr hs
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨k + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · simp
  · intro r hr
    rfl

private theorem geometricBinomialSumRange {R : Type*} [CommRing R]
    (x : R) (L : ℕ) :
    (∑ j ∈ Finset.range L, (1 - x) ^ j) =
      ∑ k ∈ Finset.range L,
        (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hfirst :
        (∑ k ∈ Finset.range (L + 1),
          (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k) =
          ∑ k ∈ Finset.range L,
            (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k := by
      rw [Finset.sum_range_succ]
      simp
    have hsecond :
        (∑ k ∈ Finset.range (L + 1),
          (-1 : R) ^ k * (Nat.choose L k : R) * x ^ k) = (1 - x) ^ L := by
      calc
        (∑ k ∈ Finset.range (L + 1),
            (-1 : R) ^ k * (Nat.choose L k : R) * x ^ k) =
            ∑ k ∈ Finset.range (L + 1),
              (-x) ^ k * (1 : R) ^ (L - k) * (Nat.choose L k : R) := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [neg_pow, one_pow]
                ring
        _ = (-x + 1) ^ L := (add_pow (-x) (1 : R) L).symm
        _ = (1 - x) ^ L := by congr 1; ring
    have hstep :
        (∑ k ∈ Finset.range (L + 1),
          (-1 : R) ^ k * (Nat.choose (L + 1) (k + 1) : R) * x ^ k) =
          (∑ k ∈ Finset.range (L + 1),
            (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k) +
            (∑ k ∈ Finset.range (L + 1),
              (-1 : R) ^ k * (Nat.choose L k : R) * x ^ k) := by
      calc
        (∑ k ∈ Finset.range (L + 1),
            (-1 : R) ^ k * (Nat.choose (L + 1) (k + 1) : R) * x ^ k) =
            ∑ k ∈ Finset.range (L + 1),
              ((-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k +
                (-1 : R) ^ k * (Nat.choose L k : R) * x ^ k) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [Nat.choose_succ_succ]
                  push_cast
                  ring
        _ = (∑ k ∈ Finset.range (L + 1),
              (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k) +
              (∑ k ∈ Finset.range (L + 1),
                (-1 : R) ^ k * (Nat.choose L k : R) * x ^ k) :=
              Finset.sum_add_distrib
    have hstep' :
        (∑ k ∈ Finset.range (L + 1),
          (-1 : R) ^ k * (Nat.choose (L + 1) (k + 1) : R) * x ^ k) =
          (∑ k ∈ Finset.range L,
            (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k) +
            (1 - x) ^ L := by
      rw [hstep, hfirst, hsecond]
    rw [Finset.sum_range_succ, ih]
    exact hstep'.symm

private theorem geometricBinomialSum {R : Type*} [CommRing R]
    (x : R) (L : ℕ) :
    (∑ j ∈ Finset.range L, (1 - x) ^ j) =
      ∑ r ∈ Finset.Icc 1 L,
        (-1 : R) ^ (r - 1) * (Nat.choose L r : R) * x ^ (r - 1) := by
  let f : ℕ → R := fun k =>
    (-1 : R) ^ k * (Nat.choose L (k + 1) : R) * x ^ k
  symm
  calc
    (∑ r ∈ Finset.Icc 1 L,
        (-1 : R) ^ (r - 1) * (Nat.choose L r : R) * x ^ (r - 1)) =
        ∑ r ∈ Finset.Icc 1 L, f (r - 1) := by
          apply Finset.sum_congr rfl
          intro r hr
          simp only [f]
          rw [Nat.sub_add_cancel (Finset.mem_Icc.mp hr).1]
    _ = ∑ k ∈ Finset.range L, f k := sum_Icc_one_sub_eq_range L f
    _ = ∑ j ∈ Finset.range L, (1 - x) ^ j :=
      (geometricBinomialSumRange x L).symm

/-- A convolution term with both factors supported above positive cutoffs
vanishes below the product of those cutoffs. -/
private theorem convolution_eq_zero_below_product
    (f g : ArithmeticFunction ℝ) {A B : ℝ} {n : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hf : ∀ (m : ℕ), (m : ℝ) ≤ A → f m = 0)
    (hg : ∀ (m : ℕ), (m : ℝ) ≤ B → g m = 0)
    (hn : (n : ℝ) ≤ A * B) : (f * g) n = 0 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hfx : (x.1 : ℝ) ≤ A
  · simp [hf x.1 hfx]
  by_cases hgx : (x.2 : ℝ) ≤ B
  · simp [hg x.2 hgx]
  have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hpairReal : (x.1 : ℝ) * (x.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hpair
  have hleft : A < (x.1 : ℝ) := lt_of_not_ge hfx
  have hright : B < (x.2 : ℝ) := lt_of_not_ge hgx
  have hxleft : 0 < (x.1 : ℝ) :=
    lt_trans zero_lt_one (lt_of_le_of_lt hA hleft)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlarge : A * B < (n : ℝ) := by
    calc
      A * B < (x.1 : ℝ) * B := mul_lt_mul_of_pos_right hleft hBpos
      _ < (x.1 : ℝ) * (x.2 : ℝ) := mul_lt_mul_of_pos_left hright hxleft
      _ = (n : ℝ) := hpairReal
  exact (not_lt_of_ge hn hlarge).elim

/-- If the right factor vanishes up to `B`, its convolution with any
arithmetic function vanishes at indices at most `B`. -/
private theorem convolution_eq_zero_of_right_cutoff
    (f g : ArithmeticFunction ℝ) {B : ℝ} {n : ℕ}
    (hn : 0 < n) (hnB : (n : ℝ) ≤ B)
    (hg : ∀ (m : ℕ), (m : ℝ) ≤ B → g m = 0) : (f * g) n = 0 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hrightDvd : x.2 ∣ n := by
    refine ⟨x.1, ?_⟩
    calc
      n = x.1 * x.2 := hpair.symm
      _ = x.2 * x.1 := Nat.mul_comm _ _
  have hrightLe : x.2 ≤ n := Nat.le_of_dvd hn hrightDvd
  have hrightBound : (x.2 : ℝ) ≤ B :=
    le_trans (by exact_mod_cast hrightLe) hnB
  simp [hg x.2 hrightBound]

/-- The error factor vanishes on the initial interval. -/
private theorem heathBrownError_eq_zero_of_le {z : ℝ} {n : ℕ}
    (hn : 0 < n) (hnz : (n : ℝ) ≤ z) : heathBrownError z n = 0 := by
  have hζμ :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  have hrewrite : heathBrownError z =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) - truncatedMobius z) := by
    dsimp [heathBrownError]
    calc
      1 - (ArithmeticFunction.zeta * truncatedMobius z) =
          (ArithmeticFunction.zeta * ArithmeticFunction.moebius) -
            (ArithmeticFunction.zeta * truncatedMobius z) := by rw [hζμ]
      _ = ArithmeticFunction.zeta *
            (ArithmeticFunction.moebius - truncatedMobius z) := by ring
  rw [hrewrite, ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdle : d ≤ n := Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1
  have hdz : (d : ℝ) ≤ z := le_trans (by exact_mod_cast hdle) hnz
  change (ArithmeticFunction.moebius d : ℝ) - truncatedMobius z d = 0
  rw [truncatedMobius_apply_of_le hdz]
  ring

/-- Every positive index up to `z^k` is outside the support of the `k`th
power of the error factor, for `k ≥ 1`. -/
private theorem heathBrownError_pow_eq_zero_of_le {z : ℝ} (hz : 1 ≤ z) :
    ∀ k, 1 ≤ k → ∀ (n : ℕ), 0 < n → (n : ℝ) ≤ z ^ k →
      ((heathBrownError z) ^ k) n = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro hk n hn hnz
      by_cases hk0 : k = 0
      · subst k
        have hnz' : (n : ℝ) ≤ z := by simpa using hnz
        simpa [pow_one] using heathBrownError_eq_zero_of_le hn hnz'
      · have hkpos : 1 ≤ k := by omega
        have hnz' : (n : ℝ) ≤ z ^ k * z := by simpa [pow_succ] using hnz
        have hleft : ∀ (m : ℕ), (m : ℝ) ≤ z ^ k →
            ((heathBrownError z) ^ k) m = 0 := by
          intro m hm
          by_cases hm0 : m = 0
          · simp [hm0]
          · exact ih hkpos m (Nat.pos_of_ne_zero hm0) hm
        have hright : ∀ (m : ℕ), (m : ℝ) ≤ z → heathBrownError z m = 0 := by
          intro m hm
          by_cases hm0 : m = 0
          · simp [hm0]
          · exact heathBrownError_eq_zero_of_le (Nat.pos_of_ne_zero hm0) hm
        rw [pow_succ]
        exact convolution_eq_zero_below_product
          ((heathBrownError z) ^ k) (heathBrownError z)
          (one_le_pow₀ hz) hz hleft hright hnz'

/-- The finite geometric identity in a commutative ring. -/
private theorem finiteGeometricIdentity {R : Type*} [CommRing R]
    (u : R) (L : ℕ) :
    (1 - u) * (∑ j ∈ Finset.range L, u ^ j) + u ^ L = 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (1 - u) * ((∑ j ∈ Finset.range L, u ^ j) + u ^ L) + u ^ L * u =
            (1 - u) * (∑ j ∈ Finset.range L, u ^ j) + u ^ L := by ring
        _ = 1 := ih

private theorem arithmeticFunction_sum_apply {α : Type*} (s : Finset α)
    (f : α → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- The arithmetic-function form of one binomial term. -/
def heathBrownArithmeticTerm (z : ℝ) (L r : ℕ) : ArithmeticFunction ℝ :=
  algebraMap ℝ (ArithmeticFunction ℝ)
      ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
    (truncatedMobius z ^ r *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1))

@[simp]
theorem heathBrownArithmeticTerm_apply (z : ℝ) (L r n : ℕ) :
    heathBrownArithmeticTerm z L r n =
      ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
        ((truncatedMobius z ^ r *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)) n) := by
  rw [heathBrownArithmeticTerm, ← Algebra.smul_def]
  simp [ArithmeticFunction.smul_map]

/-- The binomial expansion of the finite geometric sum as an identity of
arithmetic functions. -/
private theorem heathBrownExpansionFunction (z : ℝ) (L : ℕ) :
    truncatedMobius z * (∑ j ∈ Finset.range L, heathBrownError z ^ j) =
      ∑ r ∈ Finset.Icc 1 L, heathBrownArithmeticTerm z L r := by
  let M : ArithmeticFunction ℝ := truncatedMobius z
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  have hbinomial := geometricBinomialSum (Z * M) L
  have hcoeff (r : ℕ) :
      algebraMap ℝ (ArithmeticFunction ℝ)
          ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) =
        (-1 : ArithmeticFunction ℝ) ^ (r - 1) *
          (Nat.choose L r : ArithmeticFunction ℝ) := by
    simp [map_mul, map_pow]
  calc
    M * (∑ j ∈ Finset.range L, heathBrownError z ^ j) =
        M * (∑ j ∈ Finset.range L, (1 - Z * M) ^ j) := by
          simp [heathBrownError, M, Z]
    _ = M * (∑ r ∈ Finset.Icc 1 L,
          (-1 : ArithmeticFunction ℝ) ^ (r - 1) *
            (Nat.choose L r : ArithmeticFunction ℝ) * (Z * M) ^ (r - 1)) :=
          congrArg (fun f : ArithmeticFunction ℝ => M * f) hbinomial
    _ = ∑ r ∈ Finset.Icc 1 L, heathBrownArithmeticTerm z L r := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          dsimp [heathBrownArithmeticTerm, M, Z]
          have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
          have hMpow :
              truncatedMobius z * truncatedMobius z ^ (r - 1) =
                truncatedMobius z ^ r := by
            calc
              truncatedMobius z * truncatedMobius z ^ (r - 1) =
                  truncatedMobius z ^ (r - 1) * truncatedMobius z := mul_comm _ _
              _ = truncatedMobius z ^ ((r - 1) + 1) :=
                (pow_succ (truncatedMobius z) (r - 1)).symm
              _ = truncatedMobius z ^ r := by rw [Nat.sub_add_cancel hr1]
          rw [hcoeff]
          rw [mul_pow, ← hMpow]
          ring

/-- The exact truncated convolution identity for the Möbius function. -/
theorem heathBrownMobiusIdentity {L : ℕ} (hL : 1 ≤ L) {z : ℝ}
    (hz : 1 ≤ z) {n : ℕ} (hn : 0 < n) (hnz : (n : ℝ) ≤ z ^ L) :
    (ArithmeticFunction.moebius n : ℝ) =
      ∑ r ∈ Finset.Icc 1 L,
        ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
          ((truncatedMobius z ^ r *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)) n) := by
  let M : ArithmeticFunction ℝ := truncatedMobius z
  let U : ArithmeticFunction ℝ := heathBrownError z
  let μR : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  let S : ArithmeticFunction ℝ := ∑ j ∈ Finset.range L, U ^ j
  have hμζ : μR * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hOneSubU : 1 - U = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * M := by
    dsimp [U, heathBrownError, M]
    ring
  have hfactor : μR * (1 - U) = M := by
    rw [hOneSubU, ← mul_assoc, hμζ, one_mul]
  have hgeom := finiteGeometricIdentity U L
  have hgeomS : (1 - U) * S + U ^ L = 1 := by simpa [S] using hgeom
  have hfinite : μR = M * S + μR * U ^ L := by
    calc
      μR = μR * 1 := by simp
      _ = μR * ((1 - U) * S + U ^ L) := by rw [hgeomS]
      _ = μR * (1 - U) * S + μR * U ^ L := by rw [mul_add, ← mul_assoc]
      _ = M * S + μR * U ^ L := by rw [hfactor]
  have herrorPow : ∀ (m : ℕ), (m : ℝ) ≤ z ^ L → (U ^ L) m = 0 := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [hm0, U]
    · exact heathBrownError_pow_eq_zero_of_le hz L hL m
        (Nat.pos_of_ne_zero hm0) hm
  have herrorConvolution := convolution_eq_zero_of_right_cutoff
    μR (U ^ L) hn hnz herrorPow
  have hμeval : μR n = (M * S) n := by
    rw [hfinite]
    simp [herrorConvolution]
  have hexpansion := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (heathBrownExpansionFunction z L)
  rw [hexpansion] at hμeval
  have hμeval' : μR n = ∑ r ∈ Finset.Icc 1 L, heathBrownArithmeticTerm z L r n := by
    calc
      μR n = (∑ r ∈ Finset.Icc 1 L, heathBrownArithmeticTerm z L r) n := hμeval
      _ = ∑ r ∈ Finset.Icc 1 L, heathBrownArithmeticTerm z L r n :=
        arithmeticFunction_sum_apply _ _ _
  calc
    (ArithmeticFunction.moebius n : ℝ) = μR n := rfl
    _ = ∑ r ∈ Finset.Icc 1 L, heathBrownArithmeticTerm z L r n := hμeval'
    _ = ∑ r ∈ Finset.Icc 1 L,
          ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
            ((truncatedMobius z ^ r *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)) n) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact heathBrownArithmeticTerm_apply z L r n

/-- The exact truncated convolution identity for the von Mangoldt function. -/
theorem heathBrownVonMangoldtIdentity {L : ℕ} (hL : 1 ≤ L) {z : ℝ}
    (hz : 1 ≤ z) {n : ℕ} (hn : 0 < n) (hnz : (n : ℝ) ≤ z ^ L) :
    ArithmeticFunction.vonMangoldt n =
      ∑ r ∈ Finset.Icc 1 L,
        ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
          (((truncatedMobius z ^ r *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := by
  let K : ℕ → ArithmeticFunction ℝ := fun r =>
    truncatedMobius z ^ r *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)
  let c : ℕ → ℝ := fun r =>
    (-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)
  have hmobiusAt (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) :
      (ArithmeticFunction.moebius x.1 : ℝ) =
        ∑ r ∈ Finset.Icc 1 L, c r * K r x.1 := by
    have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hxpos : 0 < x.1 :=
      Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
    have hxdvd : x.1 ∣ n := ⟨x.2, hpair.symm⟩
    have hxle : x.1 ≤ n := Nat.le_of_dvd hn hxdvd
    have hxz : (x.1 : ℝ) ≤ z ^ L :=
      le_trans (by exact_mod_cast hxle) hnz
    simpa [K, c] using (heathBrownMobiusIdentity hL hz hxpos hxz)
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt,
    ArithmeticFunction.mul_apply]
  calc
    (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℝ) *
          (ArithmeticFunction.log : ArithmeticFunction ℝ) x.2) =
      ∑ x ∈ n.divisorsAntidiagonal,
        (∑ r ∈ Finset.Icc 1 L, c r * K r x.1) *
          (ArithmeticFunction.log : ArithmeticFunction ℝ) x.2 := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hmobiusAt x hx]
    _ = ∑ x ∈ n.divisorsAntidiagonal,
          ∑ r ∈ Finset.Icc 1 L,
            (c r * K r x.1) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ) x.2 := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_mul]
    _ = ∑ r ∈ Finset.Icc 1 L,
          ∑ x ∈ n.divisorsAntidiagonal,
            (c r * K r x.1) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ) x.2 := by
            rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.Icc 1 L,
          c r * ∑ x ∈ n.divisorsAntidiagonal,
            K r x.1 * (ArithmeticFunction.log : ArithmeticFunction ℝ) x.2 := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = ∑ r ∈ Finset.Icc 1 L, c r *
          ((K r * (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [ArithmeticFunction.mul_apply]
    _ = _ := by
          simp [K, c]

/-- The exact pair of truncated convolution identities in blueprint
item `lu:hb-identity`. -/
theorem heathBrownIdentity {L : ℕ} (hL : 1 ≤ L) {z : ℝ}
    (hz : 1 ≤ z) {n : ℕ} (hn : 0 < n) (hnz : (n : ℝ) ≤ z ^ L) :
    ((ArithmeticFunction.moebius n : ℝ) =
        ∑ r ∈ Finset.Icc 1 L,
          ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
            ((truncatedMobius z ^ r *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)) n)) ∧
      (ArithmeticFunction.vonMangoldt n =
        ∑ r ∈ Finset.Icc 1 L,
          ((-1 : ℝ) ^ (r - 1) * (Nat.choose L r : ℝ)) *
            (((truncatedMobius z ^ r *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r - 1)) *
                (ArithmeticFunction.log : ArithmeticFunction ℝ)) n)) := by
  exact ⟨heathBrownMobiusIdentity hL hz hn hnz,
    heathBrownVonMangoldtIdentity hL hz hn hnz⟩

#print axioms heathBrownMobiusIdentity
#print axioms heathBrownVonMangoldtIdentity
#print axioms heathBrownIdentity

end

end FractionalPrimes.Literature.Uniformity

end
