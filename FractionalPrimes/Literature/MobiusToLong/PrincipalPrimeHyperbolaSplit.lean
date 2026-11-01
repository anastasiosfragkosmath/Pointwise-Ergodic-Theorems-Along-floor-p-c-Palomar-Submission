module

public import FractionalPrimes.Core
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Finite hyperbola split for the von Mangoldt sum

This module records the exact finite real-cutoff decomposition used at the
start of `lml:principal-primes`. The second region retains the strict lower
endpoint `d > floor D` from the source.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius

namespace FractionalPrimes.Literature.MobiusToLong

private def positiveIntegerRange (N : ℕ) : Finset ℕ := Finset.Icc 1 N

private def factorPairRange (N : ℕ) : Finset (Σ _a : ℕ, ℕ) :=
  (positiveIntegerRange N).sigma (fun a => Finset.Icc 1 (N / a))

/-- Reindex a finite sum over divisor antidiagonals as a sum over positive
factor pairs. -/
private theorem sum_divisorsAntidiagonal_below (N : ℕ) (F : ℕ × ℕ → ℝ) :
    (∑ n ∈ positiveIntegerRange N, ∑ p ∈ n.divisorsAntidiagonal, F p) =
      ∑ a ∈ positiveIntegerRange N, ∑ b ∈ Finset.Icc 1 (N / a), F (a, b) := by
  classical
  let S := (positiveIntegerRange N).sigma (fun n => n.divisorsAntidiagonal)
  let T := factorPairRange N
  have hleft :
      (∑ n ∈ positiveIntegerRange N, ∑ p ∈ n.divisorsAntidiagonal, F p) =
        ∑ x ∈ S, F x.2 := by
    dsimp [S]
    rw [Finset.sum_sigma]
  have hright :
      (∑ a ∈ positiveIntegerRange N, ∑ b ∈ Finset.Icc 1 (N / a), F (a, b)) =
        ∑ y ∈ T, F (y.1, y.2) := by
    dsimp [T, factorPairRange]
    rw [Finset.sum_sigma]
  rw [hleft, hright]
  change (∑ x ∈ S, F x.2) = ∑ y ∈ T, F (y.1, y.2)
  refine Finset.sum_bij (fun x _ => ⟨x.2.1, x.2.2⟩) ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hn, hp⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hn0⟩
    have hnI' := Finset.mem_Icc.mp hn
    have haPos : 0 < x.2.1 := by
      by_contra h
      have ha0 : x.2.1 = 0 := Nat.eq_zero_of_not_pos h
      simp [ha0] at hprod
      omega
    have hbPos : 0 < x.2.2 := by
      by_contra h
      have hb0 : x.2.2 = 0 := Nat.eq_zero_of_not_pos h
      simp [hb0] at hprod
      omega
    have hadvd : x.2.1 ∣ x.1 := ⟨x.2.2, hprod.symm⟩
    have haLe : x.2.1 ≤ x.1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hadvd
    have haI : x.2.1 ∈ positiveIntegerRange N := by
      exact Finset.mem_Icc.mpr ⟨haPos, haLe.trans hnI'.2⟩
    have hbLe : x.2.2 ≤ N / x.2.1 :=
      (Nat.le_div_iff_mul_le haPos).2 (by
        calc
          x.2.2 * x.2.1 = x.2.1 * x.2.2 := Nat.mul_comm _ _
          _ = x.1 := hprod
          _ ≤ N := hnI'.2)
    exact Finset.mem_sigma.mpr ⟨haI, Finset.mem_Icc.mpr ⟨hbPos, hbLe⟩⟩
  · intro x₁ hx₁ x₂ hx₂ h
    apply Sigma.ext
    · have hp : x₁.2 = x₂.2 := by
        injection h with h₁ h₂
        exact Prod.ext h₁ h₂
      have hp₁ := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx₁).2
      have hp₂ := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx₂).2
      calc
        x₁.1 = x₁.2.1 * x₁.2.2 := hp₁.1.symm
        _ = x₂.2.1 * x₂.2.2 := by rw [hp]
        _ = x₂.1 := hp₂.1
    · have hp : x₁.2 = x₂.2 := by
        injection h with h₁ h₂
        exact Prod.ext h₁ h₂
      simp [hp]
  · intro y hy
    rcases Finset.mem_sigma.mp hy with ⟨ha, hb⟩
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    let n : ℕ := y.1 * y.2
    have hnpos : 0 < n := by
      dsimp [n]
      exact Nat.mul_pos ha'.1 hb'.1
    have hnle : n ≤ N := by
      have hle := Nat.mul_le_of_le_div y.1 y.2 N hb'.2
      simpa [n, Nat.mul_comm] using hle
    have hn : n ∈ positiveIntegerRange N := Finset.mem_Icc.mpr ⟨hnpos, hnle⟩
    have hp : (y.1, y.2) ∈ n.divisorsAntidiagonal := by
      apply Nat.mem_divisorsAntidiagonal.mpr
      exact ⟨by simp [n], by omega⟩
    refine ⟨⟨n, (y.1, y.2)⟩, Finset.mem_sigma.mpr ⟨hn, hp⟩, ?_⟩
    rfl
  · intro x hx
    rfl

def mobiusRealCoefficient (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) n

private theorem vonMangoldt_sum_eq_factor_sum (N : ℕ) :
    (∑ n ∈ positiveIntegerRange N, vonMangoldtWeight n) =
      ∑ d ∈ positiveIntegerRange N,
        ∑ m ∈ Finset.Icc 1 (N / d), mobiusRealCoefficient d * Real.log (m : ℝ) := by
  have hidentity :
      (∑ n ∈ positiveIntegerRange N, vonMangoldtWeight n) =
        ∑ n ∈ positiveIntegerRange N,
          ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            ArithmeticFunction.log) n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [vonMangoldtWeight_def]
    exact congrArg (fun f : ArithmeticFunction ℝ => f n)
      ArithmeticFunction.moebius_mul_log_eq_vonMangoldt.symm
  rw [hidentity]
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply]
  rw [sum_divisorsAntidiagonal_below]
  rfl

/-- Transpose the long factor-pair region. The hypothesis `hbound` is exactly
the real-cutoff fact that a pair with `d > floor D` has `m ≤ floor(x / D)`. -/
private theorem longFactorPairs_swap
    (N k M : ℕ) (hbound : ∀ d m, d ∈ Finset.Ioc k N →
      m ∈ Finset.Icc 1 (N / d) → m ≤ M) :
    (∑ d ∈ Finset.Ioc k N, ∑ m ∈ Finset.Icc 1 (N / d),
        mobiusRealCoefficient d * Real.log (m : ℝ)) =
      ∑ m ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Ioc k (N / m),
        mobiusRealCoefficient d * Real.log (m : ℝ) := by
  classical
  let S := (Finset.Ioc k N).sigma (fun d => Finset.Icc 1 (N / d))
  let T := (Finset.Icc 1 M).sigma (fun m => Finset.Ioc k (N / m))
  have hleft :
      (∑ d ∈ Finset.Ioc k N, ∑ m ∈ Finset.Icc 1 (N / d),
        mobiusRealCoefficient d * Real.log (m : ℝ)) =
        ∑ p ∈ S, mobiusRealCoefficient p.1 * Real.log (p.2 : ℝ) := by
    dsimp [S]
    rw [Finset.sum_sigma]
  have hright :
      (∑ m ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Ioc k (N / m),
        mobiusRealCoefficient d * Real.log (m : ℝ)) =
        ∑ q ∈ T, mobiusRealCoefficient q.2 * Real.log (q.1 : ℝ) := by
    dsimp [T]
    rw [Finset.sum_sigma]
  rw [hleft, hright]
  change (∑ p ∈ S, mobiusRealCoefficient p.1 * Real.log (p.2 : ℝ)) =
    ∑ q ∈ T, mobiusRealCoefficient q.2 * Real.log (q.1 : ℝ)
  refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_sigma.mp hp with ⟨hd, hm⟩
    have hd' := Finset.mem_Ioc.mp hd
    have hm' := Finset.mem_Icc.mp hm
    have hprod : p.1 * p.2 ≤ N := by
      simpa [Nat.mul_comm] using Nat.mul_le_of_le_div p.1 p.2 N hm'.2
    have hM : p.2 ≤ M := hbound p.1 p.2 hd hm
    have hddiv : p.1 ≤ N / p.2 :=
      (Nat.le_div_iff_mul_le hm'.1).2 (by simpa [Nat.mul_comm] using hprod)
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hm'.1, hM⟩,
      Finset.mem_Ioc.mpr ⟨hd'.1, hddiv⟩⟩
  · intro p₁ hp₁ p₂ hp₂ h
    rcases p₁ with ⟨d₁, m₁⟩
    rcases p₂ with ⟨d₂, m₂⟩
    injection h with hm hd
    subst hm
    subst hd
    rfl
  · intro q hq
    rcases Finset.mem_sigma.mp hq with ⟨hm, hd⟩
    have hm' := Finset.mem_Icc.mp hm
    have hd' := Finset.mem_Ioc.mp hd
    have hprod : q.2 * q.1 ≤ N := by
      simpa [Nat.mul_comm] using Nat.mul_le_of_le_div q.1 q.2 N hd'.2
    have hN : q.1 ≤ N / q.2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < q.2)).2
        (by simpa [Nat.mul_comm] using hprod)
    have hdN : q.2 ≤ N := by
      exact le_trans hd'.2 (Nat.div_le_self N q.1)
    have hsource : q.2 ∈ Finset.Ioc k N ∧
        q.1 ∈ Finset.Icc 1 (N / q.2) := by
      exact ⟨Finset.mem_Ioc.mpr ⟨hd'.1, hdN⟩,
        Finset.mem_Icc.mpr ⟨hm'.1, hN⟩⟩
    refine ⟨⟨q.2, q.1⟩, Finset.mem_sigma.mpr hsource, ?_⟩
    rfl
  · intro p hp
    rfl

/-- Exact finite hyperbola split for the von Mangoldt sum at real cutoffs.
The first range is inclusive through `floor D`; the complementary range is
strictly above `floor D`, as in `lml:principal-primes`. -/
theorem principalPrimeHyperbolaSplit
    {x D : ℝ} (hD : 0 < D) (hDx : D ≤ x) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), vonMangoldtWeight n) =
      (∑ d ∈ Finset.Icc 1 (Nat.floor D),
      mobiusRealCoefficient d *
          (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))), Real.log (m : ℝ))) +
      (∑ m ∈ Finset.Icc 1 (Nat.floor (x / D)),
        Real.log (m : ℝ) *
          (∑ d ∈ Finset.Ioc (Nat.floor D) (Nat.floor (x / (m : ℝ))),
        mobiusRealCoefficient d)) := by
  classical
  let N := Nat.floor x
  let k := Nat.floor D
  let M := Nat.floor (x / D)
  have hxpos : 0 < x := lt_of_lt_of_le hD hDx
  have hN : k ≤ N := Nat.floor_mono hDx
  have hconv := vonMangoldt_sum_eq_factor_sum N
  change (∑ n ∈ Finset.Icc 1 N, vonMangoldtWeight n) = _ at hconv
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 k ∪ Finset.Ioc k N := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Ioc k N) := by
    apply Finset.disjoint_left.mpr
    intro d hd₁ hd₂
    simp only [Finset.mem_Icc] at hd₁
    simp only [Finset.mem_Ioc] at hd₂
    omega
  rw [hsplit, Finset.sum_union hdisj] at hconv
  have hL :
      (∑ n ∈ Finset.Icc 1 N, vonMangoldtWeight n) =
        (∑ n ∈ Finset.Icc 1 k, vonMangoldtWeight n) +
          ∑ n ∈ Finset.Ioc k N, vonMangoldtWeight n := by
    rw [hsplit, Finset.sum_union hdisj]
  have hfirst :
      (∑ d ∈ Finset.Icc 1 k,
        ∑ m ∈ Finset.Icc 1 (N / d), mobiusRealCoefficient d * Real.log (m : ℝ)) =
      ∑ d ∈ Finset.Icc 1 k,
        mobiusRealCoefficient d *
          (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))), Real.log (m : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.floor_div_natCast x d]
    rw [Finset.mul_sum]
  have hfactor :
      (∑ d ∈ positiveIntegerRange N,
        ∑ m ∈ Finset.Icc 1 (N / d), mobiusRealCoefficient d * Real.log (m : ℝ)) =
      (∑ d ∈ Finset.Icc 1 k,
        ∑ m ∈ Finset.Icc 1 (N / d), mobiusRealCoefficient d * Real.log (m : ℝ)) +
      ∑ d ∈ Finset.Ioc k N,
        ∑ m ∈ Finset.Icc 1 (N / d), mobiusRealCoefficient d * Real.log (m : ℝ) := by
    change (∑ d ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 (N / d), mobiusRealCoefficient d * Real.log (m : ℝ)) = _
    rw [hsplit, Finset.sum_union hdisj]
  have hbound : ∀ d m, d ∈ Finset.Ioc k N →
      m ∈ Finset.Icc 1 (N / d) → m ≤ M := by
    intro d m hd hm
    have hd' := Finset.mem_Ioc.mp hd
    have hm' := Finset.mem_Icc.mp hm
    have hprod : d * m ≤ N := by
      simpa [Nat.mul_comm] using Nat.mul_le_of_le_div d m N hm'.2
    have hDlt : D < (d : ℝ) := by
      have hfloor : D < (k : ℝ) + 1 := Nat.lt_floor_add_one D
      have hsucc : k + 1 ≤ d := Nat.succ_le_of_lt hd'.1
      exact lt_of_lt_of_le hfloor (by exact_mod_cast hsucc)
    have hprodReal : (m : ℝ) * D ≤ x := by
      calc
        (m : ℝ) * D ≤ (m : ℝ) * (d : ℝ) :=
          mul_le_mul_of_nonneg_left hDlt.le (by positivity)
        _ = (d : ℝ) * (m : ℝ) := by ring
        _ ≤ (N : ℝ) := by exact_mod_cast hprod
        _ ≤ x := Nat.floor_le (le_of_lt hxpos)
    have hmquot : (m : ℝ) ≤ x / D := (le_div_iff₀ hD).2 hprodReal
    exact Nat.le_floor hmquot
  have hlong := longFactorPairs_swap N k M hbound
  have hlongReal :
      (∑ m ∈ Finset.Icc 1 M,
        ∑ d ∈ Finset.Ioc k (N / m), mobiusRealCoefficient d * Real.log (m : ℝ)) =
      ∑ m ∈ Finset.Icc 1 M,
        Real.log (m : ℝ) *
          (∑ d ∈ Finset.Ioc k (Nat.floor (x / (m : ℝ))), mobiusRealCoefficient d) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.floor_div_natCast x m]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change (∑ n ∈ Finset.Icc 1 N, vonMangoldtWeight n) = _
  rw [hL, hconv, hfactor, hfirst, hlong, hlongReal]

end FractionalPrimes.Literature.MobiusToLong
