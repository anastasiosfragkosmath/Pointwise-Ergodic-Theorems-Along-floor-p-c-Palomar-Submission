module

public import FractionalPrimes.Literature.Uniformity.DivisorFunctions
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Summatory divisor-function bound

This file formalizes the constant-one mean bound for divisor functions by
reindexing divisor antidiagonals as pairs of positive factors.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

private def positiveRange (N : ℕ) : Finset ℕ := Finset.Icc 1 N

private def factorPairRange (N : ℕ) : Finset (Σ _a : ℕ, ℕ) :=
  (positiveRange N).sigma (fun a => Finset.Icc 1 (N / a))

private theorem sum_divisorsAntidiagonal_below (N : ℕ) (F : ℕ × ℕ → ℝ) :
    (∑ n ∈ positiveRange N, ∑ p ∈ n.divisorsAntidiagonal, F p) =
      ∑ a ∈ positiveRange N, ∑ b ∈ Finset.Icc 1 (N / a), F (a, b) := by
  classical
  let S := (positiveRange N).sigma (fun n => n.divisorsAntidiagonal)
  let T := factorPairRange N
  have hleft :
      (∑ n ∈ positiveRange N, ∑ p ∈ n.divisorsAntidiagonal, F p) =
        ∑ x ∈ S, F x.2 := by
    dsimp [S]
    rw [Finset.sum_sigma]
  have hright :
      (∑ a ∈ positiveRange N, ∑ b ∈ Finset.Icc 1 (N / a), F (a, b)) =
        ∑ y ∈ T, F (y.1, y.2) := by
    dsimp [T, factorPairRange]
    rw [Finset.sum_sigma]
  rw [hleft, hright]
  change (∑ x ∈ S, F x.2) = ∑ y ∈ T, F (y.1, y.2)
  refine Finset.sum_bij (fun x _ => ⟨x.2.1, x.2.2⟩) ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hn, hp⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hn0⟩
    have hnI : x.1 ∈ positiveRange N := hn
    have hnI' := Finset.mem_Icc.mp hnI
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
    have haI : x.2.1 ∈ positiveRange N := by
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
    have hn : n ∈ positiveRange N := Finset.mem_Icc.mpr ⟨hnpos, hnle⟩
    have hp : (y.1, y.2) ∈ n.divisorsAntidiagonal := by
      apply Nat.mem_divisorsAntidiagonal.mpr
      exact ⟨by simp [n], by omega⟩
    refine ⟨⟨n, (y.1, y.2)⟩, Finset.mem_sigma.mpr ⟨hn, hp⟩, ?_⟩
    rfl
  · intro x hx
    rfl

def divisorCoefficient (m n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ m) n

theorem divisorCoefficient_eq_divisorFunction (m n : ℕ) (hn : 0 < n) :
    divisorCoefficient m n = divisorFunction m ⟨n, hn⟩ := rfl

private theorem divisorCoefficient_succ_divisor_sum (m n : ℕ) :
    divisorCoefficient (m + 1) n =
      ∑ d ∈ n.divisors, divisorCoefficient m d := by
  dsimp [divisorCoefficient]
  rw [pow_succ, ArithmeticFunction.mul_zeta_apply]

private def divisorSummatory (m N : ℕ) : ℝ :=
  ∑ n ∈ positiveRange N, (divisorCoefficient m n : ℝ)

private noncomputable def divisorWeightedSummatory (m N : ℕ) : ℝ :=
  ∑ n ∈ positiveRange N, (divisorCoefficient m n : ℝ) / (n : ℝ)

private noncomputable def reciprocalSum (N : ℕ) : ℝ :=
  ∑ n ∈ positiveRange N, (n : ℝ)⁻¹

private theorem reciprocalSum_eq_harmonic (N : ℕ) :
    reciprocalSum N = (harmonic N : ℝ) := by
  rw [reciprocalSum, harmonic_eq_sum_Icc]
  simp_rw [positiveRange, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem reciprocalSum_le_one_add_log (N : ℕ) :
    reciprocalSum N ≤ 1 + Real.log N := by
  rw [reciprocalSum_eq_harmonic]
  exact_mod_cast harmonic_le_one_add_log N

private theorem reciprocalSum_nonneg (N : ℕ) : 0 ≤ reciprocalSum N := by
  apply Finset.sum_nonneg
  intro n hn
  positivity

private theorem divisorCoefficient_nonneg (m n : ℕ) :
    0 ≤ (divisorCoefficient m n : ℝ) := by
  positivity

private theorem reciprocalSum_mono {M N : ℕ} (hMN : M ≤ N) :
    reciprocalSum M ≤ reciprocalSum N := by
  unfold reciprocalSum positiveRange
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hMN⟩
  · intro n hn _
    positivity

private theorem divisorSummatory_succ_eq_factorPairs (m N : ℕ) :
    divisorSummatory (m + 1) N =
      ∑ a ∈ positiveRange N,
        ∑ _b ∈ Finset.Icc 1 (N / a), (divisorCoefficient m a : ℝ) := by
  rw [divisorSummatory]
  calc
    (∑ n ∈ positiveRange N, (divisorCoefficient (m + 1) n : ℝ)) =
        ∑ n ∈ positiveRange N,
          ∑ p ∈ n.divisorsAntidiagonal, (divisorCoefficient m p.1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [divisorCoefficient_succ_divisor_sum, Nat.cast_sum]
            exact (Nat.sum_divisorsAntidiagonal
              (f := fun a _ => (divisorCoefficient m a : ℝ))).symm
    _ = ∑ a ∈ positiveRange N,
          ∑ b ∈ Finset.Icc 1 (N / a), (divisorCoefficient m a : ℝ) :=
        sum_divisorsAntidiagonal_below N (fun p => (divisorCoefficient m p.1 : ℝ))

private theorem divisorWeightedSummatory_succ_eq_factorPairs (m N : ℕ) :
    divisorWeightedSummatory (m + 1) N =
      ∑ a ∈ positiveRange N,
        ∑ b ∈ Finset.Icc 1 (N / a),
          (divisorCoefficient m a : ℝ) / ((a : ℝ) * (b : ℝ)) := by
  rw [divisorWeightedSummatory]
  calc
    (∑ n ∈ positiveRange N,
        (divisorCoefficient (m + 1) n : ℝ) / (n : ℝ)) =
        ∑ n ∈ positiveRange N,
          ∑ p ∈ n.divisorsAntidiagonal,
            (divisorCoefficient m p.1 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [divisorCoefficient_succ_divisor_sum, Nat.cast_sum]
            calc
              (∑ d ∈ n.divisors, (divisorCoefficient m d : ℝ)) / (n : ℝ) =
                ∑ d ∈ n.divisors,
                  (divisorCoefficient m d : ℝ) / (n : ℝ) := Finset.sum_div _ _ _
              _ =
                ∑ p ∈ n.divisorsAntidiagonal,
                  (divisorCoefficient m p.1 : ℝ) / (n : ℝ) :=
                    (Nat.sum_divisorsAntidiagonal
                      (f := fun d _ => (divisorCoefficient m d : ℝ) / (n : ℝ))).symm
              _ = ∑ p ∈ n.divisorsAntidiagonal,
                    (divisorCoefficient m p.1 : ℝ) /
                      ((p.1 : ℝ) * (p.2 : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
                    rw [show (n : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) by exact_mod_cast hprod.symm]
    _ = ∑ a ∈ positiveRange N,
          ∑ b ∈ Finset.Icc 1 (N / a),
            (divisorCoefficient m a : ℝ) / ((a : ℝ) * (b : ℝ)) :=
        sum_divisorsAntidiagonal_below N
          (fun p => (divisorCoefficient m p.1 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)))

private theorem divisorWeightedSummatory_succ_le (m N : ℕ) :
    divisorWeightedSummatory (m + 1) N ≤
      divisorWeightedSummatory m N * reciprocalSum N := by
  rw [divisorWeightedSummatory_succ_eq_factorPairs]
  calc
    (∑ a ∈ positiveRange N,
        ∑ b ∈ Finset.Icc 1 (N / a),
          (divisorCoefficient m a : ℝ) / ((a : ℝ) * (b : ℝ))) ≤
      ∑ a ∈ positiveRange N,
        ((divisorCoefficient m a : ℝ) / (a : ℝ)) * reciprocalSum N := by
          apply Finset.sum_le_sum
          intro a ha
          have haPos := (Finset.mem_Icc.mp ha).1
          calc
            (∑ b ∈ Finset.Icc 1 (N / a),
                (divisorCoefficient m a : ℝ) / ((a : ℝ) * (b : ℝ))) =
              ∑ b ∈ Finset.Icc 1 (N / a),
                ((divisorCoefficient m a : ℝ) / (a : ℝ)) * (b : ℝ)⁻¹ := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  have hbPos := (Finset.mem_Icc.mp hb).1
                  have haNe : (a : ℝ) ≠ 0 := by positivity
                  have hbNe : (b : ℝ) ≠ 0 := by positivity
                  field_simp
            _ = ((divisorCoefficient m a : ℝ) / (a : ℝ)) *
                (∑ b ∈ Finset.Icc 1 (N / a), (b : ℝ)⁻¹) := by
                  rw [Finset.mul_sum]
            _ ≤ ((divisorCoefficient m a : ℝ) / (a : ℝ)) * reciprocalSum N :=
              mul_le_mul_of_nonneg_left
                (reciprocalSum_mono (Nat.div_le_self N a)) (by positivity)
    _ = divisorWeightedSummatory m N * reciprocalSum N := by
      rw [divisorWeightedSummatory, Finset.sum_mul]

private theorem divisorSummatory_succ_le (m N : ℕ) :
    divisorSummatory (m + 1) N ≤
      (N : ℝ) * divisorWeightedSummatory m N := by
  rw [divisorSummatory_succ_eq_factorPairs]
  calc
    (∑ a ∈ positiveRange N,
        ∑ _b ∈ Finset.Icc 1 (N / a), (divisorCoefficient m a : ℝ)) ≤
      ∑ a ∈ positiveRange N,
        (N : ℝ) * ((divisorCoefficient m a : ℝ) / (a : ℝ)) := by
          apply Finset.sum_le_sum
          intro a ha
          have haPos := (Finset.mem_Icc.mp ha).1
          have haNe : (a : ℝ) ≠ 0 := by positivity
          have hcard :
              (Finset.Icc 1 (N / a)).card = N / a := by simp
          rw [show (∑ _b ∈ Finset.Icc 1 (N / a),
              (divisorCoefficient m a : ℝ)) =
              ((Finset.Icc 1 (N / a)).card : ℝ) *
                (divisorCoefficient m a : ℝ) by simp [Finset.sum_const]]
          rw [hcard]
          have hq : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
            apply (le_div_iff₀ (by positivity)).2
            have hmul := Nat.mul_div_le N a
            exact_mod_cast (by simpa [Nat.mul_comm] using hmul)
          calc
            ((N / a : ℕ) : ℝ) * (divisorCoefficient m a : ℝ) ≤
                ((N : ℝ) / (a : ℝ)) * (divisorCoefficient m a : ℝ) :=
              mul_le_mul_of_nonneg_right hq (divisorCoefficient_nonneg m a)
            _ = (N : ℝ) * ((divisorCoefficient m a : ℝ) / (a : ℝ)) := by
              field_simp
    _ = (N : ℝ) * divisorWeightedSummatory m N := by
      rw [divisorWeightedSummatory, Finset.mul_sum]

private theorem divisorWeightedSummatory_pow_bound (m N : ℕ) :
    divisorWeightedSummatory m N ≤ reciprocalSum N ^ m := by
  induction m with
  | zero =>
      by_cases hN : N = 0
      · simp [divisorWeightedSummatory, positiveRange, hN]
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
        rw [divisorWeightedSummatory]
        have h1 : 1 ∈ positiveRange N := by
          simp [positiveRange, hNpos]
        calc
          (∑ n ∈ positiveRange N,
              (divisorCoefficient 0 n : ℝ) / (n : ℝ)) =
            (divisorCoefficient 0 1 : ℝ) / (1 : ℝ) := by
              simpa using Finset.sum_eq_single_of_mem
                (s := positiveRange N)
                (f := fun n : ℕ => (divisorCoefficient 0 n : ℝ) / (n : ℝ))
                1 h1 (by
                intro n hn hne
                simp [divisorCoefficient, hne])
          _ = 1 := by simp [divisorCoefficient]
          _ ≤ reciprocalSum N ^ 0 := by simp
  | succ m ih =>
      rw [pow_succ]
      calc
        divisorWeightedSummatory (m + 1) N ≤
            divisorWeightedSummatory m N * reciprocalSum N :=
          divisorWeightedSummatory_succ_le m N
        _ ≤ reciprocalSum N ^ m * reciprocalSum N :=
          mul_le_mul_of_nonneg_right ih (reciprocalSum_nonneg N)

private theorem divisorSummatory_nat_bound (m N : ℕ) (hm : 1 ≤ m) :
    divisorSummatory m N ≤
      (N : ℝ) * reciprocalSum N ^ (m - 1) := by
  cases m with
  | zero => omega
  | succ k =>
      simp only [Nat.succ_sub_one]
      calc
        divisorSummatory (k + 1) N ≤ (N : ℝ) * divisorWeightedSummatory k N :=
          divisorSummatory_succ_le k N
        _ ≤ (N : ℝ) * reciprocalSum N ^ k :=
          mul_le_mul_of_nonneg_left (divisorWeightedSummatory_pow_bound k N)
            (by positivity)

/-- The exact constant-one summatory bound for the `m`-fold divisor function.
The sum is over positive integers at most `Y`, represented by the natural floor. -/
theorem divisorSummatory_bound (m : ℕ) (hm : 1 ≤ m) (Y : ℝ) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (divisorCoefficient m n : ℝ)) ≤
      Y * (1 + Real.log Y) ^ (m - 1) := by
  let N := Nat.floor Y
  have hN : 1 ≤ N := by
    dsimp [N]
    have hfloorpos : 0 < Nat.floor Y := Nat.floor_pos.mpr hY
    omega
  have hNcast : (N : ℝ) ≤ Y := by
    dsimp [N]
    exact Nat.floor_le (by linarith)
  have hH : reciprocalSum N ≤ 1 + Real.log Y := by
    dsimp [N]
    rw [reciprocalSum_eq_harmonic]
    exact_mod_cast harmonic_floor_le_one_add_log Y hY
  have hHnonneg : 0 ≤ reciprocalSum N := reciprocalSum_nonneg N
  have hpow : reciprocalSum N ^ (m - 1) ≤
      (1 + Real.log Y) ^ (m - 1) := by
    exact pow_le_pow_left₀ hHnonneg hH (m - 1)
  change divisorSummatory m N ≤ Y * (1 + Real.log Y) ^ (m - 1)
  calc
    divisorSummatory m N ≤ (N : ℝ) * reciprocalSum N ^ (m - 1) :=
      divisorSummatory_nat_bound m N hm
    _ ≤ Y * (1 + Real.log Y) ^ (m - 1) := by
      exact mul_le_mul hNcast hpow (pow_nonneg hHnonneg _) (by positivity)

/-- The reciprocal-weighted divisor sum has the exact constant-one
harmonic-power bound. This exposes the estimate already proved in the
induction for `divisorSummatory_bound`. -/
theorem divisorWeightedSummatory_bound (m : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (divisorCoefficient m n : ℝ) / (n : ℝ)) ≤
      (1 + Real.log Y) ^ m := by
  let N := Nat.floor Y
  have hH : reciprocalSum N ≤ 1 + Real.log Y := by
    dsimp [N]
    rw [reciprocalSum_eq_harmonic]
    exact_mod_cast harmonic_floor_le_one_add_log Y hY
  have hHnonneg : 0 ≤ reciprocalSum N := reciprocalSum_nonneg N
  have hpow : reciprocalSum N ^ m ≤ (1 + Real.log Y) ^ m :=
    pow_le_pow_left₀ hHnonneg hH m
  change divisorWeightedSummatory m N ≤ (1 + Real.log Y) ^ m
  exact (divisorWeightedSummatory_pow_bound m N).trans hpow

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.divisorSummatory_bound
#print axioms FractionalPrimes.Literature.Uniformity.divisorWeightedSummatory_bound
