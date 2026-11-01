module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.Linearity

@[expose] public section

open scoped ArithmeticFunction.Moebius

namespace FractionalPrimes.Literature.LongArithmetic

/-- The coefficient of the Möbius Dirichlet series after multiplication by `r`. -/
def mobiusMultiplierCoefficient (r : ℕ) (χ : ℕ →*₀ ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius (r * n) : ℂ) * χ n

/-- The coefficient of the Möbius series restricted to integers coprime to `r`. -/
def mobiusCoprimeFilteredCoefficient (r : ℕ) (χ : ℕ →*₀ ℂ) (n : ℕ) : ℂ :=
  if Nat.Coprime n r then (ArithmeticFunction.moebius n : ℂ) * χ n else 0

/-- Exact pointwise Möbius factorization for every multiplier, including `r = 1`
and nonsquarefree `r`. -/
theorem mobiusMultiplierCoefficient_eq
    (r : ℕ) (χ : ℕ →*₀ ℂ) (n : ℕ) :
    mobiusMultiplierCoefficient r χ n =
      (ArithmeticFunction.moebius r : ℂ) * mobiusCoprimeFilteredCoefficient r χ n := by
  by_cases hcop : Nat.Coprime n r
  · have hμ := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hcop.symm
    simp only [mobiusMultiplierCoefficient, mobiusCoprimeFilteredCoefficient,
      if_pos hcop, hμ, Int.cast_mul]
    ring
  · have hnsq : ¬ Squarefree (r * n) := by
      intro hs
      exact hcop (Nat.coprime_of_squarefree_mul hs).symm
    simp [mobiusMultiplierCoefficient, mobiusCoprimeFilteredCoefficient, hcop,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]

private theorem moebiusCoeff_norm_le_one (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

private theorem mobiusMultiplierCoefficient_norm_le_one
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) (r n : ℕ) :
    ‖mobiusMultiplierCoefficient r χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [mobiusMultiplierCoefficient, hn]
  · rw [mobiusMultiplierCoefficient, norm_mul]
    exact (mul_le_mul (moebiusCoeff_norm_le_one (r * n)) (hχ n hn)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

private theorem mobiusCoprimeFilteredCoefficient_norm_le_one
    (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1) (r n : ℕ) :
    ‖mobiusCoprimeFilteredCoefficient r χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [mobiusCoprimeFilteredCoefficient, hn]
  · by_cases hc : Nat.Coprime n r
    · rw [mobiusCoprimeFilteredCoefficient, if_pos hc, norm_mul]
      exact (mul_le_mul (moebiusCoeff_norm_le_one n) (hχ n hn)
        (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    · simp [mobiusCoprimeFilteredCoefficient, hc]

theorem mobiusMultiplierDirichletSeries_absolutelyConvergent
    (r : ℕ) (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mobiusMultiplierCoefficient r χ) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n hn => mobiusMultiplierCoefficient_norm_le_one χ hχ r n) hs

theorem mobiusCoprimeFilteredDirichletSeries_absolutelyConvergent
    (r : ℕ) (χ : ℕ →*₀ ℂ) (hχ : ∀ n ≠ 0, ‖χ n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mobiusCoprimeFilteredCoefficient r χ) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n hn => mobiusCoprimeFilteredCoefficient_norm_le_one χ hχ r n) hs

theorem mobiusMultiplierLSeries_eq
    (r : ℕ) (χ : ℕ →*₀ ℂ) {s : ℂ} :
    LSeries (mobiusMultiplierCoefficient r χ) s =
      (ArithmeticFunction.moebius r : ℂ) *
        LSeries (mobiusCoprimeFilteredCoefficient r χ) s := by
  calc
    LSeries (mobiusMultiplierCoefficient r χ) s =
        LSeries ((ArithmeticFunction.moebius r : ℂ) •
          mobiusCoprimeFilteredCoefficient r χ) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mobiusMultiplierCoefficient_eq r χ n
    _ = (ArithmeticFunction.moebius r : ℂ) *
        LSeries (mobiusCoprimeFilteredCoefficient r χ) s :=
      LSeries_smul (mobiusCoprimeFilteredCoefficient r χ)
        (ArithmeticFunction.moebius r : ℂ) s

#print axioms mobiusMultiplierCoefficient_eq
#print axioms mobiusMultiplierDirichletSeries_absolutelyConvergent
#print axioms mobiusCoprimeFilteredDirichletSeries_absolutelyConvergent
#print axioms mobiusMultiplierLSeries_eq

end FractionalPrimes.Literature.LongArithmetic
