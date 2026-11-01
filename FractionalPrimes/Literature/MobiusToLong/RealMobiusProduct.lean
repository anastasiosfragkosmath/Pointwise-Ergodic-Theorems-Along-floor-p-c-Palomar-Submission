module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import FractionalPrimes.Literature.MobiusToLong.RealZetaComparison

@[expose] public section

open scoped LSeries.notation

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The real Möbius Dirichlet series, indexed by the positive integers.
The summand at index `n` is the coefficient at the positive integer `n + 1`.
Thus this is exactly the ordered series convention `∑_{m ≥ 1} μ(m)m^(-σ)`.
-/
def realMobiusDirichletSeries (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.moebius (n + 1) : ℝ) *
    (((n + 1 : ℕ) : ℝ) ^ (-σ))

private theorem realRiemannZeta_term_norm_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖(((n + 1 : ℕ) : ℝ) ^ (-σ))‖) := by
  have hpow : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ))) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-σ))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (1 : ℕ)).2 hbase
  refine Summable.of_norm_bounded hpow ?_
  intro n
  rw [norm_norm, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

private theorem realMobiusDirichletSeries_norm_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖(ArithmeticFunction.moebius (n + 1) : ℝ) *
      (((n + 1 : ℕ) : ℝ) ^ (-σ))‖) := by
  have hpow : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ))) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-σ))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (1 : ℕ)).2 hbase
  refine Summable.of_norm_bounded hpow ?_
  intro n
  rw [norm_norm, norm_mul]
  have hpow_nonneg :
      0 ≤ (((n + 1 : ℕ) : ℝ) ^ (-σ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
  have hμ : ‖(ArithmeticFunction.moebius (n + 1) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n + 1))
  calc
    ‖(ArithmeticFunction.moebius (n + 1) : ℝ)‖ *
        (((n + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      1 * (((n + 1 : ℕ) : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_right hμ hpow_nonneg
    _ = (((n + 1 : ℕ) : ℝ) ^ (-σ)) := one_mul _

/-- Absolute convergence of the positive-index real Möbius Dirichlet series for `σ > 1`.
The comparison is with the real p-series used by `realRiemannZeta`.
-/
theorem realMobiusDirichletSeries_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius (n + 1) : ℝ) *
      (((n + 1 : ℕ) : ℝ) ^ (-σ))) := by
  exact Summable.of_norm (realMobiusDirichletSeries_norm_summable hσ)

private theorem realRiemannZeta_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ))) :=
  Summable.of_norm (realRiemannZeta_term_norm_summable hσ)

private theorem lseries_eq_shifted_terms {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) :
    LSeries f s = ∑' n : ℕ, f (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s := by
  unfold LSeries
  calc
    _ = LSeries.term f s 0 + ∑' n : ℕ, LSeries.term f s (n + 1) :=
      hf.tsum_eq_zero_add
    _ = ∑' n : ℕ, LSeries.term f s (n + 1) := by simp
    _ = ∑' n : ℕ, f (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s := by
      apply tsum_congr
      intro n
      exact LSeries.term_of_ne_zero (by omega) f s

private theorem ofReal_realRiemannZeta_eq_lseries {σ : ℝ} (hσ : 1 < σ) :
    (realRiemannZeta σ : ℂ) =
      LSeries (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) (σ : ℂ) := by
  have hs : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by simpa using hσ)
  rw [realRiemannZeta, Complex.ofReal_tsum, lseries_eq_shifted_terms hs]
  refine tsum_congr fun n => ?_
  have hn : n + 1 ≠ 0 := by omega
  rw [ArithmeticFunction.zeta_apply]
  have hzeta : (if n + 1 = 0 then 0 else 1 : ℕ) = 1 := by
    split_ifs <;> omega
  rw [hzeta]
  simp only [Nat.cast_one, one_div]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _) (-σ)]
  rw [show ((-σ : ℝ) : ℂ) = -(σ : ℂ) by simp, Complex.cpow_neg]
  simp

private theorem ofReal_realMobiusDirichletSeries_eq_lseries {σ : ℝ} (hσ : 1 < σ) :
    (realMobiusDirichletSeries σ : ℂ) =
      LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (σ : ℂ) := by
  have hs : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hσ)
  rw [realMobiusDirichletSeries, Complex.ofReal_tsum, lseries_eq_shifted_terms hs]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _) (-σ),
    Complex.ofReal_intCast]
  rw [show ((-σ : ℝ) : ℂ) = -(σ : ℂ) by simp, Complex.cpow_neg]
  simp [div_eq_mul_inv]

/-- The real Möbius Dirichlet series is the reciprocal of the real zeta series
throughout its half-plane of absolute convergence.
-/
theorem realMobiusDirichletSeries_mul_realRiemannZeta_eq_one
    {σ : ℝ} (hσ : 1 < σ) :
    realMobiusDirichletSeries σ * realRiemannZeta σ = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,
    ofReal_realMobiusDirichletSeries_eq_lseries hσ,
    ofReal_realRiemannZeta_eq_lseries hσ]
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
    (s := (σ : ℂ)) (by simpa using hσ)
  simpa [mul_comm] using hprod

end
end FractionalPrimes.Literature.MobiusToLong
