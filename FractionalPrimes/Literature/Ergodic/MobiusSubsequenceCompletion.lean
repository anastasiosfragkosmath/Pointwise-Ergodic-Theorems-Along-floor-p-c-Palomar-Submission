module

public import FractionalPrimes.Literature.Ergodic.BoundedAverageSubsequence
public import FractionalPrimes.Literature.Ergodic.ScaleConvergenceBridge
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section
namespace FractionalPrimes
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

/-- A bounded representative has one common conull set on which every
integer orbit evaluation satisfies the same essential-supremum bound. -/
theorem ae_integerOrbit_norm_le_lpNorm
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f ∞ S.μ) :
    ∀ᵐ x ∂S.μ, ∀ m : ℤ, ‖f (S.iterate m x)‖ ≤ lpNorm f ∞ S.μ := by
  apply ae_all_iff.mpr
  intro m
  exact (S.measurePreserving_integerIterate m).quasiMeasurePreserving.ae
    (ae_le_lpNorm_exponent_top hf)

/-- The actual Möbius averages converge at every positive integer scale if
they converge along a cofinal monotone sequence whose relative gaps vanish.
This supplies the all-scale passage in the source bounded-L2 argument. -/
theorem mobiusAverage_ae_tendsto_zero_of_bounded_subsequence
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f : X → ℂ) (hf : MemLp f ∞ S.μ)
    (t : ℕ → ℕ) (htpos : ∀ k, 0 < t k) (htmono : Monotone t)
    (htop : Tendsto t atTop atTop)
    (hgap : Tendsto (fun k : ℕ =>
      ((t (k + 1) : ℝ) - t k) / t k) atTop (𝓝 0))
    (hsub : ∀ᵐ x ∂S.μ, Tendsto
      (fun k : ℕ => mobiusAverage S c f ⟨t k, htpos k⟩ x) atTop (𝓝 0)) :
    ∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => mobiusAverage S c f N x)
      atTop (𝓝 0) := by
  filter_upwards [ae_integerOrbit_norm_le_lpNorm S f hf, hsub] with x hx hxs
  let a : ℕ → ℂ := fun n => (mobiusWeight n : ℂ) * f (S.iterate (floorPower c n) x)
  have hinterval (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N :=
    (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) N).symm
  have ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ lpNorm f ∞ S.μ := by
    intro n hn
    have hμ : ‖(mobiusWeight n : ℂ)‖ ≤ (1 : ℝ) := by
      rw [mobiusWeight_def, Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    calc
      ‖a n‖ = ‖(mobiusWeight n : ℂ)‖ * ‖f (S.iterate (floorPower c n) x)‖ := norm_mul _ _
      _ ≤ 1 * lpNorm f ∞ S.μ := mul_le_mul hμ (hx _) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hs : Tendsto (fun k : ℕ =>
      (t k : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc 0 (t k), a n) atTop (𝓝 0) := by
    simpa only [mobiusAverage, weightedAverage, hinterval, a] using hxs
  have hall := boundedPrefixAverage_tendsto_zero_of_subsequence a
    (lpNorm f ∞ S.μ) lpNorm_nonneg ha t htpos htmono htop hgap hs
  apply tendsto_scale_of_natSucc
  have hshift := (tendsto_add_atTop_iff_nat 1).mpr hall
  simpa only [mobiusAverage, weightedAverage, hinterval, a] using hshift

#print axioms ae_integerOrbit_norm_le_lpNorm
#print axioms mobiusAverage_ae_tendsto_zero_of_bounded_subsequence
end
end FractionalPrimes
