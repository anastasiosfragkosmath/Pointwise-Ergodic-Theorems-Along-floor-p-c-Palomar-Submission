module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.PSeries

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

open MeasureTheory

/-- The real Dirichlet series for the Riemann zeta function, indexed from
the positive integers. -/
def realRiemannZeta (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ))

private theorem rpow_antitoneOn_Ici_one {σ : ℝ} (hσ : 1 < σ) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici (↑(1 : ℕ) : ℝ)) := by
  apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono
  intro x hx
  simp only [Set.mem_Ici] at hx
  have hx' : (1 : ℝ) ≤ x := by simpa using hx
  exact Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hx')

private theorem realRiemannZeta_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n : ℝ) ^ (-σ))) := by
  exact Real.summable_nat_rpow.mpr (by linarith)

/-- Exact integral comparison for the real zeta series, with its full
half-plane hypothesis and the two constants used in `lml:mobius-moments`.
The series is the ordered positive-integer Dirichlet series. -/
theorem realRiemannZeta_bounds {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ realRiemannZeta σ ∧
      realRiemannZeta σ ≤ 1 + 1 / (σ - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-σ)
  have hanti := rpow_antitoneOn_Ici_one hσ
  have hsummable := realRiemannZeta_summable hσ
  have hint : IntegrableOn f (Set.Ioi (↑(1 : ℕ) : ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by linarith)
      (by norm_num : 0 < (↑(1 : ℕ) : ℝ))
  have hnonneg : ∀ x ∈ Set.Ioi (↑(1 : ℕ) : ℝ), 0 ≤ f x := by
    intro x hx
    dsimp [f]
    have h1 : (0 : ℝ) < (↑(1 : ℕ) : ℝ) := by norm_num
    exact Real.rpow_nonneg (le_of_lt (lt_trans h1 (Set.mem_Ioi.mp hx))) _
  have hIntegral : (∫ x in Set.Ioi (↑(1 : ℕ) : ℝ), f x) = 1 / (σ - 1) := by
    change (∫ x in Set.Ioi (↑(1 : ℕ) : ℝ), x ^ (-σ)) = _
    rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1)
      (by norm_num : 0 < (↑(1 : ℕ) : ℝ))]
    rw [show (↑(1 : ℕ) : ℝ) = (1 : ℝ) by norm_num, Real.one_rpow]
    have hden : -σ + 1 = -(σ - 1) := by ring
    rw [hden]
    field_simp
  have hlo := AntitoneOn.integral_le_tsum_comp_add
    (f := f) (N := (1 : ℕ)) hanti hsummable hnonneg
  have hSeriesLower : (∑' n : ℕ, f (n + 1)) = realRiemannZeta σ := by
    apply tsum_congr
    intro n
    simp only [f, Nat.cast_add, Nat.cast_one]
  have hLower : 1 / (σ - 1) ≤ realRiemannZeta σ := by
    rw [← hIntegral, ← hSeriesLower]
    simpa only [Nat.cast_add, Nat.cast_one] using hlo
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) (N := (1 : ℕ)) hanti hint hnonneg
  have hSeriesSplit : realRiemannZeta σ =
      1 + ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ (-σ)) := by
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ))) :=
      (summable_nat_add_iff (1 : ℕ)).2 hsummable
    have h := hshift.tsum_eq_zero_add
    simpa [realRiemannZeta, Nat.cast_add, Nat.cast_one, add_assoc] using h
  have hSeriesTail : (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ (-σ))) =
      ∑' n : ℕ, f (n + 1 + 1) := by
    apply tsum_congr
    intro n
    simp only [f, Nat.cast_add]
    congr 1
    ring
  have hTailBound :
      (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ (-σ))) ≤ 1 / (σ - 1) := by
    calc
      _ = ∑' n : ℕ, f (n + 1 + 1) := hSeriesTail
      _ ≤ ∫ x in Set.Ioi (↑(1 : ℕ) : ℝ), f x := by
        simpa only [Nat.cast_add, Nat.cast_one] using htail
      _ = 1 / (σ - 1) := hIntegral
  constructor
  · exact hLower
  · rw [hSeriesSplit]
    linarith

end
end FractionalPrimes.Literature.MobiusToLong
