module

public import FractionalPrimes.ArithmeticBasics

@[expose] public section

namespace FractionalPrimes

open MeasureTheory

private theorem polynomialCorrelation_range_bddAbove
    {s : ℕ} {I : Finset ℤ} {w : ℤ → ℂ} (hI : I.Nonempty) :
    BddAbove (Set.range fun P : {P : Polynomial ℝ // P.natDegree ≤ s - 1} =>
      ‖(∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))) /
        (I.card : ℂ)‖) := by
  have hcard : 0 < I.card := Finset.card_pos.mpr hI
  have hcardReal : 0 < (I.card : ℝ) := by exact_mod_cast hcard
  refine ⟨(∑ n ∈ I, ‖w n‖) / (I.card : ℝ), ?_⟩
  rintro y ⟨P, rfl⟩
  have hsum :
      ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ ≤
        ∑ n ∈ I, ‖w n‖ := by
    calc
      ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ ≤
          ∑ n ∈ I, ‖w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ :=
        norm_sum_le _ _
      _ = ∑ n ∈ I, ‖w n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, norm_unitFrequencyPhase, mul_one]
  have hdenom : ‖(I.card : ℂ)‖ = (I.card : ℝ) := by simp
  calc
    ‖(∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))) /
        (I.card : ℂ)‖ =
        ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ /
          ‖(I.card : ℂ)‖ := norm_div _ _
    _ = ‖∑ n ∈ I, w n * unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ /
          (I.card : ℝ) := by rw [hdenom]
    _ ≤ (∑ n ∈ I, ‖w n‖) / (I.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardReal.le

/-- Every real-polynomial phase admitted by the blueprint correlation
seminorm is bounded by that seminorm. -/
theorem norm_polynomial_phase_sum_le_polynomialCorrelation
    {s : ℕ} {I : Finset ℤ} {w : ℤ → ℂ} {P : Polynomial ℝ}
    (hI : I.Nonempty) (hP : P.natDegree ≤ s - 1) :
    ‖(∑ n ∈ I, w n * unitFrequencyPhase (-(P.eval (n : ℝ)))) /
      (I.card : ℂ)‖ ≤ polynomialCorrelation s I w := by
  unfold polynomialCorrelation
  exact le_csSup (polynomialCorrelation_range_bddAbove hI)
    ⟨⟨P, hP⟩, rfl⟩

end FractionalPrimes
