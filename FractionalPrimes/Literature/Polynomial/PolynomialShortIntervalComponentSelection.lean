module

public import FractionalPrimes.Literature.Polynomial.PolynomialTypeIInverse

/-!
# Finite component selection for the conditional integer reduction

This isolates the exact triangle-inequality step in `lupo:conditional-integer`.
It retains the source component count, approximation error, and selected
component threshold on the integer interval `(X,X+H]`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators

private theorem sourceComponentCount_le_twice
    (L C : ℝ) (b N : ℕ)
    (hL : 2 ≤ L) (hC : 1 ≤ C)
    (hCount : (N : ℝ) ≤ C * L ^ (b : ℝ) + 1) :
    (N : ℝ) ≤ 2 * C * L ^ (b : ℝ) := by
  have hLpow : 1 ≤ L ^ (b : ℝ) := by
    simpa only [Real.rpow_natCast] using
      (one_le_pow₀ (show (1 : ℝ) ≤ L by linarith))
  have hCLpow : 1 ≤ C * L ^ (b : ℝ) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ C * L ^ (b : ℝ) :=
        mul_le_mul hC hLpow (by norm_num) (by positivity)
  calc
    (N : ℝ) ≤ C * L ^ (b : ℝ) + 1 := hCount
    _ ≤ C * L ^ (b : ℝ) + C * L ^ (b : ℝ) := by nlinarith [hCLpow]
    _ = 2 * C * L ^ (b : ℝ) := by ring

/-- If a target correlation is large, a residual costs at most one quarter
of the target, and there are at most `2 C (log X)^b` components, then one
component has the exact lower bound used in (P3) of
`lupo:conditional-integer`. -/
theorem exists_component_large_correlation
    (X H : ℕ) (A C : ℝ) (b : ℕ) (ι : Type*)
    (S : Finset ι) (w r : ℤ → ℂ) (F : ι → ℤ → ℂ)
    (P : Polynomial ℝ)
    (hH : 0 < H) (hC : 0 < C) (hCgeone : 1 ≤ C)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hCount : (S.card : ℝ) ≤
      C * (Real.log (X : ℝ)) ^ (b : ℝ) + 1)
    (hDecomposition : ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n = (∑ i ∈ S, F i n) + r n)
    (hResidual :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        r n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4)
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ i ∈ S,
      (3 / (8 * C)) * (H : ℝ) *
          (Real.log (X : ℝ)) ^ (-A - (b : ℝ)) <
        ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          F i n * unitFrequencyPhase (P.eval (n : ℝ))‖ := by
  classical
  let I := realIntegerInterval (X : ℝ) (H : ℝ)
  let phase : ℤ → ℂ := fun n => unitFrequencyPhase (P.eval (n : ℝ))
  let target : ℝ := (H : ℝ) * (Real.log (X : ℝ)) ^ (-A)
  let selectedBound : ℝ :=
    (3 / (8 * C)) * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A - (b : ℝ))
  have hLpos : 0 < Real.log (X : ℝ) := by linarith
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast hH
  have htargetPos : 0 < target := by
    dsimp [target]
    positivity
  have hselectedPos : 0 ≤ selectedBound := by
    dsimp [selectedBound]
    positivity
  have hCountTwice : (S.card : ℝ) ≤
      2 * C * (Real.log (X : ℝ)) ^ (b : ℝ) :=
    sourceComponentCount_le_twice (Real.log (X : ℝ)) C b S.card hL hCgeone hCount
  have hsumDecomp :
      (∑ n ∈ I, w n * phase n) =
        (∑ i ∈ S, ∑ n ∈ I, F i n * phase n) +
          ∑ n ∈ I, r n * phase n := by
    calc
      (∑ n ∈ I, w n * phase n) =
          ∑ n ∈ I, ((∑ i ∈ S, F i n) + r n) * phase n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hDecomposition n hn]
      _ = (∑ n ∈ I, (∑ i ∈ S, F i n) * phase n) +
            ∑ n ∈ I, r n * phase n := by
        simp only [add_mul, Finset.sum_add_distrib]
      _ = (∑ n ∈ I, ∑ i ∈ S, F i n * phase n) +
            ∑ n ∈ I, r n * phase n := by
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_mul]
      _ = (∑ i ∈ S, ∑ n ∈ I, F i n * phase n) +
            ∑ n ∈ I, r n * phase n := by
        congr 1
        rw [Finset.sum_comm]
  have hComponentsLarge :
      (3 / 4 : ℝ) * target <
        ‖∑ i ∈ S, ∑ n ∈ I, F i n * phase n‖ := by
    have htriangle := norm_add_le
      (∑ i ∈ S, ∑ n ∈ I, F i n * phase n)
      (∑ n ∈ I, r n * phase n)
    have hresidual' : ‖∑ n ∈ I, r n * phase n‖ ≤ target / 4 := by
      simpa [I, phase, target] using hResidual
    have hlarge' : target < ‖
        (∑ i ∈ S, ∑ n ∈ I, F i n * phase n) +
          ∑ n ∈ I, r n * phase n‖ := by
      simpa [I, phase, target, hsumDecomp] using hLarge
    nlinarith
  have hnormSum :
      ‖∑ i ∈ S, ∑ n ∈ I, F i n * phase n‖ ≤
        ∑ i ∈ S, ‖∑ n ∈ I, F i n * phase n‖ := norm_sum_le _ _
  have hsumNormsLarge :
      (3 / 4 : ℝ) * target <
        ∑ i ∈ S, ‖∑ n ∈ I, F i n * phase n‖ := lt_of_lt_of_le hComponentsLarge hnormSum
  by_contra hnot
  push Not at hnot
  have hEach : ∀ i ∈ S, ‖∑ n ∈ I, F i n * phase n‖ ≤ selectedBound := by
    intro i hi
    exact hnot i hi
  have hsumUpper :
      (∑ i ∈ S, ‖∑ n ∈ I, F i n * phase n‖) ≤ (S.card : ℝ) * selectedBound := by
    calc
      (∑ i ∈ S, ‖∑ n ∈ I, F i n * phase n‖) ≤
          ∑ _i ∈ S, selectedBound := by
        apply Finset.sum_le_sum
        intro i hi
        exact hEach i hi
      _ = (S.card : ℝ) * selectedBound := by simp
  have hcountUpper :
      (S.card : ℝ) * selectedBound ≤
        (2 * C * (Real.log (X : ℝ)) ^ (b : ℝ)) * selectedBound :=
    mul_le_mul_of_nonneg_right hCountTwice hselectedPos
  have hproduct :
      (2 * C * (Real.log (X : ℝ)) ^ (b : ℝ)) * selectedBound =
        (3 / 4 : ℝ) * target := by
    dsimp [selectedBound, target]
    have hpower :
        (Real.log (X : ℝ)) ^ (b : ℝ) *
            (Real.log (X : ℝ)) ^ (-A - (b : ℝ)) =
          (Real.log (X : ℝ)) ^ (-A) := by
      calc
        _ = (Real.log (X : ℝ)) ^ ((b : ℝ) + (-A - (b : ℝ))) :=
          (Real.rpow_add hLpos _ _).symm
        _ = (Real.log (X : ℝ)) ^ (-A) := by congr 1 <;> ring
    calc
      (2 * C * (Real.log (X : ℝ)) ^ (b : ℝ)) *
          (3 / (8 * C) * (H : ℝ) *
            (Real.log (X : ℝ)) ^ (-A - (b : ℝ))) =
          (2 * C) * (3 / (8 * C)) * (H : ℝ) *
            ((Real.log (X : ℝ)) ^ (b : ℝ) *
              (Real.log (X : ℝ)) ^ (-A - (b : ℝ))) := by ring
      _ = (3 / 4 : ℝ) * ((H : ℝ) *
            (Real.log (X : ℝ)) ^ (-A)) := by
        rw [hpower]
        field_simp [ne_of_gt hC]
        ring
  have : (3 / 4 : ℝ) * target < (3 / 4 : ℝ) * target := by
    calc
      (3 / 4 : ℝ) * target <
          ∑ i ∈ S, ‖∑ n ∈ I, F i n * phase n‖ := hsumNormsLarge
      _ ≤ (S.card : ℝ) * selectedBound := hsumUpper
      _ ≤ (2 * C * (Real.log (X : ℝ)) ^ (b : ℝ)) * selectedBound := hcountUpper
      _ = (3 / 4 : ℝ) * target := hproduct
  exact (lt_irrefl _ this)

/-- The source threshold upgrades the component-selection lower bound to
the parameter `δ H` required by each of the three inverse clauses. -/
theorem exists_component_gt_deltaH_of_source_budget
    (X H : ℕ) (A C : ℝ) (b D : ℕ) (ι : Type*)
    (S : Finset ι) (w r : ℤ → ℂ) (F : ι → ℤ → ℂ)
    (P : Polynomial ℝ) (δ : ℝ)
    (hH : 0 < H) (hC : 0 < C) (hCgeone : 1 ≤ C)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hDelta : δ = (Real.log (X : ℝ)) ^ (-(D : ℝ)))
    (hThreshold : 4 * C < (Real.log (X : ℝ)) ^ ((D : ℝ) - A - (b : ℝ)))
    (hCount : (S.card : ℝ) ≤
      C * (Real.log (X : ℝ)) ^ (b : ℝ) + 1)
    (hDecomposition : ∀ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n = (∑ i ∈ S, F i n) + r n)
    (hResidual :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        r n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) / 4)
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ i ∈ S, δ * (H : ℝ) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        F i n * unitFrequencyPhase (P.eval (n : ℝ))‖ := by
  obtain ⟨i, hi, hcomponent⟩ := exists_component_large_correlation
    X H A C b ι S w r F P hH hC hCgeone hL hCount hDecomposition hResidual hLarge
  refine ⟨i, hi, ?_⟩
  have hLpos : 0 < Real.log (X : ℝ) := by linarith
  have hgap :
      (3 / (8 * C)) * (Real.log (X : ℝ)) ^ (-A - (b : ℝ)) >
        (Real.log (X : ℝ)) ^ (-(D : ℝ)) := by
    let x := Real.log (X : ℝ)
    have hx : 0 < x := hLpos
    have hcoef : 0 < 3 / (8 * C) := by positivity
    have hscaled : 1 < (3 / (8 * C)) * x ^ ((D : ℝ) - A - (b : ℝ)) := by
      have hmul := mul_lt_mul_of_pos_left hThreshold hcoef
      have hconst : (1 : ℝ) < (3 / (8 * C)) * (4 * C) := by
        field_simp [ne_of_gt hC]
        norm_num
      exact lt_trans hconst (by simpa [mul_assoc] using hmul)
    calc
      (3 / (8 * C)) * x ^ (-A - (b : ℝ)) =
          ((3 / (8 * C)) * x ^ ((D : ℝ) - A - (b : ℝ))) *
            x ^ (-(D : ℝ)) := by
        calc
          (3 / (8 * C)) * x ^ (-A - (b : ℝ)) =
              (3 / (8 * C)) *
                (x ^ ((D : ℝ) - A - (b : ℝ)) * x ^ (-(D : ℝ))) := by
            congr 1
            rw [← Real.rpow_add hx]
            congr 1 <;> ring
          _ = ((3 / (8 * C)) * x ^ ((D : ℝ) - A - (b : ℝ))) *
                x ^ (-(D : ℝ)) := by ring
      _ > 1 * x ^ (-(D : ℝ)) :=
        mul_lt_mul_of_pos_right hscaled (Real.rpow_pos_of_pos hx _)
      _ = x ^ (-(D : ℝ)) := by
        ring
  calc
    δ * (H : ℝ) =
        (Real.log (X : ℝ)) ^ (-(D : ℝ)) * (H : ℝ) := by rw [hDelta]
    _ < (3 / (8 * C)) * (H : ℝ) *
        (Real.log (X : ℝ)) ^ (-A - (b : ℝ)) := by
      have hHpos : 0 < (H : ℝ) := by exact_mod_cast hH
      nlinarith [hgap, hHpos]
    _ < ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        F i n * unitFrequencyPhase (P.eval (n : ℝ))‖ := hcomponent

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.exists_component_large_correlation
#print axioms FractionalPrimes.Literature.Polynomial.exists_component_gt_deltaH_of_source_budget
