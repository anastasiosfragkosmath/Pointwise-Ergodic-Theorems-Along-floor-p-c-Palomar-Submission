module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionReindex
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- Transfer the selected residue-class lower bound to the density required
by the degree induction at `N' = ⌈N/r⌉`. The factor `1/4` is the exact
source choice; the stronger intermediate bound with factor `1/2` follows
from the upper ceiling estimate. -/
theorem scalarWeyl_inductionDensityHandoff
    {N r N' : ℕ} {δ V A : ℝ}
    (hr : 0 < (r : ℝ))
    (hN'upper : (N' : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ))
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hV : 1 ≤ V)
    (hselected : δ * (N : ℝ) / ((r : ℝ) * V) ≤ A) :
    0 < δ / (4 * V) ∧ δ / (4 * V) < 1 / 2 ∧
      (δ / (4 * V)) * (N' : ℝ) ≤ A := by
  have hVpos : 0 < V := by linarith
  have hdenpos : 0 < 4 * V := by positivity
  have hδ'pos : 0 < δ / (4 * V) := div_pos hδ hdenpos
  have hδ'le : δ / (4 * V) ≤ δ / 4 := by
    rw [div_le_div_iff₀ hdenpos (by norm_num : (0 : ℝ) < 4)]
    have hδV : δ ≤ δ * V :=
      by simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hV (le_of_lt hδ))
    nlinarith
  have hδfour : δ / 4 < 1 / 8 := by
    calc
      δ / 4 < (1 / 2) / 4 :=
        div_lt_div_of_pos_right hδhalf (by norm_num : (0 : ℝ) < 4)
      _ = 1 / 8 := by norm_num
  have hδ'half : δ / (4 * V) < 1 / 2 := by
    calc
      δ / (4 * V) ≤ δ / 4 := hδ'le
      _ < 1 / 8 := hδfour
      _ < 1 / 2 := by norm_num
  have hscale : 0 ≤ δ / (4 * V) := le_of_lt hδ'pos
  have hrV : 0 < (r : ℝ) * V := mul_pos hr hVpos
  have h2rV : 0 < 2 * (r : ℝ) * V := by positivity
  have hselected' : δ * (N : ℝ) / (2 * (r : ℝ) * V) ≤ A := by
    have hquot : δ * (N : ℝ) / (2 * (r : ℝ) * V) ≤
        δ * (N : ℝ) / ((r : ℝ) * V) := by
      rw [div_le_div_iff₀ h2rV hrV]
      have hnum : 0 ≤ δ * (N : ℝ) := mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
      have hden : 0 ≤ (r : ℝ) * V := le_of_lt hrV
      have hnumden : 0 ≤ δ * (N : ℝ) * ((r : ℝ) * V) :=
        mul_nonneg hnum hden
      nlinarith
    exact hquot.trans hselected
  have hmain : (δ / (4 * V)) * (N' : ℝ) ≤ A := by
    calc
      (δ / (4 * V)) * (N' : ℝ) ≤
          (δ / (4 * V)) * (2 * (N : ℝ) / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hN'upper hscale
      _ = δ * (N : ℝ) / (2 * (r : ℝ) * V) := by
        field_simp [ne_of_gt hr, ne_of_gt hVpos, ne_of_gt h2rV]
        <;> ring
      _ ≤ A := hselected'
  exact ⟨hδ'pos, hδ'half, hmain⟩

/-- The affine polynomial encoding the substitution `n = c + r*k` has no
greater degree than the low-degree polynomial being substituted. -/
theorem scalarWeyl_affineSubstitution_degree
    {d : ℕ} (P : Polynomial ℝ) (hP : P.natDegree ≤ d - 1)
    (c : ℤ) (r : ℕ) :
    (P.comp (Polynomial.C (r : ℝ) * Polynomial.X +
      Polynomial.C (c : ℝ))).natDegree ≤ d - 1 := by
  have hlinear :
      (Polynomial.C (r : ℝ) * Polynomial.X + Polynomial.C (c : ℝ)).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  calc
    (P.comp (Polynomial.C (r : ℝ) * Polynomial.X +
        Polynomial.C (c : ℝ))).natDegree ≤
        P.natDegree *
          (Polynomial.C (r : ℝ) * Polynomial.X + Polynomial.C (c : ℝ)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ (d - 1) * 1 := Nat.mul_le_mul hP hlinear
    _ = d - 1 := by simp

/-- Evaluation of the affine polynomial substitution is exactly evaluation
at `c + r*k`, with the source's integer and natural casts. -/
theorem scalarWeyl_affineSubstitution_eval
    (P : Polynomial ℝ) (c : ℤ) (r : ℕ) (k : ℤ) :
    (P.comp (Polynomial.C (r : ℝ) * Polynomial.X +
      Polynomial.C (c : ℝ))).eval (k : ℝ) =
        P.eval ((c : ℝ) + (r : ℝ) * (k : ℝ)) := by
  rw [Polynomial.eval_comp]
  congr 1
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

end FractionalPrimes.Literature.Polynomial
