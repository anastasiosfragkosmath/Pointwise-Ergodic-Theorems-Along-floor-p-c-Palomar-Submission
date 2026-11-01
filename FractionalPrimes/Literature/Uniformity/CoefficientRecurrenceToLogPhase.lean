module

public import FractionalPrimes.Literature.Uniformity.ScalarInverseClauses
public import FractionalPrimes.Literature.Uniformity.VariationCalculusC1
public import FractionalPrimes.Literature.Uniformity.ArchimedeanTwist
public import FractionalPrimes.Literature.Uniformity.ENNRealVariationProduct
public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# From a coefficient recurrence to a logarithmic phase

This file formalizes blueprint item `lu:log-phase`.  The first group of
lemmas carries out the finite descending integer correction used in the
approved proof.  The analytic variation estimate is added after this
standalone algebraic step has been checked.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The nearest-integer choice used at one stage of the descending
coefficient correction. -/
def recurrenceNearestInteger (Q : ℕ) (r : ℕ → ℝ) (j : ℕ) : ℤ :=
  Int.floor ((Q : ℝ) * r j + 1 / 2)

/-- The explicit finite solution of
`a_j + X a_(j+1) = -k_j`, with `a_(d+1)=0`. -/
def recurrenceIntegerCorrection
    (d : ℕ) (X : ℤ) (k : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc j d, -((-X) ^ (m - j) * k m)

@[simp]
theorem recurrenceIntegerCorrection_eq_zero_of_lt
    (d : ℕ) (X : ℤ) (k : ℕ → ℤ) {j : ℕ} (hdj : d < j) :
    recurrenceIntegerCorrection d X k j = 0 := by
  rw [recurrenceIntegerCorrection, Finset.Icc_eq_empty_of_lt hdj]
  simp

/-- The explicit corrections satisfy the required descending recurrence. -/
theorem recurrenceIntegerCorrection_add_succ
    (d : ℕ) (X : ℤ) (k : ℕ → ℤ) {j : ℕ} (hjd : j ≤ d) :
    recurrenceIntegerCorrection d X k j +
        X * recurrenceIntegerCorrection d X k (j + 1) = -k j := by
  have hsplit : Finset.Icc j d = insert j (Finset.Icc (j + 1) d) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hjnot : j ∉ Finset.Icc (j + 1) d := by simp
  rw [recurrenceIntegerCorrection, hsplit, Finset.sum_insert hjnot]
  simp only [Nat.sub_self, pow_zero, one_mul]
  rw [recurrenceIntegerCorrection, Finset.mul_sum]
  have htail :
      ∑ m ∈ Finset.Icc (j + 1) d,
          -((-X) ^ (m - j) * k m) +
        ∑ m ∈ Finset.Icc (j + 1) d,
          X * -((-X) ^ (m - (j + 1)) * k m) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro m hm
    have hmj : j + 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hexp : m - j = (m - (j + 1)) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [add_assoc, htail]
  simp

/-- Above the terminal degree every integer correction vanishes. -/
@[simp]
theorem recurrenceIntegerCorrection_succ_degree
    (d : ℕ) (X : ℤ) (k : ℕ → ℤ) :
    recurrenceIntegerCorrection d X k (d + 1) = 0 := by
  exact recurrenceIntegerCorrection_eq_zero_of_lt d X k (by omega)

/-- The corrected centered coefficients from the approved descending
construction.  The constant coefficient is deliberately unchanged. -/
def correctedRecurrenceCoefficient
    (d Q : ℕ) (X : ℤ) (r : ℕ → ℝ) (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then ν 0 else
    ν j +
      (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
        ((Q : ℝ) * (j : ℝ))

/-- The nearest-integer residual is exactly the centered representative. -/
theorem recurrenceNearestInteger_residual
    (Q : ℕ) (r : ℕ → ℝ) (j : ℕ) :
    (Q : ℝ) * r j - (recurrenceNearestInteger Q r j : ℝ) =
      centeredFrequency ((Q : ℝ) * r j) := by
  rfl

/-- The absolute nearest-integer residual is the source's distance to the
integer lattice. -/
theorem abs_recurrenceNearestInteger_residual
    (Q : ℕ) (r : ℕ → ℝ) (j : ℕ) :
    |(Q : ℝ) * r j - (recurrenceNearestInteger Q r j : ℝ)| =
      realDistanceToIntegers ((Q : ℝ) * r j) := by
  rw [recurrenceNearestInteger_residual,
    realDistanceToIntegers_eq_abs_centered]

/-- The finite integer correction converts each recurrence into its centered
representative without changing the phase modulo a rational periodic factor. -/
theorem correctedRecurrenceCoefficient_identity
    (d Q : ℕ) (X : ℤ) (r ν : ℕ → ℝ)
    (hQ : 1 ≤ Q) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    (hr : r j = (j : ℝ) * ν j + (j + 1 : ℕ) * (X : ℝ) * ν (j + 1)) :
    (Q : ℝ) *
        ((j : ℝ) * correctedRecurrenceCoefficient d Q X r ν j +
          (j + 1 : ℕ) * (X : ℝ) *
            correctedRecurrenceCoefficient d Q X r ν (j + 1)) =
      centeredFrequency ((Q : ℝ) * r j) := by
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hjsucc0 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hjne : j ≠ 0 := by omega
  have hjsuccne : j + 1 ≠ 0 := by omega
  rw [correctedRecurrenceCoefficient, if_neg hjne,
    correctedRecurrenceCoefficient, if_neg hjsuccne]
  have hcorr := recurrenceIntegerCorrection_add_succ d X
    (recurrenceNearestInteger Q r) hjd
  have hcorrR :
      (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) +
          (X : ℝ) *
            (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r)
              (j + 1) : ℝ) =
        -(recurrenceNearestInteger Q r j : ℝ) := by
    exact_mod_cast hcorr
  calc
    (Q : ℝ) *
        ((j : ℝ) * (ν j +
            (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
              ((Q : ℝ) * (j : ℝ))) +
          (j + 1 : ℕ) * (X : ℝ) * (ν (j + 1) +
            (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r)
              (j + 1) : ℝ) / ((Q : ℝ) * (j + 1 : ℕ)))) =
        (Q : ℝ) * r j +
          ((recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) +
            (X : ℝ) *
              (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r)
                (j + 1) : ℝ)) := by
          rw [hr]
          field_simp [hQ0, hj0, hjsucc0]
          ring
    _ = (Q : ℝ) * r j - (recurrenceNearestInteger Q r j : ℝ) := by
      rw [hcorrR]
      ring
    _ = centeredFrequency ((Q : ℝ) * r j) :=
      recurrenceNearestInteger_residual Q r j

/-- The corrected recurrence has exactly the normalized quantitative bound
from `lu:log-phase`, with `D=B/Q` and no additional loss. -/
theorem correctedRecurrenceCoefficient_bound
    (d Q : ℕ) (X : ℤ) (H B : ℝ) (r ν : ℕ → ℝ)
    (hQ : 1 ≤ Q) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    (hr : r j = (j : ℝ) * ν j + (j + 1 : ℕ) * (X : ℝ) * ν (j + 1))
    (hrec : realDistanceToIntegers ((Q : ℝ) * r j) ≤
      B * (X : ℝ) / H ^ (j + 1)) :
    |(j : ℝ) * correctedRecurrenceCoefficient d Q X r ν j +
        (j + 1 : ℕ) * (X : ℝ) *
          correctedRecurrenceCoefficient d Q X r ν (j + 1)| ≤
      (B / (Q : ℝ)) * (X : ℝ) / H ^ (j + 1) := by
  have hQpos : (0 : ℝ) < Q := by positivity
  let s : ℝ :=
    (j : ℝ) * correctedRecurrenceCoefficient d Q X r ν j +
      (j + 1 : ℕ) * (X : ℝ) *
        correctedRecurrenceCoefficient d Q X r ν (j + 1)
  have hid : (Q : ℝ) * s = centeredFrequency ((Q : ℝ) * r j) := by
    dsimp [s]
    exact correctedRecurrenceCoefficient_identity d Q X r ν hQ hj hjd hr
  have hscaled : (Q : ℝ) * |s| =
      realDistanceToIntegers ((Q : ℝ) * r j) := by
    calc
      (Q : ℝ) * |s| = |(Q : ℝ) * s| := by
        rw [abs_mul, abs_of_pos hQpos]
      _ = |centeredFrequency ((Q : ℝ) * r j)| := by rw [hid]
      _ = realDistanceToIntegers ((Q : ℝ) * r j) := by
        rw [realDistanceToIntegers_eq_abs_centered]
  change |s| ≤ _
  calc
    |s| = ((Q : ℝ) * |s|) / (Q : ℝ) := by
      field_simp
    _ = realDistanceToIntegers ((Q : ℝ) * r j) / (Q : ℝ) := by
      rw [hscaled]
    _ ≤ (B * (X : ℝ) / H ^ (j + 1)) / (Q : ℝ) := by
      exact div_le_div_of_nonneg_right hrec hQpos.le
    _ = (B / (Q : ℝ)) * (X : ℝ) / H ^ (j + 1) := by ring

/-- The terminal corrected coefficient remains zero when the original phase
has degree at most `d`. -/
theorem correctedRecurrenceCoefficient_succ_degree
    (d Q : ℕ) (X : ℤ) (r ν : ℕ → ℝ) (hν : ν (d + 1) = 0) :
    correctedRecurrenceCoefficient d Q X r ν (d + 1) = 0 := by
  simp [correctedRecurrenceCoefficient, hν]

/-- Difference between a corrected coefficient and the coefficient sequence
of the truncated logarithm selected by its linear coefficient. -/
def logarithmicModelError (X : ℝ) (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  ν j - ((-1 : ℝ) ^ (j - 1) * ν 1) / ((j : ℝ) * X ^ (j - 1))

@[simp]
theorem logarithmicModelError_one (X : ℝ) (ν : ℕ → ℝ) :
    logarithmicModelError X ν 1 = 0 := by
  simp [logarithmicModelError]

/-- The logarithmic model is an exact homogeneous solution of the adjacent
coefficient recurrence. -/
theorem logarithmicModelError_recurrence
    (X : ℝ) (hX : X ≠ 0) (ν : ℕ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) * logarithmicModelError X ν j +
        (j + 1 : ℕ) * X * logarithmicModelError X ν (j + 1) =
      (j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1) := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hjsucc0 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsub : j + 1 - 1 = j := by omega
  have hjpow : j - 1 + 1 = j := by omega
  simp only [logarithmicModelError, hsub]
  rw [show X ^ j = X ^ (j - 1) * X by
    rw [← pow_succ, hjpow]]
  field_simp [hj0, hjsucc0, hX]
  rw [show (-1 : ℝ) ^ j = (-1 : ℝ) ^ (j - 1) * (-1) by
    rw [← pow_succ, hjpow]]
  ring

/-- The scaled error quantity `b_j=j H^j |w_j|` from the approved proof. -/
def logarithmicModelErrorBudget (H X : ℝ) (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) * H ^ j * |logarithmicModelError X ν j|

theorem logarithmicModelErrorBudget_nonneg
    (H X : ℝ) (ν : ℕ → ℝ) (j : ℕ) (hH : 0 ≤ H) :
    0 ≤ logarithmicModelErrorBudget H X ν j := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH _)) (abs_nonneg _)

/-- One quantitative step of the finite logarithmic-model induction. -/
theorem logarithmicModelErrorBudget_succ_le
    (H X D : ℝ) (ν : ℕ → ℝ) {j : ℕ}
    (hj : 1 ≤ j) (hH : 0 < H) (hX : 0 < X)
    (hrec : |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
      D * X / H ^ (j + 1)) :
    logarithmicModelErrorBudget H X ν (j + 1) ≤
      (H / X) * logarithmicModelErrorBudget H X ν j + D := by
  let w : ℕ → ℝ := logarithmicModelError X ν
  let R : ℝ := (j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)
  have hrelation : (j : ℝ) * w j + (j + 1 : ℕ) * X * w (j + 1) = R := by
    dsimp [w, R]
    exact logarithmicModelError_recurrence X hX.ne' ν hj
  have hsolve : (j + 1 : ℕ) * X * w (j + 1) = R - (j : ℝ) * w j := by
    linarith
  have habs : (j + 1 : ℕ) * X * |w (j + 1)| ≤ |R| + (j : ℝ) * |w j| := by
    calc
      (j + 1 : ℕ) * X * |w (j + 1)| =
          |(j + 1 : ℕ) * X * w (j + 1)| := by
            symm
            calc
              |(j + 1 : ℕ) * X * w (j + 1)| =
                  |((j + 1 : ℕ) : ℝ) * X| * |w (j + 1)| :=
                    abs_mul _ _
              _ = |((j + 1 : ℕ) : ℝ)| * |X| * |w (j + 1)| := by
                rw [abs_mul]
              _ = _ := by
                rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hX]
      _ = |R - (j : ℝ) * w j| := by rw [hsolve]
      _ ≤ |R| + |(j : ℝ) * w j| := abs_sub _ _
      _ = |R| + (j : ℝ) * |w j| := by
        congr 1
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hfactor : 0 ≤ H ^ (j + 1) / X := by positivity
  have hmul := mul_le_mul_of_nonneg_left habs hfactor
  have hR : |R| ≤ D * X / H ^ (j + 1) := by
    simpa [R] using hrec
  have hRmul := mul_le_mul_of_nonneg_left hR hfactor
  have hRscaled : (H ^ (j + 1) / X) * |R| ≤ D := by
    calc
      (H ^ (j + 1) / X) * |R| ≤
          (H ^ (j + 1) / X) * (D * X / H ^ (j + 1)) := hRmul
      _ = D := by
        field_simp [hX.ne', ne_of_gt (pow_pos hH (j + 1))]
  dsimp [logarithmicModelErrorBudget, w]
  calc
    (j + 1 : ℕ) * H ^ (j + 1) *
        |logarithmicModelError X ν (j + 1)| =
      (H ^ (j + 1) / X) *
        ((j + 1 : ℕ) * X * |w (j + 1)|) := by
          dsimp [w]
          field_simp [hX.ne']
    _ ≤ (H ^ (j + 1) / X) * (|R| + (j : ℝ) * |w j|) := hmul
    _ = (H ^ (j + 1) / X) * |R| +
        (H ^ (j + 1) / X) * ((j : ℝ) * |w j|) := by ring
    _ ≤ D + (H ^ (j + 1) / X) * ((j : ℝ) * |w j|) := by
      simpa [add_comm] using
        (add_le_add_right hRscaled
          ((H ^ (j + 1) / X) * ((j : ℝ) * |w j|)))
    _ = (H / X) * ((j : ℝ) * H ^ j *
        |logarithmicModelError X ν j|) + D := by
          dsimp [w]
          rw [pow_succ]
          ring

/-- Iterating the previous step gives the sharp finite bound
`b_j ≤ (j-1)D` for every `1 ≤ j ≤ d+1`. -/
theorem logarithmicModelErrorBudget_le
    (d : ℕ) (H X D : ℝ) (ν : ℕ → ℝ)
    (_hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1))
    {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d + 1) :
    logarithmicModelErrorBudget H X ν j ≤ ((j - 1 : ℕ) : ℝ) * D := by
  have hX : 0 < X := lt_of_lt_of_le hH hHX
  have hratio : H / X ≤ 1 := (div_le_one hX).2 hHX
  have hind : ∀ m : ℕ, 1 ≤ m → m ≤ d + 1 →
      logarithmicModelErrorBudget H X ν m ≤ ((m - 1 : ℕ) : ℝ) * D := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm hmd
      cases m with
      | zero => omega
      | succ k =>
        by_cases hkzero : k = 0
        · subst k
          simp [logarithmicModelErrorBudget]
        · have hk : 1 ≤ k := by omega
          have hkd : k ≤ d := by omega
          have hprev := ih k (Nat.lt_succ_self k) hk (by omega)
          have hstep := logarithmicModelErrorBudget_succ_le H X D ν hk hH hX
            (hrec k hk hkd)
          have hbnonneg := logarithmicModelErrorBudget_nonneg H X ν k hH.le
          have hmul : (H / X) * logarithmicModelErrorBudget H X ν k ≤
              logarithmicModelErrorBudget H X ν k :=
            mul_le_of_le_one_left hbnonneg hratio
          have hkcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
            exact_mod_cast (show k = (k - 1) + 1 by omega)
          calc
            logarithmicModelErrorBudget H X ν (k + 1) ≤
                (H / X) * logarithmicModelErrorBudget H X ν k + D := hstep
            _ ≤ logarithmicModelErrorBudget H X ν k + D := by linarith
            _ ≤ ((k - 1 : ℕ) : ℝ) * D + D := by linarith
            _ = (((k + 1) - 1 : ℕ) : ℝ) * D := by
              rw [show k + 1 - 1 = k by omega, hkcast]
              ring
  exact hind j hj hjd

/-- The budget induction implies the coefficientwise error bound used in the
derivative estimate. -/
theorem abs_logarithmicModelError_le
    (d : ℕ) (H X D : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1))
    {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d + 1) :
    |logarithmicModelError X ν j| ≤ D / H ^ j := by
  have hbudget := logarithmicModelErrorBudget_le d H X D ν hD hH hHX hrec hj hjd
  have hcast : (((j - 1 : ℕ) : ℝ) : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast Nat.sub_le j 1
  have hupper : logarithmicModelErrorBudget H X ν j ≤ (j : ℝ) * D :=
    hbudget.trans (mul_le_mul_of_nonneg_right hcast hD)
  have hjpos : (0 : ℝ) < j := by positivity
  have hpowpos : 0 < H ^ j := pow_pos hH j
  have hcancel : H ^ j * |logarithmicModelError X ν j| ≤ D := by
    have hupper' : (j : ℝ) *
        (H ^ j * |logarithmicModelError X ν j|) ≤ (j : ℝ) * D := by
      simpa [logarithmicModelErrorBudget, mul_assoc] using hupper
    exact (mul_le_mul_iff_of_pos_left hjpos).mp hupper'
  apply (le_div_iff₀ hpowpos).2
  simpa [mul_comm] using hcancel

/-- The zero terminal coefficient converts the sharp `b_(d+1)` bound into
the approved bound for the selected logarithmic frequency coefficient. -/
theorem abs_linearCoefficient_le_of_terminal_zero
    (d : ℕ) (hd : 1 ≤ d) (H X D : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hterminal : ν (d + 1) = 0)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1)) :
    |ν 1| ≤ (d : ℝ) * D * X ^ d / H ^ (d + 1) := by
  have hX : 0 < X := lt_of_lt_of_le hH hHX
  have hbudget := logarithmicModelErrorBudget_le d H X D ν hD hH hHX hrec
    (j := d + 1) (by omega) (by omega)
  have hw : |logarithmicModelError X ν (d + 1)| =
      |ν 1| / (((d + 1 : ℕ) : ℝ) * X ^ d) := by
    simp [logarithmicModelError, hterminal, show d + 1 - 1 = d by omega,
      abs_div, abs_mul, abs_pow, abs_of_pos hX]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
  have hformula : logarithmicModelErrorBudget H X ν (d + 1) =
      H ^ (d + 1) * |ν 1| / X ^ d := by
    rw [logarithmicModelErrorBudget, hw]
    field_simp [ne_of_gt hX, show (((d + 1 : ℕ) : ℝ) : ℝ) ≠ 0 by positivity]
  rw [hformula, show d + 1 - 1 = d by omega] at hbudget
  have hmul : H ^ (d + 1) * |ν 1| ≤ (d : ℝ) * D * X ^ d := by
    exact (div_le_iff₀ (pow_pos hX d)).mp hbudget
  apply (le_div_iff₀ (pow_pos hH (d + 1))).2
  simpa [mul_comm, mul_left_comm] using hmul

/-- The rational polynomial by which the original phase differs from its
integer-corrected phase. -/
def recurrenceRationalCorrection
    (d Q : ℕ) (X : ℤ) (r : ℕ → ℝ) (n : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 d,
    -(recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
        ((Q : ℝ) * (j : ℝ)) * (((n - X : ℤ) : ℝ) ^ j)

/-- A single rational correction term changes by an integer after the shift
`Q*d!`. -/
theorem recurrenceRationalCorrection_term_increment_int
    (d Q j : ℕ) (hQ : 1 ≤ Q) (hj : 1 ≤ j) (hjd : j ≤ d)
    (a u : ℤ) :
    ∃ z : ℤ,
      -(a : ℝ) / ((Q : ℝ) * (j : ℝ)) *
          (((u + (Q * d.factorial : ℕ) : ℤ) : ℝ) ^ j - (u : ℝ) ^ j) =
        (z : ℝ) := by
  let q : ℤ := (Q * d.factorial : ℕ)
  have hdiv : q ∣ (u + q) ^ j - u ^ j := by
    have hp := sub_dvd_pow_sub_pow (u + q) u j
    simpa [q] using hp
  rcases hdiv with ⟨v, hv⟩
  have hfacDvd : j ∣ d.factorial := Nat.dvd_factorial (by omega) hjd
  have hfac : j * (d.factorial / j) = d.factorial := Nat.mul_div_cancel' hfacDvd
  have hfacR : (j : ℝ) * ((d.factorial / j : ℕ) : ℝ) =
      (d.factorial : ℕ) := by exact_mod_cast hfac
  have hdivR : ((d.factorial / j : ℕ) : ℝ) =
      (d.factorial : ℕ) / (j : ℝ) := by
    apply (eq_div_iff (by positivity : (j : ℝ) ≠ 0)).2
    simpa [mul_comm] using hfacR
  let m : ℤ := (d.factorial / j : ℕ)
  have hmR : (m : ℝ) = (d.factorial : ℕ) / (j : ℝ) := by
    simpa only [m, Int.cast_natCast] using hdivR
  refine ⟨-a * m * v, ?_⟩
  have hvR : ((((u + q) ^ j - u ^ j : ℤ) : ℤ) : ℝ) =
      (q : ℝ) * (v : ℝ) := by exact_mod_cast hv
  change -(a : ℝ) / ((Q : ℝ) * (j : ℝ)) *
      (((u + q : ℤ) : ℝ) ^ j - (u : ℝ) ^ j) = _
  have hpowCast : (((u + q : ℤ) : ℝ) ^ j - (u : ℝ) ^ j) =
      ((((u + q) ^ j - u ^ j : ℤ) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hpowCast, hvR]
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hqR : (q : ℝ) = (Q : ℝ) * (d.factorial : ℕ) := by
    simp [q]
  rw [hqR]
  push_cast
  rw [hmR]
  field_simp [hQ0, hj0]

/-- The entire rational correction changes by an integer after the period
`Q*d!`. -/
theorem recurrenceRationalCorrection_increment_int
    (d Q : ℕ) (X : ℤ) (r : ℕ → ℝ) (hQ : 1 ≤ Q) (n : ℤ) :
    ∃ z : ℤ,
      recurrenceRationalCorrection d Q X r
          (n + (Q * d.factorial : ℕ)) -
        recurrenceRationalCorrection d Q X r n = (z : ℝ) := by
  classical
  let s := Finset.Icc 1 d
  let term : ℕ → ℝ := fun j =>
    -(recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
        ((Q : ℝ) * (j : ℝ)) *
      (((((n - X) + (Q * d.factorial : ℕ) : ℤ) : ℝ) ^ j) -
        (((n - X : ℤ) : ℝ) ^ j))
  have hterm : ∀ j ∈ s, ∃ z : ℤ, term j = (z : ℝ) := by
    intro j hjmem
    have hjb := Finset.mem_Icc.mp hjmem
    simpa [term] using recurrenceRationalCorrection_term_increment_int
      d Q j hQ hjb.1 hjb.2
        (recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j) (n - X)
  let z : ℕ → ℤ := fun j =>
    if hj : j ∈ s then Classical.choose (hterm j hj) else 0
  have hz : ∀ j ∈ s, term j = (z j : ℝ) := by
    intro j hj
    simp only [z, dif_pos hj]
    exact Classical.choose_spec (hterm j hj)
  refine ⟨∑ j ∈ s, z j, ?_⟩
  have hsum : ∑ j ∈ s, term j = ((∑ j ∈ s, z j : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hz j hj
  rw [← hsum]
  unfold recurrenceRationalCorrection
  dsimp [s, term]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The unit-frequency rational correction is periodic with the exact period
`Q*d!`. -/
theorem unitFrequencyPhase_recurrenceRationalCorrection_periodic
    (d Q : ℕ) (X : ℤ) (r : ℕ → ℝ) (hQ : 1 ≤ Q) (n : ℤ) :
    unitFrequencyPhase
        (recurrenceRationalCorrection d Q X r
          (n + (Q * d.factorial : ℕ))) =
      unitFrequencyPhase (recurrenceRationalCorrection d Q X r n) := by
  rcases recurrenceRationalCorrection_increment_int d Q X r hQ n with ⟨z, hz⟩
  have hadd : recurrenceRationalCorrection d Q X r
        (n + (Q * d.factorial : ℕ)) =
      recurrenceRationalCorrection d Q X r n + (z : ℝ) := by
    linarith
  rw [hadd, unitFrequencyPhase_add, unitFrequencyPhase_int, mul_one]

/-- The exact finite geometric remainder underlying the logarithmic-phase
comparison. -/
theorem finiteGeometricLogRemainder
    (d : ℕ) (x : ℝ) (hx : 1 - x ≠ 0) :
    (∑ k ∈ Finset.range d, x ^ k) - (1 - x)⁻¹ =
      -(x ^ d) / (1 - x) := by
  have hgeom := geom_sum_mul_neg x d
  field_simp [hx]
  linarith

/-- The source's exact finite-geometric derivative identity, written with
the index shifted from `j=1,...,d` to `k=0,...,d-1`. -/
theorem finiteLogarithmicDerivativeIdentity
    (d : ℕ) (X u c : ℝ) (hX : X ≠ 0) (hXu : X + u ≠ 0) :
    (∑ k ∈ Finset.range d,
        ((-1 : ℝ) ^ k * c / X ^ k) * u ^ k) - X * c / (X + u) =
      -c * (-u / X) ^ d / (1 + u / X) := by
  have hden : 1 - (-u / X) ≠ 0 := by
    intro hzero
    have : X + u = 0 := by
      field_simp [hX] at hzero
      linarith
    exact hXu this
  have hsum :
      ∑ k ∈ Finset.range d, ((-1 : ℝ) ^ k * c / X ^ k) * u ^ k =
        c * ∑ k ∈ Finset.range d, (-u / X) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [div_pow, neg_pow]
    ring
  have hlog : X * c / (X + u) = c * (1 - (-u / X))⁻¹ := by
    field_simp [hX, hXu, hden]
    ring
  rw [hsum, hlog]
  have hgeom := finiteGeometricLogRemainder d (-u / X) hden
  calc
    c * ∑ k ∈ Finset.range d, (-u / X) ^ k -
        c * (1 - -u / X)⁻¹ =
      c * ((∑ k ∈ Finset.range d, (-u / X) ^ k) -
        (1 - (-u / X))⁻¹) := by ring
    _ = c * (-((-u / X) ^ d) / (1 - (-u / X))) := by rw [hgeom]
    _ = -c * (-u / X) ^ d / (1 + u / X) := by ring

/-- The finite corrected polynomial in centered real coordinates. -/
def correctedCenteredRealPhase (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), ν j * (t - X) ^ j

/-- The real phase after subtracting the selected logarithmic phase. -/
def logarithmicComparisonRealPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) (t : ℝ) : ℝ :=
  correctedCenteredRealPhase d X ν t - X * ν 1 * Real.log t

/-- The smooth unit-complex factor remaining after the logarithmic twist. -/
def logarithmicComparisonPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) (t : ℝ) : ℂ :=
  unitFrequencyPhase (logarithmicComparisonRealPhase d X ν t)

/-- Exact derivative of the finite centered power expansion. -/
theorem hasDerivAt_correctedCenteredRealPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (correctedCenteredRealPhase d X ν)
      (∑ j ∈ Finset.range (d + 1),
        (j : ℝ) * ν j * (t - X) ^ (j - 1)) t := by
  unfold correctedCenteredRealPhase
  apply HasDerivAt.fun_sum
  intro j hj
  have hbase : HasDerivAt (fun y : ℝ => y - X) 1 t :=
    (hasDerivAt_id t).sub_const X
  have hpow := hbase.pow j
  have hmul := hpow.const_mul (ν j)
  convert hmul using 1 <;> ring

/-- Exact real derivative after subtracting the logarithmic phase. -/
theorem hasDerivAt_logarithmicComparisonRealPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logarithmicComparisonRealPhase d X ν)
      ((∑ j ∈ Finset.range (d + 1),
          (j : ℝ) * ν j * (t - X) ^ (j - 1)) - X * ν 1 / t) t := by
  have hpoly := hasDerivAt_correctedCenteredRealPhase d X ν t
  have hlog := (Real.hasDerivAt_log ht).const_mul (X * ν 1)
  unfold logarithmicComparisonRealPhase
  convert hpoly.sub hlog using 1 <;>
    simp only [Pi.sub_apply, div_eq_mul_inv] <;> ring

/-- Chain rule for the unit-frequency phase in the normalization
`e(s)=exp(2πis)`. -/
theorem HasDerivAt.unitFrequencyPhase_comp
    {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => unitFrequencyPhase (f x))
      (unitFrequencyPhase (f t) * (((2 * Real.pi * f' : ℝ) : ℂ) * Complex.I)) t := by
  have hscaled : HasDerivAt (fun x => (2 * Real.pi) * f x)
      ((2 * Real.pi) * f') t := hf.const_mul (2 * Real.pi)
  have hcomplex := hscaled.ofReal_comp
  have harg := hcomplex.mul_const Complex.I
  have hexp := (Complex.hasDerivAt_exp _).comp t harg
  simpa [unitFrequencyPhase, Function.comp_def, mul_assoc] using hexp

/-- Exact derivative of the smooth comparison phase. -/
theorem hasDerivAt_logarithmicComparisonPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logarithmicComparisonPhase d X ν)
      (logarithmicComparisonPhase d X ν t *
        (((2 * Real.pi *
          ((∑ j ∈ Finset.range (d + 1),
            (j : ℝ) * ν j * (t - X) ^ (j - 1)) - X * ν 1 / t) : ℝ) : ℂ) *
          Complex.I)) t := by
  unfold logarithmicComparisonPhase
  exact HasDerivAt.unitFrequencyPhase_comp
    (hasDerivAt_logarithmicComparisonRealPhase d X ν ht)

/-- The smooth comparison phase has unit modulus. -/
@[simp]
theorem norm_logarithmicComparisonPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) (t : ℝ) :
    ‖logarithmicComparisonPhase d X ν t‖ = 1 := by
  exact norm_unitFrequencyPhase _

/-- Norm of the derivative of the smooth comparison phase. -/
theorem norm_deriv_logarithmicComparisonPhase
    (d : ℕ) (X : ℝ) (ν : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖deriv (logarithmicComparisonPhase d X ν) t‖ =
      2 * Real.pi *
        |(∑ j ∈ Finset.range (d + 1),
            (j : ℝ) * ν j * (t - X) ^ (j - 1)) - X * ν 1 / t| := by
  rw [(hasDerivAt_logarithmicComparisonPhase d X ν ht).deriv,
    norm_mul, norm_logarithmicComparisonPhase, one_mul, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]

private theorem Icc_one_eq_image_range_succ (d : ℕ) :
    Finset.Icc 1 d = (Finset.range d).image (fun k => k + 1) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hj, hjd⟩
    refine ⟨j - 1, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    omega

/-- The zero derivative of the constant coefficient removes the `j=0`
term from the centered derivative sum. -/
theorem centeredDerivativeSum_eq_Icc
    (d : ℕ) (ν : ℕ → ℝ) (u : ℝ) :
    ∑ j ∈ Finset.range (d + 1),
        (j : ℝ) * ν j * u ^ (j - 1) =
      ∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * ν j * u ^ (j - 1) := by
  have hset : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp

/-- Reindex the derivative of the truncated logarithmic polynomial. -/
theorem logarithmicModelDerivativeSum_reindex
    (d : ℕ) (X u c : ℝ) :
    ∑ j ∈ Finset.Icc 1 d,
        (((-1 : ℝ) ^ (j - 1) * c / X ^ (j - 1)) * u ^ (j - 1)) =
      ∑ k ∈ Finset.range d,
        (((-1 : ℝ) ^ k * c / X ^ k) * u ^ k) := by
  rw [Icc_one_eq_image_range_succ d, Finset.sum_image]
  · simp
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab

/-- Split the corrected polynomial derivative into the error coefficients
`w_j` and the truncated logarithmic model. -/
theorem centeredDerivativeSum_decompose
    (d : ℕ) (X u : ℝ) (hX : X ≠ 0) (ν : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 d, (j : ℝ) * ν j * u ^ (j - 1) =
      (∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * logarithmicModelError X ν j * u ^ (j - 1)) +
      ∑ j ∈ Finset.Icc 1 d,
        (((-1 : ℝ) ^ (j - 1) * ν 1 / X ^ (j - 1)) * u ^ (j - 1)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hjmem
  have hj : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hXpow : X ^ (j - 1) ≠ 0 := pow_ne_zero _ hX
  unfold logarithmicModelError
  field_simp [hj0, hXpow]
  ring

/-- Exact decomposition of the real logarithmic-comparison derivative into
the controlled coefficient errors and the finite-geometric remainder. -/
theorem logarithmicComparisonDerivative_decomposition
    (d : ℕ) (X u : ℝ) (hX : X ≠ 0) (hXu : X + u ≠ 0)
    (ν : ℕ → ℝ) :
    (∑ j ∈ Finset.range (d + 1),
        (j : ℝ) * ν j * ((X + u) - X) ^ (j - 1)) - X * ν 1 / (X + u) =
      (∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * logarithmicModelError X ν j * u ^ (j - 1)) -
      ν 1 * (-u / X) ^ d / (1 + u / X) := by
  simp only [add_sub_cancel_left]
  rw [centeredDerivativeSum_eq_Icc,
    centeredDerivativeSum_decompose d X u hX ν]
  rw [add_sub_assoc]
  congr 1
  rw [logarithmicModelDerivativeSum_reindex]
  simpa only [neg_mul, neg_div] using
    finiteLogarithmicDerivativeIdentity d X u (ν 1) hX hXu

/-- The nonnegative pointwise envelope used to integrate the derivative
without losing the sharp source constant. -/
def logarithmicComparisonDerivativeEnvelope
    (d : ℕ) (X H D : ℝ) (ν : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 d,
      (j : ℝ) * (D / H ^ j) * (t - X) ^ (j - 1)) +
    |ν 1| / X ^ d * (t - X) ^ d

/-- The coefficient-error part of the derivative is bounded term by term by
the integrable power envelope on `0 ≤ u ≤ H`. -/
theorem abs_logarithmicModelErrorDerivativeSum_le
    (d : ℕ) (H X D u : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hu : 0 ≤ u) (huH : u ≤ H)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1)) :
    |∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * logarithmicModelError X ν j * u ^ (j - 1)| ≤
      ∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * (D / H ^ j) * u ^ (j - 1) := by
  calc
    |∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * logarithmicModelError X ν j * u ^ (j - 1)| ≤
        ∑ j ∈ Finset.Icc 1 d,
          |(j : ℝ) * logarithmicModelError X ν j * u ^ (j - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * (D / H ^ j) * u ^ (j - 1) := by
      apply Finset.sum_le_sum
      intro j hjmem
      have hj := (Finset.mem_Icc.mp hjmem).1
      have hjd := (Finset.mem_Icc.mp hjmem).2
      have hw := abs_logarithmicModelError_le d H X D ν hD hH hHX hrec
        hj (by omega : j ≤ d + 1)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg j), abs_pow,
        abs_of_nonneg hu]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg j))
        (pow_nonneg hu _)

/-- The finite-geometric remainder has the source's denominator gain; on the
positive interval it is bounded by the bare degree-`d` monomial. -/
theorem abs_logarithmicGeometricRemainder_le
    (d : ℕ) (X u c : ℝ) (hX : 0 < X) (hu : 0 ≤ u) :
    |c * (-u / X) ^ d / (1 + u / X)| ≤
      |c| / X ^ d * u ^ d := by
  have hratio : 0 ≤ u / X := div_nonneg hu hX.le
  have hden : 1 ≤ 1 + u / X := by linarith
  have hnum : 0 ≤ |c| * (u / X) ^ d :=
    mul_nonneg (abs_nonneg c) (pow_nonneg hratio d)
  calc
    |c * (-u / X) ^ d / (1 + u / X)| =
        (|c| * (u / X) ^ d) / (1 + u / X) := by
      rw [abs_div, abs_mul, abs_pow, abs_div, abs_neg,
        abs_of_nonneg hu, abs_of_pos hX,
        abs_of_pos (lt_of_lt_of_le zero_lt_one hden)]
    _ ≤ |c| * (u / X) ^ d := div_le_self hnum hden
    _ = |c| / X ^ d * u ^ d := by
      rw [div_pow]
      ring

/-- Pointwise control of the exact logarithmic-comparison derivative by the
nonnegative envelope retained in the approved proof. -/
theorem abs_logarithmicComparisonDerivative_le_envelope
    (d : ℕ) (X H D t : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (ht : t ∈ Set.Icc X (X + H))
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1)) :
    |(∑ j ∈ Finset.range (d + 1),
        (j : ℝ) * ν j * (t - X) ^ (j - 1)) - X * ν 1 / t| ≤
      logarithmicComparisonDerivativeEnvelope d X H D ν t := by
  have hX : 0 < X := lt_of_lt_of_le hH hHX
  have hu : 0 ≤ t - X := sub_nonneg.mpr ht.1
  have huH : t - X ≤ H := by linarith [ht.2]
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hX ht.1)
  have hXu : X + (t - X) ≠ 0 := by simpa using ht0
  have hdecomp := logarithmicComparisonDerivative_decomposition
    d X (t - X) hX.ne' hXu ν
  have hdecomp' :
      (∑ j ∈ Finset.range (d + 1),
          (j : ℝ) * ν j * (t - X) ^ (j - 1)) - X * ν 1 / t =
        (∑ j ∈ Finset.Icc 1 d,
          (j : ℝ) * logarithmicModelError X ν j *
            (t - X) ^ (j - 1)) -
        ν 1 * (-(t - X) / X) ^ d / (1 + (t - X) / X) := by
    simpa using hdecomp
  rw [hdecomp']
  unfold logarithmicComparisonDerivativeEnvelope
  calc
    |(∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * logarithmicModelError X ν j * (t - X) ^ (j - 1)) -
        ν 1 * (-(t - X) / X) ^ d / (1 + (t - X) / X)| ≤
      |∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * logarithmicModelError X ν j * (t - X) ^ (j - 1)| +
        |ν 1 * (-(t - X) / X) ^ d / (1 + (t - X) / X)| := abs_sub _ _
    _ ≤ (∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * (D / H ^ j) * (t - X) ^ (j - 1)) +
        |ν 1| / X ^ d * (t - X) ^ d :=
      add_le_add
        (abs_logarithmicModelErrorDerivativeSum_le d H X D (t - X) ν
          hD hH hHX hu huH hrec)
        (abs_logarithmicGeometricRemainder_le d X (t - X) (ν 1) hX hu)

/-- Exact integral of a shifted monomial on the positive short interval. -/
theorem intervalIntegral_shifted_pow
    (X H : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    (∫ t in X..X + H, (t - X) ^ (j - 1)) = H ^ j / (j : ℝ) := by
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := X) (b := X + H) (f := fun y : ℝ => y ^ (j - 1)) X
  have hshift' :
      (∫ t in X..X + H, (t - X) ^ (j - 1)) =
        ∫ u in 0..H, u ^ (j - 1) := by
    simpa only [sub_self, add_sub_cancel_left] using hshift
  rw [hshift', integral_pow]
  have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hj
  rw [Nat.sub_add_cancel hj]
  rw [hcast]
  simp [Nat.ne_of_gt hj]

/-- The power envelope integrates to the exact `d*D` coefficient-error
budget plus the finite-geometric remainder integral. -/
theorem integral_logarithmicComparisonDerivativeEnvelope
    (d : ℕ) (X H D : ℝ) (ν : ℕ → ℝ) (hH : 0 < H) :
    (∫ t in X..X + H,
        logarithmicComparisonDerivativeEnvelope d X H D ν t) =
      (d : ℝ) * D +
        (|ν 1| / X ^ d) * (H ^ (d + 1) / (d + 1 : ℕ)) := by
  have hinterval : X ≤ X + H := by linarith
  have hsumInt : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ Finset.Icc 1 d,
        (j : ℝ) * (D / H ^ j) * (t - X) ^ (j - 1))
      MeasureTheory.volume X (X + H) := by
    have hcont : ContinuousOn
        (fun t : ℝ => ∑ j ∈ Finset.Icc 1 d,
          (j : ℝ) * (D / H ^ j) * (t - X) ^ (j - 1))
        (Set.Icc X (X + H)) := by fun_prop
    exact hcont.intervalIntegrable_of_Icc hinterval
  have hlastInt : IntervalIntegrable
      (fun t : ℝ => |ν 1| / X ^ d * (t - X) ^ d)
      MeasureTheory.volume X (X + H) := by
    have hcont : ContinuousOn
        (fun t : ℝ => |ν 1| / X ^ d * (t - X) ^ d)
        (Set.Icc X (X + H)) := by fun_prop
    exact hcont.intervalIntegrable_of_Icc hinterval
  unfold logarithmicComparisonDerivativeEnvelope
  rw [intervalIntegral.integral_add hsumInt hlastInt]
  rw [intervalIntegral.integral_finsetSum]
  · have hterm : ∀ j ∈ Finset.Icc 1 d,
        (∫ t in X..X + H,
          (j : ℝ) * (D / H ^ j) * (t - X) ^ (j - 1)) = D := by
      intro j hjmem
      have hj : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
      have hj0 : (j : ℝ) ≠ 0 := by positivity
      have hHpow : H ^ j ≠ 0 := pow_ne_zero _ hH.ne'
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_shifted_pow X H hj]
      field_simp [hj0, hHpow]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [intervalIntegral.integral_const_mul]
    have hlastPow := intervalIntegral_shifted_pow X H
      (j := d + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hlastPow
    rw [hlastPow]
    norm_num [Nat.cast_add, add_comm]
  · intro j hjmem
    have hcont : ContinuousOn
        (fun t : ℝ => (j : ℝ) * (D / H ^ j) * (t - X) ^ (j - 1))
        (Set.Icc X (X + H)) := by fun_prop
    exact hcont.intervalIntegrable_of_Icc hinterval

/-- After the terminal coefficient is used, the integrated envelope has the
exact source bound `(d+1)D`. -/
theorem integral_logarithmicComparisonDerivativeEnvelope_le
    (d : ℕ) (hd : 1 ≤ d) (X H D : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hterminal : ν (d + 1) = 0)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1)) :
    (∫ t in X..X + H,
        logarithmicComparisonDerivativeEnvelope d X H D ν t) ≤
      (d + 1 : ℕ) * D := by
  have hX : 0 < X := lt_of_lt_of_le hH hHX
  have hnu := abs_linearCoefficient_le_of_terminal_zero
    d hd H X D ν hD hH hHX hterminal hrec
  have hHpow : H ^ (d + 1) ≠ 0 := pow_ne_zero _ hH.ne'
  have hXpow : X ^ d ≠ 0 := pow_ne_zero _ hX.ne'
  have hd1 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  let c : ℝ := H ^ (d + 1) / (X ^ d * (d + 1 : ℕ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hremRewrite :
      (|ν 1| / X ^ d) * (H ^ (d + 1) / (d + 1 : ℕ)) = |ν 1| * c := by
    dsimp [c]
    field_simp [hXpow]
  have hrem :
      (|ν 1| / X ^ d) * (H ^ (d + 1) / (d + 1 : ℕ)) ≤ D := by
    rw [hremRewrite]
    calc
      |ν 1| * c ≤
          ((d : ℝ) * D * X ^ d / H ^ (d + 1)) * c :=
        mul_le_mul_of_nonneg_right hnu hc
      _ = ((d : ℝ) / (d + 1 : ℕ)) * D := by
        dsimp [c]
        field_simp [hHpow, hXpow, hd1.ne']
      _ ≤ 1 * D := by
        apply mul_le_mul_of_nonneg_right _ hD
        exact (div_le_one hd1).2 (by norm_num)
      _ = D := one_mul D
  rw [integral_logarithmicComparisonDerivativeEnvelope d X H D ν hH]
  push_cast
  have hrem' :
      (|ν 1| / X ^ d) * (H ^ (d + 1) / ((d : ℝ) + 1)) ≤ D := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrem
  linarith [hrem']

/-- The comparison phase is continuously differentiable on every compact
positive interval. -/
theorem contDiffOn_logarithmicComparisonPhase
    (d : ℕ) (X Y : ℝ) (ν : ℕ → ℝ) (hX : 0 < X) :
    ContDiffOn ℝ 1 (logarithmicComparisonPhase d X ν) (Set.Icc X Y) := by
  have hpoly : ContDiffOn ℝ 1 (correctedCenteredRealPhase d X ν)
      (Set.Icc X Y) := by
    unfold correctedCenteredRealPhase
    fun_prop
  have hpos : Set.Icc X Y ⊆ ({0} : Set ℝ)ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hX ht.1)
  have hlog : ContDiffOn ℝ 1 Real.log (Set.Icc X Y) :=
    Real.contDiffOn_log.mono hpos
  have hreal : ContDiffOn ℝ 1 (logarithmicComparisonRealPhase d X ν)
      (Set.Icc X Y) := by
    unfold logarithmicComparisonRealPhase
    have hlogmul := hlog.const_smul (X * ν 1)
    exact hpoly.sub (by simpa [smul_eq_mul] using hlogmul)
  have hscaled : ContDiffOn ℝ 1
      (fun t => (2 * Real.pi) * logarithmicComparisonRealPhase d X ν t)
      (Set.Icc X Y) := by
    simpa [smul_eq_mul] using hreal.const_smul (2 * Real.pi)
  have hcomplex : ContDiffOn ℝ 1
      (fun t => (((2 * Real.pi) *
        logarithmicComparisonRealPhase d X ν t : ℝ) : ℂ))
      (Set.Icc X Y) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hscaled
  have harg : ContDiffOn ℝ 1
      (fun t => (((2 * Real.pi) *
        logarithmicComparisonRealPhase d X ν t : ℝ) : ℂ) * Complex.I)
      (Set.Icc X Y) := by
    simpa [smul_eq_mul, mul_comm] using hcomplex.const_smul Complex.I
  unfold logarithmicComparisonPhase unitFrequencyPhase
  convert harg.cexp using 1

/-- Integrating the norm of the comparison-phase derivative gives precisely
the `2π(d+1)D` budget used by the variation theorem. -/
theorem integral_norm_derivWithin_logarithmicComparisonPhase_le
    (d : ℕ) (hd : 1 ≤ d) (X H D : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hterminal : ν (d + 1) = 0)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1)) :
    (∫ t in X..X + H,
        ‖derivWithin (logarithmicComparisonPhase d X ν)
          (Set.Icc X (X + H)) t‖) ≤
      2 * Real.pi * ((d + 1 : ℕ) * D) := by
  have hX : 0 < X := lt_of_lt_of_le hH hHX
  have hXY : X ≤ X + H := by linarith
  have hXYlt : X < X + H := by linarith
  have hsmooth := contDiffOn_logarithmicComparisonPhase
    d X (X + H) ν hX
  let G : ℝ → ℝ := fun t =>
    ‖derivWithin (logarithmicComparisonPhase d X ν)
      (Set.Icc X (X + H)) t‖
  let E : ℝ → ℝ := fun t =>
    2 * Real.pi * logarithmicComparisonDerivativeEnvelope d X H D ν t
  have hGcont : ContinuousOn G (Set.Icc X (X + H)) := by
    dsimp [G]
    exact (hsmooth.continuousOn_derivWithin
      (uniqueDiffOn_Icc hXYlt) (by norm_num)).norm
  have hEcont : ContinuousOn E (Set.Icc X (X + H)) := by
    dsimp [E, logarithmicComparisonDerivativeEnvelope]
    fun_prop
  have hGint : IntervalIntegrable G MeasureTheory.volume X (X + H) :=
    hGcont.intervalIntegrable_of_Icc hXY
  have hEint : IntervalIntegrable E MeasureTheory.volume X (X + H) :=
    hEcont.intervalIntegrable_of_Icc hXY
  have hpoint : ∀ t ∈ Set.Ioo X (X + H), G t ≤ E t := by
    intro t ht
    have htIcc : t ∈ Set.Icc X (X + H) := ⟨ht.1.le, ht.2.le⟩
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hX ht.1)
    dsimp [G, E]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
      norm_deriv_logarithmicComparisonPhase d X ν ht0]
    exact mul_le_mul_of_nonneg_left
      (abs_logarithmicComparisonDerivative_le_envelope
        d X H D t ν hD hH hHX htIcc hrec) (by positivity)
  calc
    (∫ t in X..X + H, G t) ≤ ∫ t in X..X + H, E t :=
      intervalIntegral.integral_mono_on_of_le_Ioo hXY hGint hEint hpoint
    _ = 2 * Real.pi *
        (∫ t in X..X + H,
          logarithmicComparisonDerivativeEnvelope d X H D ν t) := by
      dsimp [E]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * Real.pi * ((d + 1 : ℕ) * D) :=
      mul_le_mul_of_nonneg_left
        (integral_logarithmicComparisonDerivativeEnvelope_le
          d hd X H D ν hD hH hHX hterminal hrec) (by positivity)

/-- The smooth comparison phase has the exact inhomogeneous variation bound
on every subset of the short integer interval. -/
theorem orderedTotalVariation_logarithmicComparisonPhase_le
    (d : ℕ) (hd : 1 ≤ d) (X H D : ℝ) (ν : ℕ → ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) (hHX : H ≤ X)
    (hterminal : ν (d + 1) = 0)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν j + (j + 1 : ℕ) * X * ν (j + 1)| ≤
        D * X / H ^ (j + 1))
    (P : Set ℤ) (hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc X (X + H)) :
    orderedTotalVariation P
        (fun n : ℤ => logarithmicComparisonPhase d X ν n) ≤
      ENNReal.ofReal (1 + 2 * Real.pi * ((d + 1 : ℕ) * D)) := by
  have hX : 0 < X := lt_of_lt_of_le hH hHX
  have hXY : X ≤ X + H := by linarith
  have hsmooth := contDiffOn_logarithmicComparisonPhase
    d X (X + H) ν hX
  have hsup : intervalNormSup X (X + H)
      (logarithmicComparisonPhase d X ν) = 1 := by
    have hrange :
        Set.range (fun t : Set.Icc X (X + H) =>
          ‖logarithmicComparisonPhase d X ν (t : ℝ)‖) = {1} := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        simp
      · intro hy
        have hy' : y = 1 := by simpa using hy
        subst y
        refine ⟨⟨X, ⟨le_rfl, hXY⟩⟩, ?_⟩
        simp
    rw [intervalNormSup, hrange]
    simp
  have hint := integral_norm_derivWithin_logarithmicComparisonPhase_le
    d hd X H D ν hD hH hHX hterminal hrec
  have hreal :
      intervalNormSup X (X + H) (logarithmicComparisonPhase d X ν) +
          (∫ t in X..X + H,
            ‖derivWithin (logarithmicComparisonPhase d X ν)
              (Set.Icc X (X + H)) t‖) ≤
        1 + 2 * Real.pi * ((d + 1 : ℕ) * D) := by
    rw [hsup]
    linarith
  exact (orderedTotalVariation_le_sup_add_integral hXY
    (logarithmicComparisonPhase d X ν) hsmooth P hP).trans
      (ENNReal.ofReal_le_ofReal hreal)

private theorem listAdjacentVariation_cons_logPhase
    (g : ℤ → ℂ) (a : ℤ) (l : List ℤ) :
    listAdjacentVariation g (a :: l) =
      (match l with
       | [] => 0
       | b :: _ => ‖g b - g a‖) + listAdjacentVariation g l := by
  cases l <;> simp [listAdjacentVariation, List.consecutivePairs,
    List.zip, List.tail]

private theorem listAdjacentVariation_cons_cons_logPhase
    (g : ℤ → ℂ) (a b : ℤ) (l : List ℤ) :
    listAdjacentVariation g (a :: b :: l) =
      ‖g b - g a‖ + listAdjacentVariation g (b :: l) := by
  simpa using listAdjacentVariation_cons_logPhase g a (b :: l)

private theorem listSupNorm_congr_on_logPhase
    (g h : ℤ → ℂ) (l : List ℤ)
    (heq : ∀ n ∈ l, g n = h n) :
    listSupNorm g l = listSupNorm h l := by
  unfold listSupNorm
  have hmap : l.map (fun n => ‖g n‖) = l.map (fun n => ‖h n‖) := by
    apply List.map_congr_left
    intro n hn
    rw [heq n hn]
  rw [hmap]

private theorem listAdjacentVariation_congr_on_logPhase
    (g h : ℤ → ℂ) (l : List ℤ)
    (heq : ∀ n ∈ l, g n = h n) :
    listAdjacentVariation g l = listAdjacentVariation h l := by
  induction l with
  | nil => simp [listAdjacentVariation, List.consecutivePairs,
      List.zip, List.tail]
  | cons a l ih =>
      cases l with
      | nil => simp [listAdjacentVariation, List.consecutivePairs,
          List.zip, List.tail]
      | cons b l =>
          have hab : ‖g b - g a‖ = ‖h b - h a‖ := by
            rw [heq b (by simp), heq a (by simp)]
          rw [listAdjacentVariation_cons_cons_logPhase,
            listAdjacentVariation_cons_cons_logPhase, hab,
            ih (fun n hn => heq n (by simp [hn]))]

/-- Finite inhomogeneous variation depends only on the values on the finite
ordered set. -/
theorem finiteOrderedTotalVariation_congr_on_logPhase
    (A : Finset ℤ) (g h : ℤ → ℂ)
    (heq : ∀ n ∈ A, g n = h n) :
    finiteOrderedTotalVariation A g = finiteOrderedTotalVariation A h := by
  unfold finiteOrderedTotalVariation
  rw [listSupNorm_congr_on_logPhase g h (A.sort (· ≤ ·))
      (fun n hn => heq n
        ((Finset.mem_sort (s := A) (r := (· ≤ ·))).1 hn)),
    listAdjacentVariation_congr_on_logPhase g h (A.sort (· ≤ ·))
      (fun n hn => heq n
        ((Finset.mem_sort (s := A) (r := (· ≤ ·))).1 hn))]

/-- Extended inhomogeneous variation depends only on the values on its
underlying ordered set. -/
theorem orderedTotalVariation_congr_on_logPhase
    (P : Set ℤ) (g h : ℤ → ℂ)
    (heq : ∀ n ∈ P, g n = h n) :
    orderedTotalVariation P g = orderedTotalVariation P h := by
  unfold orderedTotalVariation
  apply le_antisymm
  · apply iSup_le
    intro F
    exact le_iSup_of_le F (by
      rw [finiteOrderedTotalVariation_congr_on_logPhase F.1 g h
        (fun n hn => heq n (F.2 n hn))])
  · apply iSup_le
    intro F
    exact le_iSup_of_le F (by
      rw [finiteOrderedTotalVariation_congr_on_logPhase F.1 h g
        (fun n hn => (heq n (F.2 n hn)).symm)])

/-- A function that is a fixed unit scalar on a bounded ordered set has
inhomogeneous variation at most one. -/
theorem orderedTotalVariation_le_one_of_eq_unit_constant
    {X Y : ℝ} (hXY : X ≤ Y) (P : Set ℤ) (g : ℤ → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc X Y)
    (heq : ∀ n ∈ P, g n = c) :
    orderedTotalVariation P g ≤ 1 := by
  rw [orderedTotalVariation_congr_on_logPhase P g (fun _ => c) heq]
  have hsmooth : ContDiffOn ℝ 1 (fun _ : ℝ => c) (Set.Icc X Y) := by
    fun_prop
  have htv := orderedTotalVariation_le_sup_add_integral hXY
    (fun _ : ℝ => c) hsmooth P hP
  have hsup : intervalNormSup X Y (fun _ : ℝ => c) = 1 := by
    have hrange :
        Set.range (fun _ : Set.Icc X Y => ‖c‖) = {1} := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        simp [hc]
      · intro hy
        have hy' : y = 1 := by simpa using hy
        subst y
        exact ⟨⟨X, ⟨le_rfl, hXY⟩⟩, by simp [hc]⟩
    rw [intervalNormSup, hrange]
    simp
  simpa [hsup] using htv

/-- The rational correction factor is constant on each residue class modulo
the exact period `Q*d!`. -/
theorem unitFrequencyPhase_recurrenceRationalCorrection_eq_of_residue
    (d Q : ℕ) (X : ℤ) (r : ℕ → ℝ) (hQ : 1 ≤ Q)
    {a : ℕ} {n m : ℤ}
    (hn : n ∈ integerResidueClass (Q * d.factorial) a)
    (hm : m ∈ integerResidueClass (Q * d.factorial) a) :
    unitFrequencyPhase (recurrenceRationalCorrection d Q X r n) =
      unitFrequencyPhase (recurrenceRationalCorrection d Q X r m) := by
  let f : ℤ → ℂ := fun z =>
    unitFrequencyPhase (recurrenceRationalCorrection d Q X r z)
  have hper : Function.Periodic f ((Q * d.factorial : ℕ) : ℤ) := by
    intro z
    exact unitFrequencyPhase_recurrenceRationalCorrection_periodic
      d Q X r hQ z
  rcases hn with ⟨kn, rfl⟩
  rcases hm with ⟨km, rfl⟩
  have hmul := hper.int_mul (kn - km) ((a : ℤ) + (Q * d.factorial : ℕ) * km)
  dsimp [f] at hmul ⊢
  convert hmul using 1 <;> ring

/-- Adding the rational correction to the integer-corrected polynomial
recovers the original centered polynomial exactly. -/
theorem recurrenceRationalCorrection_add_correctedCenteredRealPhase
    (d Q : ℕ) (X : ℤ) (r ν : ℕ → ℝ) (n : ℤ) :
    recurrenceRationalCorrection d Q X r n +
        correctedCenteredRealPhase d (X : ℝ)
          (correctedRecurrenceCoefficient d Q X r ν) n =
      correctedCenteredRealPhase d (X : ℝ) ν n := by
  let u : ℝ := ((n - X : ℤ) : ℝ)
  have hu : (n : ℝ) - (X : ℝ) = u := by
    dsimp [u]
    push_cast
    rfl
  have hset : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : 0 ∉ Finset.Icc 1 d := by simp
  unfold recurrenceRationalCorrection correctedCenteredRealPhase
  simp only [Int.cast_sub]
  rw [hu, hset, Finset.sum_insert hzero, Finset.sum_insert hzero]
  have hcoeff0 : correctedRecurrenceCoefficient d Q X r ν 0 = ν 0 := by
    simp [correctedRecurrenceCoefficient]
  rw [hcoeff0]
  simp only [pow_zero, mul_one]
  have hsum :
      (∑ j ∈ Finset.Icc 1 d,
        -(recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
            ((Q : ℝ) * (j : ℝ)) * u ^ j) +
        ∑ j ∈ Finset.Icc 1 d,
          correctedRecurrenceCoefficient d Q X r ν j * u ^ j =
        ∑ j ∈ Finset.Icc 1 d, ν j * u ^ j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hjmem
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_Icc.mp hjmem).1
      omega
    rw [correctedRecurrenceCoefficient, if_neg hj0]
    ring
  calc
    (∑ j ∈ Finset.Icc 1 d,
          -(recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
              ((Q : ℝ) * (j : ℝ)) * u ^ j) +
        (ν 0 + ∑ j ∈ Finset.Icc 1 d,
          correctedRecurrenceCoefficient d Q X r ν j * u ^ j) =
      ν 0 +
        ((∑ j ∈ Finset.Icc 1 d,
          -(recurrenceIntegerCorrection d X (recurrenceNearestInteger Q r) j : ℝ) /
              ((Q : ℝ) * (j : ℝ)) * u ^ j) +
          ∑ j ∈ Finset.Icc 1 d,
            correctedRecurrenceCoefficient d Q X r ν j * u ^ j) := by ring
    _ = ν 0 + ∑ j ∈ Finset.Icc 1 d, ν j * u ^ j := by rw [hsum]

/-- The logarithmic twist with frequency `-2πc` is the unit-frequency
phase of `-c log x`. -/
theorem archimedeanTwist_neg_two_pi_eq_unitFrequencyPhase
    (c x : ℝ) :
    archimedeanTwist (-(2 * Real.pi * c)) x =
      unitFrequencyPhase (-c * Real.log x) := by
  unfold archimedeanTwist unitFrequencyPhase
  congr 1
  push_cast
  ring

/-- Exact pointwise factorization of the original polynomial-logarithmic
twist into its rational periodic part and smooth comparison phase. -/
theorem polynomialLogTwist_factorization
    (d Q : ℕ) (X : ℤ) (r ν : ℕ → ℝ) (n : ℤ) :
    let ν' := correctedRecurrenceCoefficient d Q X r ν
    let T := 2 * Real.pi * (X : ℝ) * ν' 1
    unitFrequencyPhase
          (correctedCenteredRealPhase d (X : ℝ) ν (n : ℝ)) *
        archimedeanTwist (-T) (n : ℝ) =
      unitFrequencyPhase (recurrenceRationalCorrection d Q X r n) *
        logarithmicComparisonPhase d (X : ℝ) ν' (n : ℝ) := by
  dsimp only
  have htwist :
      archimedeanTwist
          (-(2 * Real.pi * (X : ℝ) *
            correctedRecurrenceCoefficient d Q X r ν 1)) (n : ℝ) =
        unitFrequencyPhase
          (-((X : ℝ) * correctedRecurrenceCoefficient d Q X r ν 1) *
            Real.log (n : ℝ)) := by
    convert archimedeanTwist_neg_two_pi_eq_unitFrequencyPhase
      ((X : ℝ) * correctedRecurrenceCoefficient d Q X r ν 1) (n : ℝ) using 1 <;>
      ring
  rw [htwist, ← unitFrequencyPhase_add]
  unfold logarithmicComparisonPhase logarithmicComparisonRealPhase
  rw [← unitFrequencyPhase_add]
  congr 1
  have hphase := recurrenceRationalCorrection_add_correctedCenteredRealPhase
    d Q X r ν n
  linarith

/-- The integer points of the source interval `(X,X+H]`. -/
def logPhaseIntegerInterval (X H : ℝ) : Set ℤ :=
  {n | X < (n : ℝ) ∧ (n : ℝ) ≤ X + H}

/-- Lifting adjacent centered-coefficient recurrences and comparing the
polynomial phase with one logarithmic phase.  This is blueprint node
`lu:log-phase`, with the exact period `Q*d!` and constants from the approved
proof. -/
theorem coefficientRecurrenceToLogPhase
    (d X Q : ℕ) (H B : ℝ) (ν : ℕ → ℝ)
    (hd : 1 ≤ d) (hX : 1 ≤ X) (hH : 0 < H) (hHX : H ≤ (X : ℝ))
    (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hterminal : ν (d + 1) = 0)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      realDistanceToIntegers
          ((Q : ℝ) * bilinearDerivativeCoefficient (X : ℝ) ν j) ≤
        B * (X : ℝ) / H ^ (j + 1)) :
    ∃ T : ℝ, ∃ q : ℕ, ∃ hq : 0 < q,
      q = Q * d.factorial ∧
      |T| ≤ (2 * Real.pi * (d : ℝ) * B / (Q : ℝ)) *
        ((X : ℝ) / H) ^ (d + 1) ∧
      residueClassTotalVariation (logPhaseIntegerInterval X H)
          (fun n : ℤ =>
            unitFrequencyPhase
                (correctedCenteredRealPhase d (X : ℝ) ν (n : ℝ)) *
              archimedeanTwist (-T) (n : ℝ)) q hq ≤
        ENNReal.ofReal ((q : ℝ) *
          (1 + 2 * Real.pi * ((d + 1 : ℕ) * (B / (Q : ℝ))))) := by
  let r : ℕ → ℝ := fun j =>
    bilinearDerivativeCoefficient (X : ℝ) ν j
  let ν' : ℕ → ℝ :=
    correctedRecurrenceCoefficient d Q (X : ℤ) r ν
  let D : ℝ := B / (Q : ℝ)
  let T : ℝ := 2 * Real.pi * (X : ℝ) * ν' 1
  let q : ℕ := Q * d.factorial
  have hQreal : (0 : ℝ) < Q := by positivity
  have hXreal : (0 : ℝ) < X := by positivity
  have hD : 0 ≤ D := div_nonneg hB hQreal.le
  have hrecId : ∀ j, 1 ≤ j → j ≤ d →
      r j = (j : ℝ) * ν j + (j + 1 : ℕ) * (X : ℝ) * ν (j + 1) := by
    intro j hj hjd
    rfl
  have hrec' : ∀ j, 1 ≤ j → j ≤ d →
      |(j : ℝ) * ν' j + (j + 1 : ℕ) * (X : ℝ) * ν' (j + 1)| ≤
        D * (X : ℝ) / H ^ (j + 1) := by
    intro j hj hjd
    dsimp [ν', D]
    simpa only [Int.cast_natCast] using
      correctedRecurrenceCoefficient_bound d Q (X : ℤ) H B r ν hQ hj hjd
        (hrecId j hj hjd) (hrec j hj hjd)
  have hterminal' : ν' (d + 1) = 0 := by
    dsimp [ν']
    exact correctedRecurrenceCoefficient_succ_degree
      d Q (X : ℤ) r ν hterminal
  have hnu := abs_linearCoefficient_le_of_terminal_zero
    d hd H (X : ℝ) D ν' hD hH hHX hterminal' hrec'
  have hT : |T| ≤
      (2 * Real.pi * (d : ℝ) * B / (Q : ℝ)) *
        ((X : ℝ) / H) ^ (d + 1) := by
    have hscale : 0 ≤ 2 * Real.pi * (X : ℝ) := by positivity
    calc
      |T| = (2 * Real.pi * (X : ℝ)) * |ν' 1| := by
        dsimp [T]
        rw [abs_mul, abs_mul,
          abs_of_pos (mul_pos (by positivity : (0 : ℝ) < 2) Real.pi_pos),
          abs_of_pos hXreal]
      _ ≤ (2 * Real.pi * (X : ℝ)) *
          ((d : ℝ) * D * (X : ℝ) ^ d / H ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hnu hscale
      _ = (2 * Real.pi * (d : ℝ) * B / (Q : ℝ)) *
          ((X : ℝ) / H) ^ (d + 1) := by
        dsimp [D]
        rw [div_pow]
        field_simp [hQreal.ne', hH.ne']
        ring
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.mul_pos (by omega) (Nat.factorial_pos d)
  have hXY : (X : ℝ) ≤ (X : ℝ) + H := by linarith
  let C : ℝ := 1 + 2 * Real.pi * ((d + 1 : ℕ) * D)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hclass : ∀ a ∈ Finset.range q,
      orderedTotalVariation
          (logPhaseIntegerInterval X H ∩ integerResidueClass q a)
          (fun n : ℤ =>
            unitFrequencyPhase
                (correctedCenteredRealPhase d (X : ℝ) ν (n : ℝ)) *
              archimedeanTwist (-T) (n : ℝ)) ≤
        ENNReal.ofReal C := by
    intro a ha
    let P : Set ℤ := logPhaseIntegerInterval X H ∩ integerResidueClass q a
    let g : ℤ → ℂ := fun n =>
      unitFrequencyPhase (recurrenceRationalCorrection d Q (X : ℤ) r n)
    let k : ℤ → ℂ := fun n =>
      logarithmicComparisonPhase d (X : ℝ) ν' (n : ℝ)
    have hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc (X : ℝ) ((X : ℝ) + H) := by
      intro n hn
      exact ⟨hn.1.1.le, hn.1.2⟩
    have hfactor : ∀ n ∈ P,
        unitFrequencyPhase
              (correctedCenteredRealPhase d (X : ℝ) ν (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ) = g n * k n := by
      intro n hn
      simpa [T, g, k, ν'] using
        polynomialLogTwist_factorization d Q (X : ℤ) r ν n
    have haMem : (a : ℤ) ∈ integerResidueClass q a := by
      refine ⟨0, ?_⟩
      simp
    have hgconst : ∀ n ∈ P, g n = g (a : ℤ) := by
      intro n hn
      dsimp [g]
      exact unitFrequencyPhase_recurrenceRationalCorrection_eq_of_residue
        d Q (X : ℤ) r hQ (by simpa [q, P] using hn.2)
          (by simpa [q] using haMem)
    have hg : orderedTotalVariation P g ≤ 1 :=
      orderedTotalVariation_le_one_of_eq_unit_constant hXY P g (g (a : ℤ))
        (by simp [g, norm_unitFrequencyPhase]) hP hgconst
    have hk : orderedTotalVariation P k ≤ ENNReal.ofReal C := by
      dsimp [k, C]
      exact orderedTotalVariation_logarithmicComparisonPhase_le
        d hd (X : ℝ) H D ν' hD hH hHX hterminal' hrec' P hP
    rw [show logPhaseIntegerInterval X H ∩ integerResidueClass q a = P by rfl]
    rw [orderedTotalVariation_congr_on_logPhase P _ (fun n => g n * k n) hfactor]
    calc
      orderedTotalVariation P (fun n => g n * k n) ≤
          orderedTotalVariation P g * orderedTotalVariation P k :=
        orderedTotalVariation_mul_le P g k
      _ ≤ 1 * ENNReal.ofReal C := by
        exact mul_le_mul hg hk (by simp) (by simp)
      _ = ENNReal.ofReal C := one_mul _
  refine ⟨T, q, hq, rfl, hT, ?_⟩
  unfold residueClassTotalVariation
  calc
    (∑ a ∈ Finset.range q,
      orderedTotalVariation
        (logPhaseIntegerInterval X H ∩ integerResidueClass q a)
        (fun n : ℤ =>
          unitFrequencyPhase
              (correctedCenteredRealPhase d (X : ℝ) ν (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ))) ≤
      ∑ _a ∈ Finset.range q, ENNReal.ofReal C := by
        apply Finset.sum_le_sum
        intro a ha
        exact hclass a ha
    _ = (q : ENNReal) * ENNReal.ofReal C := by simp
    _ = ENNReal.ofReal ((q : ℝ) * C) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (q : ℝ))]
      simp
    _ = ENNReal.ofReal ((q : ℝ) *
        (1 + 2 * Real.pi * ((d + 1 : ℕ) * (B / (Q : ℝ))))) := by
      rfl

/-- The separately stated degree-zero clause: the polynomial phase is
constant, so `T=0`, `q=1`, and the inhomogeneous residue variation is at most
one without any recurrence hypothesis. -/
theorem coefficientRecurrenceToLogPhase_zero
    (X : ℕ) (H : ℝ) (ν : ℕ → ℝ) (hH : 0 ≤ H) :
    ∃ T : ℝ, ∃ q : ℕ, ∃ hq : 0 < q,
      T = 0 ∧ q = 1 ∧
      residueClassTotalVariation (logPhaseIntegerInterval X H)
          (fun n : ℤ =>
            unitFrequencyPhase
                (correctedCenteredRealPhase 0 (X : ℝ) ν (n : ℝ)) *
              archimedeanTwist (-T) (n : ℝ)) q hq ≤ 1 := by
  refine ⟨0, 1, by norm_num, rfl, rfl, ?_⟩
  let P : Set ℤ := logPhaseIntegerInterval X H ∩ integerResidueClass 1 0
  let c : ℂ := unitFrequencyPhase (ν 0)
  have hXY : (X : ℝ) ≤ (X : ℝ) + H := by linarith
  have hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc (X : ℝ) ((X : ℝ) + H) := by
    intro n hn
    exact ⟨hn.1.1.le, hn.1.2⟩
  have heq : ∀ n ∈ P,
      unitFrequencyPhase
            (correctedCenteredRealPhase 0 (X : ℝ) ν (n : ℝ)) *
          archimedeanTwist (-(0 : ℝ)) (n : ℝ) = c := by
    intro n hn
    simp [correctedCenteredRealPhase, archimedeanTwist, c]
  have hbound : orderedTotalVariation P
      (fun n : ℤ =>
        unitFrequencyPhase
              (correctedCenteredRealPhase 0 (X : ℝ) ν (n : ℝ)) *
            archimedeanTwist (-(0 : ℝ)) (n : ℝ)) ≤ 1 :=
    orderedTotalVariation_le_one_of_eq_unit_constant hXY P _ c
      (by simp [c, norm_unitFrequencyPhase]) hP heq
  unfold residueClassTotalVariation
  simpa [P] using hbound

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.coefficientRecurrenceToLogPhase
#print axioms FractionalPrimes.Literature.Uniformity.coefficientRecurrenceToLogPhase_zero
