module

public import FractionalPrimes.Literature.Polynomial.PolynomialInverseBudgets
public import FractionalPrimes.Literature.Polynomial.ScalarWeylWeightedDistance
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- The forward difference `ΔP(t)=P(t+1)-P(t)`. -/
noncomputable def polynomialForwardDifference (P : Polynomial ℝ) : Polynomial ℝ :=
  P.comp (X + C 1) - P

/-- The `k`-fold forward difference of a polynomial. -/
noncomputable def iteratedPolynomialForwardDifference :
    ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, P => P
  | k + 1, P => iteratedPolynomialForwardDifference k
      (polynomialForwardDifference P)

/-- The value at zero of the `k`th forward difference of the monomial `t^j`,
written in the power basis. The recursion is the binomial expansion of
`(t+1)^j-t^j`. -/
def monomialForwardDifferenceCoefficient : ℕ → ℕ → ℤ
  | 0, j => if j = 0 then 1 else 0
  | k + 1, j =>
      ∑ m ∈ Finset.range j,
        (Nat.choose j m : ℤ) * monomialForwardDifferenceCoefficient k m

/-- The `k`th Newton coefficient at the integer centre `Y`, namely
`(Δ^k P)(Y)` as in the source definition. -/
noncomputable def polynomialBinomialCoefficient
    (_d : ℕ) (P : Polynomial ℝ) (Y : ℤ) (k : ℕ) : ℝ :=
  (iteratedPolynomialForwardDifference k
    (P.comp (X + C (Y : ℝ)))).eval 0

/-- The approved binomial coefficient seminorm, with the source convention
that it is zero in degree zero. -/
noncomputable def polynomialBinomialCoefficientNorm
    (d : ℕ) (P : Polynomial ℝ) (Y : ℤ) (H : ℝ) : ℝ :=
  if hd : 1 ≤ d then
    (Finset.Icc 1 d).sup'
      ⟨1, Finset.mem_Icc.mpr ⟨by omega, hd⟩⟩
      (fun k => H ^ k * realDistanceToIntegers
        (polynomialBinomialCoefficient d P Y k))
  else 0

@[simp] theorem polynomialBinomialCoefficientNorm_zero
    (P : Polynomial ℝ) (Y : ℤ) (H : ℝ) :
    polynomialBinomialCoefficientNorm 0 P Y H = 0 := by
  simp [polynomialBinomialCoefficientNorm]

private theorem monomialForwardDifferenceCoefficient_eq_zero_of_lt
    {k j : ℕ} (hjk : j < k) :
    monomialForwardDifferenceCoefficient k j = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
      rw [monomialForwardDifferenceCoefficient]
      apply Finset.sum_eq_zero
      intro m hm
      have hmj : m < j := Finset.mem_range.mp hm
      have hmk : m < k := by omega
      rw [ih hmk]
      simp

private theorem monomialForwardDifferenceCoefficient_bound
    (k j : ℕ) :
    |((monomialForwardDifferenceCoefficient k j : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ k * (k : ℝ) ^ j := by
  induction k generalizing j with
  | zero =>
      cases j with
      | zero => norm_num [monomialForwardDifferenceCoefficient]
      | succ j => simp [monomialForwardDifferenceCoefficient]
  | succ k ih =>
      rw [monomialForwardDifferenceCoefficient]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      calc
        |∑ m ∈ Finset.range j,
            (↑(Nat.choose j m) : ℝ) *
              ((monomialForwardDifferenceCoefficient k m : ℤ) : ℝ)| ≤
          ∑ m ∈ Finset.range j,
            |(↑(Nat.choose j m) : ℝ) *
              ((monomialForwardDifferenceCoefficient k m : ℤ) : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.range j,
              (↑(Nat.choose j m) : ℝ) *
                ((2 : ℝ) ^ k * (k : ℝ) ^ m) := by
            apply Finset.sum_le_sum
            intro m hm
            rw [abs_mul, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (ih m) (by positivity)
        _ = (2 : ℝ) ^ k *
              ∑ m ∈ Finset.range j,
                (↑(Nat.choose j m) : ℝ) * (k : ℝ) ^ m := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
        _ ≤ (2 : ℝ) ^ k * ((k : ℝ) + 1) ^ j := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc
              ∑ m ∈ Finset.range j,
                  (↑(Nat.choose j m) : ℝ) * (k : ℝ) ^ m ≤
                ∑ m ∈ Finset.range j,
                    (↑(Nat.choose j m) : ℝ) * (k : ℝ) ^ m +
                      (↑(Nat.choose j j) : ℝ) * (k : ℝ) ^ j :=
                le_add_of_nonneg_right (by positivity)
              _ = ∑ m ∈ Finset.range (j + 1),
                    (↑(Nat.choose j m) : ℝ) * (k : ℝ) ^ m := by
                rw [Finset.sum_range_succ]
              _ = ((k : ℝ) + 1) ^ j := by
                simpa [mul_comm] using (add_pow (k : ℝ) 1 j).symm
        _ ≤ (2 : ℝ) ^ (k + 1) * (↑(k + 1) : ℝ) ^ j := by
            have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
              rw [pow_succ]
              nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
            have hcast : (↑(k + 1) : ℝ) = (k : ℝ) + 1 := by norm_cast
            rw [← hcast]
            exact mul_le_mul_of_nonneg_right hpow (by positivity)

private theorem scaled_translation_expansion
    (d : ℕ) (P : Polynomial ℝ) (Y : ℤ) (α : ℕ → ℝ) (r : ℤ)
    (hP : P.comp (X + C (Y : ℝ)) =
      ∑ j ∈ Finset.range (d + 1), C (α j) * X ^ j) :
    (C (r : ℝ) * P).comp (X + C (Y : ℝ)) =
      ∑ j ∈ Finset.range (d + 1), C ((r : ℝ) * α j) * X ^ j := by
  calc
    (C (r : ℝ) * P).comp (X + C (Y : ℝ)) =
        C (r : ℝ) * P.comp (X + C (Y : ℝ)) := by simp
    _ = C (r : ℝ) *
        (∑ j ∈ Finset.range (d + 1), C (α j) * X ^ j) := by rw [hP]
    _ = ∑ j ∈ Finset.range (d + 1), C ((r : ℝ) * α j) * X ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [mul_assoc]

private theorem iteratedPolynomialForwardDifference_add
    (k : ℕ) (P Q : Polynomial ℝ) :
    iteratedPolynomialForwardDifference k (P + Q) =
      iteratedPolynomialForwardDifference k P +
        iteratedPolynomialForwardDifference k Q := by
  induction k generalizing P Q with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedPolynomialForwardDifference]
      rw [show polynomialForwardDifference (P + Q) =
          polynomialForwardDifference P + polynomialForwardDifference Q by
        simp [polynomialForwardDifference, Polynomial.add_comp,
          sub_add_sub_comm]]
      exact ih (polynomialForwardDifference P) (polynomialForwardDifference Q)

private theorem iteratedPolynomialForwardDifference_zero (k : ℕ) :
    iteratedPolynomialForwardDifference k (0 : Polynomial ℝ) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedPolynomialForwardDifference]
      rw [show polynomialForwardDifference (0 : Polynomial ℝ) = 0 by
        simp [polynomialForwardDifference]]
      exact ih

private theorem iteratedPolynomialForwardDifference_C_mul
    (k : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    iteratedPolynomialForwardDifference k (C a * P) =
      C a * iteratedPolynomialForwardDifference k P := by
  induction k generalizing a P with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedPolynomialForwardDifference]
      rw [show polynomialForwardDifference (C a * P) =
          C a * polynomialForwardDifference P by
        simp [polynomialForwardDifference, Polynomial.mul_comp,
          Polynomial.C_comp, mul_sub]]
      exact ih a (polynomialForwardDifference P)

private theorem iteratedPolynomialForwardDifference_sum
    (k : ℕ) (s : Finset ℕ) (f : ℕ → Polynomial ℝ) :
    iteratedPolynomialForwardDifference k (∑ j ∈ s, f j) =
      ∑ j ∈ s, iteratedPolynomialForwardDifference k (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iteratedPolynomialForwardDifference_zero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [iteratedPolynomialForwardDifference_add, ih]

private theorem polynomialForwardDifference_X_pow (j : ℕ) :
    polynomialForwardDifference (X ^ j : Polynomial ℝ) =
      ∑ m ∈ Finset.range j,
        C (Nat.choose j m : ℝ) * X ^ m := by
  simp only [polynomialForwardDifference, Polynomial.pow_comp, Polynomial.X_comp]
  rw [add_pow, Finset.sum_range_succ]
  simp only [C_1, one_pow, Nat.sub_self, pow_zero, Nat.choose_self,
    Nat.cast_one, mul_one, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [← C_eq_natCast]
  ring

private theorem translation_comp_commute (Y : ℝ) :
    ((X : Polynomial ℝ) + C (1 : ℝ)).comp (X + C Y) =
      (X + C Y).comp ((X : Polynomial ℝ) + C (1 : ℝ)) := by
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  ring

private theorem polynomialForwardDifference_comp_translation
    (P : Polynomial ℝ) (Y : ℝ) :
    polynomialForwardDifference (P.comp (X + C Y)) =
      (polynomialForwardDifference P).comp (X + C Y) := by
  unfold polynomialForwardDifference
  calc
    (P.comp ((X : Polynomial ℝ) + C Y)).comp
        ((X : Polynomial ℝ) + C (1 : ℝ)) -
        P.comp ((X : Polynomial ℝ) + C Y) =
        P.comp (((X : Polynomial ℝ) + C Y).comp
          ((X : Polynomial ℝ) + C (1 : ℝ))) -
          P.comp ((X : Polynomial ℝ) + C Y) := by
          rw [Polynomial.comp_assoc]
    _ = P.comp (((X : Polynomial ℝ) + C (1 : ℝ)).comp
          ((X : Polynomial ℝ) + C Y)) -
          P.comp ((X : Polynomial ℝ) + C Y) := by
          rw [← translation_comp_commute Y]
    _ = (P.comp ((X : Polynomial ℝ) + C (1 : ℝ)) - P).comp
          ((X : Polynomial ℝ) + C Y) := by
          rw [Polynomial.sub_comp, Polynomial.comp_assoc]

private theorem iteratedPolynomialForwardDifference_comp_translation
    (k : ℕ) (P : Polynomial ℝ) (Y : ℝ) :
    iteratedPolynomialForwardDifference k (P.comp (X + C Y)) =
      (iteratedPolynomialForwardDifference k P).comp (X + C Y) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedPolynomialForwardDifference]
      rw [polynomialForwardDifference_comp_translation]
      exact ih (polynomialForwardDifference P)

/-- The translated-coordinate definition agrees with the source convention
`c_k=(Δ^k P)(Y)`. -/
theorem polynomialBinomialCoefficient_eq_centeredDifference
    (d : ℕ) (P : Polynomial ℝ) (Y : ℤ) (k : ℕ) :
    polynomialBinomialCoefficient d P Y k =
      (iteratedPolynomialForwardDifference k P).eval (Y : ℝ) := by
  unfold polynomialBinomialCoefficient
  rw [iteratedPolynomialForwardDifference_comp_translation]
  simp [Polynomial.eval_comp]

private theorem monomialForwardDifferenceCoefficient_eq_iterated
    (k j : ℕ) :
    (monomialForwardDifferenceCoefficient k j : ℝ) =
      (iteratedPolynomialForwardDifference k (X ^ j : Polynomial ℝ)).eval 0 := by
  induction k generalizing j with
  | zero =>
      cases j <;>
        norm_num [monomialForwardDifferenceCoefficient,
          iteratedPolynomialForwardDifference]
  | succ k ih =>
      simp only [monomialForwardDifferenceCoefficient, Int.cast_sum,
        Int.cast_mul, Int.cast_natCast, iteratedPolynomialForwardDifference]
      rw [polynomialForwardDifference_X_pow,
        iteratedPolynomialForwardDifference_sum]
      simp only [iteratedPolynomialForwardDifference_C_mul,
        Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
      apply Finset.sum_congr rfl
      intro m hm
      rw [ih m]

private theorem monomialForwardDifferenceCoefficient_zero_of_pos
    {k : ℕ} (hk : 0 < k) :
    monomialForwardDifferenceCoefficient k 0 = 0 := by
  cases k with
  | zero => omega
  | succ k => simp [monomialForwardDifferenceCoefficient]

/-- The public coefficient definition is exactly the source's iterated forward
difference evaluated at the translated centre. -/
theorem polynomialBinomialCoefficient_eq_iterated
    (d : ℕ) (P : Polynomial ℝ) (Y : ℤ) (k : ℕ) :
    polynomialBinomialCoefficient d P Y k =
      (iteratedPolynomialForwardDifference k
        (P.comp (X + C (Y : ℝ)))).eval 0 := rfl

/-- Under a power-basis expansion, the exact difference coefficient is the
integer-weighted sum of the translated monomial coefficients. -/
theorem polynomialBinomialCoefficient_eq_sum_of_expansion
    (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (Y : ℤ)
    (α : ℕ → ℝ) (hP : P.comp (X + C (Y : ℝ)) =
      ∑ j ∈ Finset.range (d + 1), C (α j) * X ^ j)
    {k : ℕ} (hk : 1 ≤ k) :
    polynomialBinomialCoefficient d P Y k =
      ∑ j ∈ Finset.Icc 1 d,
        (monomialForwardDifferenceCoefficient k j : ℝ) * α j := by
  have hEval :
      polynomialBinomialCoefficient d P Y k =
        ∑ j ∈ Finset.range (d + 1),
          α j * (monomialForwardDifferenceCoefficient k j : ℝ) := by
    unfold polynomialBinomialCoefficient
    rw [hP, iteratedPolynomialForwardDifference_sum]
    simp only [iteratedPolynomialForwardDifference_C_mul,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← monomialForwardDifferenceCoefficient_eq_iterated k j]
  have hset : Finset.range (d + 1) =
      insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsum :
      (∑ j ∈ Finset.Icc 1 d,
        α j * (monomialForwardDifferenceCoefficient k j : ℝ)) =
      ∑ j ∈ Finset.range (d + 1),
        α j * (monomialForwardDifferenceCoefficient k j : ℝ) := by
    rw [hset, Finset.sum_insert (by simp)]
    have hkpos : 0 < k := by omega
    rw [monomialForwardDifferenceCoefficient_zero_of_pos hkpos]
    simp
  calc
    polynomialBinomialCoefficient d P Y k =
      ∑ j ∈ Finset.range (d + 1),
        α j * (monomialForwardDifferenceCoefficient k j : ℝ) := hEval
    _ = ∑ j ∈ Finset.Icc 1 d,
        α j * (monomialForwardDifferenceCoefficient k j : ℝ) := hsum.symm
    _ = ∑ j ∈ Finset.Icc 1 d,
        (monomialForwardDifferenceCoefficient k j : ℝ) * α j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring

/-- Monomial coefficient control implies the exact binomial seminorm bound
with the source factor `E_d=1+d 2^d d^d`. -/
theorem monomialToBinomialControl
    (d : ℕ) (hd : 1 ≤ d) (Y : ℤ) (H : ℝ) (hH : 1 ≤ H)
    (P : Polynomial ℝ) (α : ℕ → ℝ)
    (hP : P.comp (X + C (Y : ℝ)) =
      ∑ j ∈ Finset.range (d + 1), C (α j) * X ^ j)
    (r : ℤ) (_hr : 1 ≤ r) (B : ℝ)
    (hmono : ∀ j ∈ Finset.Icc 1 d,
      H ^ j * realDistanceToIntegers ((r : ℝ) * α j) ≤ B) :
    polynomialBinomialCoefficientNorm d (C (r : ℝ) * P) Y H ≤
      (inverseBoundEValue d : ℝ) * B := by
  classical
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hB : 0 ≤ B := by
    have hdist : 0 ≤ realDistanceToIntegers ((r : ℝ) * α 1) := by
      unfold realDistanceToIntegers
      exact Metric.infDist_nonneg
    have hbound := hmono 1 (Finset.mem_Icc.mpr ⟨by omega, hd⟩)
    exact le_trans (mul_nonneg (by positivity) hdist) hbound
  have hE :
      (d : ℝ) * (2 : ℝ) ^ d * (d : ℝ) ^ d ≤
        (inverseBoundEValue d : ℝ) := by
    simp [inverseBoundEValue]
  have hscaled := scaled_translation_expansion d P Y α r hP
  unfold polynomialBinomialCoefficientNorm
  rw [dite_eq_left hd]
  apply Finset.sup'_le
  intro k hk
  have hklo : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkhi : k ≤ d := (Finset.mem_Icc.mp hk).2
  have hcoeffFormula :
      polynomialBinomialCoefficient d (C (r : ℝ) * P) Y k =
        ∑ j ∈ Finset.Icc 1 d,
          (monomialForwardDifferenceCoefficient k j : ℝ) * ((r : ℝ) * α j) := by
    exact polynomialBinomialCoefficient_eq_sum_of_expansion d hd
      (C (r : ℝ) * P) Y (fun j => (r : ℝ) * α j) hscaled (by omega)
  have hdist := realDistanceToIntegers_intWeightedSum_le
    (S := Finset.Icc 1 d)
    (m := fun j => monomialForwardDifferenceCoefficient k j)
    (x := fun j => (r : ℝ) * α j)
    (ε := fun j => B / H ^ j)
    (by
      intro j hj
      apply (le_div_iff₀ (pow_pos hHpos j)).2
      simpa [mul_comm] using hmono j hj)
  have hcoeffBound (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      |(monomialForwardDifferenceCoefficient k j : ℝ)| ≤
        (2 : ℝ) ^ d * (d : ℝ) ^ d := by
    have hkpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ d :=
      pow_le_pow_right₀ (by norm_num) hkhi
    have hbase : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkhi
    have hexp : j ≤ d := (Finset.mem_Icc.mp hj).2
    have hpow : (k : ℝ) ^ j ≤ (d : ℝ) ^ d := by
      calc
        (k : ℝ) ^ j ≤ (d : ℝ) ^ j :=
          pow_le_pow_left₀ (by positivity) hbase j
        _ ≤ (d : ℝ) ^ d :=
          pow_le_pow_right₀ (by exact_mod_cast hd) hexp
    calc
      |(monomialForwardDifferenceCoefficient k j : ℝ)| ≤
          (2 : ℝ) ^ k * (k : ℝ) ^ j :=
        monomialForwardDifferenceCoefficient_bound k j
      _ ≤ (2 : ℝ) ^ d * (d : ℝ) ^ d := by
        exact mul_le_mul hkpow hpow (by positivity) (by positivity)
  have htermBound (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      H ^ k *
          (|(monomialForwardDifferenceCoefficient k j : ℝ)| *
            (B / H ^ j)) ≤
        ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B := by
    by_cases hkj : k ≤ j
    · have hratio : H ^ k / H ^ j ≤ 1 :=
        (div_le_one₀ (pow_pos hHpos j)).2 (by gcongr)
      have hfactor : B * (H ^ k / H ^ j) ≤ B :=
        mul_le_of_le_one_right hB hratio
      have hweight :
          H ^ k * (B / H ^ j) = B * (H ^ k / H ^ j) := by
        field_simp [ne_of_gt (pow_pos hHpos j)]
      rw [show H ^ k *
          (|(monomialForwardDifferenceCoefficient k j : ℝ)| *
            (B / H ^ j)) =
          |(monomialForwardDifferenceCoefficient k j : ℝ)| *
            (H ^ k * (B / H ^ j)) by ring, hweight]
      calc
        |(monomialForwardDifferenceCoefficient k j : ℝ)| *
            (B * (H ^ k / H ^ j)) ≤
          ((2 : ℝ) ^ d * (d : ℝ) ^ d) *
            (B * (H ^ k / H ^ j)) :=
          mul_le_mul_of_nonneg_right (hcoeffBound j hj)
            (mul_nonneg hB (by positivity))
        _ ≤ ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
    · have hzero :=
        monomialForwardDifferenceCoefficient_eq_zero_of_lt
          (k := k) (j := j) (Nat.lt_of_not_ge hkj)
      rw [hzero]
      simp
      positivity
  have hsum :
      H ^ k *
          ∑ j ∈ Finset.Icc 1 d,
            |(monomialForwardDifferenceCoefficient k j : ℝ)| *
              (B / H ^ j) ≤
        (d : ℝ) * ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B := by
    calc
      H ^ k *
          ∑ j ∈ Finset.Icc 1 d,
            |(monomialForwardDifferenceCoefficient k j : ℝ)| *
              (B / H ^ j) =
        ∑ j ∈ Finset.Icc 1 d,
          H ^ k *
            (|(monomialForwardDifferenceCoefficient k j : ℝ)| *
              (B / H ^ j)) := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.Icc 1 d,
          ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B :=
        Finset.sum_le_sum fun j hj => htermBound j hj
      _ = (d : ℝ) * ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B := by
        rw [Finset.sum_const]
        simp [mul_assoc]
  have hnorm :
      H ^ k * realDistanceToIntegers
          (polynomialBinomialCoefficient d (C (r : ℝ) * P) Y k) ≤
        (d : ℝ) * ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B := by
    rw [hcoeffFormula]
    exact (mul_le_mul_of_nonneg_left hdist (by positivity)).trans
      (by simpa only [Finset.mul_sum] using hsum)
  calc
    H ^ k * realDistanceToIntegers
        (polynomialBinomialCoefficient d (C (r : ℝ) * P) Y k) ≤
      (d : ℝ) * ((2 : ℝ) ^ d * (d : ℝ) ^ d) * B := hnorm
    _ ≤ (inverseBoundEValue d : ℝ) * B := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hE hB

end FractionalPrimes.Literature.Polynomial
