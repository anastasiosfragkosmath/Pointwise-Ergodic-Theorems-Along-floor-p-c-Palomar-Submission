module

public import FractionalPrimes.Literature.Polynomial.PolynomialCoefficientNorm
public import FractionalPrimes.Literature.Polynomial.ScalarWeylWeightedDistance

/-!
# Integer-polynomial composition errors

This file isolates the finite integer-coefficient calculation used in the
large-`M` Type-I₂ degree descent.  Coefficients of powers of an integer
polynomial act as integer weights, so coefficientwise errors modulo the
integers are controlled by the corresponding weighted finite sum.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- The degree-`l` coefficient truncation of a real polynomial. -/
noncomputable def polynomialCoefficientTruncation
    (p : Polynomial ℝ) (l : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (l + 1), C (p.coeff j) * X ^ j

/-- The complementary coefficient tail through an approved degree bound
`d`. -/
noncomputable def polynomialCoefficientTail
    (p : Polynomial ℝ) (l d : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Ico (l + 1) (d + 1), C (p.coeff j) * X ^ j

/-- Under `natDegree p ≤ d`, truncation through `l≤d` plus the displayed
finite tail is exactly `p`. -/
theorem polynomialCoefficientTruncation_add_tail
    (p : Polynomial ℝ) {l d : ℕ} (hp : p.natDegree ≤ d)
    (hl : l ≤ d) :
    polynomialCoefficientTruncation p l +
        polynomialCoefficientTail p l d = p := by
  have hsum :
      p = ∑ j ∈ Finset.range (d + 1), C (p.coeff j) * X ^ j := by
    calc
      p = ∑ j ∈ Finset.range (p.natDegree + 1),
          C (p.coeff j) * X ^ j := p.as_sum_range_C_mul_X_pow
      _ = ∑ j ∈ Finset.range (d + 1), C (p.coeff j) * X ^ j := by
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Nat.le_trans
              (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hp))
        · intro j hj hnot
          have hjlarge : p.natDegree < j := by
            simp only [Finset.mem_range] at hj hnot
            omega
          simp [Polynomial.coeff_eq_zero_of_natDegree_lt hjlarge]
  dsimp [polynomialCoefficientTruncation, polynomialCoefficientTail]
  calc
    (∑ j ∈ Finset.range (l + 1), C (p.coeff j) * X ^ j) +
        ∑ j ∈ Finset.Ico (l + 1) (d + 1), C (p.coeff j) * X ^ j =
      ∑ j ∈ Finset.range (d + 1), C (p.coeff j) * X ^ j :=
        Finset.sum_range_add_sum_Ico
          (fun j => C (p.coeff j) * X ^ j) (Nat.succ_le_succ hl)
    _ = p := hsum.symm

theorem polynomialCoefficientTruncation_natDegree_le
    (p : Polynomial ℝ) (l : ℕ) :
    (polynomialCoefficientTruncation p l).natDegree ≤ l := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjl : j ≤ l := by
    simp only [Finset.mem_range] at hj
    omega
  calc
    (C (p.coeff j) * X ^ j).natDegree ≤
        (C (p.coeff j)).natDegree + (X ^ j).natDegree :=
      Polynomial.natDegree_mul_le
    _ = j := by simp
    _ ≤ l := hjl

@[simp] theorem polynomialCoefficientTruncation_coeff_top
    (p : Polynomial ℝ) (l : ℕ) :
    (polynomialCoefficientTruncation p l).coeff l = p.coeff l := by
  simp [polynomialCoefficientTruncation]

/-- If `V` has degree two, the degree-`2l` coefficient of the composed
truncation is exactly the degree-`l` scalar coefficient times the `l`-th
power of the quadratic coefficient of `V`. -/
theorem polynomialCoefficientTruncation_comp_coeff_two_mul
    (p V : Polynomial ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hVdegree : V.natDegree = 2) (s : ℝ) :
    ((C s * polynomialCoefficientTruncation p l).comp V).coeff (2 * l) =
      s * p.coeff l * (V.coeff 2) ^ l := by
  let T : Polynomial ℝ := polynomialCoefficientTruncation p l
  have hTdegree : T.natDegree ≤ l := by
    simpa [T] using polynomialCoefficientTruncation_natDegree_le p l
  have hTcoeff : T.coeff l = p.coeff l := by
    simp [T]
  have hcompScalar : (C s * T).comp V = C s * (T.comp V) := by
    simp only [Polynomial.comp, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rw [show polynomialCoefficientTruncation p l = T from rfl]
  rw [hcompScalar, Polynomial.coeff_C_mul]
  by_cases htop : p.coeff l = 0
  · have hTdegreePred : T.natDegree ≤ l - 1 := by
      apply (Polynomial.natDegree_le_iff_coeff_eq_zero).2
      intro n hn
      by_cases hnl : n = l
      · rw [hnl, hTcoeff, htop]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hln : l < n := by omega
        exact lt_of_le_of_lt hTdegree hln
    have hcompDegree : (T.comp V).natDegree < 2 * l := by
      calc
        (T.comp V).natDegree ≤ T.natDegree * V.natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ (l - 1) * 2 := by
          rw [hVdegree]
          exact Nat.mul_le_mul_right 2 hTdegreePred
        _ < 2 * l := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hcompDegree, htop]
    ring
  · have hTdegreeEq : T.natDegree = l :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hTdegree
        (by simpa [hTcoeff] using htop)
    have hVdegreeNe : V.natDegree ≠ 0 := by omega
    have htopCoeff :=
      Polynomial.coeff_comp_degree_mul_degree (p := T) (q := V) hVdegreeNe
    have hTleading : T.leadingCoeff = p.coeff l := by
      rw [Polynomial.leadingCoeff, hTdegreeEq, hTcoeff]
    have hVleading : V.leadingCoeff = V.coeff 2 := by
      rw [Polynomial.leadingCoeff, hVdegree]
    rw [hTdegreeEq, hVdegree, hTleading, hVleading] at htopCoeff
    rw [show (T.comp V).coeff (2 * l) =
        p.coeff l * V.coeff 2 ^ l by simpa [Nat.mul_comm] using htopCoeff]
    ring

theorem polynomialCoefficientTail_comp
    (p V : Polynomial ℝ) (l d : ℕ) :
    (polynomialCoefficientTail p l d).comp V =
      ∑ j ∈ Finset.Ico (l + 1) (d + 1), C (p.coeff j) * V ^ j := by
  simp [polynomialCoefficientTail, Polynomial.comp,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C]

/-- Composing a scalar multiple of the truncation with `V` is the full
composition minus the explicit finite higher-degree tail. -/
theorem polynomialCoefficientTruncation_comp_eq_sub_tail
    (p V : Polynomial ℝ) {l d : ℕ} (hp : p.natDegree ≤ d)
    (hl : l ≤ d) (s : ℝ) :
    (C s * polynomialCoefficientTruncation p l).comp V =
      C s * p.comp V -
        ∑ j ∈ Finset.Ico (l + 1) (d + 1),
          C (s * p.coeff j) * V ^ j := by
  have hsplit := polynomialCoefficientTruncation_add_tail p hp hl
  have htrunc :
      polynomialCoefficientTruncation p l =
        p - polynomialCoefficientTail p l d := by
    calc
      polynomialCoefficientTruncation p l =
          (polynomialCoefficientTruncation p l +
              polynomialCoefficientTail p l d) -
            polynomialCoefficientTail p l d := by ring
      _ = p - polynomialCoefficientTail p l d := by rw [hsplit]
  calc
    (C s * polynomialCoefficientTruncation p l).comp V =
        C s * (polynomialCoefficientTruncation p l).comp V := by
      simp only [Polynomial.comp, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    _ = C s * ((p - polynomialCoefficientTail p l d).comp V) := by
      rw [htrunc]
    _ = C s * (p.comp V -
        (polynomialCoefficientTail p l d).comp V) := by
      simp only [Polynomial.comp, Polynomial.eval₂_sub]
    _ = C s * p.comp V -
        C s * (polynomialCoefficientTail p l d).comp V := by ring
    _ = C s * p.comp V -
        C s * (∑ j ∈ Finset.Ico (l + 1) (d + 1),
          C (p.coeff j) * V ^ j) := by
      rw [polynomialCoefficientTail_comp]
    _ = C s * p.comp V -
        ∑ j ∈ Finset.Ico (l + 1) (d + 1),
          C (s * p.coeff j) * V ^ j := by
      rw [Finset.mul_sum]
      apply congrArg (fun q : Polynomial ℝ => C s * p.comp V - q)
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_assoc, ← Polynomial.C_mul]

/-- Distance to the integer lattice is bounded by the error from any chosen
integer representative. -/
theorem realDistanceToIntegers_le_abs_sub_int
    (x : ℝ) (z : ℤ) :
    realDistanceToIntegers x ≤ |x - (z : ℝ)| := by
  unfold realDistanceToIntegers
  calc
    Metric.infDist x (Set.range fun w : ℤ => (w : ℝ)) ≤
        dist x (z : ℝ) :=
      Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    _ = |x - (z : ℝ)| := by rw [Real.dist_eq]

/-- Circle distance satisfies the subtraction triangle inequality. -/
theorem realDistanceToIntegers_sub_le (x y : ℝ) :
    realDistanceToIntegers (x - y) ≤
      realDistanceToIntegers x + realDistanceToIntegers y := by
  obtain ⟨zx, hzx⟩ :=
    exists_int_abs_sub_le_of_realDistanceToIntegers_le
      (show realDistanceToIntegers x ≤ realDistanceToIntegers x from le_rfl)
  obtain ⟨zy, hzy⟩ :=
    exists_int_abs_sub_le_of_realDistanceToIntegers_le
      (show realDistanceToIntegers y ≤ realDistanceToIntegers y from le_rfl)
  calc
    realDistanceToIntegers (x - y) ≤
        |(x - y) - ((zx - zy : ℤ) : ℝ)| :=
      realDistanceToIntegers_le_abs_sub_int (x - y) (zx - zy)
    _ = |(x - (zx : ℝ)) - (y - (zy : ℝ))| := by
      push_cast
      congr 1
      ring
    _ ≤ |x - (zx : ℝ)| + |y - (zy : ℝ)| := abs_sub _ _
    _ ≤ realDistanceToIntegers x + realDistanceToIntegers y :=
      add_le_add hzx hzy

/-- Multiplication by an integer increases circle distance by at most the
absolute value of that integer. -/
theorem realDistanceToIntegers_int_mul_le (m : ℤ) (x : ℝ) :
    realDistanceToIntegers ((m : ℝ) * x) ≤
      |(m : ℝ)| * realDistanceToIntegers x := by
  have h := realDistanceToIntegers_intWeightedSum_le
    (S := (Finset.univ : Finset Unit))
    (m := fun _ : Unit => m)
    (x := fun _ : Unit => x)
    (ε := fun _ : Unit => realDistanceToIntegers x)
    (by intro u hu; exact le_rfl)
  simpa using h

@[simp] theorem realDistanceToIntegers_neg (x : ℝ) :
    realDistanceToIntegers (-x) = realDistanceToIntegers x := by
  apply le_antisymm
  · have h := realDistanceToIntegers_int_mul_le (-1) x
    norm_num at h ⊢
    exact h
  · have h := realDistanceToIntegers_int_mul_le (-1) (-x)
    norm_num at h ⊢
    exact h

theorem realDistanceToIntegers_neg_pow_mul (x y : ℝ) (l : ℕ) :
    realDistanceToIntegers ((-x) ^ l * y) =
      realDistanceToIntegers (x ^ l * y) := by
  rcases Nat.even_or_odd l with hl | hl
  · rw [hl.neg_pow]
  · rw [hl.neg_pow]
    simpa only [neg_mul, realDistanceToIntegers_neg]

/-- A finite linear combination of powers of an integer polynomial has, in
each coefficient, precisely the integer-weighted circle error inherited from
its scalar coefficients. -/
theorem realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_le
    (S : Finset ℕ) (x ε : ℕ → ℝ) (V : Polynomial ℤ)
    (hε : ∀ j ∈ S, realDistanceToIntegers (x j) ≤ ε j)
    (i : ℕ) :
    realDistanceToIntegers
        ((∑ j ∈ S,
          C (x j) * (V.map (Int.castRingHom ℝ)) ^ j).coeff i) ≤
      ∑ j ∈ S, |((((V ^ j).coeff i : ℤ) : ℝ))| * ε j := by
  classical
  have hcoeff :
      ((∑ j ∈ S,
          C (x j) * (V.map (Int.castRingHom ℝ)) ^ j).coeff i) =
        ∑ j ∈ S, ((((V ^ j).coeff i : ℤ) : ℝ)) * x j := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.coeff_C_mul]
    rw [← Polynomial.map_pow, Polynomial.coeff_map]
    change x j * ((((V ^ j).coeff i : ℤ) : ℝ)) = _
    ring
  rw [hcoeff]
  exact realDistanceToIntegers_intWeightedSum_le S
    (fun j => (V ^ j).coeff i) x ε hε

/-- After multiplying the coefficient in degree `i` by the ambient scale
`L^i`, the same error is bounded by the weighted coefficient norms of the
integer-polynomial powers. -/
theorem realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_weighted_le
    (S : Finset ℕ) (x ε : ℕ → ℝ) (V : Polynomial ℤ)
    (L : ℝ) (hL : 0 ≤ L)
    (hε : ∀ j ∈ S, realDistanceToIntegers (x j) ≤ ε j)
    (i : ℕ) :
    L ^ i * realDistanceToIntegers
        ((∑ j ∈ S,
          C (x j) * (V.map (Int.castRingHom ℝ)) ^ j).coeff i) ≤
      ∑ j ∈ S,
        polynomialWeightedCoefficientSum L
            ((V.map (Int.castRingHom ℝ)) ^ j) * ε j := by
  classical
  have hdist := realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_le
    S x ε V hε i
  have hεnonneg (j : ℕ) (hj : j ∈ S) : 0 ≤ ε j :=
    Metric.infDist_nonneg.trans (hε j hj)
  have hcoefficient (j : ℕ) :
      L ^ i * |((((V ^ j).coeff i : ℤ) : ℝ))| ≤
        polynomialWeightedCoefficientSum L
          ((V.map (Int.castRingHom ℝ)) ^ j) := by
    have hcast :
        ((((V ^ j).coeff i : ℤ) : ℝ)) =
          ((V.map (Int.castRingHom ℝ)) ^ j).coeff i := by
      rw [← Polynomial.map_pow, Polynomial.coeff_map]
      rfl
    rw [hcast]
    have hs := polynomialWeightedCoefficientSum_summable L
      ((V.map (Int.castRingHom ℝ)) ^ j)
    have hterm := hs.le_tsum i (fun n hn =>
      mul_nonneg (pow_nonneg hL n) (abs_nonneg _))
    simpa [polynomialWeightedCoefficientSum] using hterm
  calc
    L ^ i * realDistanceToIntegers
        ((∑ j ∈ S,
          C (x j) * (V.map (Int.castRingHom ℝ)) ^ j).coeff i) ≤
        L ^ i *
          (∑ j ∈ S, |((((V ^ j).coeff i : ℤ) : ℝ))| * ε j) :=
      mul_le_mul_of_nonneg_left hdist (pow_nonneg hL i)
    _ = ∑ j ∈ S,
        (L ^ i * |((((V ^ j).coeff i : ℤ) : ℝ))|) * ε j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j ∈ S,
        polynomialWeightedCoefficientSum L
            ((V.map (Int.castRingHom ℝ)) ^ j) * ε j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcoefficient j) (hεnonneg j hj)

/-- Source-normalized form of the finite tail estimate.  If the scalar error
in degree `j` is at most `U H⁻ʲ` and the normalized weighted coefficient norm
of `V^j` is at most `A^j`, then any coefficient of the composed tail has
normalized circle error at most `d A^d U`. -/
theorem realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_normalized_le
    (S : Finset ℕ) (x : ℕ → ℝ) (V : Polynomial ℤ)
    (H L U A : ℝ) (d i : ℕ)
    (hH : 0 < H) (hL : 0 ≤ L) (hU : 0 ≤ U) (hA : 1 ≤ A)
    (hscaled : ∀ j ∈ S,
      H ^ j * realDistanceToIntegers (x j) ≤ U)
    (hnorm : ∀ j ∈ S,
      H⁻¹ ^ j * polynomialWeightedCoefficientSum L
          ((V.map (Int.castRingHom ℝ)) ^ j) ≤ A ^ j)
    (hdegree : ∀ j ∈ S, j ≤ d) (hcard : S.card ≤ d) :
    L ^ i * realDistanceToIntegers
        ((∑ j ∈ S,
          C (x j) * (V.map (Int.castRingHom ℝ)) ^ j).coeff i) ≤
      (d : ℝ) * A ^ d * U := by
  classical
  let ε : ℕ → ℝ := fun j => U / H ^ j
  have hε (j : ℕ) (hj : j ∈ S) :
      realDistanceToIntegers (x j) ≤ ε j := by
    apply (le_div_iff₀ (pow_pos hH j)).2
    calc
      realDistanceToIntegers (x j) * H ^ j =
          H ^ j * realDistanceToIntegers (x j) := by ring
      _ ≤ U := hscaled j hj
  have hweighted :=
    realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_weighted_le
      S x ε V L hL hε i
  have hterm (j : ℕ) (hj : j ∈ S) :
      polynomialWeightedCoefficientSum L
            ((V.map (Int.castRingHom ℝ)) ^ j) * ε j ≤
        A ^ d * U := by
    calc
      polynomialWeightedCoefficientSum L
            ((V.map (Int.castRingHom ℝ)) ^ j) * ε j =
          (H⁻¹ ^ j * polynomialWeightedCoefficientSum L
              ((V.map (Int.castRingHom ℝ)) ^ j)) * U := by
        dsimp [ε]
        rw [div_eq_mul_inv, inv_pow]
        ring
      _ ≤ A ^ j * U :=
        mul_le_mul_of_nonneg_right (hnorm j hj) hU
      _ ≤ A ^ d * U :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hA (hdegree j hj)) hU
  calc
    L ^ i * realDistanceToIntegers
        ((∑ j ∈ S,
          C (x j) * (V.map (Int.castRingHom ℝ)) ^ j).coeff i) ≤
      ∑ j ∈ S,
        polynomialWeightedCoefficientSum L
            ((V.map (Int.castRingHom ℝ)) ^ j) * ε j := hweighted
    _ ≤ ∑ j ∈ S, A ^ d * U := by
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j hj
    _ = (S.card : ℝ) * (A ^ d * U) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * (A ^ d * U) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard)
        (mul_nonneg (pow_nonneg (le_trans zero_le_one hA) d) hU)
    _ = (d : ℝ) * A ^ d * U := by ring

/-- Exact algebraic error estimate for one coefficient of the truncated phase
after composition with an integer polynomial.  The first term is the original
composition error multiplied by the integer quotient `k`; the second is the
discarded higher-degree tail. -/
theorem polynomialCoefficientTruncation_comp_error_le
    (p : Polynomial ℝ) (V : Polynomial ℤ) {l d : ℕ}
    (hp : p.natDegree ≤ d) (hl : l ≤ d)
    (s v k : ℤ) (hsk : s = v * k)
    (H L U A B : ℝ) (i : ℕ)
    (hH : 0 < H) (hL : 0 ≤ L) (hU : 0 ≤ U) (hA : 1 ≤ A)
    (horiginal :
      L ^ i * realDistanceToIntegers
        ((v : ℝ) *
          (p.comp (V.map (Int.castRingHom ℝ))).coeff i) ≤ B)
    (hhigh : ∀ j ∈ Finset.Ico (l + 1) (d + 1),
      H ^ j * realDistanceToIntegers ((s : ℝ) * p.coeff j) ≤ U)
    (hnorm : ∀ j ∈ Finset.Ico (l + 1) (d + 1),
      H⁻¹ ^ j * polynomialWeightedCoefficientSum L
          ((V.map (Int.castRingHom ℝ)) ^ j) ≤ A ^ j) :
    L ^ i * realDistanceToIntegers
        (((C (s : ℝ) * polynomialCoefficientTruncation p l).comp
          (V.map (Int.castRingHom ℝ))).coeff i) ≤
      |(k : ℝ)| * B + (d : ℝ) * A ^ d * U := by
  classical
  let S : Finset ℕ := Finset.Ico (l + 1) (d + 1)
  let Vreal : Polynomial ℝ := V.map (Int.castRingHom ℝ)
  let tail : Polynomial ℝ :=
    ∑ j ∈ S, C ((s : ℝ) * p.coeff j) * Vreal ^ j
  have hpoly := polynomialCoefficientTruncation_comp_eq_sub_tail
    p Vreal hp hl (s : ℝ)
  have hcoeff :
      ((C (s : ℝ) * polynomialCoefficientTruncation p l).comp Vreal).coeff i =
        (s : ℝ) * (p.comp Vreal).coeff i - tail.coeff i := by
    have h := congrArg (fun q : Polynomial ℝ => q.coeff i) hpoly
    simpa [S, Vreal, tail, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul] using h
  have hscalar :
      (s : ℝ) * (p.comp Vreal).coeff i =
        (k : ℝ) * ((v : ℝ) * (p.comp Vreal).coeff i) := by
    rw [hsk]
    push_cast
    ring
  have hfirstDist :
      realDistanceToIntegers ((s : ℝ) * (p.comp Vreal).coeff i) ≤
        |(k : ℝ)| * realDistanceToIntegers
          ((v : ℝ) * (p.comp Vreal).coeff i) := by
    rw [hscalar]
    exact realDistanceToIntegers_int_mul_le k
      ((v : ℝ) * (p.comp Vreal).coeff i)
  have hfirst :
      L ^ i * realDistanceToIntegers
          ((s : ℝ) * (p.comp Vreal).coeff i) ≤ |(k : ℝ)| * B := by
    calc
      L ^ i * realDistanceToIntegers
          ((s : ℝ) * (p.comp Vreal).coeff i) ≤
        L ^ i * (|(k : ℝ)| * realDistanceToIntegers
          ((v : ℝ) * (p.comp Vreal).coeff i)) :=
        mul_le_mul_of_nonneg_left hfirstDist (pow_nonneg hL i)
      _ = |(k : ℝ)| *
          (L ^ i * realDistanceToIntegers
            ((v : ℝ) * (p.comp Vreal).coeff i)) := by ring
      _ ≤ |(k : ℝ)| * B :=
        mul_le_mul_of_nonneg_left (by simpa [Vreal] using horiginal)
          (abs_nonneg _)
  have htail :
      L ^ i * realDistanceToIntegers (tail.coeff i) ≤
        (d : ℝ) * A ^ d * U := by
    have hdegree : ∀ j ∈ S, j ≤ d := by
      intro j hj
      simp only [S, Finset.mem_Ico] at hj
      omega
    have hcard : S.card ≤ d := by
      simp only [S, Nat.card_Ico]
      omega
    have h :=
      realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_normalized_le
        S (fun j => (s : ℝ) * p.coeff j) V H L U A d i
        hH hL hU hA
        (by intro j hj; exact hhigh j (by simpa [S] using hj))
        (by intro j hj; exact hnorm j (by simpa [S] using hj))
        hdegree hcard
    simpa [tail, Vreal] using h
  rw [hcoeff]
  calc
    L ^ i * realDistanceToIntegers
        ((s : ℝ) * (p.comp Vreal).coeff i - tail.coeff i) ≤
      L ^ i *
        (realDistanceToIntegers ((s : ℝ) * (p.comp Vreal).coeff i) +
          realDistanceToIntegers (tail.coeff i)) :=
      mul_le_mul_of_nonneg_left
        (realDistanceToIntegers_sub_le
          ((s : ℝ) * (p.comp Vreal).coeff i) (tail.coeff i))
        (pow_nonneg hL i)
    _ = L ^ i * realDistanceToIntegers
          ((s : ℝ) * (p.comp Vreal).coeff i) +
        L ^ i * realDistanceToIntegers (tail.coeff i) := by ring
    _ ≤ |(k : ℝ)| * B + (d : ℝ) * A ^ d * U :=
      add_le_add hfirst htail

/-- The numerical absorption used immediately after the composition-error
estimate: when both the quotient and the old inverse bound are at most
`U≥1`, the two error terms fit into `(1+dA^d)U²`. -/
theorem polynomialCoefficientTruncation_error_absorb
    (d : ℕ) (A B U K : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 1 ≤ U)
    (hKU : K ≤ U) (hBU : B ≤ U) :
    K * B + (d : ℝ) * A ^ d * U ≤
      (1 + (d : ℝ) * A ^ d) * U ^ 2 := by
  have hU0 : 0 ≤ U := le_trans zero_le_one hU
  have hfirst : K * B ≤ U ^ 2 := by
    calc
      K * B ≤ U * U := mul_le_mul hKU hBU hB hU0
      _ = U ^ 2 := by ring
  have hUleSq : U ≤ U ^ 2 := by nlinarith
  have hfactor : 0 ≤ (d : ℝ) * A ^ d := by positivity
  have hsecond : (d : ℝ) * A ^ d * U ≤
      (d : ℝ) * A ^ d * U ^ 2 :=
    mul_le_mul_of_nonneg_left hUleSq hfactor
  calc
    K * B + (d : ℝ) * A ^ d * U ≤
        U ^ 2 + (d : ℝ) * A ^ d * U ^ 2 := add_le_add hfirst hsecond
    _ = (1 + (d : ℝ) * A ^ d) * U ^ 2 := by ring

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.polynomialCoefficientTruncation_add_tail
#print axioms FractionalPrimes.Literature.Polynomial.polynomialCoefficientTruncation_comp_eq_sub_tail
#print axioms FractionalPrimes.Literature.Polynomial.polynomialCoefficientTruncation_comp_error_le
#print axioms FractionalPrimes.Literature.Polynomial.polynomialCoefficientTruncation_error_absorb
#print axioms FractionalPrimes.Literature.Polynomial.realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_le
#print axioms FractionalPrimes.Literature.Polynomial.realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_weighted_le
#print axioms FractionalPrimes.Literature.Polynomial.realDistanceToIntegers_coeff_sum_C_mul_pow_map_int_normalized_le
