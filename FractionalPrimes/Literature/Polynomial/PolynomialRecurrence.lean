module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceFejerDetection
public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceDenseInterpolation
public import FractionalPrimes.Literature.Polynomial.ScalarWeylInverse
public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceBudgets
public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import FractionalPrimes.Literature.Polynomial.ScalarWeylWeightedDistance
public import Mathlib.Combinatorics.Pigeonhole

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

private theorem sumIcoOne_eq_sumRange {M : Type*} [AddCommMonoid M]
    (N : ℕ) (F : ℤ → M) :
    (∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1), F n) =
      ∑ k ∈ Finset.range N, F (1 + (k : ℤ)) := by
  have hIco : Finset.Ico (1 : ℤ) ((N : ℤ) + 1) =
      (Finset.range N).map
        (Nat.castEmbedding.trans (addLeftEmbedding (1 : ℤ))) := by
    simpa using Int.Ico_eq_finset_map (1 : ℤ) ((N : ℤ) + 1)
  rw [hIco, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]

private theorem constantCoefficient_of_good_values
    {N : ℕ} (hN : 1 ≤ N) {δ ε : ℝ} (hδ : 0 < δ)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ 0)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n : ℕ => realDistanceToIntegers
          (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)).card : ℝ)) :
    realDistanceToIntegers (P.coeff 0) ≤ ε := by
  classical
  let G : Finset ℕ := (Finset.range N).filter
    (fun n : ℕ => realDistanceToIntegers
      (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hGcard : 0 < (G.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hδ hNpos) (by simpa [G] using hgood)
  have hGpos : 0 < G.card := by exact_mod_cast hGcard
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hGpos
  have hdist : realDistanceToIntegers (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε :=
    (Finset.mem_filter.mp hn).2
  rw [Polynomial.eq_C_of_natDegree_le_zero hP] at hdist
  simpa only [Polynomial.eval_C] using hdist

private theorem coeff_C_mul_X_pow_sum_Icc
    {d j : ℕ} (a : ℕ → ℝ) (hj : j ∈ Finset.Icc 1 d) :
    (∑ i ∈ Finset.Icc 1 d, Polynomial.C (a i) * Polynomial.X ^ i).coeff j = a j := by
  classical
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hne
    simp [hne.symm]
  · intro hnot
    exact (hnot hj).elim

private theorem coeff_C_mul_X_pow_sum_Icc_zero
    (d : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 d, Polynomial.C (a i) * Polynomial.X ^ i).coeff 0 = 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hi0 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  simp
  intro hzero
  omega

private theorem natDegree_sum_C_mul_X_pow_Icc
    (d : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 d, Polynomial.C (a j) * Polynomial.X ^ j).natDegree ≤ d := by
  classical
  calc
    (∑ j ∈ Finset.Icc 1 d, Polynomial.C (a j) * Polynomial.X ^ j).natDegree ≤
        (Finset.Icc 1 d).sup
          (fun j => (Polynomial.C (a j) * Polynomial.X ^ j).natDegree) :=
      Polynomial.natDegree_sum_le _ _
    _ ≤ d := by
      apply Finset.sup_le
      intro j hj
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Finset.mem_Icc.mp hj).2

private theorem eval_sum_C_mul_X_pow_Icc
    {R : Type*} [Semiring R] (d : ℕ) (a : ℕ → R) (x : R) :
    (∑ j ∈ Finset.Icc 1 d,
      Polynomial.C (a j) * Polynomial.X ^ j).eval x =
        ∑ j ∈ Finset.Icc 1 d, a j * x ^ j := by
  simp [Polynomial.eval_finsetSum, Polynomial.eval_C]

private theorem polynomial_eval_map_int_cast (Q : Polynomial ℤ) (n : ℕ) :
    (Q.map (Int.castRingHom ℝ)).eval (n : ℝ) =
      (Int.castRingHom ℝ) (Q.eval (n : ℤ)) := by
  simpa only [Int.cast_natCast] using
    Polynomial.eval_intCast_map (Int.castRingHom ℝ) Q (n : ℤ)

private theorem realDistanceToIntegers_nat_mul_le
    (m : ℕ) (x ε : ℝ) (hx : realDistanceToIntegers x ≤ ε) :
    realDistanceToIntegers ((m : ℝ) * x) ≤ (m : ℝ) * ε := by
  classical
  have h := realDistanceToIntegers_intWeightedSum_le
    (S := (Finset.univ : Finset Unit))
    (m := fun _ : Unit => (m : ℤ))
    (x := fun _ : Unit => x) (ε := fun _ : Unit => ε)
    (by intro i hi; exact hx)
  have hAbs : |((m : ℤ) : ℝ)| = (m : ℝ) := by
    rw [abs_of_nonneg (show (0 : ℝ) ≤ ((m : ℤ) : ℝ) by exact_mod_cast Nat.zero_le m)]
    norm_cast
  simpa [hAbs] using h

private theorem floor_centered_integer_interval_card_le
    {a w J : ℝ} (hw : 0 ≤ w) (hwidth : 2 * w + 2 ≤ J) :
    (((Finset.Icc (Int.floor (a - w)) (Int.floor (a + w))).card : ℕ) : ℝ) ≤ J := by
  let lo := Int.floor (a - w)
  let hi := Int.floor (a + w)
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact Int.floor_mono (by linarith)
  have hcardZ :
      ((Finset.Icc lo hi).card : ℤ) = hi + 1 - lo := by
    simpa using Int.card_Icc_of_le (a := lo) (b := hi) (by omega)
  have hcardR :
      ((Finset.Icc lo hi).card : ℝ) = (hi : ℝ) + 1 - (lo : ℝ) := by
    exact_mod_cast hcardZ
  have hlow : (a - w) < (lo : ℝ) + 1 := by
    dsimp [lo]
    exact Int.lt_floor_add_one _
  have hhigh : (hi : ℝ) ≤ a + w := by
    dsimp [hi]
    exact Int.floor_le _
  have hcardBound : ((Finset.Icc lo hi).card : ℝ) < 2 * w + 2 := by
    rw [hcardR]
    linarith
  have hrewrite : Finset.Icc lo hi =
      Finset.Icc (Int.floor (a - w)) (Int.floor (a + w)) := by
    rfl
  rw [← hrewrite]
  linarith

private theorem eval_eq_coeff_zero_add_sum_Icc
    {d : ℕ} (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (x : ℝ) :
    P.eval x = P.coeff 0 +
      ∑ j ∈ Finset.Icc 1 d, P.coeff j * x ^ j := by
  have hrange : Finset.range (d + 1) = Finset.Icc 0 d := by
    ext j
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  have hsplit : Finset.Icc 0 d = insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP) x, hrange, hsplit,
    Finset.sum_insert]
  · simp
  · simp

private theorem realDistanceToIntegers_le_half (x : ℝ) :
    realDistanceToIntegers x ≤ 1 / 2 := by
  rw [realDistanceToIntegers_eq_abs_centered]
  exact abs_le.mpr ⟨(centeredFrequency_mem x).1,
    le_of_lt (centeredFrequency_mem x).2⟩

private theorem realDistanceToIntegers_le_abs_sub_int (x : ℝ) (z : ℤ) :
    realDistanceToIntegers x ≤ |x - (z : ℝ)| := by
  have hz : (z : ℝ) ∈ Set.range fun w : ℤ => (w : ℝ) := ⟨z, rfl⟩
  unfold realDistanceToIntegers
  calc
    Metric.infDist x (Set.range fun w : ℤ => (w : ℝ)) ≤ dist x (z : ℝ) :=
      Metric.infDist_le_dist_of_mem (x := x) hz
    _ = |x - (z : ℝ)| := by rw [Real.dist_eq]

set_option maxHeartbeats 800000 in
private theorem smallEpsilon_recurrence_coefficients
    {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hε : 0 ≤ ε)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n : ℕ => realDistanceToIntegers
          (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)).card : ℝ))
    (r : ℕ) (hrpos : 1 ≤ r)
    (hcoeff : ∀ j, 1 ≤ j → j ≤ d →
      (N : ℝ) ^ j * realDistanceToIntegers
        ((r : ℝ) * P.coeff j) ≤ recurrenceBudgetW d (δ⁻¹))
    (hrbound : (r : ℝ) ≤ 17 * δ⁻¹ * recurrenceBudgetW d (δ⁻¹))
    (hsmall : (r : ℝ) * ε < 1 / 4)
    (hNlarge : recurrenceBudgetT d (δ⁻¹) ≤ (N : ℝ)) :
    ∀ j, j ≤ d →
      (N : ℝ) ^ j * realDistanceToIntegers
        ((r : ℝ) * P.coeff j) ≤ recurrenceBudgetR d (δ⁻¹) * ε := by
  classical
  let x : ℝ := δ⁻¹
  let W : ℝ := recurrenceBudgetW d x
  let J : ℝ := recurrenceBudgetJ d x
  let L : ℝ := recurrenceBudgetL d x
  let R : ℝ := recurrenceBudgetR d x
  let η : ℝ := δ / J
  let G : Finset ℕ := (Finset.range N).filter
    (fun n : ℕ => realDistanceToIntegers
      (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hx2 : 2 ≤ x := by
    dsimp [x]
    rw [← one_div]
    exact (le_div_iff₀ hδ).2 (by nlinarith [hδhalf])
  have hW : 1 ≤ W := by
    exact recurrenceBudgetW_ge_one d hd x hx2
  have hJ : 1 ≤ J := by
    exact recurrenceBudgetJ_ge_one d hd x hx2
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hL : 1 ≤ L := recurrenceBudgetL_ge_one d x
  have hJformula : J = (2 * d + 3 : ℕ) * W := by
    dsimp [J, W, x]
    rw [recurrenceBudgetJ_eval, recurrenceBudgetW_eval]
  have hJcast : ((2 * d + 3 : ℕ) : ℝ) = 2 * (d : ℝ) + 3 := by
    push_cast
    ring
  have hJwide : 2 * (d : ℝ) * W + 3 ≤ J := by
    rw [hJformula, hJcast]
    nlinarith [hW]
  have hηpos : 0 < η := by dsimp [η]; exact div_pos hδ hJpos
  have hηle : η ≤ 1 := by
    dsimp [η]
    rw [div_le_iff₀ hJpos]
    linarith [hδhalf, hJ]
  have hηinv : η⁻¹ = J * x := by
    dsimp [η, x]
    field_simp [ne_of_gt hδ, ne_of_gt hJpos]

  have hdistCoeff (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d) :
      realDistanceToIntegers ((r : ℝ) * P.coeff j) ≤ W / (N : ℝ) ^ j := by
    apply (le_div_iff₀ (pow_pos hNreal j)).2
    simpa [W, x, mul_comm] using hcoeff j hj1 hjd
  let b : ℕ → ℤ := fun j =>
    if hj : 1 ≤ j ∧ j ≤ d then
      Classical.choose
        (exists_int_abs_sub_le_of_realDistanceToIntegers_le
          (hdistCoeff j hj.1 hj.2))
    else 0
  have hbSpec (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d) :
      |(r : ℝ) * P.coeff j - (b j : ℝ)| ≤ W / (N : ℝ) ^ j := by
    dsimp [b]
    rw [dif_pos ⟨hj1, hjd⟩]
    exact Classical.choose_spec
      (exists_int_abs_sub_le_of_realDistanceToIntegers_le
        (hdistCoeff j hj1 hjd))
  let θ : ℕ → ℝ := fun j => (r : ℝ) * P.coeff j - (b j : ℝ)
  let smoothPoly : Polynomial ℝ :=
    Polynomial.C ((r : ℝ) * P.coeff 0) +
      ∑ j ∈ Finset.Icc 1 d, Polynomial.C (θ j) * Polynomial.X ^ j
  let intPoly : Polynomial ℤ :=
    ∑ j ∈ Finset.Icc 1 d, Polynomial.C (b j) * Polynomial.X ^ j
  let intPolyReal : Polynomial ℝ := intPoly.map (Int.castRingHom ℝ)
  have hθ (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      |θ j| ≤ W / (N : ℝ) ^ j := by
    have hj' := Finset.mem_Icc.mp hj
    simpa [θ] using hbSpec j hj'.1 hj'.2
  have hSmoothEval (z : ℝ) :
      smoothPoly.eval z = (r : ℝ) * P.coeff 0 +
        ∑ j ∈ Finset.Icc 1 d, θ j * z ^ j := by
    simp [smoothPoly, eval_sum_C_mul_X_pow_Icc]
  have hIntMap : intPolyReal =
      ∑ j ∈ Finset.Icc 1 d,
        Polynomial.C ((b j : ℤ) : ℝ) * Polynomial.X ^ j := by
    dsimp [intPolyReal, intPoly]
    rw [Polynomial.map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  have hIntEval (z : ℝ) :
      intPolyReal.eval z =
        ∑ j ∈ Finset.Icc 1 d, ((b j : ℤ) : ℝ) * z ^ j := by
    rw [hIntMap]
    exact eval_sum_C_mul_X_pow_Icc d (fun j => ((b j : ℤ) : ℝ)) z
  have hsumIdentity (z : ℝ) :
      (r : ℝ) * (∑ j ∈ Finset.Icc 1 d, P.coeff j * z ^ j) -
        ∑ j ∈ Finset.Icc 1 d, θ j * z ^ j =
          ∑ j ∈ Finset.Icc 1 d, ((b j : ℤ) : ℝ) * z ^ j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [θ]
    ring
  have hDifference (n : ℕ) :
      (r : ℝ) * P.eval ((n : ℝ) + 1) -
        smoothPoly.eval ((n : ℝ) + 1) =
          intPolyReal.eval ((n : ℝ) + 1) := by
    rw [eval_eq_coeff_zero_add_sum_Icc P hP, hSmoothEval, hIntEval]
    calc
      (r : ℝ) *
          (P.coeff 0 + ∑ j ∈ Finset.Icc 1 d,
            P.coeff j * ((n : ℝ) + 1) ^ j) -
          ((r : ℝ) * P.coeff 0 +
            ∑ j ∈ Finset.Icc 1 d,
              θ j * ((n : ℝ) + 1) ^ j) =
        (r : ℝ) *
            (∑ j ∈ Finset.Icc 1 d, P.coeff j * ((n : ℝ) + 1) ^ j) -
          ∑ j ∈ Finset.Icc 1 d, θ j * ((n : ℝ) + 1) ^ j := by ring
      _ = ∑ j ∈ Finset.Icc 1 d,
          ((b j : ℤ) : ℝ) * ((n : ℝ) + 1) ^ j := hsumIdentity _
  have hGoodDistance (n : ℕ) (hn : n ∈ G) :
      realDistanceToIntegers (smoothPoly.eval ((n : ℝ) + 1)) ≤
        (r : ℝ) * ε := by
    have hsource := (Finset.mem_filter.mp hn).2
    have hsource' : realDistanceToIntegers (P.eval ((n : ℝ) + 1)) ≤ ε := by
      simpa only [Nat.cast_add, Nat.cast_one] using hsource
    have hscaled := realDistanceToIntegers_nat_mul_le r
      (P.eval ((n : ℝ) + 1)) ε hsource'
    have hdiff := hDifference n
    have hncast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by
      push_cast
      rfl
    have hdiff' : (r : ℝ) * P.eval ((n + 1 : ℕ) : ℝ) -
        smoothPoly.eval ((n + 1 : ℕ) : ℝ) =
          intPolyReal.eval ((n + 1 : ℕ) : ℝ) := by
      simpa only [hncast] using hdiff
    rw [polynomial_eval_map_int_cast] at hdiff'
    change (r : ℝ) * P.eval ((n + 1 : ℕ) : ℝ) -
        smoothPoly.eval ((n + 1 : ℕ) : ℝ) =
          ((intPoly.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) at hdiff'
    have hrel : smoothPoly.eval ((n : ℝ) + 1) =
        (r : ℝ) * P.eval ((n : ℝ) + 1) +
          (((-(intPoly.eval ((n + 1 : ℕ) : ℤ) : ℤ)) : ℤ) : ℝ) := by
      rw [hncast]
      have hcast :
          (((-(intPoly.eval ((n + 1 : ℕ) : ℤ) : ℤ)) : ℤ) : ℝ) =
            -((intPoly.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by simp
      rw [hcast]
      linarith [hdiff']
    rw [hrel]
    simpa only [Int.cast_neg] using
      (realDistanceToIntegers_add_int
        ((r : ℝ) * P.eval ((n : ℝ) + 1))
        (-(intPoly.eval ((n + 1 : ℕ) : ℤ))) |>.trans_le hscaled)
  have hterm (n j : ℕ) (hn : n < N) (hj : j ∈ Finset.Icc 1 d) :
      |θ j * ((n + 1 : ℕ) : ℝ) ^ j| ≤ W := by
    have hnle : n + 1 ≤ N := Nat.succ_le_of_lt hn
    have hz : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    have hupper : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnle
    have hpow : ((n + 1 : ℕ) : ℝ) ^ j ≤ (N : ℝ) ^ j := by
      gcongr
    have hNj : 0 < (N : ℝ) ^ j := pow_pos hNreal j
    calc
      |θ j * ((n + 1 : ℕ) : ℝ) ^ j| = |θ j| * ((n + 1 : ℕ) : ℝ) ^ j := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ j)]
      _ ≤ (W / (N : ℝ) ^ j) * (N : ℝ) ^ j :=
        mul_le_mul (hθ j hj) hpow (by positivity) (by positivity)
      _ = W := by field_simp [ne_of_gt hNj]
  have hSmoothClose (n : ℕ) (hn : n < N) :
      |smoothPoly.eval ((n + 1 : ℕ) : ℝ) -
        (r : ℝ) * P.coeff 0| ≤ (d : ℝ) * W := by
    rw [hSmoothEval]
    calc
      |(r : ℝ) * P.coeff 0 +
          ∑ j ∈ Finset.Icc 1 d,
            θ j * ((n + 1 : ℕ) : ℝ) ^ j -
          (r : ℝ) * P.coeff 0| =
        |∑ j ∈ Finset.Icc 1 d,
            θ j * ((n + 1 : ℕ) : ℝ) ^ j| := by
              congr 1
              ring
      _ ≤ ∑ j ∈ Finset.Icc 1 d,
          |θ j * ((n + 1 : ℕ) : ℝ) ^ j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 d, W := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm n j hn hj
      _ = (d : ℝ) * W := by simp [Nat.card_Icc]

  let radius : ℝ := (d : ℝ) * W + (r : ℝ) * ε
  let bfun : ℕ → ℤ := fun n =>
    if hn : n ∈ G then
      Classical.choose
        (exists_int_abs_sub_le_of_realDistanceToIntegers_le
          (hGoodDistance n hn))
    else 0
  have hbfunSpec (n : ℕ) (hn : n ∈ G) :
      |smoothPoly.eval ((n + 1 : ℕ) : ℝ) - (bfun n : ℝ)| ≤
        (r : ℝ) * ε := by
    dsimp [bfun]
    rw [dif_pos hn]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Classical.choose_spec
        (exists_int_abs_sub_le_of_realDistanceToIntegers_le
          (hGoodDistance n hn))
  have hbfunCenter (n : ℕ) (hn : n ∈ G) :
      |(bfun n : ℝ) - (r : ℝ) * P.coeff 0| ≤ radius := by
    have hclose :
        |(bfun n : ℝ) - smoothPoly.eval ((n + 1 : ℕ) : ℝ)| ≤
          (r : ℝ) * ε := by
      simpa [abs_sub_comm] using hbfunSpec n hn
    have hspan := hSmoothClose n (by
      have hmem := (Finset.mem_filter.mp hn).1
      exact Finset.mem_range.mp hmem)
    calc
      |(bfun n : ℝ) - (r : ℝ) * P.coeff 0| =
          |((bfun n : ℝ) - smoothPoly.eval ((n + 1 : ℕ) : ℝ)) +
            (smoothPoly.eval ((n + 1 : ℕ) : ℝ) - (r : ℝ) * P.coeff 0)| := by
              congr 1
              ring
      _ ≤ |(bfun n : ℝ) - smoothPoly.eval ((n + 1 : ℕ) : ℝ)| +
          |smoothPoly.eval ((n + 1 : ℕ) : ℝ) - (r : ℝ) * P.coeff 0| :=
            abs_add_le _ _
      _ ≤ (r : ℝ) * ε + (d : ℝ) * W := add_le_add hclose hspan
      _ = radius := by dsimp [radius]; ring

  let lo : ℤ := Int.floor ((r : ℝ) * P.coeff 0 - radius)
  let hi : ℤ := Int.floor ((r : ℝ) * P.coeff 0 + radius)
  let B : Finset ℤ := Finset.Icc lo hi
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hwidth : 2 * radius + 2 ≤ J := by
    have hJwide' : 2 * (d : ℝ) * W + 3 ≤ J := hJwide
    dsimp [radius]
    nlinarith [hsmall]
  have hBcard : (B.card : ℝ) ≤ J := by
    dsimp [B, lo, hi]
    exact floor_centered_integer_interval_card_le hradius hwidth
  have hbfunMem (n : ℕ) (hn : n ∈ G) : bfun n ∈ B := by
    have hspan := hbfunCenter n hn
    simp only [B, lo, hi, Finset.mem_Icc]
    constructor
    · apply (Int.floor_le_iff).2
      have h := (abs_le.mp hspan).1
      linarith
    · exact (Int.le_floor).2 (by linarith [abs_le.mp hspan])
  have hGcard : δ * (N : ℝ) ≤ (G.card : ℝ) := by
    simpa [G] using hgood
  have hGposR : 0 < (G.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hδ hNreal) hGcard
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  obtain ⟨n₀, hn₀⟩ := Finset.card_pos.mp hGpos
  have hBnonempty : B.Nonempty := ⟨bfun n₀, hbfunMem n₀ hn₀⟩
  have hJmean : (B.card : ℝ) * ((G.card : ℝ) / J) ≤ (G.card : ℝ) := by
    calc
      (B.card : ℝ) * ((G.card : ℝ) / J) ≤
          J * ((G.card : ℝ) / J) :=
        mul_le_mul_of_nonneg_right hBcard (by positivity)
      _ = (G.card : ℝ) := by field_simp [ne_of_gt hJpos]
  have hJmean' : B.card • ((G.card : ℝ) / J) ≤
      ∑ _n ∈ G, (1 : ℝ) := by
    simpa [Finset.sum_const] using hJmean
  obtain ⟨b₀, hb₀mem, hfiber⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := G) (t := B) (f := bfun) (w := fun _ : ℕ => (1 : ℝ))
      (b := (G.card : ℝ) / J) (fun n hn => hbfunMem n hn)
      hBnonempty hJmean'
  let U : Finset ℕ := G.filter (fun n => bfun n = b₀)
  have hUcard : (G.card : ℝ) / J ≤ (U.card : ℝ) := by
    simpa [U, Finset.sum_const] using hfiber
  let Sset : Finset ℕ := U.image (fun n => n + 1)
  have hSsetCard : Sset.card = U.card := by
    dsimp [Sset]
    rw [Finset.card_image_iff]
    intro a ha b' hb' hab
    exact Nat.add_right_cancel hab
  have hSsetSubset : Sset ⊆ Finset.Icc 1 N := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    have hnG : n ∈ G := (Finset.mem_filter.mp hn).1
    have hnrange := Finset.mem_range.mp (Finset.mem_filter.mp hnG).1
    simp only [Finset.mem_Icc]
    constructor
    · omega
    · exact Nat.succ_le_of_lt hnrange
  have hηN : η * (N : ℝ) ≤ (Sset.card : ℝ) := by
    have hdiv : ((δ * (N : ℝ)) / J) ≤ (U.card : ℝ) := by
      calc
        ((δ * (N : ℝ)) / J) ≤ (G.card : ℝ) / J :=
          (div_le_div_iff₀ hJpos hJpos).2
            (mul_le_mul_of_nonneg_right hGcard (le_of_lt hJpos))
        _ ≤ (U.card : ℝ) := hUcard
    have hrewrite : η * (N : ℝ) = (δ * (N : ℝ)) / J := by
      dsimp [η]
      ring
    rw [hSsetCard, hrewrite]
    exact hdiv
  let V : Polynomial ℝ := smoothPoly - Polynomial.C (b₀ : ℝ)
  have hsumDeg :
      (∑ j ∈ Finset.Icc 1 d, Polynomial.C (θ j) * Polynomial.X ^ j).natDegree ≤ d :=
    natDegree_sum_C_mul_X_pow_Icc d θ
  have hSmoothDeg : smoothPoly.natDegree ≤ d := by
    change (Polynomial.C ((r : ℝ) * P.coeff 0) +
      ∑ j ∈ Finset.Icc 1 d, Polynomial.C (θ j) * Polynomial.X ^ j).natDegree ≤ d
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by
        calc
          (Polynomial.C ((r : ℝ) * P.coeff 0)).natDegree = 0 :=
            Polynomial.natDegree_C _
          _ ≤ d := Nat.zero_le _) hsumDeg)
  have hVdeg : V.natDegree ≤ d := by
    dsimp [V]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hSmoothDeg (by simp))
  have hEvalV (m : ℕ) (hm : m ∈ Sset) :
      |V.eval (m : ℝ)| ≤ (r : ℝ) * ε := by
    rcases Finset.mem_image.mp hm with ⟨n, hnU, rfl⟩
    have hnG : n ∈ G := (Finset.mem_filter.mp hnU).1
    have hbn : bfun n = b₀ := (Finset.mem_filter.mp hnU).2
    have hclose := hbfunSpec n hnG
    rw [hbn] at hclose
    simpa [V] using hclose
  have hTform : recurrenceBudgetT d x =
      (4 * (d + 1) ^ 2 : ℕ) * J * x := by
    simpa [J] using recurrenceBudgetT_eval d hd x
  have hlengthEq :
      (4 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 / η = recurrenceBudgetT d x := by
    rw [hTform]
    dsimp [η]
    dsimp [x]
    field_simp [ne_of_gt hδ, ne_of_gt hJpos]
    norm_cast
  have hlen :
      (4 : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 / η ≤ (N : ℝ) :=
    hlengthEq.le.trans hNlarge
  have hLconst : L =
      ((d + 1 : ℕ) : ℝ) * (4 * ((d + 1 : ℕ) : ℝ)) ^ d := by
    dsimp [L]
    rw [recurrenceBudgetL_eval]
    simp [recurrenceBudgetLValue]
  have hinterp :=
    interpolateDenseSet hd hN hηpos hηle hlen Sset hSsetSubset hηN
      V hVdeg hEvalV (by positivity)
  have hInterpBound (j : ℕ) (hjd : j ≤ d) :
      (N : ℝ) ^ j * |V.coeff j| ≤ L * (J * x) ^ d * ((r : ℝ) * ε) := by
    calc
      (N : ℝ) ^ j * |V.coeff j| ≤
          ((d + 1 : ℕ) : ℝ) *
            (4 * ((d + 1 : ℕ) : ℝ)) ^ d * ((r : ℝ) * ε) / η ^ d :=
        hinterp j hjd
      _ = L * (J * x) ^ d * ((r : ℝ) * ε) := by
        rw [← hLconst, div_eq_mul_inv, ← inv_pow, hηinv]
        ring
  have hScoeff0 : smoothPoly.coeff 0 = (r : ℝ) * P.coeff 0 := by
    simp [smoothPoly]
  have hVcoeff0 : V.coeff 0 = (r : ℝ) * P.coeff 0 - (b₀ : ℝ) := by
    dsimp [V]
    rw [Polynomial.coeff_sub]
    simp [hScoeff0]
  have hVcoeff (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d) :
      V.coeff j = (r : ℝ) * P.coeff j - (b j : ℝ) := by
    dsimp [V]
    rw [Polynomial.coeff_sub]
    have hj0 : j ≠ 0 := by omega
    have hSj : smoothPoly.coeff j = θ j := by
      simp [smoothPoly, hj0, coeff_C_mul_X_pow_sum_Icc θ
        (Finset.mem_Icc.mpr ⟨hj1, hjd⟩)]
    rw [hSj]
    rw [Polynomial.coeff_C_of_ne_zero hj0]
    simp [θ, b, hj1, hjd]
  have hRmid : 17 * L * x * W * (J * x) ^ d ≤ R := by
    dsimp [R]
    rw [recurrenceBudgetR_eval d hd x]
    dsimp [L, W, J, R]
    have h₁ : 0 ≤ 68 * x * recurrenceBudgetW d x ^ 2 := by positivity
    have h₃ : 0 ≤ 17 * x * recurrenceBudgetW d x := by positivity
    linarith
  have hLR : L * (J * x) ^ d * (r : ℝ) ≤ R := by
    calc
      L * (J * x) ^ d * (r : ℝ) ≤
          L * (J * x) ^ d * (17 * x * W) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [x, W] using hrbound) (by positivity)
      _ = 17 * L * x * W * (J * x) ^ d := by ring
      _ ≤ R := hRmid
  intro j hjd
  have hjdist : realDistanceToIntegers ((r : ℝ) * P.coeff j) ≤
      |V.coeff j| := by
    by_cases hj0 : j = 0
    · subst j
      rw [hVcoeff0]
      exact realDistanceToIntegers_le_abs_sub_int
        ((r : ℝ) * P.coeff 0) b₀
    · have hj1 : 1 ≤ j := by omega
      rw [hVcoeff j hj1 hjd]
      exact realDistanceToIntegers_le_abs_sub_int
        ((r : ℝ) * P.coeff j) (b j)
  calc
    (N : ℝ) ^ j * realDistanceToIntegers ((r : ℝ) * P.coeff j) ≤
        (N : ℝ) ^ j * |V.coeff j| :=
          mul_le_mul_of_nonneg_left hjdist (by positivity)
    _ ≤ L * (J * x) ^ d * ((r : ℝ) * ε) := hInterpBound j hjd
    _ = (L * (J * x) ^ d * (r : ℝ)) * ε := by ring
    _ ≤ R * ε := mul_le_mul_of_nonneg_right hLR hε

private theorem positiveDegree_scalar_coefficient_bounds
    {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ / 64)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n : ℕ => realDistanceToIntegers
          (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)).card : ℝ)) :
    ∃ r : ℕ, 1 ≤ r ∧
      (r : ℝ) ≤ 17 * δ⁻¹ * recurrenceBudgetW d (δ⁻¹) ∧
      ∀ j, 1 ≤ j → j ≤ d →
        (N : ℝ) ^ j * realDistanceToIntegers
          ((r : ℝ) * P.coeff j) ≤ recurrenceBudgetW d (δ⁻¹) := by
  classical
  let y : ℕ → ℝ := fun n => P.eval (n : ℝ)
  obtain ⟨k, hkpos, hklt, hcor⟩ :=
    fejerDetectsRecurrence hN hδ hδhalf hε hεδ y (by simpa [y] using hgood)
  have hdelta2 : 2 * δ < 1 := by nlinarith [hδhalf]
  have hx2 : 2 ≤ δ⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).2 hdelta2.le
  have hceil : (Nat.ceil (16 / δ) : ℝ) < 16 / δ + 1 := by
    exact Nat.ceil_lt_add_one (le_of_lt (by positivity))
  have hkReal : (k : ℝ) < 17 * δ⁻¹ := by
    calc
      (k : ℝ) < (Nat.ceil (16 / δ) : ℝ) := by exact_mod_cast hklt
      _ < 16 / δ + 1 := hceil
      _ ≤ 17 * δ⁻¹ := by
        have hinv : 16 / δ = 16 * δ⁻¹ := by
          field_simp [ne_of_gt hδ]
        rw [hinv]
        nlinarith [hx2]
  have hsumEq :
      (∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
        unitFrequencyPhase ((k : ℝ) * P.eval (n : ℝ))) =
        ∑ n ∈ Finset.range N,
          unitFrequencyPhase ((k : ℝ) * P.eval ((n + 1 : ℕ) : ℝ)) := by
    rw [sumIcoOne_eq_sumRange]
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    push_cast
    ring
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hcor' : δ / 10 ≤
      ‖(∑ n ∈ Finset.range N,
        unitFrequencyPhase ((k : ℝ) * y (n + 1))) / (N : ℂ)‖ := by
    simpa [y] using hcor
  have hlargeRange : δ / 10 * (N : ℝ) ≤
      ‖∑ n ∈ Finset.range N,
        unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ := by
    have hnorm := hcor'
    rw [norm_div, Complex.norm_natCast] at hnorm
    exact (le_div_iff₀ hNreal).mp hnorm
  have hlargeIco : δ / 10 * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
        unitFrequencyPhase ((k : ℝ) * P.eval (n : ℝ))‖ := by
    rw [hsumEq]
    simpa [y] using hlargeRange
  have hJsubset : Finset.Ico (1 : ℤ) ((N : ℤ) + 1) ⊆
      Finset.Icc (1 : ℤ) (N : ℤ) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have hkPdeg : (Polynomial.C (k : ℝ) * P).natDegree ≤ d :=
    (Polynomial.natDegree_C_mul_le _ _).trans hP
  have hδ' : 0 < δ / 10 := by positivity
  have hδ'half : δ / 10 < 1 / 2 := by nlinarith [hδhalf]
  have hinv : (δ / 10)⁻¹ = 10 * δ⁻¹ := by
    field_simp [ne_of_gt hδ]
  have hlargeScalar : δ / 10 * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico (1 : ℤ) ((N : ℤ) + 1),
        unitFrequencyPhase ((Polynomial.C (k : ℝ) * P).eval (n : ℝ))‖ := by
    simpa [Polynomial.eval_mul, Polynomial.eval_C] using hlargeIco
  obtain ⟨q, hqpos, hqbound, hqcoeff⟩ :=
    scalarWeylInverse d N hd hN (δ := δ / 10) hδ' hδ'half
      (Polynomial.C (k : ℝ) * P) hkPdeg 1 ((N : ℤ) + 1)
      hJsubset hlargeScalar
  have hqW : (q : ℝ) ≤ recurrenceBudgetW d (δ⁻¹) := by
    rw [recurrenceBudgetW_eval]
    rw [hinv] at hqbound
    exact hqbound
  let r : ℕ := k * q
  refine ⟨r, ?_, ?_, ?_⟩
  · dsimp [r]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · have hkNonneg : 0 ≤ (k : ℝ) := by positivity
    have hqNonneg : 0 ≤ (q : ℝ) := by positivity
    calc
      (r : ℝ) = (q : ℝ) * (k : ℝ) := by simp [r, mul_comm]
      _ ≤ recurrenceBudgetW d (δ⁻¹) * (17 * δ⁻¹) :=
        mul_le_mul hqW hkReal.le hkNonneg (by linarith [hqW, hqpos])
      _ = 17 * δ⁻¹ * recurrenceBudgetW d (δ⁻¹) := by ring
  · intro j hj1 hjd
    have hj := hqcoeff j hj1 hjd
    rw [hinv] at hj
    have harg : (q : ℝ) * (Polynomial.C (k : ℝ) * P).coeff j =
        (r : ℝ) * P.coeff j := by
      simp [r]
      ring
    rw [harg] at hj
    rw [recurrenceBudgetW_eval]
    exact hj

/-- Polynomial recurrence from a dense set of small values modulo one.
The bound includes the constant coefficient. -/
theorem polynomialRecurrence
    {d N : ℕ} (hN : 1 ≤ N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ / 64)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n : ℕ => realDistanceToIntegers
          (P.eval ((n + 1 : ℕ) : ℝ)) ≤ ε)).card : ℝ))
    (hNlarge : recurrenceBudgetT d (δ⁻¹) ≤ (N : ℝ)) :
    ∃ r : ℕ, 1 ≤ r ∧
      (r : ℝ) ≤ recurrenceBudgetR d (δ⁻¹) ∧
      ∀ j, j ≤ d →
        (N : ℝ) ^ j * realDistanceToIntegers
          ((r : ℝ) * P.coeff j) ≤ recurrenceBudgetR d (δ⁻¹) * ε := by
  classical
  by_cases hd0 : d = 0
  · subst d
    have hconstant := constantCoefficient_of_good_values hN hδ P hP hgood
    refine ⟨1, by norm_num, ?_, ?_⟩
    · simp
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa using hconstant
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    let x : ℝ := δ⁻¹
    let W : ℝ := recurrenceBudgetW d x
    let J : ℝ := recurrenceBudgetJ d x
    let L : ℝ := recurrenceBudgetL d x
    let R : ℝ := recurrenceBudgetR d x
    have hx2 : 2 ≤ x := by
      dsimp [x]
      rw [← one_div]
      exact (le_div_iff₀ hδ).2 (by nlinarith [hδhalf])
    have hW : 1 ≤ W := by
      exact recurrenceBudgetW_ge_one d hd x hx2
    have hJ : 1 ≤ J := by
      exact recurrenceBudgetJ_ge_one d hd x hx2
    have hL : 1 ≤ L := by
      exact recurrenceBudgetL_ge_one d x
    obtain ⟨r, hrpos, hrbound, hcoeff⟩ :=
      positiveDegree_scalar_coefficient_bounds hd hN hδ hδhalf
        hε hεδ P hP hgood
    have hrbound' : (r : ℝ) ≤ 17 * x * W := by
      simpa [x, W] using hrbound
    have hRform :
        R = 68 * x * W ^ 2 +
          17 * L * x * W * (J * x) ^ d + 17 * x * W := by
      dsimp [R]
      rw [recurrenceBudgetR_eval d hd x]
    have hRthird : 17 * x * W ≤ R := by
      rw [hRform]
      have h₁ : 0 ≤ 68 * x * W ^ 2 := by positivity
      have h₂ : 0 ≤ 17 * L * x * W * (J * x) ^ d := by positivity
      linarith
    have hRfour : 4 * (r : ℝ) * W ≤ R := by
      have hWnonneg : 0 ≤ W := by linarith [hW]
      have hrW : (r : ℝ) * W ≤ 17 * x * W ^ 2 := by
        calc
          (r : ℝ) * W ≤ (17 * x * W) * W :=
            mul_le_mul_of_nonneg_right hrbound' hWnonneg
          _ = 17 * x * W ^ 2 := by ring
      calc
        4 * (r : ℝ) * W = 4 * ((r : ℝ) * W) := by ring
        _ ≤ 4 * (17 * x * W ^ 2) := by gcongr
        _ = 68 * x * W ^ 2 := by ring
        _ ≤ R := by
          rw [hRform]
          have h₂ : 0 ≤ 17 * L * x * W * (J * x) ^ d := by positivity
          have h₃ : 0 ≤ 17 * x * W := by positivity
          linarith
    have hRtwo : 2 * (r : ℝ) ≤ R := by
      have hrnonneg : 0 ≤ (r : ℝ) := by positivity
      calc
        2 * (r : ℝ) ≤ 2 * (r : ℝ) * W := by nlinarith [hW]
        _ ≤ 4 * (r : ℝ) * W := by nlinarith [hrnonneg, hW]
        _ ≤ R := hRfour
    by_cases hbig : (1 / 4 : ℝ) ≤ (r : ℝ) * ε
    · have hWsmall : W ≤ 4 * (r : ℝ) * W * ε := by
        calc
          W = (1 / 4 : ℝ) * (4 * W) := by ring
          _ ≤ ((r : ℝ) * ε) * (4 * W) :=
            mul_le_mul_of_nonneg_right hbig (by positivity)
          _ = 4 * (r : ℝ) * W * ε := by ring
      have hRfourε :
          4 * (r : ℝ) * W * ε ≤ R * ε :=
        mul_le_mul_of_nonneg_right hRfour hε
      have hRtwoε :
          2 * (r : ℝ) * ε ≤ R * ε :=
        mul_le_mul_of_nonneg_right hRtwo hε
      refine ⟨r, hrpos, ?_, ?_⟩
      · exact le_trans hrbound' hRthird
      · intro j hjd
        by_cases hj0 : j = 0
        · subst j
          calc
            (N : ℝ) ^ 0 * realDistanceToIntegers
                ((r : ℝ) * P.coeff 0) =
              realDistanceToIntegers ((r : ℝ) * P.coeff 0) := by simp
            _ ≤ 1 / 2 := realDistanceToIntegers_le_half _
            _ ≤ 2 * (r : ℝ) * ε := by nlinarith [hbig]
            _ ≤ R * ε := hRtwoε
        · have hj1 : 1 ≤ j := by omega
          calc
            (N : ℝ) ^ j * realDistanceToIntegers
                ((r : ℝ) * P.coeff j) ≤ W := hcoeff j hj1 hjd
            _ ≤ 4 * (r : ℝ) * W * ε := hWsmall
            _ ≤ R * ε := hRfourε
    · have hsmall : (r : ℝ) * ε < 1 / 4 := by linarith
      have hlow := smallEpsilon_recurrence_coefficients
        hd hN hδ hδhalf hε P hP hgood r hrpos hcoeff hrbound' hsmall
        (by simpa [x] using hNlarge)
      refine ⟨r, hrpos, ?_, ?_⟩
      · exact le_trans hrbound' hRthird
      · intro j hjd
        simpa [x, R] using hlow j hjd

end FractionalPrimes.Literature.Polynomial
