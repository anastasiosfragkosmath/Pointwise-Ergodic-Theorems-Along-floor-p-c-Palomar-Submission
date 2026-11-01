module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Tactic.Linarith

/-!
The finite exponent inequality used in the scalar Dirichlet-product mean
argument. This is the first standalone algebraic prerequisite on the
`lup:shortIntervalDirichletTask` route; it does not assert the analytic
mean-value bound for the arithmetic coefficient families.

Blueprint: `expanded-blueprint.tex:5761-5788` (`ldm:exponent-inequality`).
Astra: `sections/dirichlet-mean-closure.tex:89-116`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletMean

/-- The three possible alternatives for one factor in the finite exponent
case analysis used by the scalar short-interval Dirichlet mean argument. -/
def factorAlternative (eps r v w : ℝ) : Prop :=
  r ≤ v - 2 * w ∨
    (r ≤ 3 / 8 - eps - 2 * w ∧
      r ≤ 3 / 8 - eps + v - 6 * w ∧ r ≤ 2 * v - 4 * w) ∨
    (r ≤ 3 / 8 - eps - 4 * w ∧
      r ≤ 3 / 8 - eps + 2 * v - 12 * w)

set_option maxHeartbeats 2000000 in
/-- Exact finite exponent inequality `ldm:exponent-inequality`. All 27
alternative assignments are discharged, and both orientations of the
balance condition on `b,c` are retained. -/
theorem trilinearExponentInequality
    (eps h a b c x y z r : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 3 / 16)
    (hh0 : 0 ≤ h) (hh1 : h ≤ eps)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hr0 : 0 ≤ r)
    (hsum : a + b + c = 1)
    (ha1 : 1 / 4 - eps / 100 ≤ a)
    (ha2 : a ≤ 1 / 2 + eps / 100)
    (hbalance : |b - c| ≤ 1 / 4 + eps / 100)
    (hx1 : x ≤ a / 2 - h) (hy1 : y ≤ b / 2) (hz1 : z ≤ c / 2)
    (hA : factorAlternative eps r a x)
    (hB : factorAlternative eps r b y)
    (hC : factorAlternative eps r c z) :
    r + x + y + z ≤ 1 / 2 - h / 16 := by
  obtain ⟨hbalanceLower, hbalanceUpper⟩ := abs_le.mp hbalance
  unfold factorAlternative at hA hB hC
  rcases hA with hA | ⟨hAa, hAb, hAc⟩ | ⟨hAa, hAb⟩ <;>
    rcases hB with hB | ⟨hBa, hBb, hBc⟩ | ⟨hBa, hBb⟩ <;>
    rcases hC with hC | ⟨hCa, hCb, hCc⟩ | ⟨hCa, hCb⟩ <;>
    linarith

end FractionalPrimes.Literature.DirichletMean

#print axioms FractionalPrimes.Literature.DirichletMean.trilinearExponentInequality

namespace FractionalPrimes.Literature.LargeValues

open scoped BigOperators
open scoped ComplexConjugate
open MeasureTheory

/-- The integers indexing a Dirichlet polynomial on `(N,2N]`. -/
noncomputable def dirichletIndices (N : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (2 * N) + 1)).filter fun n => N < (n : ℝ)

/-- The finite Dirichlet polynomial with angular frequency `log n`. -/
noncomputable def dirichletTerm (a : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  a n * Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))

@[fun_prop] theorem dirichletTerm_continuous (a : ℕ → ℂ) (n : ℕ) :
    Continuous (fun t : ℝ => dirichletTerm a n t) := by
  unfold dirichletTerm
  fun_prop

noncomputable def dirichletPolynomial (N : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dirichletIndices N, dirichletTerm a n t

/-- The coefficient energy on the same half-open integer interval. -/
noncomputable def dirichletEnergy (N : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ dirichletIndices N, ‖a n‖ ^ 2

private lemma re_mul_conj_comm (z w : ℂ) :
    (z * conj w).re = (w * conj z).re := by
  calc
    (z * conj w).re = (conj (z * conj w)).re := by simp
    _ = (w * conj z).re := by simp [mul_comm]

private lemma re_conj_mul_comm (z w : ℂ) :
    (conj z * w).re = (conj w * z).re := by
  calc
    (conj z * w).re = (w * conj z).re := by congr 1 <;> ring
    _ = (z * conj w).re := re_mul_conj_comm w z
    _ = (conj w * z).re := by congr 1 <;> ring

private lemma normSq_finset_sum (ι : Type*) [DecidableEq ι] (s : Finset ι)
    (f : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i) =
      ∑ i ∈ s, ∑ j ∈ s, (conj (f i) * f j).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Complex.normSq_add, ih]
      rw [Finset.sum_add_distrib]
      have hcross :
          (f i * conj (∑ j ∈ s, f j)).re =
            ∑ j ∈ s, (conj (f j) * f i).re := by
        calc
          (f i * conj (∑ j ∈ s, f j)).re =
              (∑ j ∈ s, f i * conj (f j)).re := by
            simp only [map_sum, Finset.mul_sum]
          _ = ∑ j ∈ s, (f i * conj (f j)).re := by rw [Complex.re_sum]
          _ = ∑ j ∈ s, (conj (f j) * f i).re := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1 <;> ring
      have hdiag : Complex.normSq (f i) = (conj (f i) * f i).re := by
        simpa using congrArg Complex.re
          (Complex.normSq_eq_conj_mul_self (z := f i))
      have hsum :
          (∑ j ∈ s, (conj (f i) * f j).re) =
            ∑ j ∈ s, (conj (f j) * f i).re := by
        apply Finset.sum_congr rfl
        intro j hj
        exact re_conj_mul_comm (f i) (f j)
      rw [hcross, hdiag, hsum]
      ring

private lemma dirichletIndex_mem_iff {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    n ∈ dirichletIndices N ↔ N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  classical
  rw [dirichletIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, hNn⟩
    have hfloor : (n : ℝ) ≤ Nat.floor (2 * N) := by exact_mod_cast (Nat.le_of_lt_succ hn)
    exact ⟨hNn, le_trans hfloor (Nat.floor_le (by positivity))⟩
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, hleft⟩
    have hfloor : n ≤ Nat.floor (2 * N) := Nat.le_floor hright
    omega

private lemma interval_exp_im_norm_le (ω a U : ℝ) (hω : ω ≠ 0) :
    ‖∫ t in a..a + U, Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))‖ ≤
      2 / |ω| := by
  have hc : Complex.I * (ω : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by
    exact_mod_cast hω)
  rw [integral_exp_mul_complex hc, norm_div]
  have hnorm : ‖Complex.I * (ω : ℂ)‖ = |ω| := by simp
  rw [hnorm]
  have hnum :
      ‖Complex.exp (Complex.I * (ω : ℂ) * (a + U : ℝ)) -
        Complex.exp (Complex.I * (ω : ℂ) * (a : ℝ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (Complex.I * (ω : ℂ) * (a + U : ℝ))‖ +
          ‖Complex.exp (Complex.I * (ω : ℂ) * (a : ℝ))‖ := norm_sub_le _ _
      _ = 2 := by norm_num [Complex.norm_exp, Complex.mul_re]
  exact div_le_div_of_nonneg_right hnum (abs_nonneg ω)

private lemma dirichletTerm_cross (a : ℕ → ℂ) (m n : ℕ) (t : ℝ) :
    conj (dirichletTerm a m t) * dirichletTerm a n t =
      (conj (a m) * a n) *
        Complex.exp (Complex.I * ((Real.log (m : ℝ) - Real.log (n : ℝ)) : ℂ) * (t : ℂ)) := by
  unfold dirichletTerm
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  calc
    _ = (conj (a m) * a n) *
          (Complex.exp (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by ring
    _ = (conj (a m) * a n) *
          Complex.exp (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ) +
            -Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
    _ = (conj (a m) * a n) *
          Complex.exp (Complex.I * ((Real.log (m : ℝ) - Real.log (n : ℝ)) : ℂ) * (t : ℂ)) := by
      congr 2 <;> ring

private lemma log_gap_of_lt (N : ℝ) (hN : 0 < N) {m n : ℕ}
    (hm : N < (m : ℝ)) (hn : (n : ℝ) ≤ 2 * N) (hmn : m < n) :
    |Real.log (m : ℝ) - Real.log (n : ℝ)| ≥
      |(m : ℝ) - (n : ℝ)| / (2 * N) := by
  have hmpos : 0 < (m : ℝ) := by linarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmn)
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos hnpos)
  rw [Real.log_div hmpos.ne' hnpos.ne'] at hlog
  have hloglower : ((n : ℝ) - (m : ℝ)) / (n : ℝ) ≤
      Real.log (n : ℝ) - Real.log (m : ℝ) := by
    have hratio : (m : ℝ) / (n : ℝ) - 1 =
        -(((n : ℝ) - (m : ℝ)) / (n : ℝ)) := by field_simp <;> ring
    linarith
  have hfrac : ((n : ℝ) - (m : ℝ)) / (2 * N) ≤
      ((n : ℝ) - (m : ℝ)) / (n : ℝ) := by
    gcongr
  have hlogabs : |Real.log (m : ℝ) - Real.log (n : ℝ)| =
      Real.log (n : ℝ) - Real.log (m : ℝ) := by
    rw [abs_of_nonpos]
    · ring_nf
    · exact sub_nonpos.mpr (Real.log_le_log hmpos hmnR.le)
  have hnatabs : |(m : ℝ) - (n : ℝ)| = (n : ℝ) - (m : ℝ) := by
    calc
      |(m : ℝ) - (n : ℝ)| = -((m : ℝ) - (n : ℝ)) :=
        abs_of_nonpos (sub_nonpos.mpr hmnR.le)
      _ = (n : ℝ) - (m : ℝ) := by ring
  rw [hlogabs, hnatabs]
  linarith

private lemma log_gap_lower (N : ℝ) (hN : 0 < N) {m n : ℕ}
    (hm : N < (m : ℝ)) (hn : N < (n : ℝ))
    (hm2 : (m : ℝ) ≤ 2 * N) (hn2 : (n : ℝ) ≤ 2 * N) (hmn : m ≠ n) :
    |Real.log (m : ℝ) - Real.log (n : ℝ)| ≥
      |(m : ℝ) - (n : ℝ)| / (2 * N) := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · exact log_gap_of_lt N hN hm hn2 hmn
  · have h := log_gap_of_lt N hN hn hm2 hnm
    have hlog : |Real.log (m : ℝ) - Real.log (n : ℝ)| =
        |Real.log (n : ℝ) - Real.log (m : ℝ)| := by
      calc
        |Real.log (m : ℝ) - Real.log (n : ℝ)| =
            |-(Real.log (n : ℝ) - Real.log (m : ℝ))| := by congr 1 <;> ring
        _ = _ := abs_neg _
    have hnat : |(m : ℝ) - (n : ℝ)| = |(n : ℝ) - (m : ℝ)| := by
      calc
        |(m : ℝ) - (n : ℝ)| = |(-((n : ℝ) - (m : ℝ)))| := by congr 1 <;> ring
        _ = _ := abs_neg _
    rw [hlog, hnat]
    exact h

private lemma reciprocal_le_log_ratio (k : ℕ) (hk : 0 < k) :
    (1 : ℝ) / ((k : ℝ) + 1) ≤ Real.log (((k : ℝ) + 1) / k) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hkR hk1)
  rw [Real.log_div hkR.ne' hk1.ne'] at h
  have hratio : ((k : ℝ) / ((k : ℝ) + 1)) - 1 =
      -(1 / ((k : ℝ) + 1)) := by field_simp <;> ring
  rw [Real.log_div hk1.ne' hkR.ne']
  linarith

private lemma harmonic_sum_le_log (M : ℕ) :
    (∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + 1)) ≤ 1 + Real.log (M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      by_cases hM : M = 0
      · simp [hM]
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        have hstep := reciprocal_le_log_ratio M hMpos
        have hlogratio : Real.log (((M : ℝ) + 1) / M) =
            Real.log ((M : ℝ) + 1) - Real.log (M : ℝ) := by
          rw [Real.log_div (by positivity) (by exact_mod_cast hMpos.ne')]
        calc
          (∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + 1)) +
              (1 : ℝ) / ((M : ℝ) + 1)
              ≤ (1 + Real.log (M : ℝ)) +
                  (Real.log (((M : ℝ) + 1) / M)) := add_le_add ih hstep
          _ = 1 + Real.log ((M : ℝ) + 1) := by rw [hlogratio]; ring
          _ = 1 + Real.log ((M + 1 : ℕ) : ℝ) := by simp [Nat.cast_succ]

private lemma abs_nat_sub_eq_nat_dist (m n : ℕ) :
    |(m : ℝ) - (n : ℝ)| = (Nat.dist m n : ℝ) := by
  by_cases hmn : m ≤ n
  · have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    rw [Nat.dist_eq_sub_of_le hmn, Nat.cast_sub hmn,
      abs_of_nonpos (sub_nonpos.mpr hmnR)]
    ring
  · have hnm : n ≤ m := le_of_not_ge hmn
    have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    rw [Nat.dist_eq_sub_of_le_right hnm, Nat.cast_sub hnm,
      abs_of_nonneg (sub_nonneg.mpr hnmR)]

private def dirichletDistanceCode (n m : ℕ) : Fin 2 × ℕ :=
  (if m < n then 0 else 1, Nat.dist m n - 1)

private lemma dirichlet_row_harmonic_bound {N : ℝ} (hN : 2 ≤ N) {n : ℕ}
    (hn : n ∈ dirichletIndices N) :
    (∑ m ∈ (dirichletIndices N).filter (fun m => m ≠ n),
      (1 : ℝ) / (Nat.dist m n : ℝ)) ≤
        2 * (1 + Real.log (2 * N)) := by
  classical
  let S := (dirichletIndices N).filter (fun m => m ≠ n)
  let M := Nat.floor N
  have hNpos : 0 < N := by linarith
  have hnBounds : N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N :=
    (dirichletIndex_mem_iff (by linarith) n).mp hn
  have hmemBounds (m : ℕ) (hm : m ∈ S) :
      N < (m : ℝ) ∧ (m : ℝ) ≤ 2 * N := by
    have hm' : m ∈ dirichletIndices N := (Finset.mem_filter.mp hm).1
    exact (dirichletIndex_mem_iff (by linarith) m).mp hm'
  have hdistpos (m : ℕ) (hm : m ∈ S) : 0 < Nat.dist m n :=
    Nat.dist_pos_of_ne (Finset.mem_filter.mp hm).2
  have hdist_le (m : ℕ) (hm : m ∈ S) : (Nat.dist m n : ℝ) ≤ N := by
    have hmb := hmemBounds m hm
    rcases le_total m n with hmn | hnm
    · rw [Nat.dist_eq_sub_of_le hmn, Nat.cast_sub hmn]
      linarith [hnBounds.1, hmb.2]
    · rw [Nat.dist_eq_sub_of_le_right hnm, Nat.cast_sub hnm]
      linarith [hmb.1, hnBounds.2]
  have hdist_floor (m : ℕ) (hm : m ∈ S) : Nat.dist m n ≤ M := by
    dsimp [M]
    exact Nat.le_floor (hdist_le m hm)
  have hcode_mem (m : ℕ) (hm : m ∈ S) :
      dirichletDistanceCode n m ∈ (Finset.univ : Finset (Fin 2)).product (Finset.range M) := by
    have hdpos := hdistpos m hm
    have hdle := hdist_floor m hm
    apply Finset.mem_product.mpr
    constructor
    · simp
    · simp only [Finset.mem_range]
      unfold dirichletDistanceCode
      omega
  have hcode_inj : Set.InjOn (dirichletDistanceCode n) S := by
    intro m hm m' hm' hcode
    have hmn : m ≠ n := (Finset.mem_filter.mp hm).2
    have hm'n : m' ≠ n := (Finset.mem_filter.mp hm').2
    have hdist : Nat.dist m n - 1 = Nat.dist m' n - 1 := congrArg Prod.snd hcode
    have hleft : 0 < Nat.dist m n := Nat.dist_pos_of_ne hmn
    have hright : 0 < Nat.dist m' n := Nat.dist_pos_of_ne hm'n
    rcases lt_or_gt_of_ne hmn with hmlt | hngt
    · rcases lt_or_gt_of_ne hm'n with hm'lt | hn'gt
      · have hdistEq : Nat.dist m n = Nat.dist m' n := by omega
        rw [Nat.dist_eq_sub_of_le hmlt.le, Nat.dist_eq_sub_of_le hm'lt.le] at hdistEq
        omega
      · have hfst := congrArg Prod.fst hcode
        have hnge : ¬ m' < n := not_lt_of_ge hn'gt.le
        simp [dirichletDistanceCode, hmlt, hnge] at hfst
    · rcases lt_or_gt_of_ne hm'n with hm'lt | hn'gt
      · have hfst := congrArg Prod.fst hcode
        have hnge : ¬ m < n := not_lt_of_ge hngt.le
        simp [dirichletDistanceCode, hnge, hm'lt] at hfst
      · have hdistEq : Nat.dist m n = Nat.dist m' n := by omega
        rw [Nat.dist_eq_sub_of_le_right hngt.le,
          Nat.dist_eq_sub_of_le_right hn'gt.le] at hdistEq
        omega
  have hsumImage :
      (∑ m ∈ S, (1 : ℝ) / (Nat.dist m n : ℝ)) =
        ∑ q ∈ S.image (dirichletDistanceCode n),
          (1 : ℝ) / ((q.2 + 1 : ℕ) : ℝ) := by
    symm
    rw [Finset.sum_image hcode_inj]
    apply Finset.sum_congr rfl
    intro m hm
    have hdpos := hdistpos m hm
    have hcancel : Nat.dist m n - 1 + 1 = Nat.dist m n :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdpos))
    simp [dirichletDistanceCode, hcancel]
  have hsubset : S.image (dirichletDistanceCode n) ⊆
      (Finset.univ : Finset (Fin 2)).product (Finset.range M) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨m, hm, rfl⟩
    exact hcode_mem m hm
  have hlogM : Real.log (M : ℝ) ≤ Real.log (2 * N) := by
    apply Real.log_le_log (by
      have hMone : 1 ≤ M := by
        dsimp [M]
        have h1 : ((1 : ℕ) : ℝ) ≤ N := by norm_num; linarith
        exact Nat.le_floor h1
      exact_mod_cast (show 0 < M from lt_of_lt_of_le Nat.zero_lt_one hMone))
    have hMle : (M : ℝ) ≤ N := by
      dsimp [M]
      exact Nat.floor_le (by linarith)
    linarith
  calc
    (∑ m ∈ S, (1 : ℝ) / (Nat.dist m n : ℝ)) =
        ∑ q ∈ S.image (dirichletDistanceCode n),
          (1 : ℝ) / ((q.2 + 1 : ℕ) : ℝ) := hsumImage
    _ ≤ ∑ q ∈ (Finset.univ : Finset (Fin 2)).product (Finset.range M),
          (1 : ℝ) / ((q.2 + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
    _ = 2 * (∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + 1)) := by
      simp [Finset.sum_product]
    _ ≤ 2 * (1 + Real.log (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_sum_le_log M) (by norm_num)
    _ ≤ 2 * (1 + Real.log (2 * N)) := by nlinarith [hlogM]

private lemma intervalIntegral_re_eq {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, (f t).re) = (∫ t in a..b, f t).re := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simpa [Set.uIoc_of_le hab] using integral_re hf.def'

private lemma conj_mul_re_eq_normSq (z : ℂ) :
    (conj z * z).re = Complex.normSq z := by
  simpa using (congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))).symm

private lemma dirichletTerm_cross_diag (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    (conj (dirichletTerm a n t) * dirichletTerm a n t).re = ‖a n‖ ^ 2 := by
  rw [conj_mul_re_eq_normSq]
  have hz : (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)).re = 0 := by
    change ((-Complex.I * (t : ℂ)) * (Real.log (n : ℝ) : ℂ)).re = 0
    rw [Complex.mul_re]
    have hre : (-Complex.I * (t : ℂ)).re = 0 := by simp [Complex.mul_re]
    have him : (-Complex.I * (t : ℂ)).im = -t := by simp [Complex.mul_im]
    rw [hre, him, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold dirichletTerm
  rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp, hz]
  simp

private lemma dirichlet_meanSquare_eq_pair_sum (N u U : ℝ) (a : ℕ → ℂ) :
    (∫ t in u..u + U, Complex.normSq (dirichletPolynomial N a t)) =
      ∑ n ∈ dirichletIndices N, ∑ m ∈ dirichletIndices N,
        ∫ t in u..u + U,
          (conj (dirichletTerm a n t) * dirichletTerm a m t).re := by
  classical
  unfold dirichletPolynomial
  have hnorm (t : ℝ) :=
    normSq_finset_sum ℕ (dirichletIndices N) (fun n => dirichletTerm a n t)
  simp_rw [hnorm]
  calc
    (∫ t in u..u + U,
        ∑ n ∈ dirichletIndices N,
          ∑ m ∈ dirichletIndices N,
            (conj (dirichletTerm a n t) * dirichletTerm a m t).re) =
        ∑ n ∈ dirichletIndices N,
          ∫ t in u..u + U,
            ∑ m ∈ dirichletIndices N,
              (conj (dirichletTerm a n t) * dirichletTerm a m t).re := by
      rw [intervalIntegral.integral_finsetSum (fun n hn =>
        Continuous.intervalIntegrable (by fun_prop) _ _)]
    _ = ∑ n ∈ dirichletIndices N, ∑ m ∈ dirichletIndices N,
          ∫ t in u..u + U,
            (conj (dirichletTerm a n t) * dirichletTerm a m t).re := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_finsetSum (fun m hm =>
        Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- The first-derivative contribution of one off-diagonal pair on an
arbitrary interval. This isolates the analytic estimate used by the
mean-square argument. -/
private lemma dirichlet_cross_integral_bound (N u U : ℝ) (a : ℕ → ℂ)
    (hN : 2 ≤ N) (hU : 0 ≤ U) {n m : ℕ}
    (hn : n ∈ dirichletIndices N) (hm : m ∈ dirichletIndices N)
    (hnm : n ≠ m) :
    |∫ t in u..u + U,
      (conj (dirichletTerm a n t) * dirichletTerm a m t).re|
      ≤ 4 * N * ‖a n‖ * ‖a m‖ / (Nat.dist n m : ℝ) := by
  have hNpos : 0 < N := by linarith
  have hnBounds := (dirichletIndex_mem_iff (by linarith) n).mp hn
  have hmBounds := (dirichletIndex_mem_iff (by linarith) m).mp hm
  let ω := Real.log (n : ℝ) - Real.log (m : ℝ)
  have hgap : |ω| ≥ |(n : ℝ) - (m : ℝ)| / (2 * N) := by
    simpa [ω] using
      (log_gap_lower N hNpos hnBounds.1 hmBounds.1 hnBounds.2 hmBounds.2 hnm)
  have hdist : 0 < |(n : ℝ) - (m : ℝ)| := by
    apply abs_pos.mpr
    have hcast : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
    exact sub_ne_zero.mpr hcast
  have hω : ω ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hgap
    have hpositive : 0 < |(n : ℝ) - (m : ℝ)| / (2 * N) :=
      div_pos hdist (by positivity)
    linarith
  have hrepr :
      (∫ t in u..u + U,
        (conj (dirichletTerm a n t) * dirichletTerm a m t).re) =
        ((conj (a n) * a m) *
          ∫ t in u..u + U,
            Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))).re := by
    simp_rw [dirichletTerm_cross]
    dsimp [ω]
    have hf : IntervalIntegrable
        (fun t : ℝ => (conj (a n) * a m) *
          Complex.exp
            (Complex.I * ((Real.log (n : ℝ) - Real.log (m : ℝ)) : ℂ) * (t : ℂ)))
        volume u (u + U) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    rw [intervalIntegral_re_eq (a := u) (b := u + U)
      (le_add_of_nonneg_right hU) _ hf]
    rw [intervalIntegral.integral_const_mul]
    rw [Complex.ofReal_sub]
  rw [hrepr]
  have hexp := interval_exp_im_norm_le ω u U hω
  have hrecipAbs : (2 : ℝ) / |ω| ≤ 4 * N / |(n : ℝ) - (m : ℝ)| := by
    calc
      (2 : ℝ) / |ω| ≤ 2 / (|(n : ℝ) - (m : ℝ)| / (2 * N)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hgap
      _ = 4 * N / |(n : ℝ) - (m : ℝ)| := by
        field_simp
        <;> ring
  have hrecip : (2 : ℝ) / |ω| ≤ 4 * N / (Nat.dist n m : ℝ) := by
    simpa [abs_nat_sub_eq_nat_dist] using hrecipAbs
  calc
    |((conj (a n) * a m) *
        ∫ t in u..u + U,
          Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))).re|
        ≤ ‖(conj (a n) * a m) *
          ∫ t in u..u + U,
            Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))‖ := Complex.abs_re_le_norm _
    _ = (‖a n‖ * ‖a m‖) *
          ‖∫ t in u..u + U,
            Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))‖ := by simp
    _ ≤ (‖a n‖ * ‖a m‖) * (2 / |ω|) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (‖a n‖ * ‖a m‖) *
          (4 * N / (Nat.dist n m : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = 4 * N * ‖a n‖ * ‖a m‖ / (Nat.dist n m : ℝ) := by ring

/-- The weighted off-diagonal kernel is controlled by the row harmonic
sum. The factor `1/2` from `2ab ≤ a²+b²` is retained using symmetry. -/
private lemma dirichlet_offDiagonal_weighted_bound (N : ℝ) (a : ℕ → ℂ)
    (hN : 2 ≤ N) :
    (∑ n ∈ dirichletIndices N,
      ∑ m ∈ (dirichletIndices N).filter (fun m => m ≠ n),
        ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) ≤
      2 * (1 + Real.log (2 * N)) * dirichletEnergy N a := by
  classical
  let S := dirichletIndices N
  let P := ∑ n ∈ S,
    ∑ m ∈ S.filter (fun m => m ≠ n),
      ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)
  let A := ∑ n ∈ S,
    ∑ m ∈ S.filter (fun m => m ≠ n),
      ‖a n‖ ^ 2 / (Nat.dist m n : ℝ)
  let B := ∑ n ∈ S,
    ∑ m ∈ S.filter (fun m => m ≠ n),
      ‖a m‖ ^ 2 / (Nat.dist m n : ℝ)
  let R := ∑ n ∈ S, ‖a n‖ ^ 2 *
    (∑ m ∈ S.filter (fun m => m ≠ n), (1 : ℝ) / (Nat.dist m n : ℝ))
  have hswap : B = A := by
    dsimp [A, B]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [Nat.dist_comm, ne_comm]
  have hrowfactor : A = R := by
    dsimp [A, R]
    apply Finset.sum_congr rfl
    intro n hn
    calc
      (∑ m ∈ S.filter (fun m => m ≠ n),
          ‖a n‖ ^ 2 / (Nat.dist m n : ℝ)) =
          ∑ m ∈ S.filter (fun m => m ≠ n),
            ‖a n‖ ^ 2 * (1 / (Nat.dist m n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = ‖a n‖ ^ 2 *
          (∑ m ∈ S.filter (fun m => m ≠ n),
            (1 : ℝ) / (Nat.dist m n : ℝ)) := by
        rw [← Finset.mul_sum]
  have hR : R ≤ 2 * (1 + Real.log (2 * N)) * dirichletEnergy N a := by
    dsimp [R, S]
    calc
      _ ≤ ∑ n ∈ dirichletIndices N,
            ‖a n‖ ^ 2 * (2 * (1 + Real.log (2 * N))) := by
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left
        · exact dirichlet_row_harmonic_bound hN hn
        · positivity
      _ = (∑ n ∈ dirichletIndices N, ‖a n‖ ^ 2) *
            (2 * (1 + Real.log (2 * N))) := by
        rw [Finset.sum_mul]
      _ = 2 * (1 + Real.log (2 * N)) * dirichletEnergy N a := by
        simp [dirichletEnergy, mul_comm]
  have hdouble : 2 * P ≤ A + B := by
    dsimp [P, A, B]
    calc
      2 * (∑ n ∈ S,
          ∑ m ∈ S.filter (fun m => m ≠ n),
            ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) =
          ∑ n ∈ S,
            ∑ m ∈ S.filter (fun m => m ≠ n),
              2 * (‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) := by
        simp only [← Finset.mul_sum]
      _ ≤ ∑ n ∈ S,
            ∑ m ∈ S.filter (fun m => m ≠ n),
              (‖a n‖ ^ 2 / (Nat.dist m n : ℝ) +
                ‖a m‖ ^ 2 / (Nat.dist m n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro m hm
        have hdist : 0 < (Nat.dist m n : ℝ) := by
          have hne : m ≠ n := (Finset.mem_filter.mp hm).2
          exact_mod_cast Nat.dist_pos_of_ne hne
        have hsq : 2 * (‖a n‖ * ‖a m‖) ≤ ‖a n‖ ^ 2 + ‖a m‖ ^ 2 := by
          nlinarith [sq_nonneg (‖a n‖ - ‖a m‖)]
        have hdiv := div_le_div_of_nonneg_right hsq hdist.le
        convert hdiv using 1 <;> ring
      _ = A + B := by
        simp_rw [Finset.sum_add_distrib]
        rfl
  have hAB : A + B = 2 * R := by
    calc
      A + B = A + A := by rw [hswap]
      _ = R + R := by simp [hrowfactor]
      _ = 2 * R := by ring
  have hP : P ≤ R := by nlinarith [hdouble, hAB]
  dsimp [P]
  exact hP.trans hR

private lemma dirichlet_diagonal_integral (u U : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    (∫ t in u..u + U,
      (conj (dirichletTerm a n t) * dirichletTerm a n t).re) =
      U * ‖a n‖ ^ 2 := by
  simp_rw [dirichletTerm_cross_diag]
  rw [intervalIntegral.integral_const]
  simp

/-- Mean square of a finite Dirichlet polynomial on any real interval.
This is the source estimate `lgv:mean-square`; the parameter `u` records
the arbitrary time origin and `U` is the interval length. -/
theorem meanSquareBound (N u U : ℝ) (a : ℕ → ℂ)
    (hN : 2 ≤ N) (hU : 0 ≤ U) :
    (∫ t in u..u + U, Complex.normSq (dirichletPolynomial N a t)) ≤
      (U + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
  classical
  let S := dirichletIndices N
  let pair (n m : ℕ) :=
    ∫ t in u..u + U,
      (conj (dirichletTerm a n t) * dirichletTerm a m t).re
  let off := ∑ n ∈ S, ∑ m ∈ S.filter (fun m => m ≠ n), pair n m
  have hdiag (n : ℕ) : pair n n = U * ‖a n‖ ^ 2 := by
    dsimp [pair]
    exact dirichlet_diagonal_integral u U a n
  have hsplit (n : ℕ) (hn : n ∈ S) :
      (∑ m ∈ S, pair n m) = pair n n +
        ∑ m ∈ S.filter (fun m => m ≠ n), pair n m := by
    calc
      (∑ m ∈ S, pair n m) =
          (∑ m ∈ S.erase n, pair n m) + pair n n :=
        (Finset.sum_erase_add S (fun m => pair n m) hn).symm
      _ = pair n n + ∑ m ∈ S.filter (fun m => m ≠ n), pair n m := by
        rw [← Finset.filter_ne']
        ring
  have hdiagSum :
      (∑ n ∈ S, pair n n) = U * dirichletEnergy N a := by
    calc
      (∑ n ∈ S, pair n n) =
          ∑ n ∈ S, U * ‖a n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hdiag n
      _ = U * dirichletEnergy N a := by
        rw [← Finset.mul_sum]
        simp [dirichletEnergy, S]
  have hexpand :
      (∫ t in u..u + U, Complex.normSq (dirichletPolynomial N a t)) =
        U * dirichletEnergy N a + off := by
    rw [dirichlet_meanSquare_eq_pair_sum]
    calc
      (∑ n ∈ S, ∑ m ∈ S, pair n m) =
          ∑ n ∈ S, (pair n n +
            ∑ m ∈ S.filter (fun m => m ≠ n), pair n m) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hsplit n hn
      _ = U * dirichletEnergy N a + off := by
        rw [Finset.sum_add_distrib, hdiagSum]
  have hoff : off ≤ 8 * N * (1 + Real.log (2 * N)) *
      dirichletEnergy N a := by
    calc
      off ≤ ∑ n ∈ S,
          ∑ m ∈ S.filter (fun m => m ≠ n),
            4 * N * ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro m hm
        have hm' : m ∈ S := (Finset.mem_filter.mp hm).1
        have hne : m ≠ n := (Finset.mem_filter.mp hm).2
        have hbound := dirichlet_cross_integral_bound N u U a hN hU hn hm' hne.symm
        exact (le_abs_self (pair n m)).trans (by
          simpa [pair, Nat.dist_comm] using hbound)
      _ = 4 * N *
          (∑ n ∈ S,
            ∑ m ∈ S.filter (fun m => m ≠ n),
              ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) := by
        calc
          _ = ∑ n ∈ S,
                4 * N * (∑ m ∈ S.filter (fun m => m ≠ n),
                  ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) := by
            apply Finset.sum_congr rfl
            intro n hn
            calc
              _ = ∑ m ∈ S.filter (fun m => m ≠ n),
                    4 * N * (‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) := by
                apply Finset.sum_congr rfl
                intro m hm
                ring
              _ = 4 * N * (∑ m ∈ S.filter (fun m => m ≠ n),
                    ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) := by
                rw [← Finset.mul_sum]
          _ = 4 * N *
                (∑ n ∈ S,
                  ∑ m ∈ S.filter (fun m => m ≠ n),
                    ‖a n‖ * ‖a m‖ / (Nat.dist m n : ℝ)) := by
            rw [← Finset.mul_sum]
      _ ≤ 4 * N *
          (2 * (1 + Real.log (2 * N)) * dirichletEnergy N a) := by
        apply mul_le_mul_of_nonneg_left
        · exact dirichlet_offDiagonal_weighted_bound N a hN
        · positivity
      _ = 8 * N * (1 + Real.log (2 * N)) * dirichletEnergy N a := by ring
  rw [hexpand]
  calc
    U * dirichletEnergy N a + off ≤
        U * dirichletEnergy N a +
          8 * N * (1 + Real.log (2 * N)) * dirichletEnergy N a :=
      add_le_add_right hoff (U * dirichletEnergy N a)
    _ = (U + 8 * N * (1 + Real.log (2 * N))) *
          dirichletEnergy N a := by ring

#print axioms FractionalPrimes.Literature.LargeValues.meanSquareBound

/-- The same mean-square estimate after the source normalization by
`N^(it)`, whose modulus is identically one. -/
theorem meanSquareBound_afterTwist (N u U : ℝ) (a : ℕ → ℂ)
    (hN : 2 ≤ N) (hU : 0 ≤ U) :
    (∫ t in u..u + U,
      Complex.normSq
        (Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
          dirichletPolynomial N a t)) ≤
      (U + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
  have hexpNorm (t : ℝ) :
      Complex.normSq (Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * (Real.log N : ℂ)).re = 0 := by
      rw [Complex.mul_re]
      have hre' : (Complex.I * (t : ℂ)).re = 0 := by simp [Complex.mul_re]
      have him' : (Complex.I * (t : ℂ)).im = t := by simp [Complex.mul_im]
      rw [hre', him', Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    simp
  have hpoint (t : ℝ) :
      Complex.normSq
          (Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
            dirichletPolynomial N a t) =
        Complex.normSq (dirichletPolynomial N a t) := by
    rw [Complex.normSq_mul, hexpNorm, one_mul]
  simp_rw [hpoint]
  exact meanSquareBound N u U a hN hU

/-- Set-integral form for the half-open interval `(u,u+U]`. Every
bounded real interval differs from this representative by at most its
endpoints, which have Lebesgue measure zero. -/
theorem meanSquareBound_Ioc (N u U : ℝ) (a : ℕ → ℂ)
    (hN : 2 ≤ N) (hU : 0 ≤ U) :
    (∫ t in Set.Ioc u (u + U),
      Complex.normSq (dirichletPolynomial N a t) ∂volume) ≤
      (U + 8 * N * (1 + Real.log (2 * N))) * dirichletEnergy N a := by
  rw [← intervalIntegral.integral_of_le (le_add_of_nonneg_right hU)]
  exact meanSquareBound N u U a hN hU

#print axioms FractionalPrimes.Literature.LargeValues.meanSquareBound_afterTwist
#print axioms FractionalPrimes.Literature.LargeValues.meanSquareBound_Ioc

end FractionalPrimes.Literature.LargeValues

end
