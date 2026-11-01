module

public import FractionalPrimes.Literature.JSW.FoundationBoundary
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite Rademacher moment lower bound

The finite expectation below is taken over all sign assignments, with the
uniform product distribution on the coordinates.
-/

@[expose] public section

open scoped BigOperators
open scoped InnerProductSpace

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The finite sample space carrying independent uniform signs. -/
def jswSignSpace : ℕ → Type
  | 0 => PUnit
  | n + 1 => Bool × jswSignSpace n

instance instFintypeJswSignSpace (n : ℕ) : Fintype (jswSignSpace n) := by
  induction n with
  | zero =>
      change Fintype PUnit
      exact inferInstance
  | succ n ih =>
      change Fintype (Bool × jswSignSpace n)
      letI : Fintype (jswSignSpace n) := ih
      infer_instance

instance instNonemptyJswSignSpace (n : ℕ) : Nonempty (jswSignSpace n) := by
  induction n with
  | zero => exact ⟨PUnit.unit⟩
  | succ n ih =>
      rcases ih with ⟨ω⟩
      exact ⟨(false, ω)⟩

/-- The real Rademacher variable associated to a Boolean outcome. -/
def jswSign (b : Bool) : ℝ := if b then 1 else -1

/-- The signed sum over the recursive product sample space. -/
def jswSignSum : (n : ℕ) → jswSignSpace n → (Fin n → ℂ) → ℂ
  | 0, _, _ => 0
  | n + 1, (b, ω), z => (jswSign b : ℂ) * z 0 + jswSignSum n ω (fun i => z i.succ)

private theorem expect_bool (f : Bool → ℝ) :
    Finset.expect (Finset.univ : Finset Bool) f = (f true + f false) / 2 := by
  simp [Finset.expect, NNRat.smul_def]
  ring

private theorem expect_bool_norm_add_sq (z w : ℂ) :
    Finset.expect (Finset.univ : Finset Bool)
        (fun b => ‖(jswSign b : ℂ) * z + w‖ ^ 2) = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [expect_bool]
  simp only [jswSign, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_neg,
    neg_one_mul, one_mul]
  rw [@norm_add_sq ℂ _ _ _ _ z w, @norm_add_sq ℂ _ _ _ _ (-z) w]
  simp only [norm_neg, inner_neg_left, map_neg]
  ring

private theorem expect_bool_norm_add_fourth (z w : ℂ) :
    Finset.expect (Finset.univ : Finset Bool)
        (fun b => ‖(jswSign b : ℂ) * z + w‖ ^ 4) =
      (‖z‖ ^ 2 + ‖w‖ ^ 2) ^ 2 + 4 * (RCLike.re (inner ℂ z w)) ^ 2 := by
  rw [expect_bool]
  simp only [jswSign, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_neg,
    neg_one_mul, one_mul]
  have hpow (x : ℂ) : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
  rw [hpow, hpow, @norm_add_sq ℂ _ _ _ _ z w, @norm_add_sq ℂ _ _ _ _ (-z) w]
  simp only [norm_neg, inner_neg_left, map_neg]
  ring

private theorem expect_mono_real {α : Type*} (s : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ s, f x ≤ g x) :
    Finset.expect s f ≤ Finset.expect s g := by
  simp only [Finset.expect, NNRat.smul_def]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)

private theorem expect_mul_sq_le {α : Type*} (s : Finset α) (f g : α → ℝ) :
    (Finset.expect s (fun x => f x * g x)) ^ 2 ≤
      Finset.expect s (fun x => f x ^ 2) * Finset.expect s (fun x => g x ^ 2) := by
  by_cases hs : s.Nonempty
  · have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
    rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
      Finset.expect_eq_sum_div_card]
    field_simp
    nlinarith [Finset.sum_mul_sq_le_sq_mul_sq s f g]
  · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hse]

/-- The second moment of the complex Rademacher sum is its coefficient
energy. -/
theorem jswSignSum_secondMoment (n : ℕ) (z : Fin n → ℂ) :
    Finset.expect (Finset.univ : Finset (jswSignSpace n))
        (fun ω => ‖jswSignSum n ω z‖ ^ 2) = ∑ i, ‖z i‖ ^ 2 := by
  induction n with
  | zero => simp [jswSignSum]
  | succ n ih =>
      change Finset.expect (Finset.univ : Finset (Bool × jswSignSpace n))
        (fun ω => ‖jswSignSum (n + 1) ω z‖ ^ 2) = _
      rw [show (Finset.univ : Finset (Bool × jswSignSpace n)) =
          (Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (jswSignSpace n)) by
        ext ⟨b, ω⟩; simp]
      rw [Finset.expect_product, Finset.expect_comm]
      simp_rw [jswSignSum, expect_bool_norm_add_sq]
      rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
      simp only [ih]
      simp [Fin.sum_univ_succ]

/-- The fourth moment of a finite complex Rademacher sum is at most three
times the square of its coefficient energy. -/
theorem jswSignSum_fourthMoment_le (n : ℕ) (z : Fin n → ℂ) :
    Finset.expect (Finset.univ : Finset (jswSignSpace n))
        (fun ω => ‖jswSignSum n ω z‖ ^ 4) ≤ 3 * (∑ i, ‖z i‖ ^ 2) ^ 2 := by
  induction n with
  | zero => simp [jswSignSum]
  | succ n ih =>
      change Finset.expect (Finset.univ : Finset (Bool × jswSignSpace n))
        (fun ω => ‖jswSignSum (n + 1) ω z‖ ^ 4) ≤ _
      rw [show (Finset.univ : Finset (Bool × jswSignSpace n)) =
          (Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (jswSignSpace n)) by
        ext ⟨b, ω⟩; simp]
      rw [Finset.expect_product, Finset.expect_comm]
      simp_rw [jswSignSum, expect_bool_norm_add_fourth]
      let a : ℝ := ‖z 0‖ ^ 2
      let b : jswSignSpace n → ℝ := fun ω =>
        ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2
      let A : ℝ := ∑ i : Fin n, ‖z i.succ‖ ^ 2
      have ha : 0 ≤ a := by positivity [a]
      have hbSecond : Finset.expect Finset.univ b = A := by
        dsimp [b, A]
        exact jswSignSum_secondMoment n (fun i => z i.succ)
      have hbFourth : Finset.expect Finset.univ (fun ω => b ω ^ 2) ≤ 3 * A ^ 2 := by
        dsimp [b, A]
        calc
          Finset.expect Finset.univ (fun ω => (‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) ^ 2) =
              Finset.expect Finset.univ (fun ω => ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 4) := by
            apply Finset.expect_congr rfl
            intro ω hω
            ring
          _ ≤ 3 * (∑ i : Fin n, ‖z i.succ‖ ^ 2) ^ 2 := ih (fun i => z i.succ)
      have hpoint : ∀ ω ∈ (Finset.univ : Finset (jswSignSpace n)),
          (‖z 0‖ ^ 2 + ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) ^ 2 +
              4 * (RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))) ^ 2 ≤
            a ^ 2 + 6 * a * b ω + b ω ^ 2 := by
        intro ω hω
        have hinner :
            |RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))| ≤
              ‖z 0‖ * ‖jswSignSum n ω (fun i => z i.succ)‖ := by
          exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
        have hinnerSq :
            (RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))) ^ 2 ≤
              ‖z 0‖ ^ 2 * ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2 := by
          have hnonneg : 0 ≤ ‖z 0‖ * ‖jswSignSum n ω (fun i => z i.succ)‖ :=
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc
            (RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))) ^ 2 =
                |RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))| ^ 2 := by
              rw [sq_abs]
            _ ≤ (‖z 0‖ * ‖jswSignSum n ω (fun i => z i.succ)‖) ^ 2 :=
              (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hinner
            _ = ‖z 0‖ ^ 2 * ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2 := by ring
        dsimp [a, b]
        calc
          (‖z 0‖ ^ 2 + ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) ^ 2 +
                4 * (RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))) ^ 2 ≤
              (‖z 0‖ ^ 2 + ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) ^ 2 +
                4 * (‖z 0‖ ^ 2 * ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left hinnerSq (by norm_num : (0 : ℝ) ≤ 4)) _
          _ = (‖z 0‖ ^ 2) ^ 2 +
                6 * ‖z 0‖ ^ 2 * ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2 +
                (‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) ^ 2 := by ring
      have houter := expect_mono_real Finset.univ _ _ hpoint
      have hpoly : Finset.expect Finset.univ (fun ω =>
          a ^ 2 + 6 * a * b ω + b ω ^ 2) = a ^ 2 + 6 * a * A +
            Finset.expect Finset.univ (fun ω => b ω ^ 2) := by
        simp_rw [Finset.expect_add_distrib]
        simp [Finset.expect_const Finset.univ_nonempty, hbSecond, ← Finset.mul_expect]
      rw [hpoly] at houter
      have hbound : a ^ 2 + 6 * a * A + Finset.expect Finset.univ (fun ω => b ω ^ 2) ≤
          3 * (a + A) ^ 2 := by
        nlinarith [hbFourth, sq_nonneg A]
      calc
        Finset.expect Finset.univ (fun ω =>
            (‖z 0‖ ^ 2 + ‖jswSignSum n ω (fun i => z i.succ)‖ ^ 2) ^ 2 +
              4 * (RCLike.re (inner ℂ (z 0) (jswSignSum n ω (fun i => z i.succ)))) ^ 2)
            ≤ 3 * (a + A) ^ 2 := le_trans houter hbound
        _ = 3 * (∑ i : Fin (n + 1), ‖z i‖ ^ 2) ^ 2 := by
          congr 2
          simp [A, Fin.sum_univ_succ, a]

private theorem jswSignSum_largeProbability (n : ℕ) (z : Fin n → ℂ)
    (hA : 0 < ∑ i, ‖z i‖ ^ 2) :
    Finset.expect (Finset.univ : Finset (jswSignSpace n))
        (fun ω => if (∑ i, ‖z i‖ ^ 2) / 2 < ‖jswSignSum n ω z‖ ^ 2 then 1 else 0) ≥
      (1 / 12 : ℝ) := by
  let A : ℝ := ∑ i, ‖z i‖ ^ 2
  let X : jswSignSpace n → ℝ := fun ω => ‖jswSignSum n ω z‖ ^ 2
  let I : jswSignSpace n → ℝ := fun ω => if A / 2 < X ω then 1 else 0
  have hAdef : A = ∑ i, ‖z i‖ ^ 2 := rfl
  have hmean : Finset.expect Finset.univ X = A := by
    dsimp [X, A]
    exact jswSignSum_secondMoment n z
  have hfourth : Finset.expect Finset.univ (fun ω => X ω ^ 2) ≤ 3 * A ^ 2 := by
    dsimp [X, A]
    calc
      Finset.expect Finset.univ (fun ω => (‖jswSignSum n ω z‖ ^ 2) ^ 2) =
          Finset.expect Finset.univ (fun ω => ‖jswSignSum n ω z‖ ^ 4) := by
        apply Finset.expect_congr rfl
        intro ω hω
        ring
      _ ≤ 3 * (∑ i, ‖z i‖ ^ 2) ^ 2 := jswSignSum_fourthMoment_le n z
  have hI0 : ∀ ω, 0 ≤ I ω := by
    intro ω
    by_cases h : A / 2 < X ω <;> simp [I, h]
  have hP0 : 0 ≤ Finset.expect Finset.univ I := by
    calc
      0 = Finset.expect Finset.univ (fun _ : jswSignSpace n => (0 : ℝ)) := by simp
      _ ≤ Finset.expect Finset.univ I :=
        expect_mono_real Finset.univ (fun _ => 0) I (by intro ω hω; exact hI0 ω)
  have hY0 : 0 ≤ Finset.expect Finset.univ (fun ω => X ω * I ω) := by
    calc
      0 = Finset.expect Finset.univ (fun _ : jswSignSpace n => (0 : ℝ)) := by simp
      _ ≤ Finset.expect Finset.univ (fun ω => X ω * I ω) :=
        expect_mono_real Finset.univ (fun _ => 0) (fun ω => X ω * I ω) (by
          intro ω hω
          exact mul_nonneg (sq_nonneg _) (hI0 ω))
  have hsplit : A ≤ A / 2 + Finset.expect Finset.univ (fun ω => X ω * I ω) := by
    calc
      A = Finset.expect Finset.univ X := hmean.symm
      _ ≤ Finset.expect Finset.univ (fun ω => A / 2 + X ω * I ω) :=
        expect_mono_real Finset.univ X (fun ω => A / 2 + X ω * I ω) (by
          intro ω hω
          by_cases h : A / 2 < X ω
          · simp [I, h]
            linarith
          · simp [I, h]
            have hx : X ω ≤ A / 2 := le_of_not_gt h
            linarith)
      _ = A / 2 + Finset.expect Finset.univ (fun ω => X ω * I ω) := by
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  have hI2 : Finset.expect Finset.univ (fun ω => I ω ^ 2) = Finset.expect Finset.univ I := by
    apply Finset.expect_congr rfl
    intro ω hω
    simp [I]
  have hcs := expect_mul_sq_le (Finset.univ : Finset (jswSignSpace n)) X I
  rw [hI2] at hcs
  have hYlower : (A / 2) ^ 2 ≤ (Finset.expect Finset.univ (fun ω => X ω * I ω)) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hY0).2 (by linarith [hsplit])
  have hscaled : A ^ 2 * (1 / 4 : ℝ) ≤ A ^ 2 * (3 * Finset.expect Finset.univ I) := by
    calc
      A ^ 2 * (1 / 4 : ℝ) = (A / 2) ^ 2 := by ring
      _ ≤ (Finset.expect Finset.univ (fun ω => X ω * I ω)) ^ 2 := hYlower
      _ ≤ Finset.expect Finset.univ (fun ω => X ω ^ 2) * Finset.expect Finset.univ I := hcs
      _ ≤ (3 * A ^ 2) * Finset.expect Finset.univ I :=
        mul_le_mul_of_nonneg_right hfourth hP0
      _ = A ^ 2 * (3 * Finset.expect Finset.univ I) := by ring
  have hscaled' : (∑ i, ‖z i‖ ^ 2) ^ 2 * (1 / 4 : ℝ) ≤
      (∑ i, ‖z i‖ ^ 2) ^ 2 * (3 * Finset.expect Finset.univ I) := by
    simpa [A] using hscaled
  have hfrac : (1 / 4 : ℝ) ≤ 3 * Finset.expect Finset.univ I :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hA)).mp hscaled'
  have hprob : (1 / 12 : ℝ) ≤ Finset.expect Finset.univ I := by nlinarith [hfrac]
  simpa [I, A] using hprob

private theorem jswSign_lowerConstant_eq (A p : ℝ) (hA : 0 < A) (hp : 0 < p) :
    Real.rpow (Real.rpow (A / 2) (p / 2) / 12) (1 / p) =
      Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) * Real.rpow A (1 / 2) := by
  have hbase : 0 < A / 2 := by positivity
  have hroot : (Real.rpow (A / 2) (p / 2)) ^ (1 / p) =
      Real.rpow (A / 2) (1 / 2) := by
    calc
      (Real.rpow (A / 2) (p / 2)) ^ (1 / p) =
          Real.rpow (A / 2) ((p / 2) * (1 / p)) :=
            (Real.rpow_mul hbase.le (p / 2) (1 / p)).symm
      _ = Real.rpow (A / 2) (1 / 2) := by
        congr 1
        field_simp
  have hsplit : Real.rpow (A / 2) (1 / 2) =
      Real.rpow A (1 / 2) / Real.rpow 2 (1 / 2) :=
    Real.div_rpow hA.le (by norm_num) (1 / 2)
  have h2neg : Real.rpow 2 (-1 / 2) = (Real.rpow 2 (1 / 2))⁻¹ := by
    calc
      Real.rpow 2 (-1 / 2) = Real.rpow 2 (-(1 / 2 : ℝ)) := by congr 1; ring
      _ = (Real.rpow 2 (1 / 2))⁻¹ :=
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) _
  have h12neg : Real.rpow 12 (-1 / p) = (Real.rpow 12 (1 / p))⁻¹ := by
    calc
      Real.rpow 12 (-1 / p) = Real.rpow 12 (-(1 / p : ℝ)) := by congr 1; ring
      _ = (Real.rpow 12 (1 / p))⁻¹ :=
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (12 : ℝ)) _
  calc
    Real.rpow (Real.rpow (A / 2) (p / 2) / 12) (1 / p) =
        (Real.rpow (A / 2) (p / 2)) ^ (1 / p) / Real.rpow 12 (1 / p) :=
          Real.div_rpow (Real.rpow_nonneg (by positivity : 0 ≤ A / 2) _) (by norm_num) (1 / p)
    _ = Real.rpow (A / 2) (1 / 2) / Real.rpow 12 (1 / p) := by rw [hroot]
    _ = (Real.rpow A (1 / 2) / Real.rpow 2 (1 / 2)) / Real.rpow 12 (1 / p) := by
      rw [hsplit]
    _ = Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) * Real.rpow A (1 / 2) := by
      rw [h2neg, h12neg]
      have h2pos : 0 < Real.rpow 2 (1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
      have h12pos : 0 < Real.rpow 12 (1 / p) := Real.rpow_pos_of_pos (by norm_num) _
      field_simp

/-- The finite Rademacher sum has the blueprint's quantitative lower bound
for every positive real moment exponent. -/
theorem signMomentLowerBound (n : ℕ) (z : Fin n → ℂ) {p : ℝ} (hp : 0 < p) :
    Real.rpow
        (Finset.expect (Finset.univ : Finset (jswSignSpace n))
          (fun ω => Real.rpow ‖jswSignSum n ω z‖ p)) (1 / p) ≥
      Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) *
        Real.rpow (∑ i, ‖z i‖ ^ 2) (1 / 2) := by
  let A : ℝ := ∑ i, ‖z i‖ ^ 2
  let F : jswSignSpace n → ℝ := fun ω => Real.rpow ‖jswSignSum n ω z‖ p
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi => sq_nonneg ‖z i‖
  have hF0 : 0 ≤ Finset.expect Finset.univ F := by
    calc
      0 = Finset.expect Finset.univ (fun _ : jswSignSpace n => (0 : ℝ)) := by simp
      _ ≤ Finset.expect Finset.univ F :=
        expect_mono_real Finset.univ (fun _ => 0) F (by
          intro ω hω
          exact Real.rpow_nonneg (norm_nonneg _) p)
  by_cases hApos : 0 < A
  · let I : jswSignSpace n → ℝ := fun ω => if A / 2 < ‖jswSignSum n ω z‖ ^ 2 then 1 else 0
    have hprob : (1 / 12 : ℝ) ≤ Finset.expect Finset.univ I := by
      have h := jswSignSum_largeProbability n z (by simpa [A] using hApos)
      simpa [I, A] using h
    have hpoint : ∀ ω ∈ (Finset.univ : Finset (jswSignSpace n)),
        Real.rpow (A / 2) (p / 2) * I ω ≤ F ω := by
      intro ω hω
      by_cases hevent : A / 2 < ‖jswSignSum n ω z‖ ^ 2
      · simp [I, hevent, F]
        have hmon := Real.rpow_le_rpow (by positivity : 0 ≤ A / 2) hevent.le
          (by linarith : 0 ≤ p / 2)
        have hpowid : Real.rpow (‖jswSignSum n ω z‖ ^ 2) (p / 2) =
            Real.rpow ‖jswSignSum n ω z‖ p := by
          calc
            Real.rpow (‖jswSignSum n ω z‖ ^ 2) (p / 2) =
                Real.rpow ‖jswSignSum n ω z‖ (2 * (p / 2)) :=
                  (Real.rpow_natCast_mul (norm_nonneg _) 2 (p / 2)).symm
            _ = Real.rpow ‖jswSignSum n ω z‖ p := by congr 1; ring
        exact hmon.trans_eq hpowid
      · simp [I, hevent, F]
        exact Real.rpow_nonneg (norm_nonneg _) p
    have hmomentlower : Real.rpow (A / 2) (p / 2) * Finset.expect Finset.univ I ≤
        Finset.expect Finset.univ F := by
      calc
        _ = Finset.expect Finset.univ (fun ω => Real.rpow (A / 2) (p / 2) * I ω) := by
          rw [← Finset.mul_expect]
        _ ≤ Finset.expect Finset.univ F :=
          expect_mono_real Finset.univ _ F hpoint
    have hlow : Real.rpow (A / 2) (p / 2) / 12 ≤ Finset.expect Finset.univ F := by
      calc
        Real.rpow (A / 2) (p / 2) / 12 =
            Real.rpow (A / 2) (p / 2) * (1 / 12 : ℝ) := by ring
        _ ≤ Real.rpow (A / 2) (p / 2) * Finset.expect Finset.univ I :=
          mul_le_mul_of_nonneg_left hprob (Real.rpow_nonneg (by positivity) _)
        _ ≤ Finset.expect Finset.univ F := hmomentlower
    have hlow0 : 0 ≤ Real.rpow (A / 2) (p / 2) / 12 :=
      div_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ A / 2) _) (by norm_num)
    have hroot := Real.rpow_le_rpow hlow0 hlow (by positivity : 0 ≤ 1 / p)
    calc
      Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) * Real.rpow A (1 / 2) =
          Real.rpow (Real.rpow (A / 2) (p / 2) / 12) (1 / p) :=
            (jswSign_lowerConstant_eq A p hApos hp).symm
      _ ≤ Real.rpow (Finset.expect Finset.univ F) (1 / p) := hroot
  · have hAzero : A = 0 := le_antisymm (le_of_not_gt hApos) hA0
    have hsumzero : (∑ i, ‖z i‖ ^ 2) = 0 := by simpa [A] using hAzero
    have hright : Real.rpow 2 (-1 / 2) * Real.rpow 12 (-1 / p) *
        Real.rpow (∑ i, ‖z i‖ ^ 2) (1 / 2) = 0 := by
      rw [hsumzero]
      simp
    rw [hright]
    simpa [F] using Real.rpow_nonneg hF0 (1 / p)

end

end FractionalPrimes.Literature.JSW

end
