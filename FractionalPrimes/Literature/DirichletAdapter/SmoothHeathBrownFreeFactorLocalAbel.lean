module

public import FractionalPrimes.Literature.Twisted.SmoothSmallGroupAbelTransfer
public import FractionalPrimes.Literature.Polynomial.PolynomialSmoothMeanDecay
import Mathlib.Tactic

/-! Exact bounded-variation adapters for local theta/log free-factor sums.

The analytic input is kept as a uniform prefix estimate.  The lemmas here
insert the literal smooth Heath--Brown theta factor, the outer cutoff, and
the normalized logarithm into that estimate on the exact half-open interval.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted

private theorem sum_Ico_succ_diff (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b, (f (n + 1) - f n)) = f b - f a := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · calc
          (∑ n ∈ Finset.Ico a (b + 1), (f (n + 1) - f n)) =
              (∑ n ∈ Finset.Ico a b, (f (n + 1) - f n)) +
                (f (b + 1) - f b) := by
                  rw [Finset.sum_Ico_succ_top hab']
          _ = (f b - f a) + (f (b + 1) - f b) := by rw [ih hab']
          _ = f (b + 1) - f a := by ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

private theorem monotone_sample_variation_le_one
    {a b : ℕ} (hab : a < b) (f : ℕ → ℝ)
    (hmono : Monotone f) (hlo : ∀ n, 0 ≤ f n) (hhi : ∀ n, f n ≤ 1) :
    (∑ n ∈ Finset.Ioc a (b - 1), |f (n + 1) - f n|) ≤ 1 := by
  have hset : Finset.Ioc a (b - 1) = Finset.Ico (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset]
  have hsum :
      (∑ n ∈ Finset.Ico (a + 1) b, |f (n + 1) - f n|) =
        f b - f (a + 1) := by
    calc
      _ = ∑ n ∈ Finset.Ico (a + 1) b, (f (n + 1) - f n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [abs_of_nonneg]
        exact sub_nonneg.mpr (hmono (Nat.le_succ n))
      _ = f b - f (a + 1) := sum_Ico_succ_diff f (by omega)
  rw [hsum]
  linarith [hhi b, hlo (a + 1)]

private theorem antitone_sample_variation_le_one
    {a b : ℕ} (hab : a < b) (f : ℕ → ℝ)
    (hanti : Antitone f) (hlo : ∀ n, 0 ≤ f n) (hhi : ∀ n, f n ≤ 1) :
    (∑ n ∈ Finset.Ioc a (b - 1), |f (n + 1) - f n|) ≤ 1 := by
  have hset : Finset.Ioc a (b - 1) = Finset.Ico (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset]
  have hsum :
      (∑ n ∈ Finset.Ico (a + 1) b, |f (n + 1) - f n|) =
        f (a + 1) - f b := by
    calc
      _ = ∑ n ∈ Finset.Ico (a + 1) b, (f n - f (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hstep : f (n + 1) - f n ≤ 0 :=
          sub_nonpos.mpr (hanti (Nat.le_succ n))
        rw [abs_of_nonpos hstep]
        ring
      _ = f (a + 1) - f b := by
        have htel := sum_Ico_succ_diff (fun n => -f n) (a := a + 1) (b := b)
          (by omega)
        calc
          _ = ∑ n ∈ Finset.Ico (a + 1) b,
              ((-f (n + 1)) - (-f n)) := by
                apply Finset.sum_congr rfl
                intro n hn
                ring
          _ = (-f b) - (-f (a + 1)) := htel
          _ = f (a + 1) - f b := by ring
  rw [hsum]
  linarith [hhi (a + 1), hlo b]

private theorem real_product_step_variation
    {a b : ℝ} {c d : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (_hb : 0 ≤ b) (_hb' : b ≤ 1)
    (_hc : 0 ≤ c) (_hc' : c ≤ 1) (hd : 0 ≤ d) (_hd' : d ≤ 1) :
    |c * d - a * b| ≤ |c - a| + |d - b| := by
  calc
    |c * d - a * b| ≤ |c * d - a * d| + |a * d - a * b| := abs_sub_le _ _ _
    _ = |c - a| * |d| + |a| * |d - b| := by
      rw [show c * d - a * d = (c - a) * d by ring,
        show a * d - a * b = a * (d - b) by ring]
      simp only [abs_mul]
    _ ≤ |c - a| + |d - b| := by
      have hca : 0 ≤ |c - a| := abs_nonneg _
      have hdb : 0 ≤ |d - b| := abs_nonneg _
      rw [abs_of_nonneg hd, abs_of_nonneg ha]
      nlinarith

/-- The sampled outer cutoff has total variation at most two on every
finite natural interval.  The two factors are respectively monotone
increasing and decreasing along `m*n/X`. -/
theorem polynomialOuterCutoff_sample_variation_le_two
    {X : ℝ} (hX : 0 < X) (m : ℕ) {a b : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      |polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
        polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)|) ≤ 2 := by
  let x : ℕ → ℝ := fun n => ((m * n : ℕ) : ℝ) / X
  let u : ℕ → ℝ := fun n => Real.smoothTransition (4 * x n - 3)
  let v : ℕ → ℝ := fun n => Real.smoothTransition (5 - 2 * x n)
  have hxmono : Monotone x := by
    intro n k hnk
    dsimp [x]
    apply div_le_div_of_nonneg_right _ hX.le
    exact_mod_cast Nat.mul_le_mul_left m hnk
  have humono : Monotone u := by
    intro n k hnk
    dsimp [u]
    apply Real.smoothTransition.monotone
    linarith [hxmono hnk]
  have hvanti : Antitone v := by
    intro n k hnk
    dsimp [v]
    apply Real.smoothTransition.monotone
    linarith [hxmono hnk]
  have hu0 (n : ℕ) : 0 ≤ u n := Real.smoothTransition.nonneg _
  have hu1 (n : ℕ) : u n ≤ 1 := Real.smoothTransition.le_one _
  have hv0 (n : ℕ) : 0 ≤ v n := Real.smoothTransition.nonneg _
  have hv1 (n : ℕ) : v n ≤ 1 := Real.smoothTransition.le_one _
  have hvaru := monotone_sample_variation_le_one hab u humono hu0 hu1
  have hvarv := antitone_sample_variation_le_one hab v hvanti hv0 hv1
  have hpoint (n : ℕ) :
      |u (n + 1) * v (n + 1) - u n * v n| ≤
        |u (n + 1) - u n| + |v (n + 1) - v n| :=
    real_product_step_variation (hu0 n) (hu1 n) (hv0 n) (hv1 n)
      (hu0 (n + 1)) (hu1 (n + 1)) (hv0 (n + 1)) (hv1 (n + 1))
  have hsum :
      (∑ n ∈ Finset.Ioc a (b - 1),
        |u (n + 1) * v (n + 1) - u n * v n|) ≤
      (∑ n ∈ Finset.Ioc a (b - 1), |u (n + 1) - u n|) +
        ∑ n ∈ Finset.Ioc a (b - 1), |v (n + 1) - v n| := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc a (b - 1),
          (|u (n + 1) - u n| + |v (n + 1) - v n|) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hpoint n
      _ = _ := by rw [Finset.sum_add_distrib]
  have hdef (n : ℕ) :
      u n * v n = polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) := by
    simp [u, v, x, polynomialOuterCutoff]
  have hshift (n : ℕ) :
      u (n + 1) * v (n + 1) =
        polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) := by
    rw [hdef]
  calc
    _ = ∑ n ∈ Finset.Ioc a (b - 1),
        |u (n + 1) * v (n + 1) - u n * v n| := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hshift, hdef]
    _ ≤ _ := hsum
    _ ≤ 2 := by linarith

private theorem smoothHeathBrownThetaOuterWeight_norm_le_one
    (S X : ℝ) (m : ℕ) (n : ℕ) :
    ‖((smoothDyadicTheta ((n : ℝ) / S) *
        polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (smoothDyadicTheta_nonneg _)
      (polynomialOuterCutoff_nonneg _))]
  have hθ : smoothDyadicTheta ((n : ℝ) / S) ≤ 1 := smoothDyadicTheta_le_one _
  have hζ : polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) ≤ 1 :=
    polynomialOuterCutoff_le_one _
  have hθ0 : 0 ≤ smoothDyadicTheta ((n : ℝ) / S) := smoothDyadicTheta_nonneg _
  have hζ0 : 0 ≤ polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) :=
    polynomialOuterCutoff_nonneg _
  have hprod :
      (1 - smoothDyadicTheta ((n : ℝ) / S)) *
        (1 - polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)) ≥ 0 :=
    mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr hζ)
  nlinarith

private theorem smoothHeathBrownThetaOuterWeight_variation_le_four
    {X S : ℝ} (hS : 0 < S) (hX : 0 < X) (m : ℕ)
    {a b : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      ‖((smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) *
            polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) : ℝ) : ℂ) -
        ((smoothDyadicTheta ((n : ℝ) / S) *
            polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)‖) ≤ 4 := by
  have hθvar := smoothSmallGroupThetaSampleVariation hS hab
  have hζvar := polynomialOuterCutoff_sample_variation_le_two hX m hab
  have hθ01 (n : ℕ) : 0 ≤ smoothDyadicTheta ((n : ℝ) / S) ∧
      smoothDyadicTheta ((n : ℝ) / S) ≤ 1 :=
    ⟨smoothDyadicTheta_nonneg _, smoothDyadicTheta_le_one _⟩
  have hζ01 (n : ℕ) : 0 ≤ polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) ∧
      polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) ≤ 1 :=
    ⟨polynomialOuterCutoff_nonneg _, polynomialOuterCutoff_le_one _⟩
  have hstep (n : ℕ) :
      |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) *
            polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
          smoothDyadicTheta ((n : ℝ) / S) *
            polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)| ≤
        |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) -
            smoothDyadicTheta ((n : ℝ) / S)| +
          |polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
            polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)| := by
    exact real_product_step_variation (hθ01 n).1 (hθ01 n).2 (hζ01 n).1 (hζ01 n).2
      (hθ01 (n + 1)).1 (hθ01 (n + 1)).2 (hζ01 (n + 1)).1 (hζ01 (n + 1)).2
  have hsum :
      (∑ n ∈ Finset.Ioc a (b - 1),
        |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) *
              polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
            smoothDyadicTheta ((n : ℝ) / S) *
              polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)|) ≤
        (∑ n ∈ Finset.Ioc a (b - 1),
          |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) -
            smoothDyadicTheta ((n : ℝ) / S)|) +
        ∑ n ∈ Finset.Ioc a (b - 1),
          |polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
            polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)| := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc a (b - 1),
          (|smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) -
              smoothDyadicTheta ((n : ℝ) / S)| +
            |polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
              polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)|) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hstep n
      _ = _ := by rw [Finset.sum_add_distrib]
  calc
    _ = ∑ n ∈ Finset.Ioc a (b - 1),
        |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) *
              polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) -
            smoothDyadicTheta ((n : ℝ) / S) *
              polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)| := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := hsum
    _ ≤ 4 := by linarith

/-- Local theta-factor cancellation from a prefix estimate for the bare
periodic Mellin sequence.  The exact theta and outer-cutoff samples cost at
most five in the Abel variation factor. -/
theorem smoothHeathBrownThetaFactor_local_of_prefix
    {a b : ℕ} (hab : a < b) {S X : ℝ} (hS : 0 < S) (hX : 3 ≤ X)
    (m : ℕ) (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n, a < n → n ≤ b →
      ‖smoothSmallGroupPrefix a f n‖ ≤ C) :
    ‖∑ n ∈ Finset.Ioc a b,
      f n * ((smoothDyadicTheta ((n : ℝ) / S) *
        polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)‖ ≤ 5 * C := by
  have hweightvar :
      ‖((smoothDyadicTheta ((b : ℝ) / S) *
          polynomialOuterCutoff (((m * b : ℕ) : ℝ) / X) : ℝ) : ℂ)‖ +
        ∑ n ∈ Finset.Ioc a (b - 1),
          ‖((smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / S) *
                polynomialOuterCutoff (((m * (n + 1) : ℕ) : ℝ) / X) : ℝ) : ℂ) -
            ((smoothDyadicTheta ((n : ℝ) / S) *
                polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)‖ ≤ 5 := by
    have hterminal := smoothHeathBrownThetaOuterWeight_norm_le_one S X m b
    have hvariation := smoothHeathBrownThetaOuterWeight_variation_le_four
      (X := X) (S := S) hS (by linarith [hX]) m hab
    linarith
  calc
    _ ≤ C * 5 := smoothSmallGroupFiniteAbelTransfer hab f _ hC hprefix hweightvar
    _ = 5 * C := by ring

private theorem normalized_log_step_variation_le_one
    {X : ℝ} (hX : 3 ≤ X) {a b : ℕ} (hab : a < b)
    (hb : (b : ℝ) ≤ 16 * X) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      |Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
        Real.log (n : ℝ) / (4 * Real.log X)|) ≤ 1 := by
  have hXpos : 0 < X := by linarith
  have hXlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hXcube : 16 ≤ X ^ 3 := by
    calc
      16 ≤ (3 : ℝ) ^ 3 := by norm_num
      _ ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX _
  have hbpow : (b : ℝ) ≤ X ^ 4 := by
    calc
      (b : ℝ) ≤ 16 * X := hb
      _ ≤ X ^ 3 * X := mul_le_mul_of_nonneg_right hXcube hXpos.le
      _ = X ^ 4 := by ring
  have hlogb : Real.log (b : ℝ) ≤ 4 * Real.log X := by
    have hbposNat : 0 < b := by omega
    have hbpos : 0 < (b : ℝ) := by exact_mod_cast hbposNat
    calc
      Real.log (b : ℝ) ≤ Real.log (X ^ 4) :=
        Real.log_le_log hbpos hbpow
      _ = 4 * Real.log X := Real.log_pow X 4
  have hset : Finset.Ioc a (b - 1) = Finset.Ico (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  let g : ℕ → ℝ := fun n => Real.log (n : ℝ) / (4 * Real.log X)
  have hmon : ∀ n ∈ Finset.Ico (a + 1) b,
      0 ≤ Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
        Real.log (n : ℝ) / (4 * Real.log X) := by
    intro n hn
    have hnmem := Finset.mem_Ico.mp hn
    have hnposNat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hstep : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    rw [show Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
        Real.log (n : ℝ) / (4 * Real.log X) =
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) /
            (4 * Real.log X) by ring]
    exact div_nonneg (sub_nonneg.mpr (Real.log_le_log hnpos hstep)) (by positivity)
  have hsum :
      (∑ n ∈ Finset.Ico (a + 1) b,
        |Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
          Real.log (n : ℝ) / (4 * Real.log X)|) =
        Real.log (b : ℝ) / (4 * Real.log X) -
          Real.log ((a + 1 : ℕ) : ℝ) / (4 * Real.log X) := by
    have habs : ∀ n ∈ Finset.Ico (a + 1) b,
        |Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
          Real.log (n : ℝ) / (4 * Real.log X)| =
          Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
            Real.log (n : ℝ) / (4 * Real.log X) := by
      intro n hn
      exact abs_of_nonneg (hmon n hn)
    calc
      _ = ∑ n ∈ Finset.Ico (a + 1) b,
          (Real.log ((n + 1 : ℕ) : ℝ) / (4 * Real.log X) -
            Real.log (n : ℝ) / (4 * Real.log X)) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact habs n hn
      _ = g b - g (a + 1) := by
        simpa [g, Nat.cast_add, Nat.cast_one] using
          sum_Ico_succ_diff g (a := a + 1) (b := b) (by omega)
      _ = Real.log (b : ℝ) / (4 * Real.log X) -
          Real.log ((a + 1 : ℕ) : ℝ) / (4 * Real.log X) := by rfl
  rw [hset, hsum]
  have hloglow : 0 ≤ Real.log ((a + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : a + 1 ≠ 0))
  have hdiff :
      Real.log (b : ℝ) / (4 * Real.log X) -
        Real.log ((a + 1 : ℕ) : ℝ) / (4 * Real.log X) ≤ 1 := by
    have hupper : Real.log (b : ℝ) / (4 * Real.log X) ≤ 1 :=
      (div_le_one (by positivity)).2 hlogb
    have hlower : 0 ≤ Real.log ((a + 1 : ℕ) : ℝ) / (4 * Real.log X) :=
      div_nonneg hloglow (by positivity)
    linarith
  exact hdiff

private theorem normalized_log_weight_bounds
    {X : ℝ} (hX : 3 ≤ X) {b n : ℕ}
    (hn : 1 ≤ n) (hnb : n ≤ b) (hb : (b : ℝ) ≤ 16 * X) :
    0 ≤ Real.log (n : ℝ) / (4 * Real.log X) ∧
      Real.log (n : ℝ) / (4 * Real.log X) ≤ 1 := by
  have hXpos : 0 < X := by linarith
  have hXlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hXcube : 16 ≤ X ^ 3 := by
    calc
      16 ≤ (3 : ℝ) ^ 3 := by norm_num
      _ ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX _
  have hnpow : (n : ℝ) ≤ X ^ 4 := by
    calc
      (n : ℝ) ≤ b := by exact_mod_cast hnb
      _ ≤ 16 * X := hb
      _ ≤ X ^ 3 * X := mul_le_mul_of_nonneg_right hXcube hXpos.le
      _ = X ^ 4 := by ring
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogUpper : Real.log (n : ℝ) ≤ 4 * Real.log X := by
    calc
      Real.log (n : ℝ) ≤ Real.log (X ^ 4) := Real.log_le_log hnpos hnpow
      _ = 4 * Real.log X := Real.log_pow X 4
  exact ⟨div_nonneg hlogNonneg (by positivity),
    (div_le_one (by positivity)).2 hlogUpper⟩

/-- The normalized logarithmic smooth free-factor weight, including the
outer cutoff at the full product `m*n`. -/
noncomputable def smoothHeathBrownThetaLogOuterWeight
    (S X : ℝ) (m n : ℕ) : ℂ :=
  ((smoothDyadicTheta ((n : ℝ) / S) *
    polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) *
    (Real.log (n : ℝ) / (4 * Real.log X)) : ℝ) : ℂ)

private theorem smoothHeathBrownThetaLogOuterWeight_norm_le_one
    {S X : ℝ} (hX : 3 ≤ X) {m b : ℕ}
    (hbpos : 1 ≤ b) (hb : (b : ℝ) ≤ 16 * X) :
    ‖smoothHeathBrownThetaLogOuterWeight S X m b‖ ≤ 1 := by
  rw [smoothHeathBrownThetaLogOuterWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · have hθ : 0 ≤ smoothDyadicTheta ((b : ℝ) / S) ∧
        smoothDyadicTheta ((b : ℝ) / S) ≤ 1 :=
      ⟨smoothDyadicTheta_nonneg _, smoothDyadicTheta_le_one _⟩
    have hζ : 0 ≤ polynomialOuterCutoff (((m * b : ℕ) : ℝ) / X) ∧
        polynomialOuterCutoff (((m * b : ℕ) : ℝ) / X) ≤ 1 :=
      ⟨polynomialOuterCutoff_nonneg _, polynomialOuterCutoff_le_one _⟩
    have hlog := normalized_log_weight_bounds hX hbpos le_rfl hb
    have hprod₁ :
        smoothDyadicTheta ((b : ℝ) / S) *
          polynomialOuterCutoff (((m * b : ℕ) : ℝ) / X) ≤ 1 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hζ.2)]
    have hprod₀ :
        0 ≤ smoothDyadicTheta ((b : ℝ) / S) *
          polynomialOuterCutoff (((m * b : ℕ) : ℝ) / X) :=
      mul_nonneg hθ.1 hζ.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod₁)
      (sub_nonneg.mpr hlog.2)]
  · exact mul_nonneg (mul_nonneg (smoothDyadicTheta_nonneg _)
      (polynomialOuterCutoff_nonneg _)) (by
        exact (normalized_log_weight_bounds hX hbpos le_rfl hb).1)

private theorem smoothHeathBrownThetaLogOuterWeight_variation_le_five
    {S X : ℝ} (hS : 0 < S) (hX : 3 ≤ X) (m : ℕ)
    {a b : ℕ} (hab : a < b) (hb : (b : ℝ) ≤ 16 * X) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      ‖smoothHeathBrownThetaLogOuterWeight S X m (n + 1) -
        smoothHeathBrownThetaLogOuterWeight S X m n‖) ≤ 5 := by
  let p : ℕ → ℝ := fun n => smoothDyadicTheta ((n : ℝ) / S) *
    polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X)
  let l : ℕ → ℝ := fun n => Real.log (n : ℝ) / (4 * Real.log X)
  have hθvarComplex := smoothHeathBrownThetaOuterWeight_variation_le_four
    (X := X) (S := S) hS (by linarith [hX]) m hab
  have hθvar :
      (∑ n ∈ Finset.Ioc a (b - 1), |p (n + 1) - p n|) ≤ 4 := by
    simpa [p, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
      using hθvarComplex
  have hlogvar :
      (∑ n ∈ Finset.Ioc a (b - 1), |l (n + 1) - l n|) ≤ 1 := by
    simpa [l] using normalized_log_step_variation_le_one hX hab hb
  have hθ01 (n : ℕ) :
      0 ≤ p n ∧ p n ≤ 1 := by
    have hθ0 := smoothDyadicTheta_nonneg ((n : ℝ) / S)
    have hθ1 := smoothDyadicTheta_le_one ((n : ℝ) / S)
    have hζ0 := polynomialOuterCutoff_nonneg (((m * n : ℕ) : ℝ) / X)
    have hζ1 := polynomialOuterCutoff_le_one (((m * n : ℕ) : ℝ) / X)
    constructor
    · exact mul_nonneg hθ0 hζ0
    · nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hζ1)]
  have hlog01 (n : ℕ) (hnLower : 1 ≤ n) (hnUpper : n ≤ b) :
      0 ≤ l n ∧ l n ≤ 1 := by
    simpa [l] using normalized_log_weight_bounds hX hnLower hnUpper hb
  have hp_l_step (n : ℕ) (hn : n ∈ Finset.Ioc a (b - 1)) :
      |p (n + 1) * l (n + 1) - p n * l n| ≤
        |p (n + 1) - p n| + |l (n + 1) - l n| := by
    have hnIoc := Finset.mem_Ioc.mp hn
    have hnLower : 1 ≤ n := by omega
    have hnUpper : n ≤ b := by omega
    have hnNextLower : 1 ≤ n + 1 := by omega
    have hnNextUpper : n + 1 ≤ b := by omega
    exact real_product_step_variation (hθ01 n).1 (hθ01 n).2
      (hlog01 n hnLower hnUpper).1 (hlog01 n hnLower hnUpper).2
      (hθ01 (n + 1)).1 (hθ01 (n + 1)).2
      (hlog01 (n + 1) hnNextLower hnNextUpper).1
      (hlog01 (n + 1) hnNextLower hnNextUpper).2
  have hsum :
      (∑ n ∈ Finset.Ioc a (b - 1),
        |p (n + 1) * l (n + 1) - p n * l n|) ≤
      (∑ n ∈ Finset.Ioc a (b - 1), |p (n + 1) - p n|) +
        ∑ n ∈ Finset.Ioc a (b - 1), |l (n + 1) - l n| := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc a (b - 1),
          (|p (n + 1) - p n| + |l (n + 1) - l n|) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hp_l_step n hn
      _ = _ := by rw [Finset.sum_add_distrib]
  have hweightVariationEq :
      (∑ n ∈ Finset.Ioc a (b - 1),
        ‖smoothHeathBrownThetaLogOuterWeight S X m (n + 1) -
          smoothHeathBrownThetaLogOuterWeight S X m n‖) =
        ∑ n ∈ Finset.Ioc a (b - 1), |p (n + 1) * l (n + 1) - p n * l n| := by
    apply Finset.sum_congr rfl
    intro n hn
    change ‖((p (n + 1) * l (n + 1) : ℝ) : ℂ) -
        ((p n * l n : ℝ) : ℂ)‖ = _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hweightVariationEq]
  calc
    _ ≤ (∑ n ∈ Finset.Ioc a (b - 1), |p (n + 1) - p n|) +
        ∑ n ∈ Finset.Ioc a (b - 1), |l (n + 1) - l n| := hsum
    _ ≤ 5 := by linarith

/-- Local logarithmic-factor cancellation from a prefix estimate for the
bare periodic Mellin sequence.  On the exact source support range
`n ≤ 16X`, theta, outer-cutoff, and normalized-log variation costs at most
five, so Abel summation costs at most six including the terminal value. -/
theorem smoothHeathBrownLogFactor_local_of_prefix
    {a b : ℕ} (hab : a < b) {S X : ℝ}
    (hS : 0 < S) (hX : 3 ≤ X) (m : ℕ) (hb : (b : ℝ) ≤ 16 * X)
    (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hprefix : ∀ n, a < n → n ≤ b →
      ‖smoothSmallGroupPrefix a f n‖ ≤ C) :
    ‖∑ n ∈ Finset.Ioc a b,
      f n * smoothHeathBrownThetaLogOuterWeight S X m n‖ ≤ 6 * C := by
  have hweightvar :
      ‖smoothHeathBrownThetaLogOuterWeight S X m b‖ +
        ∑ n ∈ Finset.Ioc a (b - 1),
          ‖smoothHeathBrownThetaLogOuterWeight S X m (n + 1) -
            smoothHeathBrownThetaLogOuterWeight S X m n‖ ≤ 6 := by
    have hbpos : 1 ≤ b := by omega
    have hterminal := smoothHeathBrownThetaLogOuterWeight_norm_le_one
      (S := S) (X := X) (m := m) (b := b) hX hbpos hb
    have hvariation := smoothHeathBrownThetaLogOuterWeight_variation_le_five
      hS hX m hab hb
    linarith
  calc
    _ ≤ C * 6 := smoothSmallGroupFiniteAbelTransfer hab f _ hC hprefix hweightvar
    _ = 6 * C := by ring

/-- The actual periodic residue indicator used to select one progression. -/
def smoothHeathBrownResidueIndicator (q : ℕ) (r n : ℤ) : ℂ :=
  if n % (q : ℤ) = r % (q : ℤ) then 1 else 0

@[simp] theorem smoothHeathBrownResidueIndicator_periodic
    (q : ℕ) (r n : ℤ) :
    smoothHeathBrownResidueIndicator q r (n % (q : ℤ)) =
      smoothHeathBrownResidueIndicator q r n := by
  simp [smoothHeathBrownResidueIndicator]

theorem smoothHeathBrownResidueIndicator_norm_le_one
    (q : ℕ) (r n : ℤ) :
    ‖smoothHeathBrownResidueIndicator q r n‖ ≤ 1 := by
  by_cases h : n % (q : ℤ) = r % (q : ℤ) <;>
    simp [smoothHeathBrownResidueIndicator, h]

noncomputable def smoothHeathBrownResidueMellinTerm
    (q : ℕ) (r : ℤ) (t : ℝ) (n : ℕ) : ℂ :=
  smoothHeathBrownResidueIndicator q r (n : ℤ) *
    (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ))

private theorem smoothSmallGroupPrefix_eq_Ioc
    (a k : ℕ) (f : ℕ → ℂ) :
    smoothSmallGroupPrefix a f k = ∑ n ∈ Finset.Ioc a k, f n := by
  classical
  unfold smoothSmallGroupPrefix
  have hset :
      (Finset.range (k + 1)).filter (fun n => a < n) = Finset.Ioc a k := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter]
  rw [hset]

/-- A prefix on natural endpoints is the exact source interval sum, with the
left endpoint `x` left real and the right endpoint the selected integer `k`.
The floors preserve the original half-open convention `(x,k]`. -/
private theorem smoothSmallGroupPrefix_eq_realIntegerInterval
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (f : ℕ → ℂ) (g : ℤ → ℂ)
    (hfg : ∀ n : ℕ, f n = g (n : ℤ)) :
    smoothSmallGroupPrefix (Nat.floor x) f k =
      ∑ n ∈ FractionalPrimes.realIntegerInterval x ((k : ℝ) - x), g n := by
  have hset :
      FractionalPrimes.realIntegerInterval x ((k : ℝ) - x) =
        (Finset.Ioc (Nat.floor x) k).map Nat.castEmbedding := by
    classical
    ext n
    rw [FractionalPrimes.mem_realIntegerInterval_iff]
    simp only [Finset.mem_map, Finset.mem_Ioc]
    constructor
    · rintro ⟨hnx, hnk⟩
      have hnpos : 0 < n := by
        have hnposreal : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hx hnx
        exact_mod_cast hnposreal
      have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hnpos)
      refine ⟨n.toNat, ?_, ?_⟩
      · constructor
        · have hnatcastreal : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hncast
          exact (Nat.floor_lt hx).mpr (by rw [hnatcastreal]; exact hnx)
        · have hnatle : (n.toNat : ℝ) ≤ (k : ℝ) := by
            have hnk' : (n : ℝ) ≤ (k : ℝ) := by simpa using hnk
            have hnatcastreal : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hncast
            rw [hnatcastreal]
            exact hnk'
          exact_mod_cast hnatle
      · simpa using hncast
    · rintro ⟨m, hm, hmn⟩
      have hcast : (m : ℝ) = (n : ℝ) := by exact_mod_cast hmn
      constructor
      · have hxlt : x < (m : ℝ) := (Nat.floor_lt hx).mp hm.1
        simpa [hcast] using hxlt
      · have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm.2
        simpa [hcast] using hmk
  rw [smoothSmallGroupPrefix_eq_Ioc]
  rw [hset, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  rw [Finset.sum_congr rfl]
  intro n hn
  exact hfg n

private theorem smoothHeathBrownResiduePrefix_bound
    {alpha A X L T0 t x y : ℝ} {q : ℕ} {r : ℤ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hxL : L ≤ x) (hy2 : y ≤ 2 * L) (hxy : x ≤ y)
    {k : ℕ} (hkleft : Nat.floor x < k) (hkright : k ≤ Nat.floor y) :
    ‖smoothSmallGroupPrefix (Nat.floor x)
        (smoothHeathBrownResidueMellinTerm q r t) k‖ ≤
      periodicLogPhaseConstant alpha A * Real.sqrt L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le
    (Real.rpow_pos_of_pos hXpos _) hLlower
  have hxnonneg : 0 ≤ x := le_trans hLpos.le hxL
  have hynonneg : 0 ≤ y := le_trans hxnonneg hxy
  have hxk : x < (k : ℝ) := (Nat.floor_lt hxnonneg).mp hkleft
  have hky : (k : ℝ) ≤ y := by
    calc
      (k : ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast hkright
      _ ≤ y := Nat.floor_le hynonneg
  let omega : ℤ → ℂ := smoothHeathBrownResidueIndicator q r
  have hperiod : ∀ n : ℤ, omega n = omega (n % (q : ℤ)) := by
    intro n
    exact (smoothHeathBrownResidueIndicator_periodic q r n).symm
  have hweight : ∀ n : ℤ, ‖omega n‖ ≤ 1 := by
    intro n
    exact smoothHeathBrownResidueIndicator_norm_le_one q r n
  have hphase := periodicLogPhaseBoundedWeightDirichletInterval
    halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t htX
    hperiod hweight hxL (by
      calc
        x + ((k : ℝ) - x) = (k : ℝ) := by ring
        _ ≤ y := hky
        _ ≤ 2 * L := hy2)
  have hprefixEq :
      smoothSmallGroupPrefix (Nat.floor x)
          (smoothHeathBrownResidueMellinTerm q r t) k =
        ∑ n ∈ FractionalPrimes.realIntegerInterval x ((k : ℝ) - x),
          omega n * (n : ℂ) ^ ((-(1 / 2 : ℂ)) - Complex.I * (t : ℂ)) := by
    apply smoothSmallGroupPrefix_eq_realIntegerInterval hxnonneg
    intro n
    rfl
  rw [hprefixEq]
  simpa [omega] using hphase

private theorem smoothHeathBrownPeriodicPhaseConstant_nonneg
    (alpha A : ℝ) : 0 ≤ periodicLogPhaseConstant alpha A := by
  unfold periodicLogPhaseConstant
  exact le_trans (by norm_num) (le_max_left _ _)

/-- The source theta factor on every arbitrary subinterval of `[L,2L]`,
with the actual single-residue periodic indicator.  The periodic phase
estimate supplies all prefixes, and the exact smooth theta/outer-cutoff
weight costs the finite Abel factor five. -/
theorem smoothHeathBrownThetaFactor_periodic_interval
    {alpha A X L T0 t S x y : ℝ} {q : ℕ} {r : ℤ} (m : ℕ)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hxL : L ≤ x) (hxy : x ≤ y) (hy2 : y ≤ 2 * L) (hS : 0 < S) :
    ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
      smoothHeathBrownResidueMellinTerm q r t n *
        ((smoothDyadicTheta ((n : ℝ) / S) *
          polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)‖ ≤
      5 * periodicLogPhaseConstant alpha A * Real.sqrt L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  let C : ℝ := periodicLogPhaseConstant alpha A * Real.sqrt L *
    (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))
  have hXpos : 0 < X := by linarith
  have hT0pos : 0 < T0 := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (smoothHeathBrownPeriodicPhaseConstant_nonneg alpha A)
        (Real.sqrt_nonneg _))
      (add_nonneg (Real.rpow_nonneg hXpos.le _)
        (Real.rpow_nonneg hT0pos.le _))
  let a : ℕ := Nat.floor x
  let b : ℕ := Nat.floor y
  by_cases hab : a < b
  · have hprefix : ∀ k, a < k → k ≤ b →
        ‖smoothSmallGroupPrefix a
          (smoothHeathBrownResidueMellinTerm q r t) k‖ ≤ C := by
      intro k hak hkb
      have hk := smoothHeathBrownResiduePrefix_bound (r := r)
        halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t htX
        hxL hy2 hxy hak hkb
      simpa [a, C] using hk
    have hlocal := smoothHeathBrownThetaFactor_local_of_prefix
      (a := a) (b := b) hab hS hX m
      (f := smoothHeathBrownResidueMellinTerm q r t) hC hprefix
    simpa [a, b, C, mul_assoc, mul_left_comm, mul_comm] using hlocal
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    rw [show Finset.Ioc (Nat.floor x) (Nat.floor y) = ∅ by
      simpa [a, b] using (Finset.Ioc_eq_empty_of_le hba)]
    simp
    have hbound : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- The source normalized logarithmic factor on every arbitrary subinterval
of `[L,2L]`, with the actual single-residue periodic indicator.  The only
additional finite loss is the exact variation of `log n/(4 log X)`. -/
theorem smoothHeathBrownLogFactor_periodic_interval
    {alpha A X L T0 t S x y : ℝ} {q : ℕ} {r : ℤ} (m : ℕ)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (hX : 3 ≤ X) (hLlower : X ^ alpha ≤ L) (hLupper : L ≤ X)
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ X ^ (alpha / 2))
    (hT0 : 1 ≤ T0) (hT0t : T0 ≤ |t|) (htX : |t| ≤ X ^ A)
    (hxL : L ≤ x) (hxy : x ≤ y) (hy2 : y ≤ 2 * L) (hS : 0 < S) :
    ‖∑ n ∈ Finset.Ioc (Nat.floor x) (Nat.floor y),
      smoothHeathBrownResidueMellinTerm q r t n *
        smoothHeathBrownThetaLogOuterWeight S X m n‖ ≤
      6 * periodicLogPhaseConstant alpha A * Real.sqrt L *
        (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ)) := by
  let C : ℝ := periodicLogPhaseConstant alpha A * Real.sqrt L *
    (X ^ (-(periodicLogPhaseSaving alpha A)) + T0 ^ (-1 / 2 : ℝ))
  have hXpos : 0 < X := by linarith
  have hT0pos : 0 < T0 := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (smoothHeathBrownPeriodicPhaseConstant_nonneg alpha A)
        (Real.sqrt_nonneg _))
      (add_nonneg (Real.rpow_nonneg hXpos.le _)
        (Real.rpow_nonneg hT0pos.le _))
  let a : ℕ := Nat.floor x
  let b : ℕ := Nat.floor y
  by_cases hab : a < b
  · have hprefix : ∀ k, a < k → k ≤ b →
        ‖smoothSmallGroupPrefix a
          (smoothHeathBrownResidueMellinTerm q r t) k‖ ≤ C := by
      intro k hak hkb
      have hk := smoothHeathBrownResiduePrefix_bound (r := r)
        halpha halpha1 hA hX hLlower hLupper hq hqBound hT0 hT0t htX
        hxL hy2 hxy hak hkb
      simpa [a, C] using hk
    have hb16 : (b : ℝ) ≤ 16 * X := by
      calc
        (b : ℝ) = Nat.floor y := rfl
        _ ≤ y := Nat.floor_le (by linarith [hxL, hxy, hLlower])
        _ ≤ 2 * L := hy2
        _ ≤ 2 * X := mul_le_mul_of_nonneg_left hLupper (by norm_num)
        _ ≤ 16 * X := by nlinarith [hX]
    have hlocal := smoothHeathBrownLogFactor_local_of_prefix
      (a := a) (b := b) hab hS hX m hb16
      (f := smoothHeathBrownResidueMellinTerm q r t) hC hprefix
    simpa [a, b, C, mul_assoc, mul_left_comm, mul_comm] using hlocal
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    rw [show Finset.Ioc (Nat.floor x) (Nat.floor y) = ∅ by
      simpa [a, b] using (Finset.Ioc_eq_empty_of_le hba)]
    simp
    have hbound : 0 ≤ 6 * C := mul_nonneg (by norm_num) hC
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hbound

#print axioms smoothHeathBrownThetaFactor_local_of_prefix
#print axioms smoothHeathBrownLogFactor_local_of_prefix
#print axioms smoothHeathBrownThetaFactor_periodic_interval
#print axioms smoothHeathBrownLogFactor_periodic_interval

end FractionalPrimes.Literature.DirichletAdapter

end

