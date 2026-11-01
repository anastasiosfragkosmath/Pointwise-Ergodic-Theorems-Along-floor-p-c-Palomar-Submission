module

public import FractionalPrimes.Literature.Twisted.PeriodicLogPhaseDirichletBound
public import FractionalPrimes.Literature.Twisted.SmoothDyadicCutoff
public import Mathlib.Algebra.BigOperators.Module

/-!
# Finite cancellation transfer for a selected smooth factor

This file isolates the discrete Abel step used to insert the sampled smooth
dyadic cutoff into a periodic-factor interval estimate.  The interval is the
source half-open natural interval `(a,b]`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

/-- The initial prefix of a sequence after deleting all indices at or below
the left endpoint `a`. -/
def smoothSmallGroupPrefix (a : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (if a < j then f j else 0)

private theorem smoothSmallGroup_sum_Ico_sub_next
    (a b : ℕ) (hab : a ≤ b) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico a b, (f n - f (n + 1))) = f a - f b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · calc
          (∑ n ∈ Finset.Ico a (b + 1), (f n - f (n + 1))) =
              (∑ n ∈ Finset.Ico a b, (f n - f (n + 1))) +
                (f b - f (b + 1)) := by
                  rw [Finset.sum_Ico_succ_top hab']
          _ = (f a - f b) + (f b - f (b + 1)) := by rw [ih a hab']
          _ = f a - f (b + 1) := by ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- The discrete variation of the source smooth dyadic profile, sampled at
`n/N`, is at most two on every finite interval. -/
theorem smoothSmallGroupThetaSampleVariation
    {N : ℝ} (hN : 0 < N) {a b : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / N) -
        smoothDyadicTheta ((n : ℝ) / N)|) ≤ 2 := by
  have hsets : Finset.Ioc a (b - 1) = Finset.Ico (a + 1) b := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hdrop (c : ℕ) :
      0 ≤ smoothDyadicEta ((c : ℝ) / N) -
        smoothDyadicEta (((c + 1 : ℕ) : ℝ) / N) := by
    apply sub_nonneg.mpr
    apply smoothDyadicEta_antitone
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast Nat.le_succ c
  have hdrop2 (c : ℕ) :
      0 ≤ smoothDyadicEta (2 * ((c : ℝ) / N)) -
        smoothDyadicEta (2 * (((c + 1 : ℕ) : ℝ) / N)) := by
    apply sub_nonneg.mpr
    apply smoothDyadicEta_antitone
    have hc : (c : ℝ) / N ≤ ((c + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast Nat.le_succ c
    linarith
  have hterm (n : ℕ) :
      |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / N) -
        smoothDyadicTheta ((n : ℝ) / N)| ≤
      (smoothDyadicEta ((n : ℝ) / N) -
          smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N)) +
        (smoothDyadicEta (2 * ((n : ℝ) / N)) -
          smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N))) := by
    have hmono : (n : ℝ) / N ≤ ((n + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast Nat.le_succ n
    have htheta :
        smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / N) -
          smoothDyadicTheta ((n : ℝ) / N) =
        (smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N) -
            smoothDyadicEta ((n : ℝ) / N)) -
          (smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N)) -
            smoothDyadicEta (2 * ((n : ℝ) / N))) := by
      simp [smoothDyadicTheta]
      ring
    rw [htheta]
    calc
      |(smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N) -
          smoothDyadicEta ((n : ℝ) / N)) -
        (smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N)) -
          smoothDyadicEta (2 * ((n : ℝ) / N)))| ≤
        |smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N) -
          smoothDyadicEta ((n : ℝ) / N)| +
        |smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N)) -
          smoothDyadicEta (2 * ((n : ℝ) / N))| := abs_sub _ _
      _ = (smoothDyadicEta ((n : ℝ) / N) -
          smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N)) +
        (smoothDyadicEta (2 * ((n : ℝ) / N)) -
          smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N))) := by
            rw [abs_of_nonpos (sub_nonpos.mpr
              (smoothDyadicEta_antitone hmono))]
            rw [abs_of_nonpos (sub_nonpos.mpr
              (smoothDyadicEta_antitone (by nlinarith [hmono])))]
            ring
  have hsum1 :
      (∑ n ∈ Finset.Ico (a + 1) b,
        (smoothDyadicEta ((n : ℝ) / N) -
          smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N))) ≤ 1 := by
    rw [smoothSmallGroup_sum_Ico_sub_next]
    · have hupper := smoothDyadicEta_le_one (((a + 1 : ℕ) : ℝ) / N)
      have hlower := smoothDyadicEta_nonneg ((b : ℝ) / N)
      linarith
    · omega
  have hsum2 :
      (∑ n ∈ Finset.Ico (a + 1) b,
        (smoothDyadicEta (2 * ((n : ℝ) / N)) -
          smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N)))) ≤ 1 := by
    rw [smoothSmallGroup_sum_Ico_sub_next]
    · have hupper := smoothDyadicEta_le_one
        (2 * (((a + 1 : ℕ) : ℝ) / N))
      have hlower := smoothDyadicEta_nonneg (2 * ((b : ℝ) / N))
      linarith
    · omega
  rw [hsets]
  calc
    (∑ n ∈ Finset.Ico (a + 1) b,
        |smoothDyadicTheta (((n + 1 : ℕ) : ℝ) / N) -
          smoothDyadicTheta ((n : ℝ) / N)|) ≤
      ∑ n ∈ Finset.Ico (a + 1) b,
        ((smoothDyadicEta ((n : ℝ) / N) -
            smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N)) +
          (smoothDyadicEta (2 * ((n : ℝ) / N)) -
            smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N)))) := by
              apply Finset.sum_le_sum
              intro n hn
              exact hterm n
    _ = (∑ n ∈ Finset.Ico (a + 1) b,
          (smoothDyadicEta ((n : ℝ) / N) -
            smoothDyadicEta (((n + 1 : ℕ) : ℝ) / N))) +
        ∑ n ∈ Finset.Ico (a + 1) b,
          (smoothDyadicEta (2 * ((n : ℝ) / N)) -
            smoothDyadicEta (2 * (((n + 1 : ℕ) : ℝ) / N))) := by
              rw [Finset.sum_add_distrib]
    _ ≤ 2 := by linarith

/-- The source theta cutoff sampled at the natural points `n/N`, viewed as a
complex weight for finite Dirichlet sums. -/
noncomputable def smoothSmallGroupThetaWeight (N : ℝ) (n : ℕ) : ℂ :=
  (smoothDyadicTheta ((n : ℝ) / N) : ℂ)

/-- The sampled complex cutoff has terminal modulus at most one. -/
theorem smoothSmallGroupThetaWeight_norm_le_one (N : ℝ) (n : ℕ) :
    ‖smoothSmallGroupThetaWeight N n‖ ≤ 1 := by
  rw [smoothSmallGroupThetaWeight, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (smoothDyadicTheta_nonneg _)]
  exact smoothDyadicTheta_le_one _

/-- The sampled complex cutoff has discrete total variation at most two. -/
theorem smoothSmallGroupThetaWeightVariation
    {N : ℝ} (hN : 0 < N) {a b : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ioc a (b - 1),
      ‖smoothSmallGroupThetaWeight N (n + 1) -
        smoothSmallGroupThetaWeight N n‖) ≤ 2 := by
  simpa [smoothSmallGroupThetaWeight, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using
    (smoothSmallGroupThetaSampleVariation hN hab)

/-- Finite Abel summation transfers a uniform bound for every initial
subinterval sum on `(a,b]` to a weighted sum, with the exact terminal value
and discrete variation of the weight. -/
theorem smoothSmallGroupFiniteAbelTransfer
    {a b : ℕ} (hab : a < b) (f w : ℕ → ℂ) {C V : ℝ}
    (hC : 0 ≤ C)
    (hprefix : ∀ n, a < n → n ≤ b →
      ‖smoothSmallGroupPrefix a f n‖ ≤ C)
    (hvariation : ‖w b‖ +
      ∑ n ∈ Finset.Ioc a (b - 1), ‖w (n + 1) - w n‖ ≤ V) :
    ‖∑ n ∈ Finset.Ioc a b, f n * w n‖ ≤ C * V := by
  classical
  let g : ℕ → ℂ := fun n => if a < n then f n else 0
  let G : ℕ → ℂ := fun n => ∑ j ∈ Finset.range n, g j
  have habel := Finset.sum_Ioc_by_parts (m := a) (n := b)
    (f := w) (g := g) hab
  have hsum :
      (∑ n ∈ Finset.Ioc a b, f n * w n) =
        w b * G (b + 1) - w (a + 1) * G (a + 1) -
          ∑ n ∈ Finset.Ioc a (b - 1),
            (w (n + 1) - w n) * G (n + 1) := by
    calc
      (∑ n ∈ Finset.Ioc a b, f n * w n) =
          ∑ n ∈ Finset.Ioc a b, w n • g n := by
            apply Finset.sum_congr rfl
            intro n hn
            have hna : a < n := Finset.mem_Ioc.mp hn |>.1
            simp [g, hna, smul_eq_mul, mul_comm]
      _ = w b • G (b + 1) - w (a + 1) • G (a + 1) -
          ∑ n ∈ Finset.Ioc a (b - 1),
            (w (n + 1) - w n) • G (n + 1) := by
              simpa [G] using habel
      _ = _ := by simp only [smul_eq_mul]
  have hGa : G (a + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hna : n ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp [g, Nat.not_lt.mpr hna]
  have hG (n : ℕ) (han : a < n) (hnb : n ≤ b) :
      ‖G (n + 1)‖ ≤ C := by
    simpa [G, g, smoothSmallGroupPrefix] using hprefix n han hnb
  have hEnd : ‖G (b + 1)‖ ≤ C := hG b hab le_rfl
  have hcorrNorm :
      ‖∑ n ∈ Finset.Ioc a (b - 1),
          (w (n + 1) - w n) * G (n + 1)‖ ≤
        ∑ n ∈ Finset.Ioc a (b - 1),
          ‖(w (n + 1) - w n) * G (n + 1)‖ := norm_sum_le _ _
  have hcorrBound :
      (∑ n ∈ Finset.Ioc a (b - 1),
          (‖w (n + 1) - w n‖ * ‖G (n + 1)‖)) ≤
        ∑ n ∈ Finset.Ioc a (b - 1),
          (‖w (n + 1) - w n‖ * C) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left
      (hG n (Finset.mem_Ioc.mp hn |>.1)
        (le_trans (Finset.mem_Ioc.mp hn |>.2) (Nat.sub_le _ _)))
      (norm_nonneg _)
  calc
    ‖∑ n ∈ Finset.Ioc a b, f n * w n‖ =
        ‖w b * G (b + 1) - w (a + 1) * G (a + 1) -
          ∑ n ∈ Finset.Ioc a (b - 1),
            (w (n + 1) - w n) * G (n + 1)‖ := by rw [hsum]
    _ ≤ ‖w b * G (b + 1)‖ +
          ‖w (a + 1) * G (a + 1)‖ +
          ‖∑ n ∈ Finset.Ioc a (b - 1),
            (w (n + 1) - w n) * G (n + 1)‖ := by
          calc
            _ ≤ ‖w b * G (b + 1) - w (a + 1) * G (a + 1)‖ +
                ‖∑ n ∈ Finset.Ioc a (b - 1),
                  (w (n + 1) - w n) * G (n + 1)‖ := norm_sub_le _ _
            _ ≤ (‖w b * G (b + 1)‖ +
                  ‖w (a + 1) * G (a + 1)‖) +
                ‖∑ n ∈ Finset.Ioc a (b - 1),
                  (w (n + 1) - w n) * G (n + 1)‖ := by
                    gcongr
                    exact norm_sub_le _ _
            _ = _ := by ring
    _ = ‖w b‖ * ‖G (b + 1)‖ +
          ‖w (a + 1) * G (a + 1)‖ +
          ‖∑ n ∈ Finset.Ioc a (b - 1),
            (w (n + 1) - w n) * G (n + 1)‖ := by rw [norm_mul]
    _ = ‖w b‖ * ‖G (b + 1)‖ +
          ‖∑ n ∈ Finset.Ioc a (b - 1),
            (w (n + 1) - w n) * G (n + 1)‖ := by simp [hGa, G]
    _ ≤ ‖w b‖ * C +
          ∑ n ∈ Finset.Ioc a (b - 1),
            ‖(w (n + 1) - w n) * G (n + 1)‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hEnd (norm_nonneg _)) hcorrNorm
    _ = ‖w b‖ * C +
          ∑ n ∈ Finset.Ioc a (b - 1),
            (‖w (n + 1) - w n‖ * ‖G (n + 1)‖) := by
          rw [Finset.sum_congr rfl]
          intro n hn
          rw [norm_mul]
    _ ≤ ‖w b‖ * C +
          ∑ n ∈ Finset.Ioc a (b - 1),
            (‖w (n + 1) - w n‖ * C) := by
          exact add_le_add le_rfl hcorrBound
    _ = C * (‖w b‖ +
          ∑ n ∈ Finset.Ioc a (b - 1), ‖w (n + 1) - w n‖) := by
          rw [← Finset.sum_mul]
          ring
    _ ≤ C * V := mul_le_mul_of_nonneg_left hvariation hC

/-- The exact sampled smooth dyadic cutoff costs at most a factor of three
when inserted into any local cancellation estimate on `(a,b]`. -/
theorem smoothSmallGroupThetaFiniteAbelTransfer
    {a b : ℕ} (hab : a < b) {N : ℝ} (hN : 0 < N)
    (f : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C)
    (hprefix : ∀ n, a < n → n ≤ b →
      ‖smoothSmallGroupPrefix a f n‖ ≤ C) :
    ‖∑ n ∈ Finset.Ioc a b,
        f n * smoothSmallGroupThetaWeight N n‖ ≤ 3 * C := by
  have hvariation := smoothSmallGroupThetaWeightVariation hN hab
  have hterminal := smoothSmallGroupThetaWeight_norm_le_one N b
  have hweightvariation :
      ‖smoothSmallGroupThetaWeight N b‖ +
        ∑ n ∈ Finset.Ioc a (b - 1),
          ‖smoothSmallGroupThetaWeight N (n + 1) -
            smoothSmallGroupThetaWeight N n‖ ≤ 3 := by
    linarith
  calc
    ‖∑ n ∈ Finset.Ioc a b,
        f n * smoothSmallGroupThetaWeight N n‖ ≤ C * 3 :=
      smoothSmallGroupFiniteAbelTransfer hab f
        (smoothSmallGroupThetaWeight N) hC hprefix hweightvariation
    _ = 3 * C := by ring

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupFiniteAbelTransfer
#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupThetaSampleVariation
#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupThetaWeightVariation
#print axioms FractionalPrimes.Literature.Twisted.smoothSmallGroupThetaFiniteAbelTransfer
