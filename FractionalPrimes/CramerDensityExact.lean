module

public import FractionalPrimes.RosserWeights
public import FractionalPrimes.CramerDensityKernel
public import FractionalPrimes.CramerFiniteSum

/-!
# The explicit strict-cutoff Cramér Euler-product bound

This proves blueprint lemma `lc:product` with its approved constants and the
strict prime cutoff already used by `paperCramerDensity`.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes

noncomputable section

private def thetaPrimeCoefficient (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) else 0

private theorem thetaPrimeCoefficient_partial_sum (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, thetaPrimeCoefficient n) = paperTheta x := by
  simpa [thetaPrimeCoefficient, Finset.sum_filter] using
    (paperTheta_eq_sum_primes x).symm

private theorem reciprocalThetaKernel_abel {z : ℝ} (hz : 2 ≤ z) :
    (∑ n ∈ Finset.Ioc 2 ⌊z⌋₊,
        reciprocalThetaKernel (n : ℝ) * thetaPrimeCoefficient n) =
      reciprocalThetaKernel z * paperTheta z -
        reciprocalThetaKernel 2 * paperTheta 2 -
          ∫ t in Set.Ioc 2 z,
            deriv reciprocalThetaKernel t * paperTheta t := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) z,
      DifferentiableAt ℝ reciprocalThetaKernel t := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
    have hdiffId : DifferentiableAt ℝ (fun x : ℝ => x) t := differentiableAt_id
    have hdiffLog : DifferentiableAt ℝ Real.log t := Real.differentiableAt_log htne
    exact (hdiffId.mul hdiffLog).inv (mul_ne_zero htne hlogne)
  have hint := reciprocalThetaKernel_deriv_integrable hz
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := thetaPrimeCoefficient) (f := reciprocalThetaKernel)
    (by norm_num : (0 : ℝ) ≤ 2) hz hdiff hint
  simp_rw [thetaPrimeCoefficient_partial_sum] at habel
  have hfloor : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hfloor] at habel
  exact habel

private theorem reciprocalPrimeSum_eq_theta_integral {z : ℝ} (hz : 2 ≤ z) :
    (∑ n ∈ Finset.Icc 0 ⌊z⌋₊,
        (n : ℝ)⁻¹ * primeIndicator n) =
      paperTheta z / (z * Real.log z) +
        ∫ t in Set.Ioc 2 z,
          paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  have hN : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hpartition : Finset.Icc 0 ⌊z⌋₊ =
      Finset.Icc (0 : ℕ) 2 ∪ Finset.Ioc (2 : ℕ) ⌊z⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc (0 : ℕ) 2) (Finset.Ioc (2 : ℕ) ⌊z⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro n hn₁ hn₂
    simp only [Finset.mem_Icc] at hn₁
    simp only [Finset.mem_Ioc] at hn₂
    omega
  have hlow :
      (∑ n ∈ Finset.Icc (0 : ℕ) 2, (n : ℝ)⁻¹ * primeIndicator n) = (2 : ℝ)⁻¹ := by
    norm_num [primeIndicator, Finset.sum_Icc_succ_top]
  have hsplit :
      (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, (n : ℝ)⁻¹ * primeIndicator n) =
        (2 : ℝ)⁻¹ +
          ∑ n ∈ Finset.Ioc (2 : ℕ) ⌊z⌋₊, (n : ℝ)⁻¹ * primeIndicator n := by
    calc
      _ = ∑ n ∈ Finset.Icc (0 : ℕ) 2 ∪ Finset.Ioc (2 : ℕ) ⌊z⌋₊,
          (n : ℝ)⁻¹ * primeIndicator n := by rw [hpartition]
      _ = (∑ n ∈ Finset.Icc (0 : ℕ) 2, (n : ℝ)⁻¹ * primeIndicator n) +
          ∑ n ∈ Finset.Ioc (2 : ℕ) ⌊z⌋₊, (n : ℝ)⁻¹ * primeIndicator n :=
            Finset.sum_union hdisj
      _ = _ := by rw [hlow]
  have hterm : ∀ n ∈ Finset.Ioc (2 : ℕ) ⌊z⌋₊,
      reciprocalThetaKernel (n : ℝ) * thetaPrimeCoefficient n =
        (n : ℝ)⁻¹ * primeIndicator n := by
    intro n hn
    have hn2 : 2 < n := (Finset.mem_Ioc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    by_cases hprime : n.Prime
    · have hlogpos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      simp [thetaPrimeCoefficient, primeIndicator, hprime, reciprocalThetaKernel]
      field_simp [ne_of_gt hnpos, ne_of_gt hlogpos]
    · simp [thetaPrimeCoefficient, primeIndicator, hprime]
  have hleft :
      (∑ n ∈ Finset.Ioc (2 : ℕ) ⌊z⌋₊,
        reciprocalThetaKernel (n : ℝ) * thetaPrimeCoefficient n) =
        ∑ n ∈ Finset.Ioc (2 : ℕ) ⌊z⌋₊, (n : ℝ)⁻¹ * primeIndicator n := by
    apply Finset.sum_congr rfl
    exact fun n hn => hterm n hn
  have htheta2 : paperTheta 2 = Real.log 2 := by
    rw [paperTheta_eq_sum_primes]
    have hprimes : (Finset.Icc (0 : ℕ) 2).filter Nat.Prime = {2} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp0, hp2⟩, hprime⟩
        have hpLower : 2 ≤ p := hprime.two_le
        omega
      · intro hp
        subst p
        exact ⟨⟨by omega, by omega⟩, Nat.prime_two⟩
    rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num, hprimes]
    simp
  have hboundary : reciprocalThetaKernel 2 * paperTheta 2 = (2 : ℝ)⁻¹ := by
    rw [htheta2]
    dsimp [reciprocalThetaKernel]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hInt :
      (∫ t in Set.Ioc 2 z,
          deriv reciprocalThetaKernel t * paperTheta t) =
        -(∫ t in Set.Ioc 2 z,
          paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    change deriv reciprocalThetaKernel t * paperTheta t =
      -(paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
    rw [reciprocalThetaKernel_deriv ht1]
    ring
  have habel := reciprocalThetaKernel_abel hz
  calc
    _ = (2 : ℝ)⁻¹ +
        ∑ n ∈ Finset.Ioc 2 ⌊z⌋₊, (n : ℝ)⁻¹ * primeIndicator n := hsplit
    _ = (2 : ℝ)⁻¹ +
        ∑ n ∈ Finset.Ioc 2 ⌊z⌋₊,
          reciprocalThetaKernel (n : ℝ) * thetaPrimeCoefficient n := by rw [← hleft]
    _ = (2 : ℝ)⁻¹ + (reciprocalThetaKernel z * paperTheta z -
        reciprocalThetaKernel 2 * paperTheta 2 -
          ∫ t in Set.Ioc 2 z,
            deriv reciprocalThetaKernel t * paperTheta t) := by rw [habel]
    _ = paperTheta z / (z * Real.log z) +
        ∫ t in Set.Ioc 2 z,
          paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
      rw [hboundary, hInt]
      simp [reciprocalThetaKernel]
      ring

private theorem reciprocalTheta_integral_bound {z : ℝ} (hz : 2 ≤ z) :
    (∫ t in Set.Ioc 2 z,
        paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) ≤
      4 * Real.log 2 *
        (Real.log (Real.log z / Real.log 2) + (Real.log 2)⁻¹ - (Real.log z)⁻¹) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith [hz])
  let base : ℝ → ℝ := fun t => paperTheta t / (t * (Real.log t) ^ 2)
  let weight : ℝ → ℝ := fun t => (Real.log t + 1) / t
  have hbase : IntegrableOn base (Set.Ioc 2 z) volume := by
    have hbase' : IntegrableOn base (Set.Icc 2 z) volume := by
      simpa [base, paperTheta] using
        (Chebyshev.integrableOn_theta_div_id_mul_log_sq (x := z))
    exact hbase'.mono_set (by
      intro t ht
      exact ⟨ht.1.le, ht.2⟩)
  have hlogcont : ContinuousOn Real.log (Set.Icc 2 z) := by
    refine ContinuousOn.mono Real.continuousOn_log ?_
    intro t ht
    exact ne_of_gt (by linarith [ht.1])
  have htne : ∀ t ∈ Set.Icc 2 z, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hweight : ContinuousOn weight (Set.Icc 2 z) := by
    dsimp [weight]
    exact (hlogcont.add continuousOn_const).div continuousOn_id fun t ht => htne t ht
  have hprod : IntegrableOn (fun t => base t * weight t)
      (Set.Ioc 2 z) volume :=
    hbase.mul_continuousOn_of_subset hweight measurableSet_Ioc isCompact_Icc
      (by intro t ht; exact ⟨ht.1.le, ht.2⟩)
  have hInt : IntegrableOn
      (fun t => paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Ioc 2 z) volume := by
    apply hprod.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp [base, weight]
    have htpos : 0 < t := by linarith [ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
    <;> ring
  let majorant : ℝ → ℝ := fun t =>
    4 * Real.log 2 * ((Real.log t + 1) / (t * (Real.log t) ^ 2))
  have hmajorant_cont : ContinuousOn majorant (Set.Icc 2 z) := by
    have hlogpos : ∀ t ∈ Set.Icc (2 : ℝ) z, Real.log t ≠ 0 := by
      intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hdenne : ∀ t ∈ Set.Icc (2 : ℝ) z,
        t * (Real.log t) ^ 2 ≠ 0 := by
      intro t ht
      exact mul_ne_zero (htne t ht) (pow_ne_zero 2 (hlogpos t ht))
    have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Icc 2 z) :=
      hlogcont.add continuousOn_const
    have hden : ContinuousOn (fun t : ℝ => t * (Real.log t) ^ 2) (Set.Icc 2 z) :=
      continuousOn_id.mul (hlogcont.pow 2)
    dsimp [majorant]
    exact continuousOn_const.mul (hnum.div hden hdenne)
  have hmaj : IntegrableOn majorant (Set.Ioc 2 z) volume := by
    have hmaj' : IntegrableOn majorant (Set.Icc 2 z) volume :=
      hmajorant_cont.integrableOn_compact isCompact_Icc
    exact hmaj'.mono_set (by
      intro t ht
      exact ⟨ht.1.le, ht.2⟩)
  have hpoint : ∀ t ∈ Set.Ioc 2 z,
      paperTheta t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤ majorant t := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have htheta := paperTheta_upper_bound ht1
    have hfactor : 0 ≤ (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by
      have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      positivity
    calc
      _ ≤ (4 * Real.log 2 * t) *
          ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
        mul_le_mul_of_nonneg_right htheta hfactor
      _ = majorant t := by
        dsimp [majorant]
        have htpos : t ≠ 0 := ne_of_gt (by linarith [ht.1])
        have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
        field_simp [htpos, hlogne]
        <;> ring
  have hmono := setIntegral_mono_on hInt hmaj measurableSet_Ioc hpoint
  conv_rhs at hmono => rw [← intervalIntegral.integral_of_le hz]
  rw [intervalIntegral.integral_const_mul] at hmono
  have hweight_eval :
      (∫ t in (2 : ℝ)..z, (Real.log t + 1) / (t * (Real.log t) ^ 2)) =
        Real.log (Real.log z) - Real.log (Real.log 2) +
          (Real.log 2)⁻¹ - (Real.log z)⁻¹ := by
    have hdecomp : ∀ t ∈ Set.uIcc (2 : ℝ) z,
        (Real.log t + 1) / (t * (Real.log t) ^ 2) =
          t⁻¹ / Real.log t + t⁻¹ / (Real.log t) ^ 2 := by
      intro t ht
      have ht_ge_two : 2 ≤ t := by
        rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, hz]
      have htpos : 0 < t := by linarith [ht_ge_two]
      have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht_ge_two])
      field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
      <;> ring
    have hlogne : ∀ t ∈ Set.Icc (2 : ℝ) z, Real.log t ≠ 0 := by
      intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hInvCont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 2 z) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      change t ≠ 0
      exact ne_of_gt (by linarith [ht.1])
    have hInvLogCont : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t)
        (Set.Icc 2 z) :=
      hInvCont.div hlogcont hlogne
    have hInvLogSqCont : ContinuousOn (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2)
        (Set.Icc 2 z) :=
      hInvCont.div (hlogcont.pow 2) (fun t ht => pow_ne_zero 2 (hlogne t ht))
    have hInvLogInt : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t)
        volume 2 z := hInvLogCont.intervalIntegrable_of_Icc hz
    have hInvLogSqInt : IntervalIntegrable (fun t : ℝ => t⁻¹ / (Real.log t) ^ 2)
        volume 2 z := hInvLogSqCont.intervalIntegrable_of_Icc hz
    calc
      _ = (∫ t in (2 : ℝ)..z, t⁻¹ / Real.log t) +
          ∫ t in (2 : ℝ)..z, t⁻¹ / (Real.log t) ^ 2 := by
            rw [← intervalIntegral.integral_add hInvLogInt hInvLogSqInt]
            apply intervalIntegral.integral_congr
            intro t ht
            exact hdecomp t (Set.uIcc_of_le hz ▸ ht)
      _ = _ := by
        rw [integral_inv_div_log (by norm_num) (by linarith [hz]),
          integral_inv_div_log_sq (by norm_num) (by linarith [hz])]
        ring
  rw [hweight_eval] at hmono
  have hratio_log :
      Real.log (Real.log z / Real.log 2) =
        Real.log (Real.log z) - Real.log (Real.log 2) := by
    rw [Real.log_div (ne_of_gt hlogz) (ne_of_gt hlog2)]
  rw [← hratio_log] at hmono
  simpa [majorant] using hmono

private theorem strictPrimeReciprocalSum_le {w : ℝ} (hw : 2 ≤ w) :
    (∑ p ∈ sievePrimesBelow w, 1 / (p : ℝ)) ≤
      4 * Real.log (Real.log w) + 12 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith [hw])
  have hlogw_ge : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hratio_ge : 1 ≤ Real.log w / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by linarith)
  have hratio_nonneg : 0 ≤ Real.log (Real.log w / Real.log 2) :=
    Real.log_nonneg hratio_ge
  have hlogratio :
      Real.log (Real.log w / Real.log 2) =
        Real.log (Real.log w) - Real.log (Real.log 2) := by
    rw [Real.log_div (ne_of_gt hlogw) (ne_of_gt hlog2)]
  have htheta := paperTheta_upper_bound (x := w) (by linarith [hw])
  have hboundary : paperTheta w / (w * Real.log w) ≤
      4 * Real.log 2 / Real.log w := by
    apply (div_le_iff₀ (mul_pos (by linarith [hw]) hlogw)).2
    calc
      paperTheta w ≤ 4 * Real.log 2 * w := htheta
      _ = (4 * Real.log 2 / Real.log w) * (w * Real.log w) := by
        field_simp [ne_of_gt hlogw]
        <;> ring
  have hIntegral := reciprocalTheta_integral_bound hw
  have hformula := reciprocalPrimeSum_eq_theta_integral hw
  have hfull :
      (∑ n ∈ Finset.Icc 0 ⌊w⌋₊,
          (n : ℝ)⁻¹ * primeIndicator n) ≤
        4 * Real.log (Real.log w) + 12 := by
    rw [hformula]
    calc
      _ ≤ 4 * Real.log 2 / Real.log w +
          4 * Real.log 2 *
            (Real.log (Real.log w / Real.log 2) +
              (Real.log 2)⁻¹ - (Real.log w)⁻¹) :=
        add_le_add hboundary hIntegral
      _ = 4 * Real.log 2 * Real.log (Real.log w / Real.log 2) + 4 := by
        have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
        field_simp [hlog2ne, ne_of_gt hlogw]
        <;> ring
      _ ≤ 4 * Real.log (Real.log w) + 12 := by
        have hlog2bounds := sieveLogTwo_bounds
        have hlog23 : -1 ≤ Real.log (2 / 3 : ℝ) := by
          have hlog32 : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
            norm_num at h ⊢
            exact h
          have hinv : (2 / 3 : ℝ) = (3 / 2)⁻¹ := by norm_num
          rw [hinv, Real.log_inv]
          linarith
        have hloglog2 : -1 ≤ Real.log (Real.log 2) := by
          calc
            -1 ≤ Real.log (2 / 3 : ℝ) := hlog23
            _ ≤ Real.log (Real.log 2) :=
              Real.log_le_log (by norm_num) hlog2bounds.1
        have hcoeff : 4 * Real.log 2 ≤ 4 := by
          nlinarith [hlog2bounds.2]
        calc
          4 * Real.log 2 * Real.log (Real.log w / Real.log 2) + 4 ≤
              4 * Real.log (Real.log w / Real.log 2) + 4 := by
                nlinarith [hratio_nonneg]
          _ = 4 * Real.log (Real.log w) -
                4 * Real.log (Real.log 2) + 4 := by rw [hlogratio]; ring
          _ ≤ 4 * Real.log (Real.log w) + 8 := by nlinarith [hloglog2]
          _ ≤ 4 * Real.log (Real.log w) + 12 := by norm_num
  have hN : 2 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  have hsub : sievePrimesBelow w ⊆ (Finset.Icc 0 ⌊w⌋₊).filter Nat.Prime := by
    intro p hp
    rw [sievePrimesBelow_iff] at hp
    rcases hp with ⟨hp, hpw⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (by exact_mod_cast hpw.le)⟩, hp⟩
  have hfullFilter :
      (∑ p ∈ (Finset.Icc 0 ⌊w⌋₊).filter Nat.Prime, 1 / (p : ℝ)) ≤
        4 * Real.log (Real.log w) + 12 := by
    rw [filtered_reciprocal_sum_eq_primeIndicator_weighted_sum]
    exact hfull
  calc
    (∑ p ∈ sievePrimesBelow w, 1 / (p : ℝ)) ≤
        ∑ p ∈ (Finset.Icc 0 ⌊w⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hp hnot
          positivity
    _ ≤ 4 * Real.log (Real.log w) + 12 := hfullFilter

theorem paperCramerDensity_lc_product {w : ℝ} (hw : 2 ≤ w) :
    1 ≤ paperCramerDensity w ∧
      paperCramerDensity w ≤ Real.exp 13 * (Real.log w) ^ (4 : ℕ) := by
  have hN : 2 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  let S := sievePrimesBelow w
  have hSN : S ⊆ Finset.Icc 2 ⌊w⌋₊ := by
    intro p hp
    rw [sievePrimesBelow_iff] at hp
    rcases hp with ⟨hprime, hpw⟩
    exact Finset.mem_Icc.mpr
      ⟨hprime.two_le, Nat.le_floor (by exact_mod_cast hpw.le)⟩
  have hratio : paperCramerDensity w =
      ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
    calc
      paperCramerDensity w = (sieveDensityProduct w)⁻¹ := by
        change (sievePrimeProduct w : ℝ) /
          (Nat.totient (sievePrimeProduct w) : ℝ) = _
        exact sievePrimeRatio_eq_inv_density
      _ = (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ := by
        congr 1
      _ = ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
        rw [← Finset.prod_inv_distrib]
      _ = ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        field_simp
        <;> ring
  have hlogprod :
      Real.log (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) =
        ∑ p ∈ S, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    apply Real.log_prod
    intro p hp
    apply div_ne_zero
    · have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      exact ne_of_gt (by linarith)
    · have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      exact sub_ne_zero.mpr (by
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith)
  have hprod_pos : 0 < ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_pos fun p hp => div_pos (by
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith) (by
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (hSN hp)).1
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith)
  have hlogsum :
      (∑ p ∈ S, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
        13 + 4 * Real.log (Real.log w) := by
    calc
      _ ≤ (∑ p ∈ S, 1 / (p : ℝ)) + 1 :=
        sum_log_prime_ratio_le_reciprocals_add_one hN hSN
      _ ≤ (4 * Real.log (Real.log w) + 12) + 1 := by
        have hrecip := strictPrimeReciprocalSum_le hw
        simpa [S] using add_le_add_right hrecip 1
      _ = 13 + 4 * Real.log (Real.log w) := by ring
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith [hw])
  have hpow : Real.exp (4 * Real.log (Real.log w)) =
      (Real.log w) ^ (4 : ℕ) := by
    calc
      Real.exp (4 * Real.log (Real.log w)) =
          Real.exp ((4 : ℕ) * Real.log (Real.log w)) := by norm_num
      _ = Real.exp (Real.log (Real.log w)) ^ 4 := Real.exp_nat_mul _ _
      _ = (Real.log w) ^ 4 := by rw [Real.exp_log hlogw]
  have hupperProduct :
      (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) ≤
        Real.exp 13 * (Real.log w) ^ (4 : ℕ) := by
    have hlogBound :
        Real.log (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) ≤
          13 + 4 * Real.log (Real.log w) := by
      rw [hlogprod]
      exact hlogsum
    calc
      _ = Real.exp (Real.log (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1))) :=
        (Real.exp_log hprod_pos).symm
      _ ≤ Real.exp (13 + 4 * Real.log (Real.log w)) :=
        Real.exp_le_exp.mpr hlogBound
      _ = Real.exp 13 * Real.exp (4 * Real.log (Real.log w)) := by rw [Real.exp_add]
      _ = Real.exp 13 * (Real.log w) ^ (4 : ℕ) := by rw [hpow]
  constructor
  · exact (paperCramerDensity_bounds hw).1
  · rw [hratio]
    exact hupperProduct

end
end FractionalPrimes
