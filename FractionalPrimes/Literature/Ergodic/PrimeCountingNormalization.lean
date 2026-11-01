module

public import FractionalPrimes.Literature.Ergodic.PrimeAbelIdentity

/-!
# Prime-counting normalization bridge

This module formalizes the downstream arithmetic bridge in blueprint
`er:primecount`. It is conditional on the von Mangoldt asymptotic supplied
by the upstream comparison node; it does not claim that upstream node.
-/

@[expose] public section

open Filter
open scoped Topology
open scoped Nat.Prime

namespace FractionalPrimes

noncomputable section

/-- The normalized higher-prime-power contribution tends to zero, using the
exact square-root/logarithm estimate already checked in `Chebyshev.lean`. -/
theorem paperHigherPrimePowerThetaSum_div_tendsto_zero :
    Tendsto (fun N : ℕ => paperHigherPrimePowerThetaSum N / (N : ℝ))
      Filter.atTop (𝓝 0) := by
  have hsmallReal : Tendsto
      (fun x : ℝ => (Real.log x) ^ (2 : ℝ) / Real.sqrt x)
      Filter.atTop (𝓝 0) := by
    have h := (paper_log_rpow_isLittleO_rpow (a := 2) (b := 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa [Real.sqrt_eq_rpow] using h
  have hsmallNat : Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ (2 : ℝ) / Real.sqrt (N : ℝ))
      Filter.atTop (𝓝 0) := hsmallReal.comp tendsto_natCast_atTop_atTop
  have hmajorant : Tendsto
      (fun N : ℕ =>
        ((Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ)) / Real.log 2)
      Filter.atTop (𝓝 0) := by
    have h := hsmallNat.div_const (Real.log 2)
    convert h using 1 <;> ext N <;> simp
  have hnonneg : ∀ N : ℕ,
      0 ≤ paperHigherPrimePowerThetaSum N / (N : ℝ) := by
    intro N
    unfold paperHigherPrimePowerThetaSum
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      exact Chebyshev.theta_nonneg _
    · positivity
  have hbound : ∀ᶠ N : ℕ in Filter.atTop,
      paperHigherPrimePowerThetaSum N / (N : ℝ) ≤
        ((Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ)) / Real.log 2 := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by positivity
    have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hsum := paperHigherPrimePowerThetaSum_le hN
    calc
      paperHigherPrimePowerThetaSum N / (N : ℝ) ≤
          (((Real.log (N : ℝ)) ^ 2 / Real.log 2) * Real.sqrt (N : ℝ)) /
            (N : ℝ) := div_le_div_of_nonneg_right hsum hNpos.le
      _ = ((Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ)) / Real.log 2 := by
        field_simp [ne_of_gt hNpos, ne_of_gt hsqrtpos, ne_of_gt hlog2]
        nlinarith [Real.sq_sqrt hNpos.le]
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbound hmajorant

/-- From the frequency-zero von Mangoldt asymptotic, the exact
higher-prime-power decomposition gives the prime-log asymptotic. -/
theorem paperTheta_div_tendsto_one_of_paperPsi_div_tendsto_one
    (hpsi : Tendsto (fun N : ℕ => paperPsi N / (N : ℝ))
      Filter.atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => paperTheta (N : ℝ) / (N : ℝ))
      Filter.atTop (𝓝 1) := by
  have hrem := paperHigherPrimePowerThetaSum_div_tendsto_zero
  have hsub := hpsi.sub hrem
  have heq :
      (fun N : ℕ => paperPsi N / (N : ℝ) -
        paperHigherPrimePowerThetaSum N / (N : ℝ)) =ᶠ[Filter.atTop]
      fun N : ℕ => paperTheta (N : ℝ) / (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    rw [paperHigherPrimePowerThetaSum_eq_psi_sub_theta hN]
    have hNpos : (N : ℝ) ≠ 0 := by positivity
    field_simp [hNpos]
    ring
  have hsub : Tendsto
      (fun N : ℕ => paperPsi N / (N : ℝ) -
        paperHigherPrimePowerThetaSum N / (N : ℝ))
      Filter.atTop (𝓝 1) := by
    simpa using hpsi.sub hrem
  exact hsub.congr' heq

/-- The prime sum at constant input is the exact prime count, while the
prime-log sum is the paper's inclusive Chebyshev theta function. -/
theorem primeAbelIdentity_one_nat {N : ℕ} (hN : 2 ≤ N) :
    (paperPi (N : ℝ) : ℝ) =
      (Real.log (N : ℝ))⁻¹ * paperTheta (N : ℝ) +
        ∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * paperTheta (n : ℝ) := by
  have h := primeAbelIdentity_real (fun _ : ℕ => (1 : ℝ)) hN
  simp_rw [primeLogPartialSum_one_eq_arithmeticData,
    arithmeticData_primeLogSummatory_eq] at h
  have hleft :
      (∑ p ∈ Finset.Icc 0 N with Nat.Prime p, (1 : ℝ)) =
        (paperPi (N : ℝ) : ℝ) := by
    rw [paperPi_eq_card_primes]
    simp
  have hthetaSum (n : ℕ) :
      (∑ p ∈ Finset.Icc 0 n with Nat.Prime p, Real.log (p : ℝ)) =
        paperTheta (n : ℝ) := by
    simpa only [Nat.floor_natCast] using
      (paperTheta_eq_sum_primes (n : ℝ)).symm
  simp_rw [hthetaSum] at h
  calc
    (paperPi (N : ℝ) : ℝ) =
        ∑ p ∈ Finset.Icc 0 N with Nat.Prime p, (1 : ℝ) := hleft.symm
    _ = (Real.log (N : ℝ))⁻¹ * paperTheta (N : ℝ) +
        ∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * paperTheta (n : ℝ) := h

/-- The Abel remainder built from `θ(n)` is little-o of `N/log N` under its
linear Chebyshev bound. -/
theorem primeAbelThetaRemainder_normalized_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * paperTheta (n : ℝ)) /
            ((N : ℝ) / Real.log (N : ℝ)))
      Filter.atTop (𝓝 0) := by
  let C : ℝ := 4 * Real.log 2
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hH := primeAbelRemainderCoefficient_littleO.tendsto_div_nhds_zero
  have hmajorant : Tendsto
      (fun N : ℕ => C *
        (primeAbelRemainderCoefficient N /
          ((N : ℝ) / Real.log (N : ℝ)))) Filter.atTop (𝓝 0) := by
    simpa [mul_comm] using hH.const_mul C
  have hnonneg : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ (∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * paperTheta (n : ℝ)) /
            ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by positivity
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hNpos hlogpos
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro n hn
      apply mul_nonneg
      · exact (primeAbelDifference_pos (Finset.mem_Ico.mp hn).1).le
      · exact Chebyshev.theta_nonneg _
    · exact hden.le
  have hbound : ∀ᶠ N : ℕ in Filter.atTop,
      (∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * paperTheta (n : ℝ)) /
            ((N : ℝ) / Real.log (N : ℝ)) ≤
        C * (primeAbelRemainderCoefficient N /
          ((N : ℝ) / Real.log (N : ℝ))) := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by positivity
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hNpos hlogpos
    have hterm (n : ℕ) (hn : n ∈ Finset.Ico 2 N) :
        primeAbelDifference n * paperTheta (n : ℝ) ≤
          C * ((n : ℝ) * primeAbelDifference n) := by
      have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
      have htheta : paperTheta (n : ℝ) ≤ C * (n : ℝ) := by
        dsimp [C]
        exact paperTheta_upper_bound (by exact_mod_cast (show 1 ≤ n by omega))
      have hdn : 0 ≤ primeAbelDifference n :=
        (primeAbelDifference_pos hn2).le
      calc
        primeAbelDifference n * paperTheta (n : ℝ) ≤
            primeAbelDifference n * (C * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left htheta hdn
        _ = C * ((n : ℝ) * primeAbelDifference n) := by ring
    have hsum := Finset.sum_le_sum (s := Finset.Ico 2 N)
      (fun n hn => hterm n hn)
    have hcoef :
        (∑ n ∈ Finset.Ico 2 N,
          C * ((n : ℝ) * primeAbelDifference n)) =
          C * primeAbelRemainderCoefficient N := by
      simp [primeAbelRemainderCoefficient, Finset.mul_sum]
    rw [hcoef] at hsum
    calc
      _ ≤ (C * primeAbelRemainderCoefficient N) /
          ((N : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right hsum hden.le
      _ = C * (primeAbelRemainderCoefficient N /
          ((N : ℝ) / Real.log (N : ℝ))) := by ring
  exact squeeze_zero' hnonneg hbound hmajorant

/-- The downstream prime-counting conclusions from `er:primecount`,
conditional only on its frequency-zero von Mangoldt comparison input. This
bridge does not close the upstream comparison node. -/
theorem primeCountingNormalization_of_paperPsi_div_tendsto_one
    (hpsi : Tendsto (fun N : ℕ => paperPsi N / (N : ℝ))
      Filter.atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => paperPsi N / (N : ℝ)) Filter.atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => paperTheta (N : ℝ) / (N : ℝ))
      Filter.atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ =>
      (paperPi (N : ℝ) : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      Filter.atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => (paperPi (N : ℝ) : ℝ))
      Filter.atTop Filter.atTop := by
  have htheta := paperTheta_div_tendsto_one_of_paperPsi_div_tendsto_one hpsi
  have hrem := primeAbelThetaRemainder_normalized_tendsto_zero
  have hremScaled : Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * paperTheta (n : ℝ)) *
            Real.log (N : ℝ) / (N : ℝ)) Filter.atTop (𝓝 0) := by
    apply hrem.congr'
    filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by positivity
    have hlog : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    field_simp [ne_of_gt hNpos, ne_of_gt hlog]
  have hpiLog : Tendsto
      (fun N : ℕ =>
        (paperPi (N : ℝ) : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      Filter.atTop (𝓝 1) := by
    have heq :
        (fun N : ℕ =>
          (paperPi (N : ℝ) : ℝ) * Real.log (N : ℝ) / (N : ℝ)) =ᶠ[Filter.atTop]
        fun N : ℕ => paperTheta (N : ℝ) / (N : ℝ) +
          (∑ n ∈ Finset.Ico 2 N,
            primeAbelDifference n * paperTheta (n : ℝ)) *
              Real.log (N : ℝ) / (N : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
      have habel := primeAbelIdentity_one_nat (by omega : 2 ≤ N)
      have hNpos : 0 < (N : ℝ) := by positivity
      have hlog : 0 < Real.log (N : ℝ) := by
        exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      rw [habel]
      field_simp [ne_of_gt hNpos, ne_of_gt hlog]
    have hsum : Tendsto
        (fun N : ℕ => paperTheta (N : ℝ) / (N : ℝ) +
          (∑ n ∈ Finset.Ico 2 N,
            primeAbelDifference n * paperTheta (n : ℝ)) *
              Real.log (N : ℝ) / (N : ℝ)) Filter.atTop (𝓝 1) := by
      simpa using htheta.add hremScaled
    exact hsum.congr' heq.symm
  have hNlogAtTop : Tendsto (fun N : ℕ =>
      (N : ℝ) / Real.log (N : ℝ)) Filter.atTop Filter.atTop := by
    have hlogSqrtReal : Tendsto
        (fun x : ℝ => Real.log x / Real.sqrt x) Filter.atTop (𝓝 0) := by
      have h := (paper_log_rpow_isLittleO_rpow (a := 1) (b := 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      simpa [Real.rpow_one, Real.sqrt_eq_rpow] using h
    have hlogSqrtNat : Tendsto
        (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ))
        Filter.atTop (𝓝 0) := hlogSqrtReal.comp tendsto_natCast_atTop_atTop
    have hlogLe : ∀ᶠ N : ℕ in Filter.atTop,
        Real.log (N : ℝ) ≤ Real.sqrt (N : ℝ) := by
      filter_upwards [hlogSqrtNat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        Filter.eventually_ge_atTop (2 : ℕ)] with N hsmall hN
      have hNpos : 0 < (N : ℝ) := by positivity
      have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
      have hlogle := ((div_lt_iff₀ hsqrtpos).1 (by simpa using hsmall)).le
      simpa only [one_mul] using hlogle
    have hlower : ∀ᶠ N : ℕ in Filter.atTop,
        Real.sqrt (N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) := by
      filter_upwards [hlogLe, Filter.eventually_ge_atTop (2 : ℕ)] with N hlogle hN
      have hNpos : 0 < (N : ℝ) := by positivity
      have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
      have hlogpos : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      apply (le_div_iff₀ hlogpos).2
      calc
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤
            Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left hlogle (Real.sqrt_nonneg _)
        _ = (N : ℝ) := by
          rw [← sq, Real.sq_sqrt hNpos.le]
    have hsqrtTop : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ))
        Filter.atTop Filter.atTop := by
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact Filter.tendsto_atTop_mono' Filter.atTop hlower hsqrtTop
  have hpiPositive : ∀ᶠ N : ℕ in Filter.atTop,
      1 / 2 ≤ (paperPi (N : ℝ) : ℝ) * Real.log (N : ℝ) / (N : ℝ) := by
    filter_upwards [hpiLog.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with N hN
    exact hN.le
  have hpiLower : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) / (2 * Real.log (N : ℝ)) ≤ (paperPi (N : ℝ) : ℝ) := by
    filter_upwards [hpiPositive, Filter.eventually_ge_atTop (2 : ℕ)] with N hpi hN
    have hNpos : 0 < (N : ℝ) := by positivity
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (N : ℝ))).2
    have hmul := (le_div_iff₀ hNpos).1 hpi
    calc
      (N : ℝ) = 2 * ((1 / 2 : ℝ) * (N : ℝ)) := by ring
      _ ≤ 2 * ((paperPi (N : ℝ) : ℝ) * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = (paperPi (N : ℝ) : ℝ) * (2 * Real.log (N : ℝ)) := by ring
  have hpiTop : Tendsto (fun N : ℕ => (paperPi (N : ℝ) : ℝ))
      Filter.atTop Filter.atTop := by
    have hlowerTop : Tendsto (fun N : ℕ =>
        (N : ℝ) / (2 * Real.log (N : ℝ))) Filter.atTop Filter.atTop := by
      have hNlog := hNlogAtTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      convert hNlog using 1
      ext N
      ring
    exact Filter.tendsto_atTop_mono' Filter.atTop hpiLower hlowerTop
  exact ⟨hpsi, htheta, hpiLog, hpiTop⟩

end

end FractionalPrimes

#print axioms FractionalPrimes.paperHigherPrimePowerThetaSum_div_tendsto_zero
#print axioms FractionalPrimes.paperTheta_div_tendsto_one_of_paperPsi_div_tendsto_one
#print axioms FractionalPrimes.primeAbelIdentity_one_nat
#print axioms FractionalPrimes.primeAbelThetaRemainder_normalized_tendsto_zero
#print axioms FractionalPrimes.primeCountingNormalization_of_paperPsi_div_tendsto_one

end
