module

public import FractionalPrimes.ArithmeticBasics
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
All-scale wrappers for the progression prefix approximation in `ar:progression`.

The analytic progression estimate is already proved for all sufficiently large
scales in `ArithmeticBasics`.  This file supplies the bounded-scale argument
and the exact-average normalization stated in the blueprint.
-/

namespace FractionalPrimes

private theorem progression_divisorCutoff_le_scale {N : ℝ} {d : ℕ}
    (hN : 3 ≤ N)
    (hd : (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ))) :
    (d : ℝ) ≤ N := by
  have hNpos : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1)
        (lt_of_lt_of_le Real.exp_one_lt_three hN).le
  have hlogpow : (Real.log N) ^ (3 / 10 : ℝ) ≤ Real.log N := by
    calc
      (Real.log N) ^ (3 / 10 : ℝ) ≤ (Real.log N) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num : (3 / 10 : ℝ) ≤ 1)
      _ = Real.log N := Real.rpow_one _
  calc
    (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) := hd
    _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hlogpow
    _ = N := Real.exp_log hNpos

private theorem progression_prefix_trivial_bound
    {c N ξ : ℝ} {d : ℕ}
    (hN : 3 ≤ N)
    (hdNat : 1 ≤ d) :
    ‖((d : ℝ) / N : ℝ) •
        (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
          (fun i => unitFrequencyPhase
            (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
      continuousFractionalModel c N ξ‖ ≤ 2 := by
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hdNat)
  let L : ℕ := Nat.floor (N / (d : ℝ))
  let S : ℂ := (Finset.Ico 0 L).sum (fun i => unitFrequencyPhase
    (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)))
  have hrem := nat_floor_progression_remainder_bounds (by linarith : 0 ≤ N) hdpos
  have hLN : (d : ℝ) * (L : ℝ) ≤ N := by
    have : 0 ≤ N - (d : ℝ) * (Nat.floor (N / (d : ℝ)) : ℝ) := hrem.1
    dsimp [L]
    linarith
  have hcoef : 0 < (d : ℝ) / N := div_pos hdpos hNpos
  have hsum : ‖S‖ ≤ (L : ℝ) := by
    dsimp [S]
    calc
      ‖(Finset.Ico 0 L).sum (fun i => unitFrequencyPhase
          (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)))‖ ≤
        (Finset.Ico 0 L).sum (fun i => ‖unitFrequencyPhase
          (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))‖) :=
            norm_sum_le _ _
      _ = (L : ℝ) := by simp [norm_unitFrequencyPhase]
  have hmodel : ‖continuousFractionalModel c N ξ‖ ≤ 1 := by
    rw [continuousFractionalModel_eq_unitIntegral hNpos]
    exact norm_fractionalPhaseIntegral_unit_le_one c (ξ * N ^ c)
  have hscale : ((d : ℝ) / N) * (L : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_one hNpos).2 hLN
  change ‖((d : ℝ) / N : ℝ) • S - continuousFractionalModel c N ξ‖ ≤ 2
  calc
    ‖((d : ℝ) / N : ℝ) • S - continuousFractionalModel c N ξ‖ ≤
        ‖((d : ℝ) / N : ℝ) • S‖ + ‖continuousFractionalModel c N ξ‖ :=
          norm_sub_le _ _
    _ = ((d : ℝ) / N) * ‖S‖ + ‖continuousFractionalModel c N ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoef]
    _ ≤ ((d : ℝ) / N) * (L : ℝ) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (le_of_lt hcoef)) hmodel
    _ ≤ 2 := by linarith

/-- The full normalized prefix approximation of `ar:progression`, now for
every scale `N ≥ 3`.  The constant may depend on `c`, through the threshold
of the eventual estimate. -/
theorem exists_progression_floorPrefix_powerSaving_all_scales {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 3 ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖((d : ℝ) / N : ℝ) •
            (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
              (fun i => unitFrequencyPhase
                (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
          continuousFractionalModel c N ξ‖ ≤ C * N ^ (-δ) := by
  dsimp only
  obtain ⟨N₀, hN₀, heventual⟩ := exists_progression_floorPrefix_powerSaving hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  let A : ℝ := (2 * Real.pi + 2 * Real.pi * c + 1) +
    (3 + (Real.pi * c)⁻¹)
  let C : ℝ := max A (2 * N₀)
  have hδ := progressionParameters_delta_bounds hc
  have hδpos : 0 < δ := by simpa [j, η, δ] using hδ.1
  have hδlt : δ < 1 := by simpa [j, η, δ] using hδ.2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hCnonneg, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi
  by_cases hlarge : N₀ ≤ N
  · have hmain := heventual N hlarge d hd hdcut ξ hξlo hξhi
    have hA_C : A ≤ C := by dsimp [C]; exact le_max_left _ _
    calc
      ‖((d : ℝ) / N : ℝ) •
          (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
            (fun i => unitFrequencyPhase
              (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
          continuousFractionalModel c N ξ‖ ≤ A * N ^ (-δ) := by
            simpa [A, η, j, δ, Nat.cast_add, one_div] using hmain
      _ ≤ C * N ^ (-δ) :=
        mul_le_mul_of_nonneg_right hA_C (Real.rpow_nonneg (by linarith : 0 ≤ N) _)
  · have hsmall : N < N₀ := lt_of_not_ge hlarge
    have htrivial := progression_prefix_trivial_bound (c := c) (ξ := ξ) hN hd
    have hN1 : 1 ≤ N := by linarith
    have hpower : N ^ (-1 : ℝ) ≤ N ^ (-δ) := by
      have hexp : (-1 : ℝ) ≤ -δ := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
    have hCbig : 2 * N₀ ≤ C := by dsimp [C]; exact le_max_right _ _
    have hgoal : 2 ≤ C * N ^ (-δ) := by
      have hNpos : 0 < N := by linarith
      have hmul : N₀ / N ≤ N₀ * N ^ (-δ) := by
        have hpower' : N⁻¹ ≤ N ^ (-δ) := by
          rw [← Real.rpow_neg_one N]
          exact hpower
        calc
          N₀ / N = N₀ * N⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ N₀ * N ^ (-δ) :=
            mul_le_mul_of_nonneg_left hpower' (by linarith : 0 ≤ N₀)
      have hN0over : 1 ≤ N₀ / N := by
        rw [one_le_div hNpos]
        linarith
      have htwice : 2 ≤ (2 * N₀) * N ^ (-δ) := by
        calc
          2 ≤ 2 * (N₀ / N) := by nlinarith
          _ ≤ 2 * (N₀ * N ^ (-δ)) := by nlinarith [hmul]
          _ = (2 * N₀) * N ^ (-δ) := by ring
      exact htwice.trans (mul_le_mul_of_nonneg_right hCbig
        (Real.rpow_nonneg (by linarith : 0 ≤ N) _))
    exact htrivial.trans hgoal

private theorem progression_divisor_normalization_error_all_scales
    {N : ℝ} {d : ℕ} {δ : ℝ}
    (hN : 3 ≤ N) (hδhalf : δ ≤ 1 / 2)
    (Ndiv : ℝ) (hNdiv : 2 ≤ Ndiv)
    (hdiv : ∀ X : ℝ, Ndiv ≤ X →
      Real.exp ((Real.log X) ^ (3 / 10 : ℝ)) ≤ X ^ (1 / 2 : ℝ))
    (hd : (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ))) :
    (d : ℝ) / N ≤ Ndiv * N ^ (-δ) := by
  have hN1 : 1 ≤ N := by linarith
  have hdN : (d : ℝ) ≤ N := progression_divisorCutoff_le_scale hN hd
  have hδlt : δ < 1 := by linarith
  by_cases hlarge : Ndiv ≤ N
  · have hdhalf : (d : ℝ) ≤ N ^ (1 / 2 : ℝ) := hd.trans (hdiv N hlarge)
    have hsmallpow : N ^ (-(1 / 2 : ℝ)) ≤ N ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hcalc : (d : ℝ) / N ≤ N ^ (-(1 / 2 : ℝ)) := by
      calc
        (d : ℝ) / N ≤ N ^ (1 / 2 : ℝ) / N :=
          div_le_div_of_nonneg_right hdhalf (by linarith)
        _ = N ^ (-(1 / 2 : ℝ)) := by
          calc
            N ^ (1 / 2 : ℝ) / N = N ^ (1 / 2 : ℝ) / N ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = N ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub (by linarith : 0 < N) _ _).symm
            _ = N ^ (-(1 / 2 : ℝ)) := by congr 1; ring
    have hone : 1 ≤ Ndiv := by linarith
    exact hcalc.trans (hsmallpow.trans (by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hone
          (Real.rpow_nonneg (by linarith : 0 ≤ N) (-δ)))))
  · have hNlt : N < Ndiv := lt_of_not_ge hlarge
    have hpow : N ^ (-1 : ℝ) ≤ N ^ (-δ) := by
      have hexp : (-1 : ℝ) ≤ -δ := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
    have hbound : (d : ℝ) / N ≤ 1 := by
      exact (div_le_one (by linarith)).2 hdN
    have hdivsmall : 1 ≤ Ndiv / N := by
      rw [one_le_div (by linarith)]
      exact hNlt.le
    have hfinal : 1 ≤ Ndiv * N ^ (-δ) := by
      calc
        1 ≤ Ndiv / N := hdivsmall
        _ = Ndiv * N⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ Ndiv * N ^ (-δ) := by
          have hpow' : N⁻¹ ≤ N ^ (-δ) := by
            rw [← Real.rpow_neg_one N]
            exact hpow
          exact mul_le_mul_of_nonneg_left hpow' (by linarith : 0 ≤ Ndiv)
    exact hbound.trans hfinal

/-- The exact average with denominator `floor(N/d)` in `ar:progression`,
uniformly over every permitted scale. -/
theorem exists_progression_floorPrefix_exactAverage_all_scales {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 3 ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        let L : ℕ := Nat.floor (N / (d : ℝ))
        0 < L ∧
        ‖((L : ℝ)⁻¹ : ℝ) •
            (Finset.Ico 0 L).sum
              (fun i => unitFrequencyPhase
                (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
          continuousFractionalModel c N ξ‖ ≤ C * N ^ (-δ) := by
  dsimp only
  obtain ⟨C₀, hC₀, hnorm⟩ := exists_progression_floorPrefix_powerSaving_all_scales hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  have hδ := progressionParameters_delta_bounds hc
  have hδpos : 0 < δ := by simpa [j, η, δ] using hδ.1
  have hδhalf : δ ≤ 1 / 2 := by
    have hη := progressionParameters_eta_le_frequency_cutoff hc
    dsimp [j, η, δ] at hη ⊢
    norm_num at hη ⊢
    nlinarith
  obtain ⟨Ndiv, hNdiv, hdiv⟩ := exists_monomial_divisor_power_threshold
    (εd := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨C₀ + Ndiv, by positivity, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi
  let L : ℕ := Nat.floor (N / (d : ℝ))
  let S : ℂ := (Finset.Ico 0 L).sum (fun i => unitFrequencyPhase
    (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)))
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hd)
  have hLpos : 0 < L := by
    have hdN := progression_divisorCutoff_le_scale hN hdcut
    have hq : 1 ≤ N / (d : ℝ) := (one_le_div hdpos).2 hdN
    dsimp [L]
    exact Nat.le_floor (by exact_mod_cast hq)
  have hrem := nat_floor_progression_remainder_bounds (by linarith : 0 ≤ N) hdpos
  have hnormsum : ‖S‖ ≤ (L : ℝ) := by
    dsimp [S]
    calc
      ‖(Finset.Ico 0 L).sum (fun i => unitFrequencyPhase
          (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ)))‖ ≤
        (Finset.Ico 0 L).sum (fun i => ‖unitFrequencyPhase
          (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))‖) :=
            norm_sum_le _ _
      _ = (L : ℝ) := by simp [norm_unitFrequencyPhase]
  have hcorrection :
      ‖((L : ℝ)⁻¹ : ℝ) • S - ((d : ℝ) / N : ℝ) • S‖ ≤ (d : ℝ) / N := by
    have hLposR : 0 < (L : ℝ) := by exact_mod_cast hLpos
    have hrem' : 0 ≤ N - (d : ℝ) * (L : ℝ) ∧
        N - (d : ℝ) * (L : ℝ) < (d : ℝ) := by
      simpa [L] using hrem
    have hdiff : ((L : ℝ)⁻¹ - (d : ℝ) / N) * (L : ℝ) =
        (N - (d : ℝ) * (L : ℝ)) / N := by
      field_simp [ne_of_gt hLposR, ne_of_gt hNpos]
    have hdiffnonneg : 0 ≤ (L : ℝ)⁻¹ - (d : ℝ) / N := by
      have hright : 0 ≤ (N - (d : ℝ) * (L : ℝ)) / N :=
        div_nonneg hrem'.1 hNpos.le
      nlinarith [hdiff, hright]
    calc
      ‖((L : ℝ)⁻¹ : ℝ) • S - ((d : ℝ) / N : ℝ) • S‖ =
          |(L : ℝ)⁻¹ - (d : ℝ) / N| * ‖S‖ := by
            rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ((L : ℝ)⁻¹ - (d : ℝ) / N) * (L : ℝ) := by
            rw [abs_of_nonneg hdiffnonneg]
            exact mul_le_mul_of_nonneg_left hnormsum hdiffnonneg
      _ ≤ (d : ℝ) / N := by
        rw [hdiff]
        have hlt : (N - (d : ℝ) * (L : ℝ)) / N < (d : ℝ) / N := by
          apply (div_lt_div_iff₀ hNpos hNpos).2
          exact mul_lt_mul_of_pos_right hrem'.2 hNpos
        exact hlt.le
  have hnorm := hnorm N hN d hd hdcut ξ hξlo hξhi
  have hcorrectionPower := progression_divisor_normalization_error_all_scales
    hN hδhalf Ndiv hNdiv hdiv hdcut
  have hcorrection' :
      ‖((L : ℝ)⁻¹ : ℝ) • S - ((d : ℝ) / N : ℝ) • S‖ ≤
        Ndiv * N ^ (-δ) := hcorrection.trans hcorrectionPower
  have hfinal :
      ‖((L : ℝ)⁻¹ : ℝ) • S - continuousFractionalModel c N ξ‖ ≤
        (C₀ + Ndiv) * N ^ (-δ) := by
    calc
      ‖((L : ℝ)⁻¹ : ℝ) • S - continuousFractionalModel c N ξ‖ ≤
          ‖((L : ℝ)⁻¹ : ℝ) • S - ((d : ℝ) / N : ℝ) • S‖ +
            ‖((d : ℝ) / N : ℝ) • S - continuousFractionalModel c N ξ‖ := by
              rw [show ((L : ℝ)⁻¹ : ℝ) • S - continuousFractionalModel c N ξ =
                (((L : ℝ)⁻¹ : ℝ) • S - ((d : ℝ) / N : ℝ) • S) +
                  (((d : ℝ) / N : ℝ) • S - continuousFractionalModel c N ξ) by abel]
              exact norm_add_le _ _
      _ ≤ Ndiv * N ^ (-δ) + C₀ * N ^ (-δ) :=
        add_le_add hcorrection' hnorm
      _ ≤ (C₀ + Ndiv) * N ^ (-δ) := by
        calc
          Ndiv * N ^ (-δ) + C₀ * N ^ (-δ) =
              (C₀ + Ndiv) * N ^ (-δ) := by ring
          _ ≤ (C₀ + Ndiv) * N ^ (-δ) := le_rfl
  exact ⟨by simpa [L] using hLpos, by simpa [L, S, j, η, δ] using hfinal⟩

/-- The all-scale raw-sum formulation equivalent to the normalized prefix
estimate in `ar:progression`. -/
theorem exists_progression_floorPrefix_raw_powerSaving_all_scales {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 3 ≤ N →
      ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 10 : ℝ)) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖(∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
            unitFrequencyPhase
              (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))) -
          ((d : ℝ)⁻¹ : ℂ) *
            (∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c))‖ ≤
          C * (N ^ (1 - δ) / (d : ℝ)) := by
  dsimp only
  obtain ⟨C, hC, hnorm⟩ :=
    exists_progression_floorPrefix_powerSaving_all_scales hc hcNon
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  refine ⟨C, hC, ?_⟩
  intro N hN d hd hdcut ξ hξlo hξhi
  have hNpos : 0 < N := by linarith
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hd)
  let S : ℂ := ∑ n ∈ realIntegerInterval 0 (N / (d : ℝ)),
    unitFrequencyPhase (ξ * (Int.floor (((d : ℝ) * (n : ℝ)) ^ c) : ℝ))
  let I : ℂ := ∫ t in (0 : ℝ)..N, unitFrequencyPhase (ξ * t ^ c)
  have hsum : S =
      (Finset.Ico 0 (Nat.floor (N / (d : ℝ)))).sum
        (fun i => unitFrequencyPhase
          (ξ * ((Int.floor (((d : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) := by
    dsimp [S]
    exact progression_floorPhase_sum_reindex
      (N := N) (d := (d : ℝ)) (ξ := ξ) (c := c) (by positivity)
  have hnormalized := hnorm N hN d hd hdcut ξ hξlo hξhi
  rw [← hsum] at hnormalized
  have hbound : ‖((d : ℝ) / N : ℝ) • S - (N : ℂ)⁻¹ * I‖ ≤
      C * N ^ (-δ) := by
    simpa [I, continuousFractionalModel, j, η, δ] using hnormalized
  exact progression_normalized_error_to_raw hdpos hNpos hC S I hbound

end FractionalPrimes
