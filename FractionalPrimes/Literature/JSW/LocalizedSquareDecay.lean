module

public import FractionalPrimes.Literature.JSW.InitialSquareAndMaximal
public import FractionalPrimes.Literature.JSW.LittlewoodPaleyUpper
public import FractionalPrimes.Literature.JSW.PositiveMaximalNuVectorBound

/-!
# Frequency-localized cancellation decay

Finite-frequency coefficient estimates for `lj:localized-square`.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A translated Littlewood--Paley annulus has at most `N_b` active scales.
This is the finite overlap count needed by `lj:localized-square`. -/
private theorem localizedSquareActiveCard_le {b : ℝ} (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    (F.filter (fun k =>
      littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ) ≠ 0)).card ≤
        littlewoodPaleyNb b := by
  let S : Finset ℤ := F.filter (fun k =>
    littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ) ≠ 0)
  have hbpos : 0 < b := by linarith
  have hb₀ : b ≠ 0 := ne_of_gt hbpos
  have hξabs : 0 < |ξ| := abs_pos.mpr hξ
  by_cases hS : S.Nonempty
  · let m : ℤ := S.min' hS
    let M : ℤ := S.max' hS
    have hmin : m ∈ S := by simpa [m] using Finset.min'_mem S hS
    have hmax : M ∈ S := by simpa [M] using Finset.max'_mem S hS
    have hle : m ≤ M := Finset.min'_le S M hmax
    have hannulus (k : ℤ) (hk : k ∈ S) :
        1 / b ≤ |b ^ (k + j) * ξ| ∧ |b ^ (k + j) * ξ| ≤ 2 := by
      have hp := (Finset.mem_filter.mp hk).2
      constructor
      · by_contra h
        have hsmall : |b ^ (k + j) * ξ| < 1 / b := lt_of_not_ge h
        exact hp (littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus hb
          (Or.inl hsmall))
      · by_contra h
        have hlarge : 2 < |b ^ (k + j) * ξ| := lt_of_not_ge h
        exact hp (littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus hb
          (Or.inr hlarge))
    have hscale (k : ℤ) : |b ^ (k + j) * ξ| = b ^ (k + j) * |ξ| := by
      rw [abs_mul, abs_of_pos (zpow_pos hbpos (k + j))]
    have hlow : 1 / b ≤ b ^ (m + j) * |ξ| := by
      simpa [hscale m] using (hannulus m hmin).1
    have hhigh : b ^ (M + j) * |ξ| ≤ 2 := by
      simpa [hscale M] using (hannulus M hmax).2
    have hratio : b ^ (M - m) =
        (b ^ (M + j) * |ξ|) / (b ^ (m + j) * |ξ|) := by
      calc
        b ^ (M - m) = b ^ ((M + j) - (m + j)) := by congr 1 <;> omega
        _ = b ^ (M + j) / b ^ (m + j) := zpow_sub₀ hb₀ _ _
        _ = (b ^ (M + j) * |ξ|) / (b ^ (m + j) * |ξ|) := by
          field_simp [ne_of_gt (mul_pos (zpow_pos hbpos (m + j)) hξabs)]
    have hdenpos : 0 < b ^ (m + j) * |ξ| :=
      mul_pos (zpow_pos hbpos (m + j)) hξabs
    have hratioBound : b ^ (M - m) ≤ 2 * b := by
      have hquot : (b ^ (M + j) * |ξ|) / (b ^ (m + j) * |ξ|) ≤
          2 / (b ^ (m + j) * |ξ|) :=
        div_le_div_of_nonneg_right hhigh hdenpos.le
      have hinv' : 1 / (b ^ (m + j) * |ξ|) ≤ 1 / (1 / b) :=
        one_div_le_one_div_of_le (by positivity : 0 < 1 / b) hlow
      have hinv : (b ^ (m + j) * |ξ|)⁻¹ ≤ (1 / b)⁻¹ := by
        simpa only [one_div] using hinv'
      calc
        b ^ (M - m) =
            (b ^ (M + j) * |ξ|) / (b ^ (m + j) * |ξ|) := hratio
        _ ≤ 2 / (b ^ (m + j) * |ξ|) := hquot
        _ = 2 * (b ^ (m + j) * |ξ|)⁻¹ := by ring
        _ ≤ 2 * (1 / b)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2 * b := by field_simp [ne_of_gt hbpos]
    have hlog : (M - m : ℝ) ≤ Real.logb b (2 * b) := by
      have hlogmono := (Real.logb_le_logb (b := b) hb (zpow_pos hbpos (M - m))
        (by positivity : 0 < 2 * b)).2 hratioBound
      have hlogpow : Real.logb b (b ^ (M - m)) = (M - m : ℝ) := by
        rw [← Real.rpow_intCast b (M - m), Real.logb_rpow hbpos (ne_of_gt hb)]
        simp [Int.cast_sub]
      rw [hlogpow] at hlogmono
      exact hlogmono
    have hwidth : M - m ≤ (Nat.ceil (Real.logb b (2 * b)) : ℤ) := by
      exact_mod_cast hlog.trans (Nat.le_ceil (Real.logb b (2 * b)))
    have hsubset : S ⊆ Finset.Icc m M := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
    have hcard : (S.card : ℤ) ≤ M - m + 1 := by
      calc
        (S.card : ℤ) ≤ (Finset.Icc m M).card := by
          exact_mod_cast (Finset.card_le_card hsubset)
        _ = M + 1 - m := by
          simpa using (Int.card_Icc_of_le (a := m) M (by omega))
        _ = M - m + 1 := by ring
    have hcard' : S.card ≤ Nat.ceil (Real.logb b (2 * b)) + 1 := by
      exact_mod_cast (hcard.trans (by omega : M - m + 1 ≤
        (Nat.ceil (Real.logb b (2 * b)) : ℤ) + 1))
    have hcard'' : S.card ≤ Nat.ceil (Real.logb b (2 * b)) + 2 := by omega
    simpa [S, littlewoodPaleyNb] using hcard''
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hSempty, littlewoodPaleyNb]

private theorem localizedSquareAnnulus_of_ne_zero {b : ℝ} (hb : 1 < b)
    {ξ : ℝ} (hp : littlewoodPaleyCutoffDifference b ξ ≠ 0) :
    1 / b ≤ |ξ| ∧ |ξ| ≤ 2 := by
  constructor
  · by_contra h
    have hsmall : |ξ| < 1 / b := lt_of_not_ge h
    exact hp (littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus hb
      (Or.inl hsmall))
  · by_contra h
    have hlarge : 2 < |ξ| := lt_of_not_ge h
    exact hp (littlewoodPaleyCutoffDifference_eq_zero_of_not_annulus hb
      (Or.inr hlarge))

private theorem localizedSquareNuFourier_single_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (j k : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0)
    (hcut : littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ) ≠ 0) :
    ‖measureSplittingNuFourier σ (b ^ k * ξ) *
      littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ)‖ ≤
      (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
        Real.rpow b (-min 1 β * |(j : ℝ)|) := by
  have hbpos : 0 < b := by linarith
  have hb₀ : b ≠ 0 := ne_of_gt hbpos
  have hxi : 0 < |ξ| := abs_pos.mpr hξ
  have hannulus := localizedSquareAnnulus_of_ne_zero hb hcut
  let H : ℝ := 2 * Real.pi + 2 * |D|
  let ε : ℝ := min 1 β
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hε0 : 0 ≤ ε := le_min (by norm_num) hβ.le
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεβ : ε ≤ β := min_le_right _ _
  have hpowj : Real.rpow b (-(j : ℝ)) = b ^ (-j : ℤ) := by
    rw [← Int.cast_neg]
    exact Real.rpow_intCast b (-j)
  have hpowprod : b ^ k = b ^ (-j) * b ^ (k + j) := by
    calc
      b ^ k = b ^ ((-j) + (k + j)) := by congr 1 <;> omega
      _ = b ^ (-j) * b ^ (k + j) := zpow_add₀ hb₀ _ _
  have hscale : |b ^ k * ξ| = Real.rpow b (-(j : ℝ)) *
      |b ^ (k + j) * ξ| := by
    calc
      |b ^ k * ξ| = b ^ k * |ξ| := by
        rw [abs_mul, abs_of_pos (zpow_pos hbpos k)]
      _ = b ^ (-j) * b ^ (k + j) * |ξ| := by
        rw [hpowprod]
      _ = b ^ (-j) * (b ^ (k + j) * |ξ|) := by ring
      _ = b ^ (-j) * |b ^ (k + j) * ξ| := by
        rw [abs_mul, abs_of_pos (zpow_pos hbpos (k + j))]
      _ = Real.rpow b (-(j : ℝ)) * |b ^ (k + j) * ξ| := by
        rw [hpowj]
  have hnuarg : b ^ k * ξ ≠ 0 := mul_ne_zero (ne_of_gt (zpow_pos hbpos k)) hξ
  have hdecay := hσ.nu_fourier_decay hnuarg
  have hcutnorm : ‖littlewoodPaleyCutoffDifference b
      (b ^ (k + j) * ξ)‖ ≤ 1 :=
    littlewoodPaleyCutoffDifference_norm_le _ _
  have hjcases : (j : ℝ) < 0 ∨ 0 ≤ (j : ℝ) := lt_or_ge (j : ℝ) 0
  have hnu : ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
      H * max 2 (Real.rpow b β) *
        Real.rpow b (-ε * |(j : ℝ)|) := by
    rcases hjcases with hj | hj
    · have hlarge : 1 / b ≤ |b ^ (k + j) * ξ| := hannulus.1
      have habsj : |(j : ℝ)| = -(j : ℝ) := abs_of_neg hj
      have hpowabs : Real.rpow b (|(j : ℝ)|) = b ^ (-j : ℤ) := by
        rw [habsj]
        exact hpowj
      have hbase : Real.rpow b (|(j : ℝ)| - 1) ≤ |b ^ k * ξ| := by
        have hsub := Real.rpow_sub_one hb₀ (|(j : ℝ)|)
        calc
          Real.rpow b (|(j : ℝ)| - 1) =
              Real.rpow b (|(j : ℝ)|) / b := hsub
          _ = b ^ (-j : ℤ) / b := by rw [hpowabs]
          _ ≤ b ^ (-j : ℤ) * |b ^ (k + j) * ξ| := by
            have hc : 0 ≤ b ^ (-j : ℤ) := (zpow_pos hbpos _).le
            have hlarge' : b⁻¹ ≤ |b ^ (k + j) * ξ| := by
              simpa [one_div] using hlarge
            calc
              b ^ (-j : ℤ) / b = b ^ (-j : ℤ) * b⁻¹ := by rw [div_eq_mul_inv]
              _ ≤ b ^ (-j : ℤ) * |b ^ (k + j) * ξ| :=
                mul_le_mul_of_nonneg_left hlarge' hc
          _ = |b ^ k * ξ| := by
            rw [← hpowj]
            exact hscale.symm
      have hbasepos : 0 < Real.rpow b (|(j : ℝ)| - 1) :=
        Real.rpow_pos_of_pos hbpos _
      have hhigh := Real.rpow_le_rpow_of_nonpos hbasepos hbase
        (by linarith : -β ≤ 0)
      have hpowmul :
          Real.rpow (Real.rpow b (|(j : ℝ)| - 1)) (-β) =
            Real.rpow b ((|(j : ℝ)| - 1) * (-β)) := by
        exact (Real.rpow_mul (by linarith : 0 ≤ b)
          (|(j : ℝ)| - 1) (-β)).symm
      have hexp : (|(j : ℝ)| - 1) * (-β) ≤
          β - ε * |(j : ℝ)| := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hεβ) (abs_nonneg (j : ℝ))]
      have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ b) hexp
      have hfactor : Real.rpow b (β - ε * |(j : ℝ)|) =
          Real.rpow b β * Real.rpow b (-ε * |(j : ℝ)|) := by
        simpa [sub_eq_add_neg] using Real.rpow_add hbpos β (-ε * |(j : ℝ)|)
      have hFourier : ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
          H * Real.rpow b (β - ε * |(j : ℝ)|) := by
        calc
          _ ≤ H * min |b ^ k * ξ| (Real.rpow |b ^ k * ξ| (-β)) := hdecay
          _ ≤ H * Real.rpow |b ^ k * ξ| (-β) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hH
          _ ≤ H * Real.rpow (Real.rpow b (|(j : ℝ)| - 1)) (-β) :=
              mul_le_mul_of_nonneg_left hhigh hH
          _ = H * Real.rpow b ((|(j : ℝ)| - 1) * (-β)) := by rw [hpowmul]
          _ ≤ H * Real.rpow b (β - ε * |(j : ℝ)|) :=
              mul_le_mul_of_nonneg_left hpow hH
      have hmax : Real.rpow b β ≤ max 2 (Real.rpow b β) := le_max_right _ _
      have htail : 0 ≤ Real.rpow b (-ε * |(j : ℝ)|) :=
        Real.rpow_nonneg (by linarith) _
      calc
        ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
            H * Real.rpow b β * Real.rpow b (-ε * |(j : ℝ)|) := by
              rw [hfactor] at hFourier
              simpa [mul_assoc] using hFourier
        _ ≤ H * max 2 (Real.rpow b β) *
              Real.rpow b (-ε * |(j : ℝ)|) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hmax hH) htail
    · have hsmall : |b ^ (k + j) * ξ| ≤ 2 := hannulus.2
      have hexp : -(j : ℝ) ≤ -ε * |(j : ℝ)| := by
        rw [abs_of_nonneg hj]
        nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hj]
      have hpow : Real.rpow b (-(j : ℝ)) ≤
          Real.rpow b (-ε * |(j : ℝ)|) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ b) hexp
      have hv : |b ^ k * ξ| ≤
          2 * Real.rpow b (-ε * |(j : ℝ)|) := by
        calc
          |b ^ k * ξ| = Real.rpow b (-(j : ℝ)) *
              |b ^ (k + j) * ξ| := hscale
          _ ≤ Real.rpow b (-(j : ℝ)) * 2 :=
              mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (by linarith) _)
          _ ≤ Real.rpow b (-ε * |(j : ℝ)|) * 2 :=
              mul_le_mul_of_nonneg_right hpow (by norm_num)
          _ = 2 * Real.rpow b (-ε * |(j : ℝ)|) := by ring
      have hmin : min |b ^ k * ξ| (Real.rpow |b ^ k * ξ| (-β)) ≤
          |b ^ k * ξ| := min_le_left _ _
      have hFourier : ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
          H * |b ^ k * ξ| := by
        calc
          _ ≤ H * min |b ^ k * ξ| (Real.rpow |b ^ k * ξ| (-β)) := hdecay
          _ ≤ H * |b ^ k * ξ| := mul_le_mul_of_nonneg_left
            (min_le_left _ _) hH
      calc
        ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ ≤
            H * (2 * Real.rpow b (-ε * |(j : ℝ)|)) :=
              hFourier.trans (mul_le_mul_of_nonneg_left hv hH)
        _ ≤ H * max 2 (Real.rpow b β) *
              Real.rpow b (-ε * |(j : ℝ)|) := by
                have hmax : 2 ≤ max 2 (Real.rpow b β) := le_max_left _ _
                have hpowNonneg : 0 ≤ Real.rpow b (-ε * |(j : ℝ)|) :=
                  Real.rpow_nonneg (by linarith) _
                calc
                  H * (2 * Real.rpow b (-ε * |(j : ℝ)|)) =
                      (H * 2) * Real.rpow b (-ε * |(j : ℝ)|) := by ring
                  _ ≤ (H * max 2 (Real.rpow b β)) *
                      Real.rpow b (-ε * |(j : ℝ)|) := by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left hmax hH) hpowNonneg
                  _ = _ := by ring
  calc
    ‖measureSplittingNuFourier σ (b ^ k * ξ) *
        littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ)‖ =
      ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ *
        ‖littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ)‖ := norm_mul _ _
    _ ≤ ‖measureSplittingNuFourier σ (b ^ k * ξ)‖ * 1 :=
      mul_le_mul_of_nonneg_left hcutnorm (norm_nonneg _)
    _ ≤ (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
        Real.rpow b (-min 1 β * |(j : ℝ)|) := by
      simpa [H, ε, mul_assoc] using hnu

/-- The localized multiplier has the exact pointwise square-sum decay used
in the finite Plancherel estimate. -/
theorem localizedSquareNuMultiplier_square_sum_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (j : ℤ) (F : Finset ℤ) (ξ : ℝ) :
    (∑ k ∈ F, ‖measureSplittingNuFourier σ (b ^ k * ξ) *
      littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ)‖ ^ 2) ≤
      ((2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
        Real.rpow b (-min 1 β * |(j : ℝ)|)) ^ 2 * littlewoodPaleyNb b := by
  classical
  let C : ℝ := (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
    Real.rpow b (-min 1 β * |(j : ℝ)|)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  by_cases hξ : ξ = 0
  · subst ξ
    have hzero (k : ℤ) :
        ‖measureSplittingNuFourier σ (b ^ k * 0) *
          littlewoodPaleyCutoffDifference b (b ^ (k + j) * 0)‖ ^ 2 = 0 := by
      simp [littlewoodPaleyCutoffDifference]
    calc
      (∑ k ∈ F, ‖measureSplittingNuFourier σ (b ^ k * 0) *
          littlewoodPaleyCutoffDifference b (b ^ (k + j) * 0)‖ ^ 2) = 0 := by
            rw [Finset.sum_eq_zero]
            intro k hk
            exact hzero k
      _ ≤ C ^ 2 * littlewoodPaleyNb b := by positivity
  · let S : Finset ℤ := F.filter (fun k =>
      littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ) ≠ 0)
    let f : ℤ → ℝ := fun k =>
      ‖measureSplittingNuFourier σ (b ^ k * ξ) *
        littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ)‖ ^ 2
    have hterm (k : ℤ) (hk : k ∈ S) : f k ≤ C ^ 2 := by
      have hkF : k ∈ F := (Finset.mem_filter.mp hk).1
      have hkcut : littlewoodPaleyCutoffDifference b
          (b ^ (k + j) * ξ) ≠ 0 := (Finset.mem_filter.mp hk).2
      have hsingle := localizedSquareNuFourier_single_bound hσ hb hβ j k hξ hkcut
      dsimp [f, C]
      exact (sq_le_sq₀ (norm_nonneg _) hC).2 hsingle
    have hcard : S.card ≤ littlewoodPaleyNb b := by
      simpa [S] using localizedSquareActiveCard_le hb j F hξ
    have hzero : ∑ k ∈ F.filter (fun k =>
        ¬ littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ) ≠ 0), f k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hknot := (Finset.mem_filter.mp hk).2
      have hcut : littlewoodPaleyCutoffDifference b
          (b ^ (k + j) * ξ) = 0 := not_ne_iff.mp hknot
      simp [f, hcut]
    calc
      (∑ k ∈ F, f k) = ∑ k ∈ S, f k := by
        rw [← Finset.sum_filter_add_sum_filter_not
          (s := F)
          (p := fun k => littlewoodPaleyCutoffDifference b
            (b ^ (k + j) * ξ) ≠ 0) (f := f)]
        rw [hzero]
        simp [S]
      _ ≤ ∑ k ∈ S, C ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (S.card : ℝ) * C ^ 2 := by simp
      _ ≤ (littlewoodPaleyNb b : ℝ) * C ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg C)
      _ = C ^ 2 * littlewoodPaleyNb b := by ring
      _ = _ := by simpa [C]

/-- The L² realization of `P_n`, using the scaled Schwartz kernel already
identified with the paper's Littlewood--Paley projection. -/
noncomputable def localizedSquareProjectionL2 {b : ℝ}
    (hb : 1 < b) (n : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) := by
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  exact kernelConvolutionL2Operator
    (littlewoodPaleyScaledKernel b hb₀ n)
    (littlewoodPaleyScaledKernel_integrable hb₀ n)

/-- Source representative bridge for `localizedSquareProjectionL2`: this is
the same `P_n` used by `lj:littlewood-paley`, on every L² input. -/
theorem littlewoodPaleyProjectionLp_ae_eq_localizedSquareProjectionL2
    {b p : ℝ} (hb : 1 < b) (hp : 1 < p) (n : ℤ)
    (G : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hG₂ : MemLp (G : ℝ → ℂ) 2 volume) :
    (littlewoodPaleyProjectionLp hb hp n G : ℝ → ℂ) =ᵐ[volume]
      (localizedSquareProjectionL2 hb n (hG₂.toLp (G : ℝ → ℂ)) : ℝ → ℂ) := by
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  exact littlewoodPaleyProjectionLp_l2Kernel hb hp n G hG₂

private noncomputable def localizedSquareMultiplierProduct
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ) :
    {k : ℤ // k ∈ F} → Lp ℂ ∞ (volume : Measure ℝ) := by
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let Mν := initialSquareNuFiniteScaleMultipliers hSupp hσ b F
  let Mp (k : {k : ℤ // k ∈ F}) :=
    littlewoodPaleyKernelFourierLpTop
      (littlewoodPaleyScaledKernel b hb₀ (k.1 + j))
      (littlewoodPaleyScaledKernel_integrable hb₀ (k.1 + j))
  exact fun k => (ContinuousLinearMap.mul ℂ ℂ).holder ∞ (Mν k) (Mp k)

private theorem localizedSquareMultiplierProduct_ae
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ) :
    ∀ k : {k : ℤ // k ∈ F},
      (localizedSquareMultiplierProduct hSupp hσ hb j F k : ℝ → ℂ) =ᵐ[volume]
        fun ξ => measureSplittingNuFourier σ (b ^ k.1 * ξ) *
          littlewoodPaleyCutoffDifference b (b ^ (k.1 + j) * ξ) := by
  intro k
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  let μk : ComplexMeasure ℝ := initialSquareDilateComplexMeasure μ (b ^ k.1)
  have hμfinite : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  have hμkfinite : IsFiniteMeasure μk.variation := by
    dsimp [μk, μ]
    change IsFiniteMeasure
      ((initialSquareNuComplexMeasure σ).map (fun x : ℝ => b ^ k.1 * x)).variation
    infer_instance
  letI : IsFiniteMeasure μk.variation := hμkfinite
  have hν : (initialSquareNuFiniteScaleMultipliers hSupp hσ b F k : ℝ → ℂ) =ᵐ[volume]
      complexMeasureFourier μk := by
    change (complexMeasureFourierLpTop μk : ℝ → ℂ) =ᵐ[volume] _
    exact coeFn_complexMeasureFourierLpTop μk
  have hν' : (initialSquareNuFiniteScaleMultipliers hSupp hσ b F k : ℝ → ℂ) =ᵐ[volume]
      fun ξ => measureSplittingNuFourier σ (b ^ k.1 * ξ) := by
    filter_upwards [hν] with ξ hξ
    rw [hξ]
    exact initialSquareNuDilateComplexMeasure_fourier_eq (b ^ k.1) ξ
  have hp' :
      (littlewoodPaleyKernelFourierLpTop
        (littlewoodPaleyScaledKernel b hb₀ (k.1 + j))
        (littlewoodPaleyScaledKernel_integrable hb₀ (k.1 + j)) : ℝ → ℂ) =ᵐ[volume]
        fun ξ => littlewoodPaleyCutoffDifference b (b ^ (k.1 + j) * ξ) :=
    littlewoodPaleyScaledKernelFourierLpTop_ae hb hb₀ (k.1 + j)
  have hprod := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := ∞)
    (initialSquareNuFiniteScaleMultipliers hSupp hσ b F k)
    (littlewoodPaleyKernelFourierLpTop
      (littlewoodPaleyScaledKernel b hb₀ (k.1 + j))
      (littlewoodPaleyScaledKernel_integrable hb₀ (k.1 + j)))
  unfold localizedSquareMultiplierProduct
  filter_upwards [hprod, hν', hp'] with ξ hprod hν hψ
  rw [hprod, hν, hψ]
  simp [ContinuousLinearMap.mul_apply]

private theorem realLpMultiplier_mul
    (M N : Lp ℂ ∞ (volume : Measure ℝ))
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    realLpMultiplier M (realLpMultiplier N G) =
      realLpMultiplier ((ContinuousLinearMap.mul ℂ ℂ).holder ∞ M N) G := by
  apply Lp.ext
  filter_upwards [coeFn_realLpMultiplier M (realLpMultiplier N G),
    coeFn_realLpMultiplier N G,
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := ∞) M N,
    coeFn_realLpMultiplier ((ContinuousLinearMap.mul ℂ ℂ).holder ∞ M N) G]
    with ξ hM hN hMN hresult
  rw [hM, hN, hresult, hMN]
  simp [ContinuousLinearMap.mul] <;> ring

/-- A single localized cancellation output, with the source projection
realized by its scaled Schwartz kernel. -/
noncomputable def localizedSquareNuProjectionConvolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (j k : ℤ) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  initialSquareNuConvolution hSupp hσ b k
    (localizedSquareProjectionL2 hb (k + j) G)

private theorem localizedSquareNuProjectionConvolution_fourier
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ) (k : ℤ) (hk : k ∈ F)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    realFourierTransformL2
        (localizedSquareNuProjectionConvolution hSupp hσ hb j k G) =
      realLpMultiplier (localizedSquareMultiplierProduct hSupp hσ hb j F ⟨k, hk⟩)
        (realFourierTransformL2 G) := by
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  let μk : ComplexMeasure ℝ := initialSquareDilateComplexMeasure μ (b ^ k)
  have hμfinite : IsFiniteMeasure μ.variation := by
    exact initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  have hμkfinite : IsFiniteMeasure μk.variation := by
    change IsFiniteMeasure
      ((initialSquareNuComplexMeasure σ).map (fun x : ℝ => b ^ k * x)).variation
    infer_instance
  letI : IsFiniteMeasure μ.variation := hμfinite
  letI : IsFiniteMeasure μk.variation := hμkfinite
  let Mν := initialSquareNuFiniteScaleMultipliers hSupp hσ b F
  let Mp := littlewoodPaleyKernelFourierLpTop
    (littlewoodPaleyScaledKernel b hb₀ (k + j))
    (littlewoodPaleyScaledKernel_integrable hb₀ (k + j))
  have hνFourier :
      realFourierTransformL2
          (localizedSquareNuProjectionConvolution hSupp hσ hb j k G) =
        realLpMultiplier (Mν ⟨k, hk⟩)
          (realFourierTransformL2 (localizedSquareProjectionL2 hb (k + j) G)) := by
    change realFourierTransformL2
        (lpComplexMeasureConvolution 2 μk
          (localizedSquareProjectionL2 hb (k + j) G)) =
      realLpMultiplier (complexMeasureFourierLpTop μk)
        (realFourierTransformL2 (localizedSquareProjectionL2 hb (k + j) G))
    exact fourier_lpComplexMeasureConvolution μk
      (localizedSquareProjectionL2 hb (k + j) G)
  have hPfourier :
      realFourierTransformL2 (localizedSquareProjectionL2 hb (k + j) G) =
        realLpMultiplier Mp (realFourierTransformL2 G) := by
    let K := littlewoodPaleyScaledKernel b hb₀ (k + j)
    have hK : Integrable K volume := littlewoodPaleyScaledKernel_integrable hb₀ (k + j)
    simpa [localizedSquareProjectionL2, K, hb₀] using
      littlewoodPaleyKernelL2_fourier K hK G
  calc
    realFourierTransformL2
        (localizedSquareNuProjectionConvolution hSupp hσ hb j k G) =
      realLpMultiplier (Mν ⟨k, hk⟩)
          (realFourierTransformL2 (localizedSquareProjectionL2 hb (k + j) G)) :=
      hνFourier
    _ = realLpMultiplier (Mν ⟨k, hk⟩)
          (realLpMultiplier Mp (realFourierTransformL2 G)) :=
      congrArg (realLpMultiplier (Mν ⟨k, hk⟩)) hPfourier
    _ = realLpMultiplier
        ((ContinuousLinearMap.mul ℂ ℂ).holder ∞ (Mν ⟨k, hk⟩) Mp)
        (realFourierTransformL2 G) := realLpMultiplier_mul _ _ _
    _ = realLpMultiplier
        (localizedSquareMultiplierProduct hSupp hσ hb j F ⟨k, hk⟩)
        (realFourierTransformL2 G) := by
            simp [localizedSquareMultiplierProduct, Mν, Mp, hb₀]

private theorem localizedSquareMultiplierProduct_frequency_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (j : ℤ) (F : Finset ℤ) :
    ∀ᵐ ξ ∂(volume : Measure ℝ),
      (∑ k : {k : ℤ // k ∈ F},
        ‖(localizedSquareMultiplierProduct hSupp hσ hb j F k : ℝ → ℂ) ξ‖ ^ 2) ≤
        ((2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
          Real.rpow b (-min 1 β * |(j : ℝ)|)) ^ 2 * littlewoodPaleyNb b := by
  have hterms := localizedSquareMultiplierProduct_ae hSupp hσ hb j F
  have htermsAll : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ∀ k : {k : ℤ // k ∈ F},
        (localizedSquareMultiplierProduct hSupp hσ hb j F k : ℝ → ℂ) ξ =
          measureSplittingNuFourier σ (b ^ k.1 * ξ) *
            littlewoodPaleyCutoffDifference b (b ^ (k.1 + j) * ξ) := by
    rw [ae_all_iff]
    exact hterms
  filter_upwards [htermsAll] with ξ hξ
  calc
    (∑ k : {k : ℤ // k ∈ F},
        ‖(localizedSquareMultiplierProduct hSupp hσ hb j F k : ℝ → ℂ) ξ‖ ^ 2) =
        ∑ k : {k : ℤ // k ∈ F},
          ‖measureSplittingNuFourier σ (b ^ k.1 * ξ) *
            littlewoodPaleyCutoffDifference b (b ^ (k.1 + j) * ξ)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hξ k]
    _ = ∑ k ∈ F.attach, ‖measureSplittingNuFourier σ (b ^ (k : ℤ) * ξ) *
          littlewoodPaleyCutoffDifference b (b ^ ((k : ℤ) + j) * ξ)‖ ^ 2 :=
            Finset.sum_coe_sort_eq_attach F (fun n : {k // k ∈ F} =>
              ‖measureSplittingNuFourier σ (b ^ (n : ℤ) * ξ) *
                littlewoodPaleyCutoffDifference b (b ^ ((n : ℤ) + j) * ξ)‖ ^ 2)
    _ = ∑ k ∈ F, ‖measureSplittingNuFourier σ (b ^ k * ξ) *
          littlewoodPaleyCutoffDifference b (b ^ (k + j) * ξ)‖ ^ 2 :=
            Finset.sum_attach F (fun n : ℤ =>
              ‖measureSplittingNuFourier σ (b ^ n * ξ) *
                littlewoodPaleyCutoffDifference b (b ^ (n + j) * ξ)‖ ^ 2)
    _ ≤ ((2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
          Real.rpow b (-min 1 β * |(j : ℝ)|)) ^ 2 * littlewoodPaleyNb b :=
        localizedSquareNuMultiplier_square_sum_bound hσ hb hβ j F ξ

private theorem localizedSquare_lp_two_norm_sq_eq_integral_norm_sq
    (U : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖U‖ ^ 2 = ∫ x, ‖U x‖ ^ 2 ∂(volume : Measure ℝ) := by
  calc
    ‖U‖ ^ 2 = RCLike.re (inner ℂ U U) :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) U).symm
    _ = RCLike.re (∫ x, inner ℂ (U x) (U x) ∂(volume : Measure ℝ)) := by
      rw [L2.inner_def]
    _ = ∫ x, RCLike.re (inner ℂ (U x) (U x)) ∂(volume : Measure ℝ) :=
      (integral_re (L2.integrable_inner U U)).symm
    _ = ∫ x, ‖U x‖ ^ 2 ∂(volume : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (U x)

private noncomputable def localizedSquareFiniteMultiplier
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ) :
    {k : ℤ // k ∈ F} → Lp ℂ ∞ (volume : Measure ℝ) :=
  localizedSquareMultiplierProduct hSupp hσ hb j F

/-- The `L²` finite-scale estimate in `lj:localized-square`. This is the
finite Plancherel step, with the exact overlap factor `sqrt(N_b)`. -/
theorem localizedSquare_finite_l2_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (j : ℤ) (F : Finset ℤ) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Real.sqrt (∫ x, ∑ k ∈ F,
      ‖localizedSquareNuProjectionConvolution hSupp hσ hb j k G x‖ ^ 2
        ∂(volume : Measure ℝ)) ≤
      (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
        Real.sqrt (littlewoodPaleyNb b) *
          Real.rpow b (-(min 1 β * |(j : ℝ)|)) * ‖G‖ := by
  classical
  let M : {k : ℤ // k ∈ F} → Lp ℂ ∞ (volume : Measure ℝ) :=
    localizedSquareFiniteMultiplier hSupp hσ hb j F
  let a : ℝ := (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
    Real.rpow b (-(min 1 β * |(j : ℝ)|))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hcoeff : ∀ᵐ ξ ∂(volume : Measure ℝ),
      (∑ k : {k : ℤ // k ∈ F}, ‖(M k : ℝ → ℂ) ξ‖ ^ 2) ≤
        a ^ 2 * littlewoodPaleyNb b := by
    simpa [M, a, localizedSquareFiniteMultiplier] using
      localizedSquareMultiplierProduct_frequency_bound hSupp hσ hb hβ j F
  have hC : 0 ≤ a ^ 2 * littlewoodPaleyNb b := by positivity
  have hmultiplier_bound :=
    finiteFourierMultiplierSquareFunction_norm_le_of_frequency_bound
      M G hC hcoeff
  have hroot : Real.sqrt (a ^ 2 * littlewoodPaleyNb b) =
      a * Real.sqrt (littlewoodPaleyNb b) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
      abs_of_nonneg ha]
  have hconv (k : {k : ℤ // k ∈ F}) :
      localizedSquareNuProjectionConvolution hSupp hσ hb j k.1 G =
        realFourierMultiplier (M k) G := by
    apply realFourierTransformL2.injective
    rw [localizedSquareNuProjectionConvolution_fourier
      hSupp hσ hb j F k.1 k.2 G]
    simp [M, localizedSquareFiniteMultiplier, realFourierMultiplier]
  have hconvAll : ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ k : {k : ℤ // k ∈ F},
        localizedSquareNuProjectionConvolution hSupp hσ hb j k.1 G x =
          realFourierMultiplier (M k) G x := by
    rw [ae_all_iff]
    intro k
    exact Lp.ext_iff.mp (hconv k)
  have hsqAE : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖finiteFourierMultiplierSquareFunctionLp M G x‖ ^ 2 =
        ∑ k ∈ F,
          ‖localizedSquareNuProjectionConvolution hSupp hσ hb j k G x‖ ^ 2 := by
    have hcoea := coeFn_finiteFourierMultiplierSquareFunctionLp M G
    filter_upwards [hcoea, hconvAll] with x hx houtputs
    have hnonneg : 0 ≤ ∑ k : {k : ℤ // k ∈ F},
        ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2 :=
      Finset.sum_nonneg fun k hk => sq_nonneg _
    calc
      ‖finiteFourierMultiplierSquareFunctionLp M G x‖ ^ 2 =
          (Real.sqrt (∑ k : {k : ℤ // k ∈ F},
            ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2)) ^ 2 := by
              rw [hx]
              simp [finiteFourierMultiplierSquareFunction,
                Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ = ∑ k : {k : ℤ // k ∈ F},
          ‖(realFourierMultiplier (M k) G : ℝ → ℂ) x‖ ^ 2 :=
            Real.sq_sqrt hnonneg
      _ =
          ∑ k ∈ F, ‖localizedSquareNuProjectionConvolution
            hSupp hσ hb j k G x‖ ^ 2 := by
              calc
                _ = ∑ k : {k : ℤ // k ∈ F},
                    ‖localizedSquareNuProjectionConvolution
                      hSupp hσ hb j k.1 G x‖ ^ 2 := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        rw [← houtputs k]
                _ = ∑ k ∈ F.attach, ‖localizedSquareNuProjectionConvolution
                    hSupp hσ hb j (k : ℤ) G x‖ ^ 2 :=
                      Finset.sum_coe_sort_eq_attach F (fun n : {k // k ∈ F} =>
                        ‖localizedSquareNuProjectionConvolution
                          hSupp hσ hb j (n : ℤ) G x‖ ^ 2)
                _ = ∑ k ∈ F, ‖localizedSquareNuProjectionConvolution
                    hSupp hσ hb j k G x‖ ^ 2 :=
                      Finset.sum_attach F (fun n : ℤ =>
                        ‖localizedSquareNuProjectionConvolution
                          hSupp hσ hb j n G x‖ ^ 2)
  have henergy :
      (∫ x, ∑ k ∈ F,
        ‖localizedSquareNuProjectionConvolution hSupp hσ hb j k G x‖ ^ 2
          ∂(volume : Measure ℝ)) =
        ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 := by
    calc
      _ = ∫ x, ‖finiteFourierMultiplierSquareFunctionLp M G x‖ ^ 2
            ∂(volume : Measure ℝ) := by
              apply integral_congr_ae
              filter_upwards [hsqAE] with x hx
              exact hx.symm
      _ = ‖finiteFourierMultiplierSquareFunctionLp M G‖ ^ 2 :=
            (localizedSquare_lp_two_norm_sq_eq_integral_norm_sq _).symm
  have hnorm :
      ‖finiteFourierMultiplierSquareFunctionLp M G‖ ≤
        a * Real.sqrt (littlewoodPaleyNb b) * ‖G‖ := by
    calc
      _ ≤ Real.sqrt (a ^ 2 * littlewoodPaleyNb b) * ‖G‖ := hmultiplier_bound
      _ = a * Real.sqrt (littlewoodPaleyNb b) * ‖G‖ := by rw [hroot]
  rw [henergy, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa [a, mul_assoc, mul_left_comm, mul_comm] using hnorm

/-- The `Lᵘ` realization of convolution by the dilated cancellation measure.
This is the diagonal operator appearing in the conditional clause of
`lj:localized-square`. -/
noncomputable def localizedSquareNuLpConvolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (u b : ℝ) (hu : 1 < u) (k : ℤ)
    (G : Lp ℂ (ENNReal.ofReal u) (volume : Measure ℝ)) :
    Lp ℂ (ENNReal.ofReal u) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal u) :=
    ⟨ENNReal.one_le_ofReal.mpr hu.le⟩
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμvar : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure μ.variation := hμvar
  let μk := initialSquareDilateComplexMeasure μ (b ^ k)
  have hμkvar : IsFiniteMeasure μk.variation := by
    dsimp [μk, μ, initialSquareDilateComplexMeasure]
    infer_instance
  letI : IsFiniteMeasure μk.variation := hμkvar
  exact lpComplexMeasureConvolution (ENNReal.ofReal u) μk G

private theorem localizedSquare_sum_subtype_eq_nested
    {F : Finset ℤ} (f : {k : ℤ // k ∈ F} → ℝ) (g : ℤ → ℝ)
    (hfg : ∀ k, f k = g k.1) :
    (∑ k : {k : ℤ // k ∈ F}, f k) = ∑ k ∈ F, g k := by
  calc
    (∑ k : {k : ℤ // k ∈ F}, f k) =
        ∑ k ∈ F.attach, g (k : ℤ) := by
          calc
            _ = ∑ k : {k : ℤ // k ∈ F}, g k.1 := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hfg k
            _ = ∑ k ∈ F.attach, g (k : ℤ) :=
              Finset.sum_coe_sort_eq_attach F (fun k : {k // k ∈ F} => g k.1)
    _ = ∑ k ∈ F, g k := Finset.sum_attach F g

/-- Conditional `Lᵘ(ℓ²)` clause of `lj:localized-square`: a uniform
finite-family bound for the diagonal cancellation operator transfers through
the Littlewood--Paley upper estimate, uniformly in the scale shift and the
finite index set. -/
theorem localizedSquare_finite_lp_bound_of_diagonal
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b u : ℝ} (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hu : 1 < u) (B : NNReal)
    (hdiag : ∀ (F : Finset ℤ)
      (g : {k : ℤ // k ∈ F} → Lp ℂ (ENNReal.ofReal u) (volume : Measure ℝ)),
      lpNorm (fun x : ℝ => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp u b hu k.1 (g k) : ℝ → ℂ) x))
          (ENNReal.ofReal u) volume ≤
        (B : ℝ) * lpNorm (fun x : ℝ => WithLp.toLp 2
          (fun k : {k : ℤ // k ∈ F} => (g k : ℝ → ℂ) x))
          (ENNReal.ofReal u) volume)
    (j : ℤ) (F : Finset ℤ)
    (f : Lp ℂ (ENNReal.ofReal u) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => WithLp.toLp 2
      (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp u b hu k.1
          (littlewoodPaleyProjectionLp hb hu (k.1 + j) f) : ℝ → ℂ) x))
      (ENNReal.ofReal u) volume ≤
      (B : ℝ) * littlewoodPaleyUpperConstant u b
        (ne_of_gt (by linarith : 0 < b)) * ‖f‖ := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal u
  let hb₀ : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hu.le⟩
  let g : {k : ℤ // k ∈ F} → Lp ℂ P (volume : Measure ℝ) :=
    fun k => littlewoodPaleyProjectionLp hb hu (k.1 + j) f
  let V : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F} := fun x =>
    WithLp.toLp 2 (fun k => (g k : ℝ → ℂ) x)
  let U : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F} := fun x =>
    WithLp.toLp 2 (fun k =>
      (localizedSquareNuLpConvolution hSupp u b hu k.1 (g k) : ℝ → ℂ) x)
  let Fshift : Finset ℤ := F.image (fun k => k + j)
  have hinj : Set.InjOn (fun k : ℤ => k + j) F := by
    intro x hx y hy hxy
    exact add_right_cancel hxy
  have hV : MemLp V P volume := by
    apply MemLp.of_eval_piLp
    intro k
    exact Lp.memLp (g k)
  have hpoint (x : ℝ) :
      ‖V x‖ = Real.sqrt (∑ n ∈ Fshift,
        ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2) := by
    have hcoords :
        (∑ k : {k : ℤ // k ∈ F}, ‖V x k‖ ^ 2) =
          ∑ k ∈ F, ‖(littlewoodPaleyProjectionLp hb hu (k + j) f : ℝ → ℂ) x‖ ^ 2 := by
      calc
        _ = ∑ k : {k : ℤ // k ∈ F},
            ‖(littlewoodPaleyProjectionLp hb hu (k.1 + j) f : ℝ → ℂ) x‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              simp [V, g]
        _ = ∑ k ∈ F,
            ‖(littlewoodPaleyProjectionLp hb hu (k + j) f : ℝ → ℂ) x‖ ^ 2 :=
              localizedSquare_sum_subtype_eq_nested
                (fun k => ‖(littlewoodPaleyProjectionLp hb hu (k.1 + j) f : ℝ → ℂ) x‖ ^ 2)
                (fun k => ‖(littlewoodPaleyProjectionLp hb hu (k + j) f : ℝ → ℂ) x‖ ^ 2)
                (fun _ => rfl)
    have hshift :
        (∑ k ∈ F, ‖(littlewoodPaleyProjectionLp hb hu (k + j) f : ℝ → ℂ) x‖ ^ 2) =
          ∑ n ∈ Fshift,
            ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2 := by
      dsimp [Fshift]
      exact (Finset.sum_image (f := fun n : ℤ =>
        ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2) hinj).symm
    calc
      ‖V x‖ = Real.sqrt (‖V x‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt (∑ k : {k : ℤ // k ∈ F}, ‖V x k‖ ^ 2) := by
        rw [EuclideanSpace.norm_sq_eq]
      _ = Real.sqrt (∑ n ∈ Fshift,
          ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2) := by
        rw [hcoords, hshift]
  have hLpNormV :
      lpNorm (fun x : ℝ => V x) P volume =
        lpNorm (fun x : ℝ => Real.sqrt (∑ n ∈ Fshift,
          ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2))
          P volume := by
    unfold lpNorm
    apply congrArg ENNReal.toReal
    calc
      eLpNorm (fun x : ℝ => V x) P volume =
          eLpNorm (fun x : ℝ => ‖V x‖) P volume :=
            (eLpNorm_norm (fun x : ℝ => V x) hV.aestronglyMeasurable).symm
      _ = eLpNorm (fun x : ℝ => Real.sqrt (∑ n ∈ Fshift,
            ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2)) P volume :=
            eLpNorm_congr_ae (Filter.Eventually.of_forall hpoint)
  have hLP : lpNorm (fun x : ℝ => Real.sqrt (∑ n ∈ Fshift,
      ‖(littlewoodPaleyProjectionLp hb hu n f : ℝ → ℂ) x‖ ^ 2))
        P volume ≤ littlewoodPaleyUpperConstant u b hb₀ * ‖f‖ := by
    simpa [P] using littlewoodPaleyUpper_square hb hu Fshift f
  have hInput : lpNorm (fun x : ℝ => V x) P volume ≤
      littlewoodPaleyUpperConstant u b hb₀ * ‖f‖ := by
    rw [hLpNormV]
    exact hLP
  have hB : 0 ≤ (B : ℝ) := B.2
  have hdiagBound := hdiag F g
  change lpNorm (fun x : ℝ => U x) P volume ≤
      (B : ℝ) * lpNorm (fun x : ℝ => V x) P volume at hdiagBound
  calc
    lpNorm (fun x : ℝ => U x) P volume ≤
        (B : ℝ) * lpNorm (fun x : ℝ => V x) P volume := by
          simpa [U, V, g, localizedSquareNuLpConvolution] using hdiagBound
    _ ≤ (B : ℝ) * (littlewoodPaleyUpperConstant u b hb₀ * ‖f‖) :=
      mul_le_mul_of_nonneg_left hInput hB
    _ = (B : ℝ) * littlewoodPaleyUpperConstant u b hb₀ * ‖f‖ := by ring

#print axioms localizedSquare_finite_l2_bound
#print axioms localizedSquare_finite_lp_bound_of_diagonal

end
end FractionalPrimes.Literature.JSW

end
