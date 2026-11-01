module

public import FractionalPrimes.Literature.Twisted.FullFrequencyMellinData
public import FractionalPrimes.Literature.Twisted.LocalMassMellinIdentity
public import FractionalPrimes.Literature.Polynomial.NormalizedWindowKernelBounds
public import FractionalPrimes.PolynomialKernelAngularFourierProperties
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory

noncomputable section

/-- The exact Mellin kernel attached to full-frequency coefficient data has
the source's pointwise size and tail envelope. The minimum is assigned value
one at zero. -/
theorem fullFrequencyMellinKernel_norm_le
    (d : FullFrequencyMellinData) (t : ℝ) :
    ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
      (3 / Real.sqrt d.X) *
        (if t = 0 then 1 else min 1 ((d.X / d.H) / |t|)) := by
  have hX : 0 < d.X := by linarith [d.X_lower]
  have hbounds := Polynomial.normalizedWindowKernelBounds
    d.X d.H d.H t hX d.H_pos le_rfl d.H_upper
  have hsize := hbounds.1
  have hdecay := hbounds.2.2.1
  have hpow : d.X ^ ((-1 / 2 : ℝ)) = (Real.sqrt d.X)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hX.le, ← Real.sqrt_eq_rpow]
  have hsize' :
      ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
        1 / Real.sqrt d.X := by
    calc
      ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
          d.X ^ ((-1 / 2 : ℝ)) := hsize
      _ = (Real.sqrt d.X)⁻¹ := hpow
      _ = 1 / Real.sqrt d.X := by rw [one_div]
  have hdecay' (ht : t ≠ 0) :
      ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
        (3 / Real.sqrt d.X) * ((d.X / d.H) / |t|) := by
    have hbase := hdecay ht
    have hsqrt : 0 < Real.sqrt d.X := Real.sqrt_pos.2 hX
    calc
      ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
          3 * Real.sqrt d.X / (d.H * |t|) := hbase
      _ = (3 / Real.sqrt d.X) * ((d.X / d.H) / |t|) := by
        field_simp [d.H_pos.ne', (abs_pos.mpr ht).ne', hsqrt.ne']
        rw [Real.sq_sqrt hX.le]
  have hsize3 :
      ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
        3 / Real.sqrt d.X := by
    calc
      ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
          1 / Real.sqrt d.X := hsize'
      _ ≤ 3 / Real.sqrt d.X := by
        exact div_le_div_of_nonneg_right (by norm_num)
          (Real.sqrt_nonneg _)
  by_cases ht : t = 0
  · simpa [ht] using hsize3
  · rw [if_neg ht]
    have hratio : 0 ≤ (d.X / d.H) / |t| :=
      div_nonneg (div_nonneg hX.le d.H_pos.le) (abs_nonneg _)
    by_cases hr : (d.X / d.H) / |t| ≤ 1
    · rw [min_eq_right hr]
      exact hdecay' ht
    · rw [min_eq_left (le_of_not_ge hr)]
      simpa using hsize3

/-- Each cumulative full-frequency integral is bounded by its attained
envelope, scaled by the ratio of its endpoint to the base frequency. This
bound does not assume a relation between `T0` and `W`. -/
theorem fullFrequencyAbsoluteIntegral_le_envelope
    (d : FullFrequencyMellinData) {T0 W U : ℝ}
    (hT0 : 0 < T0) (hW : 2 ≤ W)
    (hU : T0 ≤ U ∧ U ≤ T0 * W ^ 4) :
    fullFrequencyAbsoluteIntegral d U ≤
      (U / T0) * fullFrequencyEnvelope d T0 W := by
  have hUpos : 0 < U := lt_of_lt_of_le hT0 hU.1
  obtain ⟨Umax, hUmax, hmaxEq, hmax⟩ :=
    fullFrequencyEnvelope_hasMaximum d hT0 hW
  have hobj := hmax U hU
  have hobj' :
      (T0 / U) * fullFrequencyAbsoluteIntegral d U ≤
        fullFrequencyEnvelope d T0 W := by
    simpa [fullFrequencyEnvelopeObjective] using hobj
  have hcancel :
      (U / T0) * ((T0 / U) * fullFrequencyAbsoluteIntegral d U) =
        fullFrequencyAbsoluteIntegral d U := by
    field_simp [hT0.ne', hUpos.ne']
  calc
    fullFrequencyAbsoluteIntegral d U =
        (U / T0) * ((T0 / U) * fullFrequencyAbsoluteIntegral d U) :=
      hcancel.symm
    _ ≤ (U / T0) * fullFrequencyEnvelope d T0 W :=
      mul_le_mul_of_nonneg_left hobj'
        (div_nonneg (le_trans hT0.le hU.1) hT0.le)

private theorem exists_fullFrequency_dyadic_bracket {x : ℝ} {n : ℕ}
    (hx : 1 < x) (hxn : x ≤ (2 : ℝ) ^ n) :
    ∃ j < n, (2 : ℝ) ^ j < x ∧ x ≤ (2 : ℝ) ^ (j + 1) := by
  revert x hx hxn
  induction n with
  | zero =>
      intro x hx hxn
      simp at hxn
      linarith
  | succ n ih =>
      intro x hx hxn
      rw [pow_succ] at hxn
      by_cases hx2 : x ≤ 2
      · refine ⟨0, Nat.zero_lt_succ _, ?_, ?_⟩
        · simpa using hx
        · simpa using hx2
      · have hx2' : 2 < x := lt_of_not_ge hx2
        have hxdiv : 1 < x / 2 := by linarith
        have hdivn : x / 2 ≤ (2 : ℝ) ^ n :=
          (div_le_iff₀ (by norm_num)).2 hxn
        obtain ⟨j, hjn, hlow, hupp⟩ := ih hxdiv hdivn
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · have hlow' : (2 : ℝ) ^ j * 2 < x :=
            (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hlow
          simpa [pow_succ] using hlow'
        · have hupp' : x ≤ (2 : ℝ) ^ (j + 1) * 2 :=
            (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hupp
          simpa [pow_succ, Nat.add_assoc] using hupp'

private noncomputable def fullFrequencyDyadicBandCount (W : ℝ) : ℕ :=
  Nat.ceil (4 * Real.log W / Real.log 2)

private theorem fullFrequencyDyadicBandCount_covers
    {W : ℝ} (hW : 2 ≤ W) :
    W ^ 4 ≤ (2 : ℝ) ^ fullFrequencyDyadicBandCount W := by
  have hlogW : 0 < Real.log W := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : 4 * Real.log W / Real.log 2 ≤
      (fullFrequencyDyadicBandCount W : ℝ) := Nat.le_ceil _
  have hmul : 4 * Real.log W ≤
      (fullFrequencyDyadicBandCount W : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp hceil
  have hexp := Real.exp_le_exp.mpr hmul
  have hleft : Real.exp (4 * Real.log W) = W ^ 4 := by
    have hfour : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [hfour, Real.exp_nat_mul, Real.exp_log (by linarith : 0 < W)]
  have hright :
      Real.exp ((fullFrequencyDyadicBandCount W : ℝ) * Real.log 2) =
        (2 : ℝ) ^ fullFrequencyDyadicBandCount W := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hleft, hright] at hexp
  exact hexp

private theorem fullFrequencyDyadicBandCount_bound
    {W : ℝ} (hW : 2 ≤ W) :
    1 + 2 * (fullFrequencyDyadicBandCount W : ℝ) ≤
      3 + 12 * Real.log W := by
  have hlogW : 0 ≤ Real.log W := (Real.log_pos (by linarith)).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : (fullFrequencyDyadicBandCount W : ℝ) <
      4 * Real.log W / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by positivity) hlog2.le)
  have hlogLower : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hratio : 8 * Real.log W / Real.log 2 ≤ 12 * Real.log W :=
    (div_le_iff₀ hlog2).2 (by
      have hmul := mul_le_mul_of_nonneg_left hlogLower
        (show 0 ≤ 12 * Real.log W by positivity)
      nlinarith)
  calc
    1 + 2 * (fullFrequencyDyadicBandCount W : ℝ) ≤
        1 + 2 * (4 * Real.log W / Real.log 2 + 1) := by nlinarith
    _ = 3 + 8 * Real.log W / Real.log 2 := by ring
    _ ≤ 3 + 12 * Real.log W := by linarith

private def fullFrequencyDyadicPieceSet (T0 W : ℝ) {J : ℕ} :
    Unit ⊕ Fin J → Set ℝ
  | Sum.inl _ => (fun t : ℝ => abs t) ⁻¹' Set.Iic T0
  | Sum.inr j =>
      (fun t : ℝ => abs t) ⁻¹' Set.Ioc (T0 * (2 : ℝ) ^ j.val)
        (min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)))

private theorem fullFrequencyDyadicPieceSet_measurable
    {T0 W : ℝ} {J : ℕ} (i : Unit ⊕ Fin J) :
    MeasurableSet (fullFrequencyDyadicPieceSet T0 W i) := by
  cases i with
  | inl u =>
      change MeasurableSet ((fun t : ℝ => abs t) ⁻¹' Set.Iic T0)
      exact measurableSet_Iic.preimage continuous_abs.measurable
  | inr j =>
      change MeasurableSet ((fun t : ℝ => abs t) ⁻¹'
        Set.Ioc (T0 * (2 : ℝ) ^ j.val)
          (min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1))))
      exact measurableSet_Ioc.preimage continuous_abs.measurable

private theorem fullFrequencyBall_isCompact {U : ℝ} :
    IsCompact ((fun t : ℝ => abs t) ⁻¹' Set.Iic U) := by
  have hclosed : IsClosed ((fun t : ℝ => abs t) ⁻¹' Set.Iic U) := by
    change IsClosed ((fun t : ℝ => abs t) ⁻¹' Set.Iic U)
    exact isClosed_Iic.preimage continuous_abs
  let R : ℝ := max 0 U
  have hsub : ((fun t : ℝ => abs t) ⁻¹' Set.Iic U) ⊆ Set.Icc (-R) R := by
    intro t ht
    change abs t ≤ U at ht
    have hR : abs t ≤ R := ht.trans (le_max_right 0 U)
    constructor
    · dsimp [R]
      exact (neg_le_neg hR).trans (neg_abs_le t)
    · exact (le_abs_self t).trans hR
  exact IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact (Set.Icc (-R) R))
    hclosed hsub

private theorem fullFrequencyDyadicPieceSet_iUnion_eq
    {T0 W : ℝ} (hT0 : 0 < T0) (hW : 2 ≤ W) :
    (⋃ i : Unit ⊕ Fin (fullFrequencyDyadicBandCount W),
      fullFrequencyDyadicPieceSet T0 W i) =
      (fun t : ℝ => abs t) ⁻¹' Set.Iic (T0 * W ^ 4) := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl u =>
        change abs t ≤ T0 at hi
        have hW1 : 1 ≤ W := by linarith
        have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
        exact le_trans hi (by nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hW4)])
    | inr j =>
        change T0 * (2 : ℝ) ^ j.val < abs t ∧
          abs t ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at hi
        exact (le_min_iff.mp hi.2).1
  · intro ht
    change abs t ≤ T0 * W ^ 4 at ht
    by_cases hlow : abs t ≤ T0
    · exact ⟨Sum.inl (), hlow⟩
    · have habove : T0 < |t| := lt_of_not_ge hlow
      have hW4pow := fullFrequencyDyadicBandCount_covers hW
      have hxlo : 1 < abs t / T0 := (lt_div_iff₀ hT0).2 (by simpa using habove)
      have hxhi : abs t / T0 ≤
          (2 : ℝ) ^ fullFrequencyDyadicBandCount W :=
        (div_le_iff₀ hT0).2 (by nlinarith [ht, hW4pow])
      obtain ⟨j, hjJ, hpowlo, hpowhi⟩ :=
        exists_fullFrequency_dyadic_bracket hxlo hxhi
      let j' : Fin (fullFrequencyDyadicBandCount W) := ⟨j, hjJ⟩
      refine ⟨Sum.inr j', ?_⟩
      change T0 * (2 : ℝ) ^ j < abs t ∧
        abs t ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j + 1))
      constructor
      · simpa [mul_comm] using (lt_div_iff₀ hT0).mp hpowlo
      · apply le_min
        · exact ht
        · have hupper := (div_le_iff₀ hT0).mp hpowhi
          simpa [mul_comm] using hupper

private theorem fullFrequencyDyadicPieceSet_pairwiseDisjoint
    {T0 W : ℝ} {J : ℕ} (hT0 : 0 ≤ T0) :
    Pairwise (fun i j : Unit ⊕ Fin J =>
      Disjoint (fullFrequencyDyadicPieceSet T0 W i)
        (fullFrequencyDyadicPieceSet T0 W j)) := by
  intro i k hik
  cases i with
  | inl u =>
      cases k with
      | inl v =>
          cases u
          cases v
          exact (hik rfl).elim
      | inr l =>
          apply Set.disjoint_left.mpr
          intro t hlow hband
          change |t| ≤ T0 at hlow
          change T0 * (2 : ℝ) ^ l.val < |t| ∧ _ at hband
          have hp : 1 ≤ (2 : ℝ) ^ l.val := one_le_pow₀ (by norm_num)
          have hTle : T0 ≤ T0 * (2 : ℝ) ^ l.val :=
            by nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hp)]
          linarith
  | inr j =>
      cases k with
      | inl u =>
          apply Set.disjoint_left.mpr
          intro t hband hlow
          change T0 * (2 : ℝ) ^ j.val < |t| ∧ _ at hband
          change |t| ≤ T0 at hlow
          have hp : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
          have hTle : T0 ≤ T0 * (2 : ℝ) ^ j.val :=
            by nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hp)]
          linarith
      | inr l =>
          apply Set.disjoint_left.mpr
          intro t hbandj hbandl
          change T0 * (2 : ℝ) ^ j.val < |t| ∧
            |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at hbandj
          change T0 * (2 : ℝ) ^ l.val < |t| ∧
            |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (l.val + 1)) at hbandl
          have hvals : j.val ≠ l.val := by
            intro h
            apply hik
            exact congrArg Sum.inr (Fin.ext h)
          rcases lt_or_gt_of_ne hvals with hjl | hlj
          · have hp : (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ l.val := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
            have hupper := hbandj.2.trans (min_le_right _ _)
            nlinarith [hbandl.1, hupper, hT0]
          · have hp : (2 : ℝ) ^ (l.val + 1) ≤ (2 : ℝ) ^ j.val := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
            have hupper := hbandl.2.trans (min_le_right _ _)
            nlinarith [hbandj.1, hupper, hT0]

private noncomputable def fullFrequencyMellinKernelWeight
    (T0 t : ℝ) : ℝ := T0 / max T0 |t|

private theorem fullFrequencyMellinKernelWeight_eq
    {T0 t : ℝ} (hT0 : 0 < T0) :
    fullFrequencyMellinKernelWeight T0 t =
      (if t = 0 then 1 else min 1 (T0 / |t|)) := by
  by_cases ht : t = 0
  · simp [fullFrequencyMellinKernelWeight, ht, max_eq_left hT0.le,
      div_self hT0.ne']
  · have hAbs : 0 < |t| := abs_pos.mpr ht
    by_cases h : |t| ≤ T0
    · have hratio : 1 ≤ T0 / |t| := (le_div_iff₀ hAbs).2 (by simpa using h)
      simp [fullFrequencyMellinKernelWeight, ht, max_eq_left h,
        min_eq_left hratio, hT0.ne']
    · have h' : T0 < |t| := lt_of_not_ge h
      have hratio : T0 / |t| ≤ 1 :=
        (div_le_iff₀ hAbs).2 (by simpa using h'.le)
      simp [fullFrequencyMellinKernelWeight, ht, max_eq_right h'.le,
        min_eq_right hratio]

/-- Full-frequency dyadic integration for the exact attained envelope. This
includes the low-frequency ball and needs only `W ≥ 2`, not `T0 ≥ W`. -/
theorem fullFrequencyMellinWeightedIntegral_le
    (d : FullFrequencyMellinData) {T0 W : ℝ}
    (hT0 : 0 < T0) (hW : 2 ≤ W) :
    (∫ t in (fun t : ℝ => |t|) ⁻¹' Set.Iic (T0 * W ^ 4),
      ‖fullFrequencyMellinPolynomial d t‖ *
        (if t = 0 then 1 else min 1 (T0 / |t|))) ≤
      (3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W := by
  classical
  let E : Set ℝ := (fun t : ℝ => |t|) ⁻¹' Set.Iic (T0 * W ^ 4)
  let J : ℕ := fullFrequencyDyadicBandCount W
  let P : Unit ⊕ Fin J → Set ℝ := fullFrequencyDyadicPieceSet T0 W
  let weight : ℝ → ℝ := fullFrequencyMellinKernelWeight T0
  let g : ℝ → ℝ := fun t => ‖fullFrequencyMellinPolynomial d t‖ * weight t
  have hcap : T0 ≤ T0 * W ^ 4 := by
    have hW1 : 1 ≤ W := by linarith
    have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
    nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hW4)]
  have hEcompact : IsCompact E := by
    simpa [E] using fullFrequencyBall_isCompact (U := T0 * W ^ 4)
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_Iic.preimage continuous_abs.measurable
  have hAcont : Continuous (fullFrequencyMellinPolynomial d) :=
    fullFrequencyMellinPolynomial_continuous d
  have hnormcont : Continuous (fun t : ℝ =>
      ‖fullFrequencyMellinPolynomial d t‖) := continuous_norm.comp hAcont
  have hweightcont : Continuous weight := by
    dsimp [weight, fullFrequencyMellinKernelWeight]
    refine continuous_const.div (continuous_const.max continuous_abs) ?_
    intro t
    exact ne_of_gt (lt_of_lt_of_le hT0 (le_max_left T0 |t|))
  have hgcont : Continuous g := by
    dsimp [g]
    exact hnormcont.mul hweightcont
  have hgE : IntegrableOn g E := hgcont.continuousOn.integrableOn_compact hEcompact
  have hcover : (⋃ i : Unit ⊕ Fin J, P i) = E := by
    simpa [E, P, J] using fullFrequencyDyadicPieceSet_iUnion_eq hT0 hW
  have hPieceMeas : ∀ i : Unit ⊕ Fin J, MeasurableSet (P i) := by
    intro i
    simpa [P] using fullFrequencyDyadicPieceSet_measurable i
  have hPairwise : Pairwise (fun i j : Unit ⊕ Fin J =>
      Disjoint (P i) (P j)) := by
    simpa [P] using fullFrequencyDyadicPieceSet_pairwiseDisjoint
      (T0 := T0) (W := W) (J := J) hT0.le
  have hUnionIntegrable : IntegrableOn g (⋃ i : Unit ⊕ Fin J, P i) := by
    rw [hcover]
    exact hgE
  have hdecomp :
      (∫ t in E, g t) = ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t := by
    calc
      (∫ t in E, g t) = ∫ t in ⋃ i : Unit ⊕ Fin J, P i, g t := by rw [hcover]
      _ = ∑' i : Unit ⊕ Fin J, ∫ t in P i, g t :=
        integral_iUnion hPieceMeas hPairwise hUnionIntegrable
      _ = ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t := by simp
  have hEnvNonneg : 0 ≤ fullFrequencyEnvelope d T0 W := by
    have hmass : 0 ≤ fullFrequencyAbsoluteIntegral d T0 := by
      unfold fullFrequencyAbsoluteIntegral
      apply setIntegral_nonneg
      · exact measurableSet_Iic.preimage continuous_abs.measurable
      · intro t ht
        exact norm_nonneg (fullFrequencyMellinPolynomial d t)
    have hbound := fullFrequencyAbsoluteIntegral_le_envelope d hT0 hW
      ⟨le_rfl, hcap⟩
    have hbound' : fullFrequencyAbsoluteIntegral d T0 ≤
        fullFrequencyEnvelope d T0 W := by
      simpa [div_self hT0.ne'] using hbound
    exact le_trans hmass hbound'
  have hLow : ∫ t in P (Sum.inl ()), g t ≤
      fullFrequencyEnvelope d T0 W := by
    have hlowEq : ∫ t in P (Sum.inl ()), g t =
        fullFrequencyAbsoluteIntegral d T0 := by
      unfold fullFrequencyAbsoluteIntegral
      apply setIntegral_congr_fun
      · exact hPieceMeas _
      · intro t ht
        change |t| ≤ T0 at ht
        simp [P, g, weight, fullFrequencyMellinKernelWeight,
          max_eq_left ht, div_self hT0.ne']
    calc
      ∫ t in P (Sum.inl ()), g t = fullFrequencyAbsoluteIntegral d T0 := hlowEq
      _ ≤ fullFrequencyEnvelope d T0 W := by
        have hbound := fullFrequencyAbsoluteIntegral_le_envelope d hT0 hW
          ⟨le_rfl, hcap⟩
        simpa [div_self hT0.ne'] using hbound
  have hBand (j : Fin J) : ∫ t in P (Sum.inr j), g t ≤
      2 * fullFrequencyEnvelope d T0 W := by
    let V : ℝ := min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1))
    have hpow1 : 1 ≤ (2 : ℝ) ^ (j.val + 1) := one_le_pow₀ (by norm_num)
    have hT0lepow : T0 ≤ T0 * (2 : ℝ) ^ (j.val + 1) := by
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hpow1)]
    have hVmem : V ∈ Set.Icc T0 (T0 * W ^ 4) := by
      constructor
      · exact le_min hcap hT0lepow
      · exact min_le_left _ _
    have hVpos : 0 < V := lt_of_lt_of_le hT0 hVmem.1
    have hBandSubsetV : P (Sum.inr j) ⊆
        (fun t : ℝ => |t|) ⁻¹' Set.Iic V := by
      intro t ht
      change T0 * (2 : ℝ) ^ j.val < |t| ∧
        |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at ht
      change |t| ≤ V
      simpa [V] using ht.2
    have hBandMeas : MeasurableSet (P (Sum.inr j)) := hPieceMeas _
    have hnormV : IntegrableOn (fun t : ℝ =>
        ‖fullFrequencyMellinPolynomial d t‖)
        ((fun t : ℝ => |t|) ⁻¹' Set.Iic V) := by
      have hcompact : IsCompact ((fun t : ℝ => |t|) ⁻¹' Set.Iic V) :=
        fullFrequencyBall_isCompact
      exact hnormcont.continuousOn.integrableOn_compact hcompact
    have hnormBand : IntegrableOn (fun t : ℝ =>
        ‖fullFrequencyMellinPolynomial d t‖) (P (Sum.inr j)) :=
      hnormV.mono_set hBandSubsetV
    have hnormNonneg : 0 ≤ᵐ[volume.restrict ((fun t : ℝ => |t|) ⁻¹' Set.Iic V)]
        (fun t : ℝ => ‖fullFrequencyMellinPolynomial d t‖) :=
      Filter.Eventually.of_forall fun t => norm_nonneg _
    have hBandSubsetAe : (P (Sum.inr j) : Set ℝ) ≤ᵐ[volume]
        ((fun t : ℝ => |t|) ⁻¹' Set.Iic V) := by
      filter_upwards with t ht
      exact hBandSubsetV ht
    have hnormIntegral :
        (∫ t in P (Sum.inr j), ‖fullFrequencyMellinPolynomial d t‖) ≤
          fullFrequencyAbsoluteIntegral d V := by
      unfold fullFrequencyAbsoluteIntegral
      exact setIntegral_mono_set hnormV hnormNonneg hBandSubsetAe
    have hpow : 0 < (2 : ℝ) ^ j.val := pow_pos (by norm_num) _
    have hT0lej : T0 ≤ T0 * (2 : ℝ) ^ j.val := by
      have hpow' : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hpow')]
    have hweightPoint (t : ℝ) (ht : t ∈ P (Sum.inr j)) :
        weight t ≤ ((2 : ℝ) ^ j.val)⁻¹ := by
      change T0 * (2 : ℝ) ^ j.val < |t| ∧
        |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at ht
      have hT0abs : T0 ≤ |t| := le_trans hT0lej ht.1.le
      have habs : 0 < |t| := lt_of_lt_of_le hT0 hT0abs
      have hratio : T0 / |t| ≤ ((2 : ℝ) ^ j.val)⁻¹ :=
        (div_le_iff₀ habs).2 (by
          calc
            T0 ≤ |t| / (2 : ℝ) ^ j.val :=
              (le_div_iff₀ hpow).2 ht.1.le
            _ = ((2 : ℝ) ^ j.val)⁻¹ * |t| := by ring)
      dsimp [weight, fullFrequencyMellinKernelWeight]
      simp [max_eq_right hT0abs]
      exact hratio
    have hconstBand : IntegrableOn
        (fun t : ℝ => ((2 : ℝ) ^ j.val)⁻¹ *
          ‖fullFrequencyMellinPolynomial d t‖) (P (Sum.inr j)) :=
      hnormBand.const_mul _
    have hGband : IntegrableOn g (P (Sum.inr j)) :=
      hgE.mono_set (by
        intro t ht
        have hV := hBandSubsetV ht
        change |t| ≤ T0 * W ^ 4
        exact hV.trans (min_le_left _ _))
    have hmono :
        (∫ t in P (Sum.inr j), g t) ≤
          ∫ t in P (Sum.inr j), ((2 : ℝ) ^ j.val)⁻¹ *
            ‖fullFrequencyMellinPolynomial d t‖ := by
      apply setIntegral_mono_on hGband hconstBand hBandMeas
      intro t ht
      dsimp [g]
      calc
        ‖fullFrequencyMellinPolynomial d t‖ * weight t ≤
            ‖fullFrequencyMellinPolynomial d t‖ * ((2 : ℝ) ^ j.val)⁻¹ :=
          mul_le_mul_of_nonneg_left (hweightPoint t ht) (norm_nonneg _)
        _ = ((2 : ℝ) ^ j.val)⁻¹ *
            ‖fullFrequencyMellinPolynomial d t‖ := by ring
    have hVupper : V / T0 ≤ (2 : ℝ) ^ (j.val + 1) := by
      apply (div_le_iff₀ hT0).2
      have hVle : V ≤ T0 * (2 : ℝ) ^ (j.val + 1) := min_le_right _ _
      simpa only [mul_comm] using hVle
    have htail := fullFrequencyAbsoluteIntegral_le_envelope d hT0 hW hVmem
    have hinvnonneg : 0 ≤ ((2 : ℝ) ^ j.val)⁻¹ := inv_nonneg.mpr hpow.le
    have hscaled : ((2 : ℝ) ^ j.val)⁻¹ *
        ((V / T0) * fullFrequencyEnvelope d T0 W) ≤
          2 * fullFrequencyEnvelope d T0 W := by
      have hDscaled : (V / T0) * fullFrequencyEnvelope d T0 W ≤
          (2 : ℝ) ^ (j.val + 1) * fullFrequencyEnvelope d T0 W :=
        mul_le_mul_of_nonneg_right hVupper hEnvNonneg
      calc
        _ ≤ ((2 : ℝ) ^ j.val)⁻¹ *
            ((2 : ℝ) ^ (j.val + 1) * fullFrequencyEnvelope d T0 W) :=
              mul_le_mul_of_nonneg_left hDscaled hinvnonneg
        _ = 2 * fullFrequencyEnvelope d T0 W := by
          rw [pow_succ]
          field_simp [pow_ne_zero j.val (by norm_num : (2 : ℝ) ≠ 0)]
    calc
      (∫ t in P (Sum.inr j), g t) ≤
          ∫ t in P (Sum.inr j), ((2 : ℝ) ^ j.val)⁻¹ *
            ‖fullFrequencyMellinPolynomial d t‖ := hmono
      _ = ((2 : ℝ) ^ j.val)⁻¹ *
          ∫ t in P (Sum.inr j), ‖fullFrequencyMellinPolynomial d t‖ :=
        by rw [integral_const_mul]
      _ ≤ ((2 : ℝ) ^ j.val)⁻¹ * fullFrequencyAbsoluteIntegral d V :=
        mul_le_mul_of_nonneg_left hnormIntegral hinvnonneg
      _ ≤ ((2 : ℝ) ^ j.val)⁻¹ *
          ((V / T0) * fullFrequencyEnvelope d T0 W) :=
        mul_le_mul_of_nonneg_left htail hinvnonneg
      _ ≤ 2 * fullFrequencyEnvelope d T0 W := hscaled
  let bound : Unit ⊕ Fin J → ℝ := Sum.elim
    (fun _ => fullFrequencyEnvelope d T0 W)
    (fun _ => 2 * fullFrequencyEnvelope d T0 W)
  have hsumBound :
      (∑ i : Unit ⊕ Fin J, ∫ t in P i, g t) ≤
        ∑ i : Unit ⊕ Fin J, bound i := by
    apply Finset.sum_le_sum
    intro i hi
    cases i with
    | inl u => simpa [bound] using hLow
    | inr j => simpa [bound] using hBand j
  have hsumEq :
      (∑ i : Unit ⊕ Fin J, bound i) =
        (1 + 2 * (J : ℝ)) * fullFrequencyEnvelope d T0 W := by
    simp [bound, Fintype.sum_sum_type, Finset.sum_const,
      nsmul_eq_mul, mul_comm, mul_assoc]
    ring
  calc
    (∫ t in E, ‖fullFrequencyMellinPolynomial d t‖ *
        (if t = 0 then 1 else min 1 (T0 / |t|))) =
      ∫ t in E, g t := by
        apply setIntegral_congr_fun hEmeas
        intro t ht
        dsimp [g, weight]
        rw [fullFrequencyMellinKernelWeight_eq hT0]
    _ = ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t := hdecomp
    _ ≤ ∑ i : Unit ⊕ Fin J, bound i := hsumBound
    _ = (1 + 2 * (J : ℝ)) * fullFrequencyEnvelope d T0 W := hsumEq
    _ ≤ (3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W :=
      mul_le_mul_of_nonneg_right (fullFrequencyDyadicBandCount_bound hW)
        hEnvNonneg

end

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.fullFrequencyMellinKernel_norm_le
#print axioms FractionalPrimes.Literature.Twisted.fullFrequencyAbsoluteIntegral_le_envelope
#print axioms FractionalPrimes.Literature.Twisted.fullFrequencyMellinWeightedIntegral_le

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The exact absolute short-interval transfer from the full-frequency
Mellin envelope, with the source hypotheses and constants. -/
theorem absoluteShortIntervalTransfer
    (d : FullFrequencyMellinData) {W : ℝ}
    (hW : 2 ≤ W) (hHW : d.h0 * W ^ 2 ≤ d.H) :
    ‖fullFrequencyMellinMean d‖ ≤
      (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
        (d.K / W ^ 2 +
          (1 + Real.log W) / Real.sqrt d.X *
            fullFrequencyEnvelope d (d.X / d.H) W) := by
  let T0 : ℝ := d.X / d.H
  let T : ℝ := T0 * W ^ 4
  have hX : 0 < d.X := by linarith [d.X_lower]
  have hWpos : 0 < W := by linarith
  have hT0 : 0 < T0 := div_pos hX d.H_pos
  have hT : 0 < T := mul_pos hT0 (pow_pos hWpos 4)
  have hM1 : 0 ≤ FractionalPrimes.polynomialKernelM1 := by
    unfold FractionalPrimes.polynomialKernelM1
    exact integral_nonneg fun u =>
      mul_nonneg (abs_nonneg u) (FractionalPrimes.polynomialKernelRho_nonneg u)
  have hM1ratio :
      FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) =
        FractionalPrimes.polynomialKernelM1 / W ^ 4 := by
    calc
      FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) =
          FractionalPrimes.polynomialKernelM1 * (d.X / (d.H * T)) := by ring
      _ = FractionalPrimes.polynomialKernelM1 / W ^ 4 := by
        congr 1
        dsimp [T, T0]
        field_simp [d.H_pos.ne', hX.ne', pow_ne_zero 4 hWpos.ne']
  have hmassratio : d.h0 / d.H ≤ 1 / W ^ 2 := by
    apply (div_le_div_iff₀ d.H_pos (pow_pos hWpos 2)).2
    simpa [one_mul, mul_comm] using hHW
  have hWsq : 1 ≤ W ^ 2 := by nlinarith
  have hWsq_le_fourth : W ^ 2 ≤ W ^ 4 := by
    nlinarith [sq_nonneg (W ^ 2 - 1)]
  have hM1ratio_le :
      FractionalPrimes.polynomialKernelM1 / W ^ 4 ≤
        FractionalPrimes.polynomialKernelM1 / W ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hWpos 4) (pow_pos hWpos 2)).2
    nlinarith [mul_le_mul_of_nonneg_left hWsq_le_fourth hM1]
  have hlocalError :
      ‖fullFrequencyMellinMean d - fullFrequencySmoothedSum d T‖ ≤
        (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
          (d.K / W ^ 2) := by
    have herr := (smoothedMellinFromLocalMass d (T := T) hT).2
    have hterm :
        FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) +
            d.h0 / d.H ≤ (1 + FractionalPrimes.polynomialKernelM1) / W ^ 2 := by
      calc
        _ = FractionalPrimes.polynomialKernelM1 / W ^ 4 + d.h0 / d.H := by
          rw [hM1ratio]
        _ ≤ FractionalPrimes.polynomialKernelM1 / W ^ 2 + 1 / W ^ 2 :=
          add_le_add hM1ratio_le hmassratio
        _ = (1 + FractionalPrimes.polynomialKernelM1) / W ^ 2 := by ring
    have hscale : 0 ≤ (2 : ℝ) ^ 36 * d.K :=
      mul_nonneg (by positivity) d.K_nonneg
    calc
      ‖fullFrequencyMellinMean d - fullFrequencySmoothedSum d T‖ ≤
          (2 : ℝ) ^ 36 * d.K *
            (FractionalPrimes.polynomialKernelM1 * d.X / (d.H * T) +
              d.h0 / d.H) := by simpa [T] using herr
      _ ≤ (2 : ℝ) ^ 36 * d.K *
          ((1 + FractionalPrimes.polynomialKernelM1) / W ^ 2) :=
        mul_le_mul_of_nonneg_left hterm hscale
      _ = (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
          (d.K / W ^ 2) := by ring
  let S : Set ℝ := Set.Icc (-T) T
  let weight : ℝ → ℝ := fullFrequencyMellinKernelWeight T0
  let g : ℝ → ℝ := fun t =>
    ‖fullFrequencyMellinPolynomial d t‖ * weight t
  let f : ℝ → ℂ := fun t =>
    fullFrequencyMellinPolynomial d t * fullFrequencyMellinKernel d t *
      FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)
  have hFourierCont :
      Continuous FractionalPrimes.polynomialKernelRhoAngularFourier := by
    have hFourierEval : Continuous (fun t : ℝ =>
        𝓕 Polynomial.polynomialKernelRhoComplexSchwartz
          (t / (2 * Real.pi))) := by
      fun_prop
    apply hFourierEval.congr
    intro t
    exact (Polynomial.polynomialKernelRhoAngularFourier_eq_fourier t).symm
  have hKernelCont : Continuous (fun t : ℝ => fullFrequencyMellinKernel d t) := by
    have hnum : Continuous (fun t : ℝ =>
        Polynomial.mellinHalfItPower (d.X + d.H) t -
          Polynomial.mellinHalfItPower d.X t) := by
      unfold Polynomial.mellinHalfItPower
      fun_prop
    have hden : Continuous (fun t : ℝ =>
        (d.H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      fun_prop
    have hden_ne (t : ℝ) :
        (d.H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast d.H_pos.ne'
      · exact Polynomial.mellinWindowDenominator_ne_zero t
    unfold fullFrequencyMellinKernel
    exact hnum.div₀ hden hden_ne
  have hFcont : Continuous f := by
    dsimp [f]
    exact (fullFrequencyMellinPolynomial_continuous d).mul hKernelCont |>.mul
      (hFourierCont.comp (by fun_prop))
  have hWeightCont : Continuous weight := by
    dsimp [weight, fullFrequencyMellinKernelWeight]
    refine continuous_const.div (continuous_const.max continuous_abs) ?_
    intro t
    exact ne_of_gt (lt_of_lt_of_le hT0 (le_max_left T0 |t|))
  have hGcont : Continuous g := by
    dsimp [g]
    exact (continuous_norm.comp (fullFrequencyMellinPolynomial_continuous d)).mul
      hWeightCont
  have hScompact : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_Icc
  have hfint : IntegrableOn f S := hFcont.continuousOn.integrableOn_compact hScompact
  have hgint : IntegrableOn g S := hGcont.continuousOn.integrableOn_compact hScompact
  have hnormint :
      ‖∫ t in S, f t‖ ≤ ∫ t in S, ‖f t‖ := by
    simpa [S] using
      (norm_integral_le_integral_norm (f := f) (μ := volume.restrict S))
  have hkernelBound (t : ℝ) :
      ‖fullFrequencyMellinKernel d t‖ ≤ (3 / Real.sqrt d.X) * weight t := by
    change ‖Polynomial.normalizedMellinWindowKernel d.X d.H t‖ ≤
      (3 / Real.sqrt d.X) * fullFrequencyMellinKernelWeight T0 t
    rw [fullFrequencyMellinKernelWeight_eq hT0]
    have hb := fullFrequencyMellinKernel_norm_le d t
    simpa [T0] using hb
  have hpoint (t : ℝ) : ‖f t‖ ≤ (3 / Real.sqrt d.X) * g t := by
    dsimp [f, g]
    calc
      ‖fullFrequencyMellinPolynomial d t *
          fullFrequencyMellinKernel d t *
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)‖ =
        ‖fullFrequencyMellinPolynomial d t‖ *
          ‖fullFrequencyMellinKernel d t‖ *
          ‖FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)‖ := by
            simp [norm_mul, mul_assoc]
      _ ≤ ‖fullFrequencyMellinPolynomial d t‖ *
          ‖fullFrequencyMellinKernel d t‖ * 1 := by
            exact mul_le_mul_of_nonneg_left
              (FractionalPrimes.polynomialKernelRhoAngularFourier_norm_le_one (t / T))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ ‖fullFrequencyMellinPolynomial d t‖ *
          ((3 / Real.sqrt d.X) * weight t) := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (hkernelBound t)
                (norm_nonneg (fullFrequencyMellinPolynomial d t)))
      _ = (3 / Real.sqrt d.X) *
          (‖fullFrequencyMellinPolynomial d t‖ * weight t) := by ring
  have hscaledInt :
      IntegrableOn (fun t : ℝ => (3 / Real.sqrt d.X) * g t) S :=
    hgint.const_mul _
  have hnormFint : IntegrableOn (fun t : ℝ => ‖f t‖) S := by
    exact (continuous_norm.comp hFcont).continuousOn.integrableOn_compact hScompact
  have hpointInt :
      (∫ t in S, ‖f t‖) ≤
        ∫ t in S, (3 / Real.sqrt d.X) * g t := by
    apply setIntegral_mono_on hnormFint hscaledInt hSmeas
    intro t ht
    exact hpoint t
  have hS_eq : S = (fun t : ℝ => |t|) ⁻¹' Set.Iic (T0 * W ^ 4) := by
    ext t
    simp [S, T, abs_le]
  have hweighted :
      (∫ t in S, g t) ≤
        (3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W := by
    calc
      (∫ t in S, g t) =
          ∫ t in (fun t : ℝ => |t|) ⁻¹' Set.Iic (T0 * W ^ 4),
            ‖fullFrequencyMellinPolynomial d t‖ *
              (if t = 0 then 1 else min 1 (T0 / |t|)) := by
        rw [hS_eq]
        apply setIntegral_congr_fun
          (measurableSet_Iic.preimage continuous_abs.measurable)
        intro t ht
        dsimp [g, weight]
        rw [fullFrequencyMellinKernelWeight_eq hT0]
      _ ≤ (3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W :=
        fullFrequencyMellinWeightedIntegral_le d hT0 hW
  have hM1nonneg : 0 ≤ FractionalPrimes.polynomialKernelM1 := hM1
  have hWlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  have hEnvNonneg : 0 ≤ fullFrequencyEnvelope d T0 W := by
    have hmass : 0 ≤ fullFrequencyAbsoluteIntegral d T0 := by
      unfold fullFrequencyAbsoluteIntegral
      apply setIntegral_nonneg
      · exact measurableSet_Iic.preimage continuous_abs.measurable
      · intro t ht
        exact norm_nonneg _
    have hcap : T0 ≤ T0 * W ^ 4 := by
      have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ (by linarith : 1 ≤ W)
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hW4)]
    have hbound := fullFrequencyAbsoluteIntegral_le_envelope d hT0 hW
      ⟨le_rfl, hcap⟩
    have hbound' : fullFrequencyAbsoluteIntegral d T0 ≤
        fullFrequencyEnvelope d T0 W := by
      simpa [div_self hT0.ne'] using hbound
    exact le_trans hmass hbound'
  have hcoeff : 0 ≤ 3 / Real.sqrt d.X := by positivity
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hlogbound : 3 + 12 * Real.log W ≤ 16 * (1 + Real.log W) := by
    nlinarith
  have hscaledbound :
      (3 / Real.sqrt d.X) *
          ((3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W) ≤
        48 * (1 + Real.log W) / Real.sqrt d.X *
          fullFrequencyEnvelope d T0 W := by
    have hsqrt : 0 < Real.sqrt d.X := Real.sqrt_pos.2 hX
    have hfactor :
        (3 / Real.sqrt d.X) * (3 + 12 * Real.log W) ≤
          48 * (1 + Real.log W) / Real.sqrt d.X := by
      calc
        (3 / Real.sqrt d.X) * (3 + 12 * Real.log W) =
            (3 * (3 + 12 * Real.log W)) / Real.sqrt d.X := by ring
        _ ≤ (48 * (1 + Real.log W)) / Real.sqrt d.X :=
          div_le_div_of_nonneg_right (by nlinarith [hlogbound]) hsqrt.le
        _ = 48 * (1 + Real.log W) / Real.sqrt d.X := by ring
    calc
      _ = ((3 / Real.sqrt d.X) * (3 + 12 * Real.log W)) *
          fullFrequencyEnvelope d T0 W := by ring
      _ ≤ (48 * (1 + Real.log W) / Real.sqrt d.X) *
          fullFrequencyEnvelope d T0 W :=
        mul_le_mul_of_nonneg_right hfactor hEnvNonneg
      _ = _ := by ring
  have hscalar : ‖((2 * Real.pi)⁻¹ : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    rw [← one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hsmoothedEq :
      fullFrequencySmoothedSum d T = ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ t in S, f t := by
    simpa [S, f] using (smoothedMellinFromLocalMass d (T := T) hT).1
  have hsmoothedBound :
      ‖fullFrequencySmoothedSum d T‖ ≤
        48 * (1 + Real.log W) / Real.sqrt d.X *
          fullFrequencyEnvelope d T0 W := by
    calc
      ‖fullFrequencySmoothedSum d T‖ =
          ‖((2 * Real.pi)⁻¹ : ℝ) • ∫ t in S, f t‖ := by rw [hsmoothedEq]
      _ = ‖((2 * Real.pi)⁻¹ : ℝ)‖ * ‖∫ t in S, f t‖ := norm_smul _ _
      _ ≤ ‖∫ t in S, f t‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hscalar
      _ ≤ (3 / Real.sqrt d.X) *
          ((3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W) := by
        calc
          ‖∫ t in S, f t‖ ≤ ∫ t in S, ‖f t‖ := hnormint
          _ ≤ ∫ t in S, (3 / Real.sqrt d.X) * g t := hpointInt
          _ = (3 / Real.sqrt d.X) * ∫ t in S, g t := by rw [integral_const_mul]
          _ ≤ (3 / Real.sqrt d.X) *
              ((3 + 12 * Real.log W) * fullFrequencyEnvelope d T0 W) :=
            mul_le_mul_of_nonneg_left hweighted hcoeff
      _ ≤ 48 * (1 + Real.log W) / Real.sqrt d.X *
          fullFrequencyEnvelope d T0 W := hscaledbound
  have hOuterSmooth :
      48 * (1 + Real.log W) / Real.sqrt d.X *
          fullFrequencyEnvelope d T0 W ≤
        (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
          ((1 + Real.log W) / Real.sqrt d.X *
            fullFrequencyEnvelope d T0 W) := by
    have hfactor :
        0 ≤ (1 + Real.log W) / Real.sqrt d.X *
          fullFrequencyEnvelope d T0 W := by positivity
    have hcoef : 48 ≤ (2 : ℝ) ^ 36 *
        (1 + FractionalPrimes.polynomialKernelM1) := by
      nlinarith [hM1nonneg]
    calc
      _ = 48 * ((1 + Real.log W) / Real.sqrt d.X *
          fullFrequencyEnvelope d T0 W) := by ring
      _ ≤ (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
          ((1 + Real.log W) / Real.sqrt d.X *
            fullFrequencyEnvelope d T0 W) :=
        mul_le_mul_of_nonneg_right hcoef hfactor
  have htriangle :
      ‖fullFrequencyMellinMean d‖ ≤
        ‖fullFrequencyMellinMean d - fullFrequencySmoothedSum d T‖ +
          ‖fullFrequencySmoothedSum d T‖ := by
    calc
      ‖fullFrequencyMellinMean d‖ =
          ‖(fullFrequencyMellinMean d - fullFrequencySmoothedSum d T) +
            fullFrequencySmoothedSum d T‖ := by congr 1 <;> ring
      _ ≤ _ := norm_add_le _ _
  calc
    ‖fullFrequencyMellinMean d‖ ≤
        (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
          (d.K / W ^ 2) +
        (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
          ((1 + Real.log W) / Real.sqrt d.X *
            fullFrequencyEnvelope d T0 W) := by
      exact htriangle.trans (add_le_add hlocalError
        (hsmoothedBound.trans hOuterSmooth))
    _ = (2 : ℝ) ^ 36 * (1 + FractionalPrimes.polynomialKernelM1) *
        (d.K / W ^ 2 +
          (1 + Real.log W) / Real.sqrt d.X *
            fullFrequencyEnvelope d (d.X / d.H) W) := by
      simp only [T0]
      ring

end

end FractionalPrimes.Literature.Twisted

end

#print axioms FractionalPrimes.Literature.Twisted.absoluteShortIntervalTransfer
