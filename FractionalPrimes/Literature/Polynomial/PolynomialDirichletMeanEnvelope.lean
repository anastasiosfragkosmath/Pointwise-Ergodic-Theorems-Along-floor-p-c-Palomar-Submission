module

public import FractionalPrimes.Literature.Polynomial.MellinWindowData
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open scoped BigOperators

/-- The tail of the finite Dirichlet polynomial over the symmetric interval
`W ≤ |t| ≤ U`, with the Lebesgue set-integral convention of the source. -/
noncomputable def dirichletAbsoluteTailIntegral
    (w : MellinWindowData) (W U : ℝ) : ℝ :=
  ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U}, ‖w.A_X t‖

/-- The normalized objective whose maximum defines the exact mean-value
envelope. -/
noncomputable def dirichletMeanEnvelopeObjective
    (w : MellinWindowData) (T0 W U : ℝ) : ℝ :=
  (T0 / U) * dirichletAbsoluteTailIntegral w W U

/-- The exact mean-value envelope from `lup:dp-envelope`, represented by the
supremum of its objective on the closed parameter interval. The compact
maximum theorem below proves this supremum is attained, so this is exactly the
displayed maximum. -/
noncomputable def dirichletMeanEnvelope
    (w : MellinWindowData) (T0 W : ℝ) : ℝ :=
  sSup (dirichletMeanEnvelopeObjective w T0 W '' Set.Icc T0 (T0 * W ^ 4))

/-- The `A_X` field produced by the exact finite Dirichlet-window constructor
is a continuous finite sum. -/
theorem mellinWindowData_A_X_continuous
    (rho : ℝ → ℝ) (X H B : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) :
    Continuous (mellinWindowData rho X H B a hX hH hHX hB hsupport hbound).A_X := by
  unfold mellinWindowData
  dsimp
  refine continuous_finsetSum _ ?_
  intro n hn
  apply continuous_const.mul
  unfold mellinDirichletMonomial
  fun_prop

private theorem absTail_set_eq_union_Icc
    {W U : ℝ} (hW : 0 < W) :
    {t : ℝ | W ≤ |t| ∧ |t| ≤ U} = Set.Icc W U ∪ Set.Icc (-U) (-W) := by
  ext t
  constructor
  · intro ht
    change W ≤ |t| ∧ |t| ≤ U at ht
    by_cases ht0 : 0 ≤ t
    · apply Set.mem_union_left
      apply Set.mem_Icc.mpr
      rw [abs_of_nonneg ht0] at ht
      exact ht
    · have htneg : t < 0 := lt_of_not_ge ht0
      apply Set.mem_union_right
      apply Set.mem_Icc.mpr
      rw [abs_of_neg htneg] at ht
      constructor <;> linarith [ht.1, ht.2]
  · intro ht
    simp only [Set.mem_union] at ht
    rcases ht with hp | hn
    · have hp' := Set.mem_Icc.mp hp
      have ht0 : 0 ≤ t := le_trans (le_of_lt hW) hp'.1
      change W ≤ |t| ∧ |t| ≤ U
      rw [abs_of_nonneg ht0]
      exact hp'
    · have hn' := Set.mem_Icc.mp hn
      have ht0 : t < 0 := lt_of_le_of_lt hn'.2 (neg_neg_of_pos hW)
      change W ≤ |t| ∧ |t| ≤ U
      rw [abs_of_neg ht0]
      constructor <;> linarith [hn'.1, hn'.2]

private theorem absTail_intervals_disjoint
    {W U : ℝ} (hW : 0 < W) :
    Disjoint (Set.Icc W U) (Set.Icc (-U) (-W)) := by
  rw [Set.disjoint_left]
  intro t hp hn
  have hp' := Set.mem_Icc.mp hp
  have hn' := Set.mem_Icc.mp hn
  linarith

/-- On the domain `W ≤ U`, the source's symmetric set integral is the sum of
the positive and negative interval integrals. -/
theorem dirichletAbsoluteTailIntegral_eq_intervalIntegrals
    (w : MellinWindowData) (hA : Continuous w.A_X) {W U : ℝ}
    (hW : 0 < W) (hWU : W ≤ U) :
    dirichletAbsoluteTailIntegral w W U =
      (∫ t in W..U, ‖w.A_X t‖) + (∫ t in -U..-W, ‖w.A_X t‖) := by
  unfold dirichletAbsoluteTailIntegral
  rw [absTail_set_eq_union_Icc hW,
    setIntegral_union (absTail_intervals_disjoint hW) measurableSet_Icc]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hWU,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -U ≤ -W)]
  · exact (continuous_norm.comp hA).continuousOn.integrableOn_compact isCompact_Icc
  · exact (continuous_norm.comp hA).continuousOn.integrableOn_compact isCompact_Icc

/-- The absolute-tail integral is a continuous function of its outer endpoint
on every range where that endpoint is at least `W`. -/
theorem dirichletAbsoluteTailIntegral_eq_primitive
    (w : MellinWindowData) (hA : Continuous w.A_X) {W U : ℝ}
    (hW : 0 < W) (hWU : W ≤ U) :
    dirichletAbsoluteTailIntegral w W U =
      (∫ t in 0..U, ‖w.A_X t‖) - (∫ t in 0..W, ‖w.A_X t‖) +
        (∫ t in 0..(-W), ‖w.A_X t‖) - (∫ t in 0..(-U), ‖w.A_X t‖) := by
  have hf : Continuous (fun t : ℝ => ‖w.A_X t‖) := continuous_norm.comp hA
  have hpos := intervalIntegral.integral_interval_sub_left
    (μ := volume) (hf.intervalIntegrable 0 U) (hf.intervalIntegrable 0 W)
  have hneg := intervalIntegral.integral_interval_sub_left
    (μ := volume) (hf.intervalIntegrable 0 (-W)) (hf.intervalIntegrable 0 (-U))
  rw [dirichletAbsoluteTailIntegral_eq_intervalIntegrals w hA hW hWU]
  rw [hpos.symm, hneg.symm]
  ring

private theorem continuous_dirichletMeanTailPrimitive
    (w : MellinWindowData) (hA : Continuous w.A_X) :
    Continuous (fun u : ℝ => ∫ t in 0..u, ‖w.A_X t‖) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact ((continuous_norm.comp hA).integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt

private theorem dirichletMeanEnvelope_domain_nonempty
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    (Set.Icc T0 (T0 * W ^ 4)).Nonempty := by
  have hT0 : 0 ≤ T0 := le_trans (by linarith) hWT
  have hW1 : 1 ≤ W := by linarith
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
  refine ⟨T0, ?_⟩
  constructor
  · rfl
  · have hmul : 0 ≤ T0 * (W ^ 4 - 1) :=
      mul_nonneg hT0 (sub_nonneg.mpr hW4)
    nlinarith

/-- The normalized objective is continuous on the parameter interval in the
source definition. -/
theorem dirichletMeanEnvelopeObjective_continuousOn
    (w : MellinWindowData) (hA : Continuous w.A_X)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    ContinuousOn (fun U => dirichletMeanEnvelopeObjective w T0 W U)
      (Set.Icc T0 (T0 * W ^ 4)) := by
  have hWpos : 0 < W := by linarith
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by linarith) hWT
  let G : ℝ → ℝ := fun u => ∫ t in 0..u, ‖w.A_X t‖
  have hG : Continuous G := by
    simpa [G] using continuous_dirichletMeanTailPrimitive w hA
  have htail : Continuous (fun U : ℝ =>
      G U - G W + G (-W) - G (-U)) := by
    fun_prop
  have hrat : ContinuousOn (fun U : ℝ => T0 / U)
      (Set.Icc T0 (T0 * W ^ 4)) := by
    refine continuousOn_const.div continuousOn_id ?_
    intro U hU
    exact ne_of_gt (lt_of_lt_of_le hT0pos hU.1)
  have hformula : ContinuousOn (fun U : ℝ =>
      (T0 / U) * (G U - G W + G (-W) - G (-U)))
      (Set.Icc T0 (T0 * W ^ 4)) :=
    hrat.mul htail.continuousOn
  apply hformula.congr
  intro U hU
  have hWU : W ≤ U := le_trans hWT hU.1
  simp only [dirichletMeanEnvelopeObjective]
  rw [dirichletAbsoluteTailIntegral_eq_primitive w hA hWpos hWU]

/-- The exact envelope maximum exists and equals the supremum-based
definition above. In particular, the source's displayed finite maximum is
attained on the whole closed interval. -/
theorem dirichletMeanEnvelope_hasMaximum
    (w : MellinWindowData) (hA : Continuous w.A_X)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    ∃ U ∈ Set.Icc T0 (T0 * W ^ 4),
      dirichletMeanEnvelopeObjective w T0 W U = dirichletMeanEnvelope w T0 W ∧
      ∀ V ∈ Set.Icc T0 (T0 * W ^ 4),
        dirichletMeanEnvelopeObjective w T0 W V ≤ dirichletMeanEnvelope w T0 W := by
  let S : Set ℝ := Set.Icc T0 (T0 * W ^ 4)
  let F : ℝ → ℝ := dirichletMeanEnvelopeObjective w T0 W
  have hne : S.Nonempty := dirichletMeanEnvelope_domain_nonempty hW hWT
  have hcont : ContinuousOn F S := by
    simpa [F, S] using dirichletMeanEnvelopeObjective_continuousOn w hA hW hWT
  obtain ⟨U, hU, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  have hbdd : BddAbove (F '' S) := by
    refine ⟨F U, ?_⟩
    rintro y ⟨V, hV, rfl⟩
    exact hmax hV
  have hImageNe : (F '' S).Nonempty := ⟨F U, ⟨U, hU, rfl⟩⟩
  have hsup_le : sSup (F '' S) ≤ F U := csSup_le hImageNe (by
    rintro y ⟨V, hV, rfl⟩
    exact hmax hV)
  have hle_sup : F U ≤ sSup (F '' S) := le_csSup hbdd ⟨U, hU, rfl⟩
  have hEq : sSup (F '' S) = F U := le_antisymm hsup_le hle_sup
  refine ⟨U, hU, ?_, ?_⟩
  · simpa [F, S, dirichletMeanEnvelope] using hEq.symm
  · intro V hV
    change F V ≤ sSup (F '' S)
    rw [hEq]
    exact hmax hV

/-- Continuous realization of the source weight, with its value at zero
interpreted as one. -/
private noncomputable def dirichletMellinKernelWeight (T0 t : ℝ) : ℝ :=
  T0 / max T0 |t|

private theorem dirichletMellinKernelWeight_eq_min
    {T0 t : ℝ} (hT0 : 0 < T0) (ht : t ≠ 0) :
    dirichletMellinKernelWeight T0 t = min 1 (T0 / |t|) := by
  have hAbs : 0 < |t| := abs_pos.mpr ht
  by_cases h : |t| ≤ T0
  · have hr : 1 ≤ T0 / |t| := (le_div_iff₀ hAbs).2 (by simpa using h)
    simp [dirichletMellinKernelWeight, max_eq_left h, min_eq_left hr, hT0.ne']
  · have h' : T0 < |t| := lt_of_not_ge h
    have hr : T0 / |t| ≤ 1 := (div_le_iff₀ hAbs).2 (by simpa using h'.le)
    simp [dirichletMellinKernelWeight, max_eq_right h'.le, min_eq_right hr]

/-- Every real number in `(1,2^n]` lies in one of the first `n` dyadic
half-open intervals. -/
private theorem exists_dyadic_bracket {x : ℝ} {n : ℕ}
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
        have hdivn : x / 2 ≤ (2 : ℝ) ^ n := (div_le_iff₀ (by norm_num)).2 hxn
        obtain ⟨j, hjn, hlow, hupp⟩ := ih hxdiv hdivn
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · have hlow' : (2 : ℝ) ^ j * 2 < x :=
            (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hlow
          simpa [pow_succ] using hlow'
        · have hupp' : x ≤ (2 : ℝ) ^ (j + 1) * 2 :=
            (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hupp
          simpa [pow_succ, Nat.add_assoc] using hupp'

/-- Number of dyadic intervals used in the finite decomposition. -/
private noncomputable def dyadicMellinBandCount (W : ℝ) : ℕ :=
  Nat.ceil (4 * Real.log W / Real.log 2)

private theorem dyadicMellinBandCount_covers
    {W : ℝ} (hW : 2 ≤ W) :
    W ^ 4 ≤ (2 : ℝ) ^ dyadicMellinBandCount W := by
  have hlogW : 0 < Real.log W := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : 4 * Real.log W / Real.log 2 ≤ (dyadicMellinBandCount W : ℝ) :=
    Nat.le_ceil _
  have hmul : 4 * Real.log W ≤ (dyadicMellinBandCount W : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp hceil
  have hexp := Real.exp_le_exp.mpr hmul
  have hleft : Real.exp (4 * Real.log W) = W ^ 4 := by
    have hfour : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [hfour, Real.exp_nat_mul, Real.exp_log (by linarith : 0 < W)]
  have hright : Real.exp ((dyadicMellinBandCount W : ℝ) * Real.log 2) =
      (2 : ℝ) ^ dyadicMellinBandCount W := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hleft, hright] at hexp
  exact hexp

private theorem dyadicMellinBandCount_bound
    {W : ℝ} (hW : 2 ≤ W) :
    1 + 2 * (dyadicMellinBandCount W : ℝ) ≤ 3 + 12 * Real.log W := by
  have hlogW : 0 ≤ Real.log W := (Real.log_pos (by linarith)).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : (dyadicMellinBandCount W : ℝ) <
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
    1 + 2 * (dyadicMellinBandCount W : ℝ) ≤
        1 + 2 * (4 * Real.log W / Real.log 2 + 1) := by nlinarith
    _ = 3 + 8 * Real.log W / Real.log 2 := by ring
    _ ≤ 3 + 12 * Real.log W := by linarith

/-- The initial interval together with the finitely many truncated dyadic
bands used in the source partition. -/
private def dirichletMellinPieceSet (T0 W : ℝ) {J : ℕ} :
    Unit ⊕ Fin J → Set ℝ
  | Sum.inl _ => {t | W ≤ |t| ∧ |t| ≤ T0}
  | Sum.inr j =>
      {t | T0 * (2 : ℝ) ^ j.val < |t| ∧
        |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1))}

private theorem dirichletMellinPieceSet_measurable
    {T0 W : ℝ} {J : ℕ} (i : Unit ⊕ Fin J) :
    MeasurableSet (dirichletMellinPieceSet T0 W i) := by
  cases i with
  | inl u =>
      change MeasurableSet ((fun t : ℝ => |t|) ⁻¹' Set.Icc W T0)
      exact measurableSet_Icc.preimage continuous_abs.measurable
  | inr j =>
      change MeasurableSet ((fun t : ℝ => |t|) ⁻¹'
        Set.Ioc (T0 * (2 : ℝ) ^ j.val)
          (min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1))))
      exact measurableSet_Ioc.preimage continuous_abs.measurable

private theorem dirichletAbsTailSet_isCompact
    {W U : ℝ} :
    IsCompact {t : ℝ | W ≤ |t| ∧ |t| ≤ U} := by
  have hclosed : IsClosed {t : ℝ | W ≤ |t| ∧ |t| ≤ U} := by
    change IsClosed ((fun t : ℝ => |t|) ⁻¹' Set.Icc W U)
    exact isClosed_Icc.preimage continuous_abs
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro t ht
  change W ≤ |t| ∧ |t| ≤ U at ht
  constructor
  · have hneg : -U ≤ -|t| := by linarith [ht.2]
    exact le_trans hneg (neg_abs_le t)
  · exact le_trans (le_abs_self t) ht.2

private theorem dirichletMellinPieceSet_iUnion_eq
    {T0 W : ℝ} (hT0 : 0 < T0) (hW : 2 ≤ W) (hWT : W ≤ T0) :
    (⋃ i : Unit ⊕ Fin (dyadicMellinBandCount W),
      dirichletMellinPieceSet T0 W i) =
      {t : ℝ | W ≤ |t| ∧ |t| ≤ T0 * W ^ 4} := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | inl u =>
        change W ≤ |t| ∧ |t| ≤ T0 at hi
        constructor
        · exact hi.1
        · have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ (by linarith : 1 ≤ W)
          have hfactor : 0 ≤ W ^ 4 - 1 := sub_nonneg.mpr hW4
          have hcap : T0 ≤ T0 * W ^ 4 := by
            nlinarith [mul_nonneg hT0.le hfactor]
          exact le_trans hi.2 hcap
    | inr j =>
        change T0 * (2 : ℝ) ^ j.val < |t| ∧
          |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at hi
        constructor
        · have hp : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
          have hfactor : 0 ≤ (2 : ℝ) ^ j.val - 1 := sub_nonneg.mpr hp
          have hTle : T0 ≤ T0 * (2 : ℝ) ^ j.val := by
            nlinarith [mul_nonneg hT0.le hfactor]
          exact hWT.trans (le_trans hTle hi.1.le)
        · exact (le_min_iff.mp hi.2).1
  · intro ht
    change W ≤ |t| ∧ |t| ≤ T0 * W ^ 4 at ht
    by_cases hlow : |t| ≤ T0
    · refine ⟨Sum.inl (), ?_⟩
      change W ≤ |t| ∧ |t| ≤ T0
      exact ⟨ht.1, hlow⟩
    · have habove : T0 < |t| := lt_of_not_ge hlow
      have hWpos : 0 < W := by linarith
      have hW4pow := dyadicMellinBandCount_covers hW
      have hxlo : 1 < |t| / T0 := (lt_div_iff₀ hT0).2 (by simpa using habove)
      have hxhi : |t| / T0 ≤ (2 : ℝ) ^ dyadicMellinBandCount W :=
        (div_le_iff₀ hT0).2 (by
          have hmul := ht.2
          nlinarith [hW4pow, hT0])
      obtain ⟨j, hjJ, hpowlo, hpowhi⟩ := exists_dyadic_bracket hxlo hxhi
      let j' : Fin (dyadicMellinBandCount W) := ⟨j, hjJ⟩
      refine ⟨Sum.inr j', ?_⟩
      change T0 * (2 : ℝ) ^ j < |t| ∧
        |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j + 1))
      constructor
      · simpa [mul_comm] using (lt_div_iff₀ hT0).mp hpowlo
      · apply le_min
        · exact ht.2
        · have hupper := (div_le_iff₀ hT0).mp hpowhi
          simpa [mul_comm] using hupper

private theorem dirichletMellinPieceSet_pairwiseDisjoint
    {T0 W : ℝ} {J : ℕ} (hT0 : 0 ≤ T0) :
    Pairwise (fun i j : Unit ⊕ Fin J =>
      Disjoint (dirichletMellinPieceSet T0 W i) (dirichletMellinPieceSet T0 W j)) := by
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
          change W ≤ |t| ∧ |t| ≤ T0 at hlow
          change T0 * (2 : ℝ) ^ l.val < |t| ∧
            |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (l.val + 1)) at hband
          have hp : 1 ≤ (2 : ℝ) ^ l.val := one_le_pow₀ (by norm_num)
          have hp' : 0 ≤ (2 : ℝ) ^ l.val - 1 := sub_nonneg.mpr hp
          have hTle : T0 ≤ T0 * (2 : ℝ) ^ l.val := by
            nlinarith [mul_nonneg hT0 hp']
          linarith
  | inr j =>
      cases k with
      | inl u =>
          apply Set.disjoint_left.mpr
          intro t hband hlow
          change T0 * (2 : ℝ) ^ j.val < |t| ∧
            |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at hband
          change W ≤ |t| ∧ |t| ≤ T0 at hlow
          have hp : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
          have hp' : 0 ≤ (2 : ℝ) ^ j.val - 1 := sub_nonneg.mpr hp
          have hTle : T0 ≤ T0 * (2 : ℝ) ^ j.val := by
            nlinarith [mul_nonneg hT0 hp']
          linarith
      | inr k =>
          apply Set.disjoint_left.mpr
          intro t hbandj hbandk
          change T0 * (2 : ℝ) ^ j.val < |t| ∧
            |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at hbandj
          change T0 * (2 : ℝ) ^ k.val < |t| ∧
            |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (k.val + 1)) at hbandk
          have hjk : j.val ≠ k.val := by
            intro h
            apply hik
            exact congrArg Sum.inr (Fin.ext h)
          rcases lt_or_gt_of_ne hjk with hjk | hkj
          · have hjksucc : j.val + 1 ≤ k.val := by omega
            have hpow : (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ k.val :=
              pow_le_pow_right₀ (by norm_num) hjksucc
            have hmul := mul_le_mul_of_nonneg_left hpow hT0
            have hupper := (le_min_iff.mp hbandj.2).2
            linarith [hbandk.1]
          · have hkjsucc : k.val + 1 ≤ j.val := by omega
            have hpow : (2 : ℝ) ^ (k.val + 1) ≤ (2 : ℝ) ^ j.val :=
              pow_le_pow_right₀ (by norm_num) hkjsucc
            have hmul := mul_le_mul_of_nonneg_left hpow hT0
            have hupper := (le_min_iff.mp hbandk.2).2
            linarith [hbandj.1]

private theorem dirichletMeanEnvelope_nonneg
    (w : MellinWindowData) (hA : Continuous w.A_X)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    0 ≤ dirichletMeanEnvelope w T0 W := by
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by linarith) hWT
  have hcap : T0 ≤ T0 * W ^ 4 := by
    have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ (by linarith : 1 ≤ W)
    nlinarith [mul_nonneg hT0pos.le (sub_nonneg.mpr hW4)]
  obtain ⟨V, hV, hval, hmax⟩ :=
    dirichletMeanEnvelope_hasMaximum w hA hW hWT
  have hT0mem : T0 ∈ Set.Icc T0 (T0 * W ^ 4) := ⟨le_rfl, hcap⟩
  have hTailMeas : MeasurableSet {t : ℝ | W ≤ |t| ∧ |t| ≤ T0} :=
    (dirichletAbsTailSet_isCompact (W := W) (U := T0)).isClosed.measurableSet
  have hTailNonneg : 0 ≤ dirichletAbsoluteTailIntegral w W T0 :=
    setIntegral_nonneg hTailMeas (by intro t ht; exact norm_nonneg _)
  have hObj : dirichletMeanEnvelopeObjective w T0 W T0 =
      dirichletAbsoluteTailIntegral w W T0 := by
    simp [dirichletMeanEnvelopeObjective, div_self hT0pos.ne']
  have hle := hmax T0 hT0mem
  rw [hObj] at hle
  exact le_trans hTailNonneg hle

private theorem dirichletMeanEnvelope_tailIntegral_le
    (w : MellinWindowData) (hA : Continuous w.A_X)
    {T0 W U : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hU : U ∈ Set.Icc T0 (T0 * W ^ 4)) :
    dirichletAbsoluteTailIntegral w W U ≤
      (U / T0) * dirichletMeanEnvelope w T0 W := by
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by linarith) hWT
  have hUpos : 0 < U := lt_of_lt_of_le hT0pos hU.1
  obtain ⟨V, hV, hval, hmax⟩ :=
    dirichletMeanEnvelope_hasMaximum w hA hW hWT
  have hcancel : (U / T0) *
      ((T0 / U) * dirichletAbsoluteTailIntegral w W U) =
        dirichletAbsoluteTailIntegral w W U := by
    field_simp [hT0pos.ne', hUpos.ne']
  calc
    dirichletAbsoluteTailIntegral w W U =
        (U / T0) *
          ((T0 / U) * dirichletAbsoluteTailIntegral w W U) := hcancel.symm
    _ ≤ (U / T0) * dirichletMeanEnvelope w T0 W :=
      mul_le_mul_of_nonneg_left (hmax U hU)
        (div_nonneg hUpos.le hT0pos.le)

private theorem dirichletMellinKernelWeight_continuous
    {T0 : ℝ} (hT0 : 0 < T0) :
    Continuous (fun t : ℝ => dirichletMellinKernelWeight T0 t) := by
  have hden : Continuous (fun t : ℝ => max T0 |t|) :=
    continuous_const.max continuous_abs
  have hden_ne (t : ℝ) : max T0 |t| ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hT0 (le_max_left T0 |t|))
  exact continuous_const.div hden hden_ne

/-- Dyadic summation of the Mellin kernel, with the exact source constant. -/
theorem dyadicMellinIntegral
    (w : MellinWindowData) (hA : Continuous w.A_X)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ T0 * W ^ 4},
      ‖w.A_X t‖ * min 1 (T0 / |t|) ≤
        (3 + 12 * Real.log W) * dirichletMeanEnvelope w T0 W := by
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by linarith) hWT
  have hWpos : 0 < W := by linarith
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ (by linarith : 1 ≤ W)
  have hcap : T0 ≤ T0 * W ^ 4 := by
    nlinarith [mul_nonneg hT0pos.le (sub_nonneg.mpr hW4)]
  have hDnonneg := dirichletMeanEnvelope_nonneg w hA hW hWT
  obtain ⟨Umax, hUmax, hmaxval, hmax⟩ :=
    dirichletMeanEnvelope_hasMaximum w hA hW hWT
  let E : Set ℝ := {t : ℝ | W ≤ |t| ∧ |t| ≤ T0 * W ^ 4}
  let J : ℕ := dyadicMellinBandCount W
  let P : Unit ⊕ Fin J → Set ℝ := dirichletMellinPieceSet T0 W
  let g : ℝ → ℝ := fun t =>
    ‖w.A_X t‖ * dirichletMellinKernelWeight T0 t
  have hEcompact : IsCompact E := by
    simpa [E] using dirichletAbsTailSet_isCompact (W := W) (U := T0 * W ^ 4)
  have hEmeas : MeasurableSet E := hEcompact.isClosed.measurableSet
  have hnorm : Continuous (fun t : ℝ => ‖w.A_X t‖) := continuous_norm.comp hA
  have hweight : Continuous (fun t : ℝ => dirichletMellinKernelWeight T0 t) :=
    dirichletMellinKernelWeight_continuous hT0pos
  have hg : Continuous g := by
    change Continuous (fun t : ℝ => ‖w.A_X t‖ * dirichletMellinKernelWeight T0 t)
    exact hnorm.mul hweight
  have hgE : IntegrableOn g E := hg.continuousOn.integrableOn_compact hEcompact
  have hsourceEq :
      ∫ t in E, ‖w.A_X t‖ * min 1 (T0 / |t|) = ∫ t in E, g t := by
    apply setIntegral_congr_fun hEmeas
    intro t ht
    change W ≤ |t| ∧ |t| ≤ T0 * W ^ 4 at ht
    have htne : t ≠ 0 := by
      intro hzero
      simp [hzero] at ht
      linarith
    simp [g, dirichletMellinKernelWeight_eq_min hT0pos htne]
  have htailmeas : MeasurableSet {t : ℝ | W ≤ |t| ∧ |t| ≤ T0} :=
    (dirichletAbsTailSet_isCompact (W := W) (U := T0)).isClosed.measurableSet
  have htailnonneg : 0 ≤ dirichletAbsoluteTailIntegral w W T0 :=
    setIntegral_nonneg htailmeas (by intro t ht; exact norm_nonneg _)
  have hobjT0 : dirichletMeanEnvelopeObjective w T0 W T0 =
      dirichletAbsoluteTailIntegral w W T0 := by
    simp [dirichletMeanEnvelopeObjective, div_self hT0pos.ne']
  have hT0mem : T0 ∈ Set.Icc T0 (T0 * W ^ 4) := ⟨le_rfl, hcap⟩
  have hDnonneg' : 0 ≤ dirichletMeanEnvelope w T0 W := by
    calc
      0 ≤ dirichletAbsoluteTailIntegral w W T0 := htailnonneg
      _ = dirichletMeanEnvelopeObjective w T0 W T0 := hobjT0.symm
      _ ≤ dirichletMeanEnvelope w T0 W := hmax T0 hT0mem
  have hCover : (⋃ i : Unit ⊕ Fin J, P i) = E := by
    simpa [P, E, J] using
      dirichletMellinPieceSet_iUnion_eq hT0pos hW hWT
  have hPieceMeas : ∀ i : Unit ⊕ Fin J, MeasurableSet (P i) := by
    intro i
    simpa [P] using dirichletMellinPieceSet_measurable i
  have hPiecesDisjoint : Pairwise (fun i j : Unit ⊕ Fin J => Disjoint (P i) (P j)) := by
    simpa [P] using (dirichletMellinPieceSet_pairwiseDisjoint
      (T0 := T0) (W := W) (J := J) hT0pos.le)
  have hUnionIntegrable : IntegrableOn g (⋃ i : Unit ⊕ Fin J, P i) := by
    rw [hCover]
    exact hgE
  have hdecomp :
      ∫ t in E, g t = ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t := by
    calc
      ∫ t in E, g t = ∫ t in ⋃ i : Unit ⊕ Fin J, P i, g t := by rw [hCover]
      _ = ∑' i : Unit ⊕ Fin J, ∫ t in P i, g t :=
        integral_iUnion hPieceMeas hPiecesDisjoint hUnionIntegrable
      _ = ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t := by simp
  have hLow : ∫ t in P (Sum.inl ()), g t ≤ dirichletMeanEnvelope w T0 W := by
    have hlowmeas : MeasurableSet (P (Sum.inl ())) := hPieceMeas _
    have hlowEq : ∫ t in P (Sum.inl ()), g t =
        dirichletAbsoluteTailIntegral w W T0 := by
      unfold dirichletAbsoluteTailIntegral
      apply setIntegral_congr_fun hlowmeas
      intro t ht
      change W ≤ |t| ∧ |t| ≤ T0 at ht
      simp [g, dirichletMellinKernelWeight, max_eq_left ht.2, div_self hT0pos.ne']
    calc
      ∫ t in P (Sum.inl ()), g t = dirichletAbsoluteTailIntegral w W T0 := hlowEq
      _ = dirichletMeanEnvelopeObjective w T0 W T0 := hobjT0.symm
      _ ≤ dirichletMeanEnvelope w T0 W := hmax T0 hT0mem
  have hBand (j : Fin J) :
      ∫ t in P (Sum.inr j), g t ≤ 2 * dirichletMeanEnvelope w T0 W := by
    let V : ℝ := min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1))
    have hpow1 : 1 ≤ (2 : ℝ) ^ (j.val + 1) := one_le_pow₀ (by norm_num)
    have hpowfac : 0 ≤ (2 : ℝ) ^ (j.val + 1) - 1 := sub_nonneg.mpr hpow1
    have hT0lepow : T0 ≤ T0 * (2 : ℝ) ^ (j.val + 1) := by
      nlinarith [mul_nonneg hT0pos.le hpowfac]
    have hVmem : V ∈ Set.Icc T0 (T0 * W ^ 4) := by
      constructor
      · exact le_min hcap hT0lepow
      · exact min_le_left _ _
    have hVpos : 0 < V := lt_of_lt_of_le hT0pos hVmem.1
    have hBandTail : P (Sum.inr j) ⊆ {t : ℝ | W ≤ |t| ∧ |t| ≤ V} := by
      intro t ht
      change T0 * (2 : ℝ) ^ j.val < |t| ∧
        |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at ht
      change W ≤ |t| ∧ |t| ≤ V
      constructor
      · have hpow : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
        have hpowfac' : 0 ≤ (2 : ℝ) ^ j.val - 1 := sub_nonneg.mpr hpow
        have hT0lej : T0 ≤ T0 * (2 : ℝ) ^ j.val := by
          nlinarith [mul_nonneg hT0pos.le hpowfac']
        exact hWT.trans (le_trans hT0lej ht.1.le)
      · simpa [V] using ht.2
    have hBandSubsetE : P (Sum.inr j) ⊆ E := by
      intro t ht
      have ht' := hBandTail ht
      change W ≤ |t| ∧ |t| ≤ T0 * W ^ 4
      exact ⟨ht'.1, le_trans ht'.2 (min_le_left _ _)⟩
    have hBandMeas : MeasurableSet (P (Sum.inr j)) := hPieceMeas _
    have hGband : IntegrableOn g (P (Sum.inr j)) := hgE.mono_set hBandSubsetE
    have hnormE : IntegrableOn (fun t : ℝ => ‖w.A_X t‖) E :=
      hnorm.continuousOn.integrableOn_compact hEcompact
    have hnormBand : IntegrableOn (fun t : ℝ => ‖w.A_X t‖) (P (Sum.inr j)) :=
      hnormE.mono_set hBandSubsetE
    have hnormTail : IntegrableOn (fun t : ℝ => ‖w.A_X t‖)
        {t : ℝ | W ≤ |t| ∧ |t| ≤ V} :=
      hnorm.continuousOn.integrableOn_compact
        (dirichletAbsTailSet_isCompact (W := W) (U := V))
    have hnormNonneg : 0 ≤ᵐ[volume.restrict {t : ℝ | W ≤ |t| ∧ |t| ≤ V}]
        (fun t : ℝ => ‖w.A_X t‖) := ae_of_all _ (fun t => norm_nonneg _)
    have hBandSubsetAe : (P (Sum.inr j) : Set ℝ) ≤ᵐ[volume]
        {t : ℝ | W ≤ |t| ∧ |t| ≤ V} := by
      filter_upwards with t ht
      exact hBandTail ht
    have hnormIntegralLe :
        ∫ t in P (Sum.inr j), ‖w.A_X t‖ ≤ dirichletAbsoluteTailIntegral w W V :=
      setIntegral_mono_set hnormTail hnormNonneg hBandSubsetAe
    have hpow : 0 < (2 : ℝ) ^ j.val := pow_pos (by norm_num) _
    have hweightPoint (t : ℝ) (ht : t ∈ P (Sum.inr j)) :
        dirichletMellinKernelWeight T0 t ≤ ((2 : ℝ) ^ j.val)⁻¹ := by
      change T0 * (2 : ℝ) ^ j.val < |t| ∧
        |t| ≤ min (T0 * W ^ 4) (T0 * (2 : ℝ) ^ (j.val + 1)) at ht
      have hT0lej : T0 ≤ T0 * (2 : ℝ) ^ j.val := by
        have hpow1' : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
        have hpowfac' : 0 ≤ (2 : ℝ) ^ j.val - 1 := sub_nonneg.mpr hpow1'
        nlinarith [mul_nonneg hT0pos.le hpowfac']
      have hT0abs : T0 ≤ |t| := le_trans hT0lej ht.1.le
      have habs : 0 < |t| := lt_of_lt_of_le hT0pos hT0abs
      have hratio : T0 / |t| ≤ ((2 : ℝ) ^ j.val)⁻¹ :=
        (div_le_iff₀ habs).2 (by
          calc
            T0 ≤ |t| / (2 : ℝ) ^ j.val :=
              (le_div_iff₀ hpow).2 ht.1.le
            _ = ((2 : ℝ) ^ j.val)⁻¹ * |t| := by ring)
      simpa [dirichletMellinKernelWeight, max_eq_right hT0abs] using hratio
    have hconstBand : IntegrableOn
        (fun t : ℝ => ((2 : ℝ) ^ j.val)⁻¹ * ‖w.A_X t‖) (P (Sum.inr j)) := by
      exact hnormBand.const_mul _
    have hmono :
        ∫ t in P (Sum.inr j), g t ≤
          ∫ t in P (Sum.inr j), ((2 : ℝ) ^ j.val)⁻¹ * ‖w.A_X t‖ := by
      apply setIntegral_mono_on hGband hconstBand hBandMeas
      intro t ht
      calc
        g t = ‖w.A_X t‖ * dirichletMellinKernelWeight T0 t := rfl
        _ ≤ ‖w.A_X t‖ * ((2 : ℝ) ^ j.val)⁻¹ :=
          mul_le_mul_of_nonneg_left (hweightPoint t ht) (norm_nonneg _)
        _ = ((2 : ℝ) ^ j.val)⁻¹ * ‖w.A_X t‖ := by ring
    have hVupper : V / T0 ≤ (2 : ℝ) ^ (j.val + 1) := by
      apply (div_le_iff₀ hT0pos).2
      have hVle : V ≤ T0 * (2 : ℝ) ^ (j.val + 1) := min_le_right _ _
      simpa only [mul_comm] using hVle
    have htailBound := dirichletMeanEnvelope_tailIntegral_le w hA hW hWT hVmem
    have hinvnonneg : 0 ≤ ((2 : ℝ) ^ j.val)⁻¹ := (inv_nonneg.mpr hpow.le)
    have hscaled :
        ((2 : ℝ) ^ j.val)⁻¹ * ((V / T0) * dirichletMeanEnvelope w T0 W) ≤
          2 * dirichletMeanEnvelope w T0 W := by
      have hDscaled : (V / T0) * dirichletMeanEnvelope w T0 W ≤
          (2 : ℝ) ^ (j.val + 1) * dirichletMeanEnvelope w T0 W :=
        mul_le_mul_of_nonneg_right hVupper hDnonneg
      calc
        _ ≤ ((2 : ℝ) ^ j.val)⁻¹ *
            ((2 : ℝ) ^ (j.val + 1) * dirichletMeanEnvelope w T0 W) :=
              mul_le_mul_of_nonneg_left hDscaled hinvnonneg
        _ = 2 * dirichletMeanEnvelope w T0 W := by
              rw [pow_succ]
              field_simp [pow_ne_zero j.val (by norm_num : (2 : ℝ) ≠ 0)]
    calc
      ∫ t in P (Sum.inr j), g t ≤
          ∫ t in P (Sum.inr j), ((2 : ℝ) ^ j.val)⁻¹ * ‖w.A_X t‖ := hmono
      _ = ((2 : ℝ) ^ j.val)⁻¹ *
          ∫ t in P (Sum.inr j), ‖w.A_X t‖ := by rw [integral_const_mul]
      _ ≤ ((2 : ℝ) ^ j.val)⁻¹ * dirichletAbsoluteTailIntegral w W V :=
        mul_le_mul_of_nonneg_left hnormIntegralLe hinvnonneg
      _ ≤ ((2 : ℝ) ^ j.val)⁻¹ *
          ((V / T0) * dirichletMeanEnvelope w T0 W) :=
        mul_le_mul_of_nonneg_left htailBound hinvnonneg
      _ ≤ 2 * dirichletMeanEnvelope w T0 W := hscaled
  let bound : Unit ⊕ Fin J → ℝ := Sum.elim (fun _ => dirichletMeanEnvelope w T0 W)
      (fun _ => 2 * dirichletMeanEnvelope w T0 W)
  have hsumBound :
      ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t ≤ ∑ i : Unit ⊕ Fin J, bound i := by
    apply Finset.sum_le_sum
    intro i hi
    cases i with
    | inl u => simpa [bound] using hLow
    | inr j => simpa [bound] using hBand j
  have hsumEq :
      ∑ i : Unit ⊕ Fin J, bound i =
        (1 + 2 * (J : ℝ)) * dirichletMeanEnvelope w T0 W := by
    simp [bound, Fintype.sum_sum_type, Finset.sum_const,
      nsmul_eq_mul, mul_comm, mul_assoc]
    ring
  calc
    ∫ t in E, ‖w.A_X t‖ * min 1 (T0 / |t|) = ∫ t in E, g t := hsourceEq
    _ = ∑ i : Unit ⊕ Fin J, ∫ t in P i, g t := hdecomp
    _ ≤ ∑ i : Unit ⊕ Fin J, bound i := hsumBound
    _ = (1 + 2 * (J : ℝ)) * dirichletMeanEnvelope w T0 W := hsumEq
    _ ≤ (3 + 12 * Real.log W) * dirichletMeanEnvelope w T0 W := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [J] using dyadicMellinBandCount_bound hW) hDnonneg'

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.dirichletMeanEnvelope_hasMaximum
#print axioms FractionalPrimes.Literature.Polynomial.mellinWindowData_A_X_continuous
#print axioms FractionalPrimes.Literature.Polynomial.dyadicMellinIntegral

