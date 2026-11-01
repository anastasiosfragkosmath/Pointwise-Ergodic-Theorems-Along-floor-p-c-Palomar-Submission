module

public import FractionalPrimes.Literature.Polynomial.MellinWindowData
public import FractionalPrimes.PolynomialKernelProperties
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open MeasureTheory

noncomputable section

/-- The exact arithmetic and local-mass hypotheses of `ltw:absolute-data`.
The smoothing density is the fixed `polynomialKernelRho` of
`lup:kernel-data`, rather than a free choice. -/
structure FullFrequencyMellinData where
  X : ℝ
  H : ℝ
  a : ℕ → ℂ
  K : ℝ
  h0 : ℝ
  X_lower : 3 ≤ X
  H_pos : 0 < H
  H_upper : H ≤ X
  K_nonneg : 0 ≤ K
  h0_pos : 0 < h0
  h0_upper : h0 ≤ X
  coefficient_support : ∀ n, a n ≠ 0 →
    X / (2 : ℝ) ^ 21 < (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ 22 * X
  local_mass : ∀ (x h : ℝ), 0 ≤ h →
    (∑ n ∈ Polynomial.mellinIntervalIndices x (x + h), ‖a n‖) ≤
      K * (h + h0)

/-- Package the source hypotheses without an extra coefficient bound or a
relation between `T₀` and `W`. -/
noncomputable def fullFrequencyMellinData
    (X H K h0 : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X)
    (hK : 0 ≤ K) (hh0 : 0 < h0) (hh0X : h0 ≤ X)
    (hsupport : ∀ n, a n ≠ 0 →
      X / (2 : ℝ) ^ 21 < (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ 22 * X)
    (hmass : ∀ (x h : ℝ), 0 ≤ h →
      (∑ n ∈ Polynomial.mellinIntervalIndices x (x + h), ‖a n‖) ≤
        K * (h + h0)) : FullFrequencyMellinData :=
  ⟨X, H, a, K, h0, hX, hH, hHX, hK, hh0, hh0X, hsupport, hmass⟩

/-- The finite support interval `(2⁻²¹ X,2²² X]`. -/
noncomputable def fullFrequencySupportIndices (X : ℝ) : Finset ℕ :=
  Polynomial.mellinIntervalIndices (X / (2 : ℝ) ^ 21) ((2 : ℝ) ^ 22 * X)

theorem FullFrequencyMellinData.coefficient_eq_zero_off_support
    (d : FullFrequencyMellinData) (n : ℕ)
    (hn : n ∉ fullFrequencySupportIndices d.X) : d.a n = 0 := by
  by_contra hnonzero
  have hsupport := d.coefficient_support n hnonzero
  have hleft : 0 ≤ d.X / (2 : ℝ) ^ 21 := by
    exact div_nonneg (by linarith [d.X_lower]) (by positivity)
  have hmem := (Polynomial.mellinIntervalIndices_mem_iff hleft n).2 hsupport
  exact hn hmem

/-- The complete Dirichlet polynomial, including all frequencies. -/
noncomputable def fullFrequencyMellinPolynomial
    (d : FullFrequencyMellinData) (t : ℝ) : ℂ :=
  ∑ n ∈ fullFrequencySupportIndices d.X,
    d.a n * Polynomial.mellinDirichletMonomial n t

/-- The normalized mean on the exact half-open interval `(X,X+H]`. -/
noncomputable def fullFrequencyMellinMean (d : FullFrequencyMellinData) : ℂ :=
  (↑(d.H⁻¹) : ℂ) *
    ∑ n ∈ Polynomial.mellinWindowAverageIndices d.X d.H, d.a n

/-- The full symmetric frequency integral. There is no low-frequency cutoff. -/
noncomputable def fullFrequencyAbsoluteIntegral
    (d : FullFrequencyMellinData) (U : ℝ) : ℝ :=
  ∫ t in {t : ℝ | |t| ≤ U}, ‖fullFrequencyMellinPolynomial d t‖

/-- The exact objective inside the compact maximum defining `𝔈`. -/
noncomputable def fullFrequencyEnvelopeObjective
    (d : FullFrequencyMellinData) (T0 U : ℝ) : ℝ :=
  (T0 / U) * fullFrequencyAbsoluteIntegral d U

/-- The exact full-frequency envelope, whose supremum is attained below. -/
noncomputable def fullFrequencyEnvelope
    (d : FullFrequencyMellinData) (T0 W : ℝ) : ℝ :=
  sSup (fullFrequencyEnvelopeObjective d T0 '' Set.Icc T0 (T0 * W ^ 4))

/-- The unique density chosen in `lup:kernel-data`. -/
noncomputable def fullFrequencyKernel : ℝ → ℝ := polynomialKernelRho

theorem fullFrequencyMellinPolynomial_continuous
    (d : FullFrequencyMellinData) :
    Continuous (fullFrequencyMellinPolynomial d) := by
  unfold fullFrequencyMellinPolynomial
  refine continuous_finsetSum _ ?_
  intro n hn
  apply continuous_const.mul
  unfold Polynomial.mellinDirichletMonomial
  fun_prop

private theorem fullFrequencyAbsoluteIntegral_eq_primitive
    (d : FullFrequencyMellinData) {U : ℝ} (hU : 0 ≤ U) :
    fullFrequencyAbsoluteIntegral d U =
      (∫ t in 0..U, ‖fullFrequencyMellinPolynomial d t‖) -
        (∫ t in 0..(-U), ‖fullFrequencyMellinPolynomial d t‖) := by
  have hset : {t : ℝ | |t| ≤ U} = Set.Icc (-U) U := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    exact abs_le
  have hf : Continuous (fun t : ℝ => ‖fullFrequencyMellinPolynomial d t‖) :=
    continuous_norm.comp (fullFrequencyMellinPolynomial_continuous d)
  unfold fullFrequencyAbsoluteIntegral
  rw [hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
  exact (intervalIntegral.integral_interval_sub_left
    (hf.intervalIntegrable 0 U) (hf.intervalIntegrable 0 (-U))).symm

private theorem continuous_fullFrequencyPrimitive
    (d : FullFrequencyMellinData) :
    Continuous (fun u : ℝ =>
      ∫ t in 0..u, ‖fullFrequencyMellinPolynomial d t‖) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact ((continuous_norm.comp
    (fullFrequencyMellinPolynomial_continuous d)).integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt

theorem fullFrequencyEnvelopeObjective_continuousOn
    (d : FullFrequencyMellinData) {T0 W : ℝ}
    (hT0 : 0 < T0) (hW : 2 ≤ W) :
    ContinuousOn (fullFrequencyEnvelopeObjective d T0)
      (Set.Icc T0 (T0 * W ^ 4)) := by
  let G : ℝ → ℝ := fun u =>
    ∫ t in 0..u, ‖fullFrequencyMellinPolynomial d t‖
  have hG : Continuous G := continuous_fullFrequencyPrimitive d
  have hrat : ContinuousOn (fun U : ℝ => T0 / U)
      (Set.Icc T0 (T0 * W ^ 4)) := by
    refine continuousOn_const.div continuousOn_id ?_
    intro U hU
    exact ne_of_gt (lt_of_lt_of_le hT0 hU.1)
  have hformula : ContinuousOn (fun U : ℝ =>
      (T0 / U) * (G U - G (-U)))
      (Set.Icc T0 (T0 * W ^ 4)) :=
    hrat.mul (hG.sub (hG.comp continuous_neg)).continuousOn
  apply hformula.congr
  intro U hU
  unfold fullFrequencyEnvelopeObjective
  rw [fullFrequencyAbsoluteIntegral_eq_primitive d (le_trans hT0.le hU.1)]

theorem fullFrequencyEnvelope_hasMaximum
    (d : FullFrequencyMellinData) {T0 W : ℝ}
    (hT0 : 0 < T0) (hW : 2 ≤ W) :
    ∃ U ∈ Set.Icc T0 (T0 * W ^ 4),
      fullFrequencyEnvelopeObjective d T0 U = fullFrequencyEnvelope d T0 W ∧
      ∀ V ∈ Set.Icc T0 (T0 * W ^ 4),
        fullFrequencyEnvelopeObjective d T0 V ≤ fullFrequencyEnvelope d T0 W := by
  let S : Set ℝ := Set.Icc T0 (T0 * W ^ 4)
  let F : ℝ → ℝ := fullFrequencyEnvelopeObjective d T0
  have hW1 : 1 ≤ W := by linarith
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
  have hne : S.Nonempty := by
    refine ⟨T0, ?_⟩
    constructor
    · rfl
    · nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hW4)]
  have hcont : ContinuousOn F S := by
    simpa [F, S] using fullFrequencyEnvelopeObjective_continuousOn d hT0 hW
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
  · simpa [F, S, fullFrequencyEnvelope] using hEq.symm
  · intro V hV
    change F V ≤ sSup (F '' S)
    rw [hEq]
    exact hmax hV

end

end FractionalPrimes.Literature.Twisted

end
