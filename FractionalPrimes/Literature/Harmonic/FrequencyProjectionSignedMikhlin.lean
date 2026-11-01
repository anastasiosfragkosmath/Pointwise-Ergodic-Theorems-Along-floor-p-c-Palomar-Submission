module

public import FractionalPrimes.Literature.Harmonic.FrequencyProjectionSmoothLift

/-!
# Uniform Mikhlin data for finite signed frequency resolutions

This file packages the exact finite signed source symbols for the
periodic multiplier theorem. The symbol and derivative bounds are
uniform in the truncation and signs.
-/

@[expose] public section

open scoped BigOperators ContDiff

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier

noncomputable section

def finiteFrequencyProjectionSignedLift
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) (ξ : ℝ) : ℂ :=
  ∑ h ∈ Finset.range (N + 1),
    (ε h : ℂ) * frequencyProjectionPeriodicLift c (h : ℤ) ξ

theorem finiteFrequencyProjectionSignedLift_eq_representative
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) {ξ : ℝ}
    (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    finiteFrequencyProjectionSignedLift c N ε ξ =
      (finiteFrequencyProjectionSignedSymbol c N ε ξ : ℂ) := by
  unfold finiteFrequencyProjectionSignedLift finiteFrequencyProjectionSignedSymbol
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro h hh
  have hshift := frequencyProjectionPeriodicLift_eq_shift c (h : ℤ) 0
    (by simpa using hξ)
  simpa using congrArg (fun z : ℂ => (ε h : ℂ) * z) hshift

theorem finiteFrequencyProjectionSignedLift_periodic
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) :
    Function.Periodic (finiteFrequencyProjectionSignedLift c N ε) 1 := by
  intro ξ
  simp only [finiteFrequencyProjectionSignedLift]
  apply Finset.sum_congr rfl
  intro h hh
  rw [frequencyProjectionPeriodicLift_periodic c (h : ℤ) ξ]

theorem finiteFrequencyProjectionSignedLift_contDiffOn_punctured
    {c : ℝ} (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ) :
    ContDiffOn ℝ 2 (finiteFrequencyProjectionSignedLift c N ε)
      puncturedTorusLift := by
  unfold finiteFrequencyProjectionSignedLift
  apply ContDiffOn.sum
  intro h hh
  exact contDiffOn_const.mul
    (frequencyProjectionPeriodicLift_contDiffOn_punctured hc (h : ℤ))

theorem finiteFrequencyProjectionSignedLift_norm_le_two
    {c : ℝ} (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) (ξ : ℝ) :
    ‖finiteFrequencyProjectionSignedLift c N ε ξ‖ ≤ 2 := by
  let y : ℝ := toIocMod (by norm_num : (0 : ℝ) < 1)
    (-(1 / 2 : ℝ)) ξ
  have hy : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    have hy' := toIocMod_mem_Ioc
      (by norm_num : (0 : ℝ) < 1) (-(1 / 2 : ℝ)) ξ
    simpa only [y, show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring] using hy'
  have hmod (h : ℤ) :
      frequencyProjectionPeriodicLift c h ξ =
        frequencyProjectionPeriodicLift c h y := by
    simp [frequencyProjectionPeriodicLift, y, toIocMod_eq_toIocMod]
  have hsum : finiteFrequencyProjectionSignedLift c N ε ξ =
      finiteFrequencyProjectionSignedLift c N ε y := by
    unfold finiteFrequencyProjectionSignedLift
    apply Finset.sum_congr rfl
    intro h hh
    rw [hmod]
  rw [hsum, finiteFrequencyProjectionSignedLift_eq_representative c N ε hy,
    Complex.norm_real, Real.norm_eq_abs]
  exact finiteFrequencyProjectionSignedSymbol_abs_le_two hc N ε hε

theorem finiteFrequencyProjectionSignedSymbol_contDiff
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (finiteFrequencyProjectionSignedSymbol c N ε) := by
  unfold finiteFrequencyProjectionSignedSymbol
  apply ContDiff.sum
  intro h hh
  exact contDiff_const.mul (frequencyProjectionSymbolRepresentative_contDiff c (h : ℤ))

private theorem deriv_complex_ofReal
    (f : ℝ → ℝ) (hf : ContDiff ℝ (∞ : ℕ∞ω) f) (ξ : ℝ) :
    deriv (fun x : ℝ => (f x : ℂ)) ξ = ((deriv f ξ : ℝ) : ℂ) := by
  have hderiv : HasDerivAt f (deriv f ξ) ξ :=
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact hderiv.ofReal_comp.deriv

private theorem iteratedDeriv_two_complex_ofReal
    (f : ℝ → ℝ) (hf : ContDiff ℝ (∞ : ℕ∞ω) f) (ξ : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => (f x : ℂ)) ξ =
      ((iteratedDeriv 2 f ξ : ℝ) : ℂ) := by
  have hderivFun :
      deriv (fun x : ℝ => (f x : ℂ)) =
        fun x => ((deriv f x : ℝ) : ℂ) := by
    funext x
    exact deriv_complex_ofReal f hf x
  have hf' : ContDiff ℝ (∞ : ℕ∞ω) (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2
  simp only [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ', iteratedDeriv_one, hderivFun]
  exact deriv_complex_ofReal (deriv f) hf' ξ

private theorem finiteFrequencyProjectionSignedLift_eventuallyEq_representative
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) {ξ : ℝ}
    (hξ : |ξ| < 1 / 2) :
    finiteFrequencyProjectionSignedLift c N ε =ᶠ[nhds ξ]
      fun x => (finiteFrequencyProjectionSignedSymbol c N ε x : ℂ) := by
  have hξIoo : ξ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rcases abs_lt.mp hξ with ⟨hl, hr⟩
    exact ⟨hl, hr⟩
  filter_upwards [isOpen_Ioo.mem_nhds hξIoo] with x hx
  exact finiteFrequencyProjectionSignedLift_eq_representative c N ε
    ⟨hx.1, hx.2.le⟩

theorem finiteFrequencyProjectionSignedLift_deriv
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) {ξ : ℝ} (hξ : |ξ| < 1 / 2) :
    deriv (finiteFrequencyProjectionSignedLift c N ε) ξ =
      ((deriv (finiteFrequencyProjectionSignedSymbol c N ε) ξ : ℝ) : ℂ) := by
  have hEv := finiteFrequencyProjectionSignedLift_eventuallyEq_representative
    c N ε hξ
  rw [hEv.deriv_eq]
  exact deriv_complex_ofReal _
    (finiteFrequencyProjectionSignedSymbol_contDiff c N ε) ξ

theorem finiteFrequencyProjectionSignedLift_iteratedDeriv_two
    (c : ℝ) (N : ℕ) (ε : ℕ → ℝ) {ξ : ℝ} (hξ : |ξ| < 1 / 2) :
    iteratedDeriv 2 (finiteFrequencyProjectionSignedLift c N ε) ξ =
      ((iteratedDeriv 2
        (finiteFrequencyProjectionSignedSymbol c N ε) ξ : ℝ) : ℂ) := by
  have hEv := finiteFrequencyProjectionSignedLift_eventuallyEq_representative
    c N ε hξ
  rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hEv]
  exact iteratedDeriv_two_complex_ofReal _
    (finiteFrequencyProjectionSignedSymbol_contDiff c N ε) ξ

theorem finiteFrequencyProjectionSignedLift_weightedDeriv_le
    {c : ℝ} (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) {ξ : ℝ} (hξ : |ξ| < 1 / 2) :
    ‖(ξ : ℂ) * deriv (finiteFrequencyProjectionSignedLift c N ε) ξ‖ ≤
      2 * ((3 / 8 : ℝ) * (ψDerivSup / 2)) := by
  have hcoeff : ∀ j ≤ N, |frequencyProjectionSignDifference N ε j| ≤ 2 := by
    intro j hj
    exact frequencyProjectionSignDifference_abs_le_two N ε hε j
  have hreal := finiteFrequencyProjectionScaledDerivative_weighted_le
    hc N (frequencyProjectionSignDifference N ε) hcoeff (ξ := ξ)
  calc
    ‖(ξ : ℂ) * deriv (finiteFrequencyProjectionSignedLift c N ε) ξ‖ =
        ‖((ξ * deriv (finiteFrequencyProjectionSignedSymbol c N ε) ξ : ℝ) : ℂ)‖ := by
          rw [finiteFrequencyProjectionSignedLift_deriv c N ε hξ]
          push_cast
          rfl
    _ = ‖ξ * deriv (finiteFrequencyProjectionSignedSymbol c N ε) ξ‖ := by
          simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by
          rw [finiteFrequencyProjectionSignedSymbol_deriv]
          exact hreal

theorem finiteFrequencyProjectionSignedLift_weightedIteratedDerivTwo_le
    {c : ℝ} (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) {ξ : ℝ} (hξ : |ξ| < 1 / 2) :
    ‖(ξ : ℂ) ^ 2 *
      iteratedDeriv 2 (finiteFrequencyProjectionSignedLift c N ε) ξ‖ ≤
      2 * ((3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4)) := by
  have hcoeff : ∀ j ≤ N, |frequencyProjectionSignDifference N ε j| ≤ 2 := by
    intro j hj
    exact frequencyProjectionSignDifference_abs_le_two N ε hε j
  have hreal := finiteFrequencyProjectionScaledIteratedDerivTwo_weighted_le
    hc N (frequencyProjectionSignDifference N ε) hcoeff (ξ := ξ)
  calc
    ‖(ξ : ℂ) ^ 2 *
      iteratedDeriv 2 (finiteFrequencyProjectionSignedLift c N ε) ξ‖ =
        ‖((ξ ^ 2 * iteratedDeriv 2
          (finiteFrequencyProjectionSignedSymbol c N ε) ξ : ℝ) : ℂ)‖ := by
          rw [finiteFrequencyProjectionSignedLift_iteratedDeriv_two c N ε hξ]
          push_cast
          rfl
    _ = ‖ξ ^ 2 * iteratedDeriv 2
        (finiteFrequencyProjectionSignedSymbol c N ε) ξ‖ := by
          simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by
          rw [finiteFrequencyProjectionSignedSymbol_iteratedDeriv_two]
          exact hreal

/-- A fixed admissible source constant for all finite signed dyadic
resolutions. It is independent of the truncation and signs. -/
def frequencyProjectionSignedMikhlinConstant : ℝ :=
  2 + 2 * ((3 / 8 : ℝ) * (ψDerivSup / 2)) +
    2 * ((3 / 8 : ℝ) ^ 2 * (ψSecondDerivSup / 4))

/-- Every finite signed resolution satisfies the periodic Mikhlin
hypotheses with the same constant, including all three seam identities. -/
theorem finiteFrequencyProjectionSignedMikhlin
    {c : ℝ} (hc : 1 < c) (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ h ≤ N, |ε h| = 1) :
    PeriodicMikhlinHypotheses
      (finiteFrequencyProjectionSignedLift c N ε)
      frequencyProjectionSignedMikhlinConstant := by
  let m := finiteFrequencyProjectionSignedLift c N ε
  have hper : Function.Periodic m 1 :=
    finiteFrequencyProjectionSignedLift_periodic c N ε
  have hend : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by ring
  refine {
    bounded := ⟨2, finiteFrequencyProjectionSignedLift_norm_le_two hc N ε hε⟩
    periodic := hper
    smoothOnPuncturedTorus :=
      finiteFrequencyProjectionSignedLift_contDiffOn_punctured hc N ε
    seamValue := ?_
    seamFirstDerivative := ?_
    seamSecondDerivative := ?_
    weightedDerivativeBound := ?_
  }
  · have h := hper (-(1 / 2 : ℝ))
    change m (-(1 / 2 : ℝ)) = m (1 / 2)
    rw [hend] at h
    exact h.symm
  · have h := deriv_periodic_one m hper (-(1 / 2 : ℝ))
    change deriv m (-(1 / 2 : ℝ)) = deriv m (1 / 2)
    rw [hend] at h
    exact h.symm
  · have h := iteratedDeriv_two_periodic_one m hper (-(1 / 2 : ℝ))
    change iteratedDeriv 2 m (-(1 / 2 : ℝ)) = iteratedDeriv 2 m (1 / 2)
    rw [hend] at h
    exact h.symm
  · intro ξ hξ0 hξ
    have hzero := finiteFrequencyProjectionSignedLift_norm_le_two hc N ε hε ξ
    have hfirst := finiteFrequencyProjectionSignedLift_weightedDeriv_le
      hc N ε hε hξ
    have hsecond := finiteFrequencyProjectionSignedLift_weightedIteratedDerivTwo_le
      hc N ε hε hξ
    dsimp [m, frequencyProjectionSignedMikhlinConstant]
    linarith

end

end FractionalPrimes.Literature.Harmonic

end
