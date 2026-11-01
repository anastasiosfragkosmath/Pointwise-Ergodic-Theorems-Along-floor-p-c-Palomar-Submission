module

public import FractionalPrimes.Literature.DirichletAdapter.MellinLogSubstitution

/-! Compactness and smoothness of the complexified Mellin profile. -/

@[expose] public section

open MeasureTheory
open scoped ContDiff CompactlySupported FourierTransform

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The approved real Mellin profile is smooth for each parameter. -/
theorem smoothDyadicMellinH_contDiff (p : ℝ × ℝ × ℝ) :
    ContDiff ℝ ∞ (Twisted.smoothDyadicMellinH p) := by
  have hp : ContDiff ℝ ∞ (fun w : ℝ => (p, w)) := by fun_prop
  have h := Twisted.smoothDyadicMellinHJoint_contDiff.comp hp
  simpa only [Function.comp_def, Twisted.smoothDyadicMellinHJoint_eq] using h

/-- The real Mellin profile has compact support in the exact log annulus. -/
theorem smoothDyadicMellinH_hasCompactSupport (p : ℝ × ℝ × ℝ) :
    HasCompactSupport (Twisted.smoothDyadicMellinH p) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact Twisted.smoothDyadicMellinH_support_subset p

/-- Complexification preserves the compact log support. -/
theorem smoothDyadicMellinH_complex_hasCompactSupport (p : ℝ × ℝ × ℝ) :
    HasCompactSupport (fun w : ℝ => (Twisted.smoothDyadicMellinH p w : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro w hw
  apply Twisted.smoothDyadicMellinH_support_subset p
  change (Twisted.smoothDyadicMellinH p w : ℂ) ≠ 0 at hw
  change Twisted.smoothDyadicMellinH p w ≠ 0
  exact_mod_cast hw

/-- Complexification preserves smoothness. -/
theorem smoothDyadicMellinH_complex_contDiff (p : ℝ × ℝ × ℝ) :
    ContDiff ℝ ∞ (fun w : ℝ => (Twisted.smoothDyadicMellinH p w : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp (smoothDyadicMellinH_contDiff p)

/-- Every derivative needed for Fourier integration by parts is integrable. -/
theorem smoothDyadicMellinH_complex_iteratedDeriv_integrable
    (p : ℝ × ℝ × ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n
      (fun w : ℝ => (Twisted.smoothDyadicMellinH p w : ℂ))) volume :=
  compactSmooth_iteratedDeriv_integrable _
    (smoothDyadicMellinH_complex_hasCompactSupport p)
    (smoothDyadicMellinH_complex_contDiff p) n

/-- The complexified derivative norm is exactly the real objective in
the approved definition of `B_j`. -/
theorem smoothDyadicMellinH_complex_derivativeL1_eq_BObjective
    (j : ℕ) (p : ℝ × ℝ × ℝ) :
    (∫ w : ℝ, ‖iteratedDeriv j
      (fun x : ℝ => (Twisted.smoothDyadicMellinH p x : ℂ)) w‖ ∂volume) =
      Twisted.smoothDyadicBObjective j p := by
  unfold Twisted.smoothDyadicBObjective Twisted.smoothDyadicMellinDerivativeL1
  congr 1
  funext w
  rw [iteratedDeriv_complex_ofReal _ (smoothDyadicMellinH_contDiff p)]
  simp

/-- Exact `B_j` Fourier decay at the blueprint's Mellin frequency. -/
theorem smoothDyadicMellinH_fourier_le_B
    (j : ℕ) (p : ℝ × ℝ × ℝ)
    (hp : p ∈ Twisted.smoothDyadicProfileParameterBox)
    (t : ℝ) (ht : t ≠ 0) :
    ‖𝓕 (fun w : ℝ => (Twisted.smoothDyadicMellinH p w : ℂ))
      (t / (2 * Real.pi))‖ ≤
      Twisted.smoothDyadicB j / |t| ^ j := by
  have hfreq : t / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero ht (by positivity)
  have hdecay := fourier_iteratedDeriv_div_bound
    (fun w : ℝ => (Twisted.smoothDyadicMellinH p w : ℂ)) j
    (smoothDyadicMellinH_complex_contDiff p)
    (smoothDyadicMellinH_complex_iteratedDeriv_integrable p)
    (t / (2 * Real.pi)) hfreq
  have hden : 2 * Real.pi * |t / (2 * Real.pi)| = |t| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  rw [hden, smoothDyadicMellinH_complex_derivativeL1_eq_BObjective] at hdecay
  exact hdecay.trans (div_le_div_of_nonneg_right
    (Twisted.smoothDyadicB_isMaximum j p hp) (pow_nonneg (abs_nonneg t) j))

/-- The exact special-profile mean term from `lda:quadrature`. -/
theorem smoothDyadicQuadratureSource_integral_le_B
    (j : ℕ) (N t : ℝ) (p : ℝ × ℝ × ℝ)
    (hN : 0 < N) (hp : p ∈ Twisted.smoothDyadicProfileParameterBox)
    (ht : t ≠ 0) :
    ‖∫ x : ℝ, Twisted.smoothDyadicQuadratureSource N t p x ∂volume‖ ≤
      Real.sqrt N * (Twisted.smoothDyadicB j / |t| ^ j) := by
  rw [smoothDyadicQuadratureSource_integral_eq_fourier N t p hN]
  have hscale : N * N ^ (-(1 / 2 : ℝ)) = Real.sqrt N := by
    have h := (Real.rpow_add hN (1 : ℝ) (-(1 / 2 : ℝ))).symm
    calc
      N * N ^ (-(1 / 2 : ℝ)) = N ^ (1 + -(1 / 2 : ℝ)) := by simpa using h
      _ = N ^ (1 / 2 : ℝ) := by congr 1; ring
      _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
  have hnorm : ‖(N : ℂ) ^ Twisted.smoothDyadicTwistExponent t‖ =
      N ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,
      Twisted.smoothDyadicTwistExponent_re]
    norm_num
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN, norm_mul, hnorm,
    ← mul_assoc, hscale]
  exact mul_le_mul_of_nonneg_left
    (smoothDyadicMellinH_fourier_le_B j p hp t ht) (Real.sqrt_nonneg N)

#print axioms smoothDyadicMellinH_complex_iteratedDeriv_integrable
#print axioms smoothDyadicMellinH_fourier_le_B
#print axioms smoothDyadicQuadratureSource_integral_le_B

end FractionalPrimes.Literature.DirichletAdapter

end
