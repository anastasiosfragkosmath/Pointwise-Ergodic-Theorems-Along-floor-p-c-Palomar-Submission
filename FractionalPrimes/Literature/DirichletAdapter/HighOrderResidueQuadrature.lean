module

public import FractionalPrimes.Literature.DirichletAdapter.QuadratureModeAlgebra

/-! The generic high-order residue-lattice quadrature estimate. -/

@[expose] public section

open MeasureTheory Real
open scoped FourierTransform ContDiff CompactlySupported

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The blueprint quadrature estimate in the affine-lattice parametrization. -/
theorem highOrderAffineLatticeQuadrature
    (F : ℝ → ℂ) (hcompact : HasCompactSupport F)
    (hsmooth : ContDiff ℝ ∞ F)
    (hInt : ∀ n : ℕ, Integrable (iteratedDeriv n F) volume)
    (q b : ℝ) (hq : 0 < q) (j : ℕ) (hj : 2 ≤ j) :
    ‖(∑' m : ℤ, F (b + q * (m : ℝ))) -
        q⁻¹ • ∫ x : ℝ, F x ∂volume‖ ≤
      4 * q ^ (j - 1) *
        ∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume := by
  let g : ℝ → ℂ := fun x => F (b + q * x)
  have hgcompact : HasCompactSupport g := residueAffine_hasCompactSupport F hcompact q b hq
  have hgsmooth : ContDiff ℝ ∞ g := residueAffine_contDiff F hsmooth q b
  have hseries : Summable (fun k : ℤ => 𝓕 g (k : ℝ)) :=
    compactSmooth_fourier_int_summable g hgcompact hgsmooth
  have hpoisson :
      (∑' m : ℤ, F (b + q * (m : ℝ))) =
        ∑' k : ℤ, 𝓕 g (k : ℝ) := by
    simpa [g] using compactSmooth_poisson g hgcompact hgsmooth 0
  have hzero : 𝓕 g (0 : ℝ) = q⁻¹ • ∫ x : ℝ, F x ∂volume := by
    rw [show g = fun x : ℝ => F (b + q * x) from rfl,
      fourier_comp_residue_affine F q b 0 hq]
    simp [Real.fourier_real_eq]
  have hA : 0 ≤ ∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume :=
    integral_nonneg fun x => norm_nonneg _
  let C : ℝ := q ^ (j - 1) *
    ∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmajor : Summable (fun k : ℤ => C * reciprocalMode j k) :=
    (reciprocalMode_summable j hj).mul_left C
  have hrest : Summable (fun k : ℤ =>
      if k = 0 then (0 : ℝ) else ‖𝓕 g (k : ℝ)‖) := by
    apply hseries.norm.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
    simp [hk]
  have hpoint (k : ℤ) :
      (if k = 0 then (0 : ℝ) else ‖𝓕 g (k : ℝ)‖) ≤
        C * reciprocalMode j k := by
    by_cases hk : k = 0
    · simp [hk, reciprocalMode, hC]
    · simp only [if_neg hk]
      simpa only [g, C, mul_assoc] using
        affine_fourier_mode_le_reciprocal F j (by omega) hsmooth hInt q b hq k hk
  calc
    ‖(∑' m : ℤ, F (b + q * (m : ℝ))) -
        q⁻¹ • ∫ x : ℝ, F x ∂volume‖ =
      ‖(∑' k : ℤ, 𝓕 g (k : ℝ)) - 𝓕 g (0 : ℝ)‖ := by
        rw [hpoisson, hzero]
    _ ≤ ∑' k : ℤ, if k = 0 then (0 : ℝ) else ‖𝓕 g (k : ℝ)‖ := by
      simpa only [Int.cast_zero] using norm_tsum_sub_zero_le _ hseries
    _ ≤ ∑' k : ℤ, C * reciprocalMode j k :=
      hrest.tsum_le_tsum hpoint hmajor
    _ = C * ∑' k : ℤ, reciprocalMode j k := by
      rw [tsum_mul_left]
    _ ≤ C * 4 := mul_le_mul_of_nonneg_left
      (reciprocal_integer_modes_le_four j hj) hC
    _ = 4 * q ^ (j - 1) *
        ∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume := by
      dsimp [C]
      ring

#print axioms highOrderAffineLatticeQuadrature

/-- High-order quadrature on an arbitrary integer residue class, with the
exact blueprint constant and no coprimality condition. -/
theorem highOrderResidueQuadrature
    (F : C_c(ℝ, ℂ)) (hsmooth : ContDiff ℝ ∞ (F : ℝ → ℂ))
    (q : ℕ) (hq : 1 ≤ q) (b : ℤ) (j : ℕ) (hj : 2 ≤ j) :
    ‖(∑' n : ResidueLattice (q : ℤ) b, F (n.1 : ℝ)) -
        ((q : ℝ)⁻¹) • ∫ x : ℝ, F x ∂volume‖ ≤
      4 * (q : ℝ) ^ (j - 1) *
        ∫ x : ℝ, ‖iteratedDeriv j (F : ℝ → ℂ) x‖ ∂volume := by
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqint : 1 ≤ (q : ℤ) := by exact_mod_cast hq
  have hInt : ∀ n : ℕ, Integrable (iteratedDeriv n (F : ℝ → ℂ)) volume :=
    compactSmooth_iteratedDeriv_integrable (F : ℝ → ℂ) F.hasCompactSupport hsmooth
  have hraw := highOrderAffineLatticeQuadrature (F : ℝ → ℂ)
    F.hasCompactSupport hsmooth hInt (q : ℝ) (b : ℝ) hqreal j hj
  have hreindex := residueLatticePeriodization_zero F (q : ℤ) b hqint
  have hsum :
      (∑' m : ℤ, F ((b : ℝ) + (q : ℝ) * (m : ℝ))) =
        ∑' n : ResidueLattice (q : ℤ) b, F (n.1 : ℝ) := by
    simpa [residueLatticePeriodization] using hreindex
  rw [← hsum]
  exact hraw

#print axioms highOrderResidueQuadrature

end FractionalPrimes.Literature.DirichletAdapter

end
