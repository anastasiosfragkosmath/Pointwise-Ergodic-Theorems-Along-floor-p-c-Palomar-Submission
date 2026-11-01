module

public import FractionalPrimes.Literature.Multiplier.WeakStrongInterpolation

/-!
# The lower-exponent periodic multiplier application

This file applies the finite-input layer-cake theorem to the normalized
Fourier multiplier `TmL2 h / D` when `D > 0`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped ENNReal

noncomputable section

private def finiteSequenceL2Linear :
    (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun := finiteSequenceL2
  map_add' f g := by
    apply lp.ext
    funext k
    simp
  map_smul' c f := by
    apply lp.ext
    funext k
    simp

/-- For `1 < p < 2` and positive symbol size `D`, the periodic `ℓ²`
multiplier applied to a finite input has an `ℓᵖ` representative with the
blueprint's exact interpolation constant times `D`. -/
theorem exists_TmL2_lp_of_finsupp
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hD : 0 < D)
    (hp1 : 1 < p) (hp2 : p < 2) (f : ℤ →₀ ℂ) :
    ∃ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ((F : ℤ → ℂ) = fun k => TmL2 h (finiteSequenceL2 f) k) ∧
      ‖F‖ ≤
        (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) * D *
          (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by
  classical
  let U : (ℤ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
    (D : ℂ)⁻¹ •
      ((TmL2CLM h).toLinearMap.comp finiteSequenceL2Linear)
  have hU_apply (g : ℤ →₀ ℂ) :
      U g = (D : ℂ)⁻¹ • TmL2 h (finiteSequenceL2 g) := by
    change (D : ℂ)⁻¹ • TmL2CLM h (finiteSequenceL2 g) = _
    rw [← TmL2_eq_TmL2CLM h (finiteSequenceL2 g)]
  have hDinvNorm : ‖(D : ℂ)⁻¹‖ = 1 / D := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    simp [one_div]
  have hU_point (g : ℤ →₀ ℂ) (x : ℤ) :
      U g x = (D : ℂ)⁻¹ * TmL2 h (finiteSequenceL2 g) x := by
    have h := congrArg (fun v : lp (fun _ : ℤ => ℂ) 2 => v x) (hU_apply g)
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using h
  have hweak : ∀ g : ℤ →₀ ℂ, ∀ r : ℝ, 0 < r →
      (Set.ncard {x : ℤ | r < ‖U g x‖} : ℝ) ≤
        W / r * discreteL1Norm (g : ℤ → ℂ) := by
    intro g r hr
    have hfiniteSequence :
        finiteIntegerSequenceL2 g.support (g : ℤ → ℂ) = finiteSequenceL2 g := by
      apply lp.ext
      funext k
      rw [finiteIntegerSequenceL2_apply, finiteSequenceL2_apply]
      by_cases hk : k ∈ g.support
      · simp [hk]
      · have hgk : g k = 0 := by
          by_contra hne
          exact hk (Finsupp.mem_support_iff.mpr hne)
        simp [hk, hgk]
    have hfiniteSet : g.hasFiniteSupport.toFinset = g.support := by
      ext k
      simp [Function.support, Finsupp.mem_support_iff]
    have hlevel :
        {x : ℤ | r < ‖U g x‖} =
          {x : ℤ | D * r < ‖TmL2 h (finiteSequenceL2 g) x‖} := by
      ext x
      have hnorm : ‖U g x‖ = ‖TmL2 h (finiteSequenceL2 g) x‖ / D := by
        rw [hU_point, norm_mul, hDinvNorm]
        ring
      change (r < ‖U g x‖) ↔
        D * r < ‖TmL2 h (finiteSequenceL2 g) x‖
      rw [hnorm]
      constructor
      · intro hx
        have hx' := (lt_div_iff₀ hD).mp hx
        simpa [mul_comm] using hx'
      · intro hx
        apply (lt_div_iff₀ hD).mpr
        simpa [mul_comm] using hx
    calc
      (Set.ncard {x : ℤ | r < ‖U g x‖} : ℝ) =
          (Set.ncard {x : ℤ | D * r <
            ‖TmL2 h (finiteSequenceL2 g) x‖} : ℝ) := by
              rw [hlevel]
      _ ≤ W * D / (D * r) * discreteL1Norm (g : ℤ → ℂ) := by
        have hkernel :=
          kernelWeakType h (g : ℤ → ℂ) g.hasFiniteSupport (mul_pos hD hr)
        rw [hfiniteSet, hfiniteSequence] at hkernel
        exact hkernel
      _ = W / r * discreteL1Norm (g : ℤ → ℂ) := by
        field_simp [ne_of_gt hD, ne_of_gt hr]
  have hstrong : ∀ g : ℤ →₀ ℂ,
      ‖U g‖ ≤ ‖finiteSequenceL2 g‖ := by
    intro g
    have hTm :
        ‖TmL2 h (finiteSequenceL2 g)‖ ≤ D * ‖finiteSequenceL2 g‖ := by
      calc
        ‖TmL2 h (finiteSequenceL2 g)‖ ≤
            ‖torusSymbolLp h‖ * ‖finiteSequenceL2 g‖ :=
          norm_TmL2_le h _
        _ ≤ D * ‖finiteSequenceL2 g‖ :=
          mul_le_mul_of_nonneg_right (norm_torusSymbolLp_le_D h)
            (norm_nonneg (finiteSequenceL2 g))
    rw [hU_apply, norm_smul, hDinvNorm]
    calc
      (1 / D) * ‖TmL2 h (finiteSequenceL2 g)‖ ≤
          (1 / D) * (D * ‖finiteSequenceL2 g‖) :=
        mul_le_mul_of_nonneg_left hTm (by positivity)
      _ = ‖finiteSequenceL2 g‖ := by field_simp [ne_of_gt hD]
  obtain ⟨G, hG, hGnorm⟩ :=
    weakStrongInterpolation hp1 hp2 U hweak hstrong f
  have hpENN1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact (ENNReal.one_le_ofReal).2 (by linarith)
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hpENN1⟩
  refine ⟨(D : ℂ) • G, ?_, ?_⟩
  · funext k
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [congrFun hG k, hU_point f k]
    rw [← mul_assoc]
    have hDcomplex : (D : ℂ) * (D : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hD)
    rw [hDcomplex, one_mul]
  · calc
      ‖(D : ℂ) • G‖ = D * ‖G‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
      _ ≤ D *
          ((2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) *
            (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p)) :=
        mul_le_mul_of_nonneg_left hGnorm hD.le
      _ = (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) * D *
          (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by ring

/-- A zero symbol-size constant forces the entire `ℓ²` multiplier to vanish.
This is the zero-constant branch of the periodic multiplier theorem. -/
theorem TmL2_eq_zero_of_D_eq_zero
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (hD : D = 0)
    (u : lp (fun _ : ℤ => ℂ) 2) : TmL2 h u = 0 := by
  have hbound : ‖TmL2 h u‖ ≤ 0 := by
    calc
      ‖TmL2 h u‖ ≤ ‖torusSymbolLp h‖ * ‖u‖ := norm_TmL2_le h u
      _ ≤ D * ‖u‖ :=
        mul_le_mul_of_nonneg_right (norm_torusSymbolLp_le_D h)
          (norm_nonneg u)
      _ = 0 := by simp [hD]
  have hnorm : ‖TmL2 h u‖ = 0 := le_antisymm hbound (norm_nonneg _)
  exact norm_eq_zero.mp hnorm

/-- The exact finite-input `p=2` estimate. Its interpolation constant is
`C₂ = 1`, so the operator bound is exactly `D` times the represented input
`ℓ²` norm. -/
theorem norm_TmL2_finiteSequenceL2_le
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (f : ℤ →₀ ℂ) :
    ‖TmL2 h (finiteSequenceL2 f)‖ ≤ D * ‖finiteSequenceL2 f‖ := by
  calc
    ‖TmL2 h (finiteSequenceL2 f)‖ ≤
        ‖torusSymbolLp h‖ * ‖finiteSequenceL2 f‖ :=
      norm_TmL2_le h _
    _ ≤ D * ‖finiteSequenceL2 f‖ :=
      mul_le_mul_of_nonneg_right (norm_torusSymbolLp_le_D h)
        (norm_nonneg (finiteSequenceL2 f))

end

end FractionalPrimes.Literature.Multiplier
