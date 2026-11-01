module

public import FractionalPrimes.Literature.JSW.SmoothDyadicScalarAdjointPairing

/-! The scalar source adjoint pairing for the actual continuous L2 operators. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem integral_real_inner_eq_re_mul_conj
    {f g : ℝ → ℂ} (h : Integrable (fun x => f x*conj (g x)) volume) :
    (∫ x, inner ℝ (f x) (g x) ∂volume) =
      (∫ x, f x*conj (g x) ∂volume).re := by
  calc
    _ = ∫ x, (f x*conj (g x)).re ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
      change (g x*conj (f x)).re = (f x*conj (g x)).re
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    _ = _ := integral_re h

theorem smoothDyadic_scalar_operatorAt_pairing
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (m : ℤ)
    (F G : Lp ℂ P (volume : Measure ℝ)) :
    (∫ x, inner ℝ ((smoothDyadicErrorOperatorAt hP hSupp τ m F : ℝ → ℂ) x) (G x) ∂volume) =
      ∫ x, inner ℝ (F x) ((smoothDyadicReflectedErrorOperatorAt hP hSupp τ m G : ℝ → ℂ) x) ∂volume := by
  subst P
  let T := smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num) τ m
  let S := smoothDyadicReflectedErrorLpOperator hSupp (p := 2) (by norm_num) τ m
  have ht := smoothDyadicErrorLpOperator_ae_eq_of_memLp hSupp (p := 2) (by norm_num)
    τ m F (F : ℝ → ℂ) (Lp.memLp F) Filter.EventuallyEq.rfl
  have hs := smoothDyadicReflectedErrorLpOperator_ae_eq hSupp (p := 2) (by norm_num)
    hτ m G (G : ℝ → ℂ) (Lp.memLp G) Filter.EventuallyEq.rfl
  have hf : MemLp (F : ℝ → ℂ) 2 volume := by simpa using Lp.memLp F
  have hg : MemLp (G : ℝ → ℂ) 2 volume := by simpa using Lp.memLp G
  have hc : (∫ x, (T F : ℝ → ℂ) x*conj (G x) ∂volume) =
      ∫ x, F x*conj ((S G : ℝ → ℂ) x) ∂volume := by
    calc
      _ = ∫ x, (jswConvolution (Measure.map (fun z : ℝ => τ*z)
          (initialSquarePsiProbabilityMeasure σ)) (F : ℝ → ℂ) x-
            dyadicAverage m (F : ℝ → ℂ) x)*conj (G x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [ht] with x hx
        rw [hx]
      _ = ∫ x, F x*conj (smoothPsiReflectedConvolution σ τ (G : ℝ → ℂ) x-
          dyadicAverage m (G : ℝ → ℂ) x) ∂volume :=
        smoothDyadic_scalar_raw_adjoint_pairing hSupp hτ m hf hg
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hs] with x hx
        rw [hx]
  have ht₂ : MemLp (T F : ℝ → ℂ) 2 volume := by simpa using Lp.memLp (T F)
  have hs₂ : MemLp (S G : ℝ → ℂ) 2 volume := by simpa using Lp.memLp (S G)
  change (∫ x, inner ℝ ((T F : ℝ → ℂ) x) (G x) ∂volume) =
    ∫ x, inner ℝ (F x) ((S G : ℝ → ℂ) x) ∂volume
  rw [integral_real_inner_eq_re_mul_conj (MemLp.integrable_mul ht₂ hg.star),
    integral_real_inner_eq_re_mul_conj (MemLp.integrable_mul hf hs₂.star), hc]

#print axioms smoothDyadic_scalar_operatorAt_pairing
end
end FractionalPrimes.Literature.JSW
end
