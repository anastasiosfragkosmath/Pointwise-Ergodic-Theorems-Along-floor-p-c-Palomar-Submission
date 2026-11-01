module

public import FractionalPrimes.Literature.Twisted.NonunitTripleCharacterFactorization
public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorTrilinearBridge
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Exact integration of the finite character/allocation average in the
nonunit type-II Mellin identity. The character cardinality cancels its
totient normalization; only the finite allocation count remains. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- Integrating the normalized finite character/allocation average costs
one copy of the per-term trilinear bound for each gcd allocation. The
factor `(d : ℂ)^(-1/2-it+iT)` contributes exactly `d^(-1/2)`, and the
`φ(Q)` characters cancel the source normalization `1/φ(Q)`. -/
theorem finiteAllocatedCharacterAverageIntegral_bound
    {R : Type*} [Fintype R]
    {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (a' : ℤ) (ha' : IsCoprime a' (Q : ℤ))
    (U T K : ℝ)
    (F : R → BlueprintCharacter Q → ℝ → ℂ)
    (hFcont : ∀ r χ, Continuous (F r χ))
    (hFbound : ∀ r χ,
      (∫ t in Set.Icc (-U) U, ‖F r χ t‖ ∂volume) ≤ K) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : R, ∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') * F r χ t‖ ∂volume) ≤
      (d : ℝ) ^ (-(1 / 2 : ℝ)) * (Fintype.card R : ℝ) * K := by
  classical
  let E : Set ℝ := Set.Icc (-U) U
  let exponent : ℝ → ℂ := fun t =>
    -(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)
  let scale : ℝ → ℂ := fun t =>
    Complex.exp (Complex.log (d : ℂ) * exponent t)
  let charSum : ℝ → ℂ := fun t =>
    ∑ r : R, ∑ χ : BlueprintCharacter Q,
      star (evalInt χ a') * F r χ t
  let integrand : ℝ → ℝ := fun t =>
    ‖(scale t / (Q.totient : ℂ)) * charSum t‖
  let majorant : ℝ → ℝ := fun t =>
    ((d : ℝ) ^ (-(1 / 2 : ℝ)) / (Q.totient : ℝ)) *
      ∑ r : R, ∑ χ : BlueprintCharacter Q, ‖F r χ t‖
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hcard := blueprintCharacters_card (q := Q)
  have hcardR : (Fintype.card (BlueprintCharacter Q) : ℝ) =
      (Q.totient : ℝ) := by exact_mod_cast hcard
  have hφNat : 0 < Q.totient := Nat.totient_pos.mpr hQ
  have hφ : 0 < (Q.totient : ℝ) := by exact_mod_cast hφNat
  have hφnorm : ‖(Q.totient : ℂ)‖ = (Q.totient : ℝ) := by simp
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hscaleCpow (t : ℝ) :
      scale t = (d : ℂ) ^ exponent t := by
    dsimp [scale, exponent]
    symm
    exact Complex.cpow_def_of_ne_zero hdC _
  have hscaleNorm (t : ℝ) :
      ‖scale t‖ = (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hscaleCpow, Complex.norm_natCast_cpow_of_pos hd]
    simp [exponent]
  have hDnonneg : 0 ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hEcompact : IsCompact E := by
    exact isCompact_Icc
  have hUnit : IsUnit (a' : ZMod Q) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a' Q).2 (isCoprime_comm.mpr ha')
  have hweight (χ : BlueprintCharacter Q) :
      ‖evalInt χ a'‖ = 1 := by
    simpa [evalInt] using unit_value_norm χ hUnit
  have hsumNorm (t : ℝ) :
      ‖charSum t‖ ≤
        ∑ r : R, ∑ χ : BlueprintCharacter Q, ‖F r χ t‖ := by
    dsimp [charSum]
    calc
      ‖∑ r : R, ∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') * F r χ t‖ ≤
        ∑ r : R, ‖∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') * F r χ t‖ := norm_sum_le _ _
      _ ≤ ∑ r : R, ∑ χ : BlueprintCharacter Q, ‖F r χ t‖ := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          ‖∑ χ : BlueprintCharacter Q,
              star (evalInt χ a') * F r χ t‖ ≤
            ∑ χ : BlueprintCharacter Q,
              ‖star (evalInt χ a') * F r χ t‖ := norm_sum_le _ _
          _ ≤ ∑ χ : BlueprintCharacter Q, ‖F r χ t‖ := by
            apply Finset.sum_le_sum
            intro χ hχ
            simp [hweight χ]
  have hpoint (t : ℝ) : integrand t ≤ majorant t := by
    dsimp [integrand, majorant]
    rw [norm_mul, norm_div, hscaleNorm t, hφnorm]
    exact mul_le_mul_of_nonneg_left (hsumNorm t)
      (div_nonneg hDnonneg hφ.le)
  have hFint (r : R) (χ : BlueprintCharacter Q) :
      IntegrableOn (fun t : ℝ => ‖F r χ t‖) E := by
    exact (continuous_norm.comp (hFcont r χ)).continuousOn.integrableOn_compact
      hEcompact
  have hinnerCont (r : R) :
      Continuous (fun t : ℝ =>
        ∑ χ : BlueprintCharacter Q, ‖F r χ t‖) := by
    exact continuous_finsetSum Finset.univ fun χ hχ =>
      continuous_norm.comp (hFcont r χ)
  have hsumCont :
      Continuous (fun t : ℝ =>
        ∑ r : R, ∑ χ : BlueprintCharacter Q, ‖F r χ t‖) := by
    exact continuous_finsetSum Finset.univ fun r hr => hinnerCont r
  have hmajorCont : Continuous majorant := by
    dsimp [majorant]
    exact continuous_const.mul hsumCont
  have hintIntegrand : IntegrableOn integrand E := by
    have hcont : Continuous integrand := by
      dsimp [integrand, charSum]
      fun_prop
    exact hcont.continuousOn.integrableOn_compact hEcompact
  have hintMajorant : IntegrableOn majorant E :=
    hmajorCont.continuousOn.integrableOn_compact hEcompact
  have hmono :
      (∫ t in E, integrand t ∂volume) ≤
        ∫ t in E, majorant t ∂volume := by
    exact integral_mono hintIntegrand hintMajorant hpoint
  have hsumIntegral :
      (∫ t in E,
          ∑ r : R, ∑ χ : BlueprintCharacter Q, ‖F r χ t‖ ∂volume) =
        ∑ r : R, ∑ χ : BlueprintCharacter Q,
          ∫ t in E, ‖F r χ t‖ ∂volume := by
    calc
      (∫ t in E,
          ∑ r : R, ∑ χ : BlueprintCharacter Q, ‖F r χ t‖ ∂volume) =
        ∑ r : R, ∫ t in E,
          ∑ χ : BlueprintCharacter Q, ‖F r χ t‖ ∂volume := by
            apply integral_finsetSum Finset.univ
            intro r hr
            exact (hinnerCont r).continuousOn.integrableOn_compact hEcompact
      _ = ∑ r : R, ∑ χ : BlueprintCharacter Q,
          ∫ t in E, ‖F r χ t‖ ∂volume := by
            apply Finset.sum_congr rfl
            intro r hr
            apply integral_finsetSum Finset.univ
            intro χ hχ
            exact hFint r χ
  have hsumBound :
      (∑ r : R, ∑ χ : BlueprintCharacter Q,
        ∫ t in E, ‖F r χ t‖ ∂volume) ≤
      (Fintype.card R : ℝ) *
        (Fintype.card (BlueprintCharacter Q) : ℝ) * K := by
    calc
      _ ≤ ∑ r : R, ∑ χ : BlueprintCharacter Q, K := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro χ hχ
        exact hFbound r χ
      _ = (Fintype.card R : ℝ) *
            (Fintype.card (BlueprintCharacter Q) : ℝ) * K := by simp [mul_assoc]
  have hresult :
      (∫ t in E, integrand t ∂volume) ≤
        (d : ℝ) ^ (-(1 / 2 : ℝ)) * (Fintype.card R : ℝ) * K := by
   calc
    (∫ t in E, integrand t ∂volume) ≤
        ∫ t in E, majorant t ∂volume := hmono
    _ = ((d : ℝ) ^ (-(1 / 2 : ℝ)) / (Q.totient : ℝ)) *
          ∑ r : R, ∑ χ : BlueprintCharacter Q,
            ∫ t in E, ‖F r χ t‖ ∂volume := by
      dsimp [majorant]
      rw [integral_const_mul, hsumIntegral]
    _ ≤ ((d : ℝ) ^ (-(1 / 2 : ℝ)) / (Q.totient : ℝ)) *
          ((Fintype.card R : ℝ) *
            (Fintype.card (BlueprintCharacter Q) : ℝ) * K) :=
      mul_le_mul_of_nonneg_left hsumBound (div_nonneg hDnonneg hφ.le)
    _ = (d : ℝ) ^ (-(1 / 2 : ℝ)) * (Fintype.card R : ℝ) * K := by
      rw [hcardR]
      field_simp [ne_of_gt hφ]
  simpa [E, integrand, scale, charSum, exponent,
    Complex.cpow_def_of_ne_zero hdC] using hresult

#print axioms finiteAllocatedCharacterAverageIntegral_bound

end FractionalPrimes.Literature.DirichletMean

end
