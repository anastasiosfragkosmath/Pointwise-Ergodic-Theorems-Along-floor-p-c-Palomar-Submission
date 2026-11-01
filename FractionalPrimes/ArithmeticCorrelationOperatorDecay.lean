module
public import FractionalPrimes.ArithmeticCorrelationPrefixAssembly
public import FractionalPrimes.Literature.Ergodic.ArithmeticDiscreteOperatorDecay
public import FractionalPrimes.Literature.Ergodic.ArithmeticSystemOperatorDecay
@[expose] public section

/-!
# Operator decay from whole-prefix arithmetic correlations

This adapter converts the source's half-open centered-frequency prefix bounds
to the exact Fourier hypotheses used by the discrete arithmetic operator
decay theorem.  The Dirichlet and restricted PTW tasks remain explicit.
-/

namespace FractionalPrimes

open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section

private theorem paperLambda_natCast_eq {n : ℕ} (hn : 1 ≤ n) :
    paperLambda (n : ℤ) = vonMangoldtWeight n := by
  have hnpos : 0 < (n : ℤ) := by exact_mod_cast hn
  rw [paperLambda, if_pos hnpos]
  simp

private theorem paperMu_natCast_eq {n : ℕ} (hn : 1 ≤ n) :
    paperMu (n : ℤ) = mobiusWeight n := by
  have hnpos : 0 < (n : ℤ) := by exact_mod_cast hn
  rw [paperMu, if_pos hnpos]
  simp

private theorem primeCorrelationPrefix_sum_eq {c ξ : ℝ} {N : ℕ} :
    (∑ n ∈ Finset.Ioc 0 N,
      ((paperLambda (n : ℤ) - 1 : ℝ) : ℂ) *
        unitFrequencyPhase (centeredFrequency ξ *
          (Int.floor ((n : ℝ) ^ c) : ℝ))) =
    ∑ n ∈ Finset.Icc 1 N,
      ((vonMangoldtWeight n : ℂ) - 1) *
        unitFrequencyPhase (ξ * (floorPower c n : ℝ)) := by
  rw [(Finset.Icc_succ_left_eq_Ioc (0 : ℕ) N).symm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlo : 1 ≤ n := by
    change Nat.succ 0 ≤ n
    exact (Finset.mem_Icc.mp hn).1
  have hweight := paperLambda_natCast_eq hnlo
  have hphase :
      unitFrequencyPhase (centeredFrequency ξ *
        (Int.floor ((n : ℝ) ^ c) : ℝ)) =
      unitFrequencyPhase (ξ * (floorPower c n : ℝ)) := by
    simpa only [floorPower, Real.rpow_eq_pow] using
      (unitFrequencyPhase_mul_int_centered ξ (floorPower c n)).symm
  rw [hweight, hphase]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

private theorem mobiusCorrelationPrefix_sum_eq {c ξ : ℝ} {N : ℕ} :
    (∑ n ∈ Finset.Ioc 0 N,
      (paperMu (n : ℤ) : ℂ) *
        unitFrequencyPhase (centeredFrequency ξ *
          (Int.floor ((n : ℝ) ^ c) : ℝ))) =
    ∑ n ∈ Finset.Icc 1 N,
      (mobiusWeight n : ℂ) *
        unitFrequencyPhase (ξ * (floorPower c n : ℝ)) := by
  rw [(Finset.Icc_succ_left_eq_Ioc (0 : ℕ) N).symm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlo : 1 ≤ n := by
    change Nat.succ 0 ≤ n
    exact (Finset.mem_Icc.mp hn).1
  have hweight := paperMu_natCast_eq hnlo
  have hphase :
      unitFrequencyPhase (centeredFrequency ξ *
        (Int.floor ((n : ℝ) ^ c) : ℝ)) =
      unitFrequencyPhase (ξ * (floorPower c n : ℝ)) := by
    simpa only [floorPower, Real.rpow_eq_pow] using
      (unitFrequencyPhase_mul_int_centered ξ (floorPower c n)).symm
  rw [hweight, hphase]

private theorem norm_natCast_inv_mul_eq_div {N : ℕ} (z : ℂ) :
    ‖(N : ℂ)⁻¹ * z‖ = ‖z‖ / (N : ℝ) := by
  rw [norm_mul, norm_inv]
  simp only [Complex.norm_natCast]
  rw [div_eq_mul_inv]
  ring

private theorem primeMultiplierFourierOfPrefix {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
          ((vonMangoldtWeight n : ℂ) - 1) *
            unitFrequencyPhase (ξ * (floorPower c n : ℝ))‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A : ℝ) := by
  intro A hA
  obtain ⟨C, hC, hprefix⟩ :=
    primeMultiplierComparisonOf_OAISource_DP_PTW hc hcNon hDP hPTW A hA
  refine ⟨C, hC.le, ?_⟩
  intro N hN ξ
  rw [norm_natCast_inv_mul_eq_div,
    ← primeCorrelationPrefix_sum_eq (c := c) (ξ := ξ)]
  exact hprefix N.val hN ξ

private theorem mobiusMultiplierFourierOfPrefix {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
          (mobiusWeight n : ℂ) *
            unitFrequencyPhase (ξ * (floorPower c n : ℝ))‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A : ℝ) := by
  intro A hA
  obtain ⟨C, hC, hprefix⟩ :=
    mobiusMultiplierDecayOf_OAISource_DP_PTW hc hcNon hDP hPTW A hA
  refine ⟨C, hC.le, ?_⟩
  intro N hN ξ
  rw [norm_natCast_inv_mul_eq_div,
    ← mobiusCorrelationPrefix_sum_eq (c := c) (ξ := ξ)]
  exact hprefix N.val hN ξ

/-- Discrete arithmetic operator decay from the source whole-prefix
correlation estimate.  Its only analytic inputs are the stated short-interval
Dirichlet and restricted polynomial twisted tasks. -/
theorem arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW
    {p c : ℝ} (hp : 1 < p) (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∀ D : ℝ, 0 < D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
            (primeComparisonIntegerKernel c N)‖ +
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
            (mobiusIntegerKernel c N)‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-D : ℝ) := by
  exact arithmeticComparisonDiscreteOperatorDecay_of_fourier hp c
    (primeMultiplierFourierOfPrefix hc hcNon hDP hPTW)
    (mobiusMultiplierFourierOfPrefix hc hcNon hDP hPTW)

/-- System-level norm transfer of the conditional discrete operator decay. -/
theorem arithmeticComparisonSystemNormDecayOf_OAISource_DP_PTW
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    {p c : ℝ} (hp : 1 < p) (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ f : X → ℂ,
        MemLp f (ENNReal.ofReal p) S.μ →
        eLpNorm (vonMangoldtAverage S c f N - unweightedAverage S c f N)
            (ENNReal.ofReal p) S.μ +
          eLpNorm (mobiusAverage S c f N) (ENNReal.ofReal p) S.μ ≤
          ENNReal.ofReal (C * (Real.log (N.val : ℝ)) ^ (-D : ℝ)) *
            eLpNorm f (ENNReal.ofReal p) S.μ := by
  obtain ⟨C, hC, hdecay⟩ :=
    arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW
      hp hc hcNon hDP hPTW D hD
  refine ⟨C, hC, ?_⟩
  intro N hN f hf
  exact arithmeticComparisonSystemNorm_le_of_discrete S hp c N
    (C * (Real.log (N.val : ℝ)) ^ (-D : ℝ)) (hdecay N hN) f hf

#print axioms arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW
#print axioms arithmeticComparisonSystemNormDecayOf_OAISource_DP_PTW

end
end FractionalPrimes
