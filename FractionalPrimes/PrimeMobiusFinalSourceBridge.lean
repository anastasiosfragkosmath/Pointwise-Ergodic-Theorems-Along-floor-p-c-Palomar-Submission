module
public import FractionalPrimes.PrimeMobiusConvergenceConditionalArithmetic
public import FractionalPrimes.Literature.Ergodic.PrimeVariationSystem
public import FractionalPrimes.ArithmeticCorrelationOperatorDecay
@[expose] public section

/-!
# Exact final-source cutoff and variation bridges

The prime-convergence adapter is indexed by `n + 2`, which enumerates exactly
the source cutoffs `N ≥ 2`. This file makes that reindexing explicit and also
composes the checked operator-decay-to-variation theorem with the same
conditional arithmetic adapter.
-/

namespace FractionalPrimes

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Natural prime cutoffs in the domain of the source normalization
`P_N = π(N)⁻¹ ∑_{p≤N} …`. -/
abbrev AdmissiblePrimeCutoff := {N : ℕ // 2 ≤ N}

/-- A convergence statement sampled at `n + 2` is exactly convergence over
all source cutoffs `N ≥ 2`. -/
theorem tendsto_admissiblePrimeCutoff_of_nat_add_two
    {Y : Type*} [TopologicalSpace Y]
    (F : AdmissiblePrimeCutoff → Y) {y : Y}
    (h : Tendsto (fun n : ℕ => F ⟨n + 2, by omega⟩) atTop (𝓝 y)) :
    Tendsto F atTop (𝓝 y) := by
  let index : AdmissiblePrimeCutoff → ℕ := fun N => N.1 - 2
  have hindex : Tendsto index atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards
      [eventually_ge_atTop (⟨b + 2, by omega⟩ : AdmissiblePrimeCutoff)]
      with N hN
    change b + 2 ≤ N.1 at hN
    dsimp [index]
    omega
  have hcomp : Tendsto (fun N : AdmissiblePrimeCutoff =>
      F ⟨index N + 2, by omega⟩) atTop (𝓝 y) := h.comp hindex
  have heq : (fun N : AdmissiblePrimeCutoff =>
      F ⟨index N + 2, by omega⟩) = F := by
    funext N
    apply congrArg F
    apply Subtype.ext
    dsimp [index]
    omega
  rw [heq] at hcomp
  exact hcomp

/-- Pointwise cutoff convergence in the exact source domain `N ≥ 2`, from the
`n + 2` form returned by the conditional prime theorem. -/
theorem primeAverage_ae_tendsto_admissibleCutoff_of_nat_add_two
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f g : X → ℂ)
    (h : ∀ᵐ x ∂S.μ, Tendsto
      (fun n : ℕ => primeAverage S c f (n + 2) (by omega) x)
      atTop (𝓝 (g x))) :
    ∀ᵐ x ∂S.μ, Tendsto
      (fun N : AdmissiblePrimeCutoff =>
        primeAverage S c f N.1 N.2 x)
      atTop (𝓝 (g x)) := by
  filter_upwards [h] with x hx
  exact tendsto_admissiblePrimeCutoff_of_nat_add_two
    (fun N => primeAverage S c f N.1 N.2 x) hx

/-- Lp cutoff convergence in the exact source domain `N ≥ 2`, from the
`n + 2` form returned by the conditional prime theorem. -/
theorem primeAverage_eLpNorm_tendsto_admissibleCutoff_of_nat_add_two
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f g : X → ℂ) (p : ℝ≥0∞)
    (h : Tendsto (fun n : ℕ =>
      eLpNorm (primeAverage S c f (n + 2) (by omega) - g) p S.μ)
      atTop (𝓝 0)) :
    Tendsto (fun N : AdmissiblePrimeCutoff =>
      eLpNorm (primeAverage S c f N.1 N.2 - g) p S.μ)
      atTop (𝓝 0) :=
  tendsto_admissiblePrimeCutoff_of_nat_add_two
    (fun N => eLpNorm (primeAverage S c f N.1 N.2 - g) p S.μ) h

/-- Exact source-domain form of the joint prime/Möbius convergence package.
The ordinary prime cutoff is now indexed by all and only `N ≥ 2`; the
von-Mangoldt, enumerated-prime, and Möbius conclusions are preserved. -/
theorem primeAndMobiusConvergenceAtCutoffsOf_OAISource_DP_PTW
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (vonMangoldtAverage S c.value f N - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : AdmissiblePrimeCutoff =>
          primeAverage S c.value f N.1 N.2 x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : AdmissiblePrimeCutoff =>
        eLpNorm (primeAverage S c.value f N.1 N.2 - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun J : Scale => enumeratedPrimeAverage S c.value f J x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun J : Scale =>
        eLpNorm (enumeratedPrimeAverage S c.value f J - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => mobiusAverage S c.value f N x)
        atTop (𝓝 0)) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
        atTop (𝓝 0) := by
  obtain ⟨g, hg, hΛAE, hΛLp, hprimeAE, hprimeLp, henumeratedAE,
      henumeratedLp, hμAE, hμLp⟩ :=
    primeAndMobiusConvergenceOf_OAISource_DP_PTW
      hp c hDP hPTW S f hf
  exact ⟨g, hg, hΛAE, hΛLp,
    primeAverage_ae_tendsto_admissibleCutoff_of_nat_add_two
      S c.value f g hprimeAE,
    primeAverage_eLpNorm_tendsto_admissibleCutoff_of_nat_add_two
      S c.value f g (ENNReal.ofReal p) hprimeLp,
    henumeratedAE, henumeratedLp, hμAE, hμLp⟩

/-- The headline prime-power variation theorem under precisely the source
DP and restricted PTW inputs: their arithmetic adapter supplies the prime
operator decay required by the checked variation/transference chain. -/
theorem primePowerVariationOf_OAISource_DP_PTW
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : FractionalExponent)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
        (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
        eLpNorm (rVariationFun r
          (fun N => vonMangoldtAverage S c.value f N))
            (ENNReal.ofReal p) S.μ ≤
          C * eLpNorm f (ENNReal.ofReal p) S.μ := by
  have hprimeDecay :
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D) := by
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    intro D hD
    obtain ⟨C, hC, hbound⟩ :=
      arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW
        (p := p) (c := c.value) hp c.one_lt c.nonIntegral hDP hPTW D hD
    refine ⟨C, ?_⟩
    intro N hN
    have hsum := hbound N hN
    exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) hsum
  exact primePowerVariation_of_operatorDecay hp hr c hprimeDecay

#print axioms tendsto_admissiblePrimeCutoff_of_nat_add_two
#print axioms primeAverage_ae_tendsto_admissibleCutoff_of_nat_add_two
#print axioms primeAverage_eLpNorm_tendsto_admissibleCutoff_of_nat_add_two
#print axioms primeAndMobiusConvergenceAtCutoffsOf_OAISource_DP_PTW
#print axioms primePowerVariationOf_OAISource_DP_PTW

end
end FractionalPrimes
