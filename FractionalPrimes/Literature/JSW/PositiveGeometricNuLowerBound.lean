module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuVectorRealization
public import FractionalPrimes.Literature.JSW.PositiveDifferenceLowerBound

/-!
# Lower-exponent geometric cancellation vector bound

The source σ and smooth ψ maximal constants are inserted into the
checked abstract signed-vector duality theorem without changing the
geometric cancellation measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Source-specific lower-exponent ν vector bound from the σ and ψ
geometric maximal estimates at the dual maximal exponent. -/
theorem finiteGeometricNuVector_lowerLp_bound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {β D b p q s : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 1 < p)
    (hpq : p.HolderConjugate q)
    (hqs : (q / 2).HolderConjugate s) (hs : 2 < s)
    (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i)) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (localizedSquareNuLpConvolution hSupp p b hp (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      (Real.sqrt (weakTypeInterpolationStrongTwoInfinityConstant s
          (initialSquareSigmaPositiveMaximalB2 β D b)) +
        Real.sqrt ((4 * lpNorm φ ∞ volume) *
          ((6 * s * 2 ^ (s - 1) / (s - 1)) ^ (1 / s)))) *
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  classical
  have hq : 2 < q := by linarith [hqs.lt]
  let F : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => f i x)
  have hF : MemLp F (ENNReal.ofReal p) volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact hf i
  obtain ⟨Uσ, Uψ, hUσ, hUψ, hUσraw, hUψraw, hUνeq⟩ :=
    finiteGeometricNuVector_difference_realization hSupp hp κ f hf hstrong
  let Uν : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i =>
      (localizedSquareNuLpConvolution hSupp p b hp (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x)
  have hUν : MemLp Uν (ENNReal.ofReal p) volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp _
  let ψbase : Measure ℝ := initialSquarePsiProbabilityMeasure σ
  have hψprob : IsProbabilityMeasure ψbase :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  let μσ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) σ
  let μψ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) ψbase
  have hμσ (i : ι) : IsProbabilityMeasure (μσ i) := by
    dsimp [μσ]
    infer_instance
  have hμψ (i : ι) : IsProbabilityMeasure (μψ i) := by
    letI : IsProbabilityMeasure ψbase := hψprob
    dsimp [μψ]
    infer_instance
  let Bσ : ℝ := weakTypeInterpolationStrongTwoInfinityConstant s
    (initialSquareSigmaPositiveMaximalB2 β D b)
  let Bψ : ℝ := (4 * lpNorm φ ∞ volume) *
    ((6 * s * 2 ^ (s - 1) / (s - 1)) ^ (1 / s))
  have hBσ : 0 ≤ Bσ := by
    dsimp [Bσ, weakTypeInterpolationStrongTwoInfinityConstant]
    have hbase : 0 ≤ s / (s - 2) := by
      apply div_nonneg
      · linarith
      · linarith
    have hA : 0 ≤ initialSquareSigmaPositiveMaximalB2 β D b :=
      initialSquareSigmaPositiveMaximalB2_nonneg hb hβ
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase _))
      (Real.rpow_nonneg hA _)
  have hBψ : 0 ≤ Bψ := by
    dsimp [Bψ]
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) lpNorm_nonneg
    · apply Real.rpow_nonneg
      apply div_nonneg
      · positivity
      · linarith
  have hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μσ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal s) volume := by
    intro g hg
    simpa [μσ, Bσ] using
      (finiteGeometricSigmaPositiveMaximalBound hSupp hdecay hb hβ hs κ g hg)
  have hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μψ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal s) volume := by
    intro g hg
    simpa [μψ, ψbase, Bψ] using
      (finiteGeometricPsiPositiveMaximalBound hSupp hb (by linarith : 1 < s)
        κ g hg)
  have hbound := finiteProbabilityDifference_lowerLp_bound_of_maximal
    hpq hq hqs μσ μψ hμσ hμψ F Uσ Uψ Uν
    hF hUσ hUψ hUν hUνeq hUσraw hUψraw
    Bσ Bψ hBσ hBψ hMaxσ hMaxψ
  simpa [F, Uν, Bσ, Bψ] using hbound

#print axioms finiteGeometricNuVector_lowerLp_bound

end

end FractionalPrimes.Literature.JSW

end
