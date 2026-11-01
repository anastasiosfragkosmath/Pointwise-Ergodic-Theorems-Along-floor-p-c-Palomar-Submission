module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuVectorRealization
public import FractionalPrimes.Literature.JSW.PositiveMaximalNuVectorBound
public import FractionalPrimes.Literature.JSW.PositiveDifferenceLowerBound

/-! Source geometric cancellation under abstract positive maximal inputs. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The upper-exponent geometric ν vector estimate with the positive
maximal constants kept as explicit inputs. This is the source-specific
finite-vector transfer needed when the rough-square bootstrap improves
the maximal exponent below its initial value `2`. -/
theorem finiteGeometricNuVector_upper_of_maximal
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hp : 2 < p) (hpq : (p / 2).HolderConjugate q)
    (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i))
    (Bσ Bψ : ℝ) (hBσ : 0 ≤ Bσ) (hBψ : 0 ≤ Bψ)
    (hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i,
          (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y) σ) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal q) volume)
    (hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i,
          (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y)
            (initialSquarePsiProbabilityMeasure σ)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal q) volume) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (localizedSquareNuLpConvolution hSupp p b (by linarith) (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      (Real.sqrt Bσ + Real.sqrt Bψ) *
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  classical
  let μσ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) σ
  let μψ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y)
      (initialSquarePsiProbabilityMeasure σ)
  have hμσ : ∀ i, IsProbabilityMeasure (μσ i) := by
    intro i
    dsimp [μσ]
    infer_instance
  have hμψ : ∀ i, IsProbabilityMeasure (μψ i) := by
    intro i
    letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
      initialSquarePsiProbabilityMeasure_isProbability hSupp
    dsimp [μψ]
    infer_instance
  obtain ⟨Uσ, Uψ, hUσ, hUψ, hUσraw, hUψraw, hUνeq⟩ :=
    finiteGeometricNuVector_difference_realization hSupp (by linarith : 1 < p)
      κ f hf hstrong
  have hdiff := finiteProbabilityDifference_lp_bound hp hpq μσ μψ
    hμσ hμψ f hf hstrong Uσ Uψ hUσ hUψ hUσraw hUψraw
    Bσ Bψ hBσ hBψ
    (by simpa [μσ] using hMaxσ)
    (by simpa [μψ] using hMaxψ)
  have hnorm :
      lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
        (localizedSquareNuLpConvolution hSupp p b (by linarith) (κ i)
          ((hf i).toLp (f i)) : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume =
      lpNorm (Uσ - Uψ) (ENNReal.ofReal p) volume := by
    unfold lpNorm
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hUνeq)
  rw [hnorm]
  exact hdiff

#print axioms finiteGeometricNuVector_upper_of_maximal

/-- The lower-exponent source geometric ν estimate from the positive
maximal bounds at the reflected dual exponent. This is the exact adjoint
half of the conditional `lj:positivity` transfer. -/
theorem finiteGeometricNuVector_lower_of_maximal
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p q s : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hp : 1 < p) (hpq : p.HolderConjugate q)
    (hq : 2 < q) (hqs : (q / 2).HolderConjugate s)
    (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i))
    (Bσ Bψ : ℝ) (hBσ : 0 ≤ Bσ) (hBψ : 0 ≤ Bψ)
    (hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i,
          (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y) σ) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal s) volume)
    (hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i,
          (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y)
            (initialSquarePsiProbabilityMeasure σ)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal s) volume) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (localizedSquareNuLpConvolution hSupp p b hp (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      (Real.sqrt Bσ + Real.sqrt Bψ) *
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
          (ENNReal.ofReal p) volume := by
  classical
  let F : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => f i x)
  have hF : MemLp F (ENNReal.ofReal p) volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact hf i
  let Uν : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i =>
      (localizedSquareNuLpConvolution hSupp p b hp (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x)
  have hUν : MemLp Uν (ENNReal.ofReal p) volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp _
  let μσ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) σ
  let μψ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y)
      (initialSquarePsiProbabilityMeasure σ)
  have hμσ : ∀ i, IsProbabilityMeasure (μσ i) := by
    intro i
    dsimp [μσ]
    infer_instance
  have hμψ : ∀ i, IsProbabilityMeasure (μψ i) := by
    intro i
    letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
      initialSquarePsiProbabilityMeasure_isProbability hSupp
    dsimp [μψ]
    infer_instance
  obtain ⟨Uσ, Uψ, hUσ, hUψ, hUσraw, hUψraw, hUνeq⟩ :=
    finiteGeometricNuVector_difference_realization hSupp hp κ f hf hstrong
  have hdiff := finiteProbabilityDifference_lowerLp_bound_of_maximal
    hpq hq hqs μσ μψ hμσ hμψ F Uσ Uψ Uν
    hF hUσ hUψ hUν hUνeq hUσraw hUψraw
    Bσ Bψ hBσ hBψ
    (by simpa [μσ, F] using hMaxσ)
    (by simpa [μψ, F] using hMaxψ)
  simpa [F, Uν] using hdiff

#print axioms finiteGeometricNuVector_lower_of_maximal

end

end FractionalPrimes.Literature.JSW

end
