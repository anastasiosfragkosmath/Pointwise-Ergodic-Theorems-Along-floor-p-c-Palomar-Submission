module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuLowerBound
public import FractionalPrimes.Literature.JSW.PositiveMaximalVectorAssembly
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-vector L² norm identity for the positivity endpoint

This is the Hilbert endpoint bookkeeping needed by the `p=2` clause
of `lj:positivity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The squared `L²` norm of a Hilbert-valued representative is the
integral of its squared pointwise norm. -/
theorem lpNorm_two_sq_eq_integral_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (f : ℝ → E) (hf : MemLp f 2 volume) :
    lpNorm f 2 volume ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂volume := by
  let F : Lp E 2 (volume : Measure ℝ) := hf.toLp f
  have hF : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂volume := by
    calc
      ‖F‖ ^ 2 = RCLike.re (inner ℂ F F) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) F).symm
      _ = RCLike.re (∫ x, inner ℂ (F x) (F x) ∂volume) := by
        rw [L2.inner_def]
      _ = ∫ x, RCLike.re (inner ℂ (F x) (F x)) ∂volume :=
        (integral_re (L2.integrable_inner F F)).symm
      _ = ∫ x, ‖F x‖ ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (F x)
  have hrep : (F : ℝ → E) =ᵐ[volume] f := MemLp.coeFn_toLp hf
  calc
    lpNorm f 2 volume ^ 2 = ‖F‖ ^ 2 := by
      rw [Lp.norm_toLp]
      rfl
    _ = ∫ x, ‖F x‖ ^ 2 ∂volume := hF
    _ = ∫ x, ‖f x‖ ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx]

#print axioms lpNorm_two_sq_eq_integral_norm_sq

/-- The finite Euclidean-vector `L²` norm is the sum of the coordinate
`L²` energies, with no hidden cardinality factor. -/
theorem lpNorm_finiteEuclidean_two_sq_eq_sum
    {ι : Type*} [Fintype ι]
    (F : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F 2 volume) :
    lpNorm F 2 volume ^ 2 =
      ∑ i : ι, lpNorm (fun x => F x i) 2 volume ^ 2 := by
  have hcoord (i : ι) : MemLp (fun x => F x i) 2 volume :=
    hF.eval_piLp i
  rw [lpNorm_two_sq_eq_integral_norm_sq F hF]
  simp_rw [lpNorm_two_sq_eq_integral_norm_sq _ (hcoord _)]
  have hint (i : ι) : Integrable (fun x => ‖F x i‖ ^ 2) volume :=
    (hcoord i).integrable_norm_pow (by norm_num)
  calc
    (∫ x, ‖F x‖ ^ 2 ∂volume) =
        ∫ x, ∑ i : ι, ‖F x i‖ ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [EuclideanSpace.norm_sq_eq]
    _ = ∑ i : ι, ∫ x, ‖F x i‖ ^ 2 ∂volume :=
      integral_finset_sum Finset.univ (fun i _ => hint i)

#print axioms lpNorm_finiteEuclidean_two_sq_eq_sum

/-- Coordinatewise `L²` contractions combine to a finite-vector
`L²(ℓ²)` contraction with the same constant. -/
theorem finiteEuclidean_two_norm_le_of_coord
    {ι : Type*} [Fintype ι]
    (F U : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F 2 volume) (hU : MemLp U 2 volume)
    (hcoord : ∀ i, lpNorm (fun x => U x i) 2 volume ≤
      lpNorm (fun x => F x i) 2 volume) :
    lpNorm U 2 volume ≤ lpNorm F 2 volume := by
  have hsq : lpNorm U 2 volume ^ 2 ≤ lpNorm F 2 volume ^ 2 := by
    rw [lpNorm_finiteEuclidean_two_sq_eq_sum U hU,
      lpNorm_finiteEuclidean_two_sq_eq_sum F hF]
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ lpNorm_nonneg (hcoord i) 2
  exact (sq_le_sq₀ lpNorm_nonneg lpNorm_nonneg).1 hsq

#print axioms finiteEuclidean_two_norm_le_of_coord

/-- The `L²` convolution by the complexification of one probability
measure, with variation finiteness supplied inside the definition. -/
noncomputable def probabilityConvolutionLpTwo
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) := by
  letI : IsProbabilityMeasure μ := hμ
  have hvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μ).variation := hvar
  exact lpComplexMeasureConvolution 2
    (initialSquareSigmaComplexMeasure μ) F

/-- A finite family of probability convolutions is contractive on
`L²(ℓ²)` with the exact complex-measure `Lp` coordinate outputs. -/
theorem finiteProbabilityConvolution_vector_two_bound
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) 2 volume) :
    ∃ U : ℝ → EuclideanSpace ℂ ι,
      MemLp U 2 volume ∧
      (∀ i, (fun x => U x i) =ᵐ[volume]
        (fun x => (probabilityConvolutionLpTwo (μ i) (hμ i)
          ((hf i).toLp (f i)) : ℝ → ℂ) x)) ∧
      lpNorm U 2 volume ≤
        lpNorm (fun x => WithLp.toLp 2 (fun i => f i x)) 2 volume := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let F : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => f i x)
  have hF : MemLp F 2 volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact hf i
  let T : ι → Lp ℂ 2 volume := fun i =>
    probabilityConvolutionLpTwo (μ i) (hμ i) ((hf i).toLp (f i))
  let U : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => (T i) x)
  have hU : MemLp U 2 volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (T i)
  have hraw (i : ι) : (fun x => U x i) =ᵐ[volume]
      (fun x => (probabilityConvolutionLpTwo (μ i) (hμ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hcoord (i : ι) : lpNorm (fun x => U x i) 2 volume ≤
      lpNorm (fun x => F x i) 2 volume := by
    letI : IsProbabilityMeasure (μ i) := hμ i
    have hvar : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μ i)).variation := by
      rw [initialSquareSigmaComplexMeasure_variation_eq]
      infer_instance
    letI : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μ i)).variation := hvar
    have hmass : (μ i).real Set.univ = 1 := by
      simp [Measure.real, measure_univ]
    have hT : ‖T i‖ ≤ ‖(hf i).toLp (f i)‖ := by
      have hYoung := norm_lpComplexMeasureConvolution_le
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        (initialSquareSigmaComplexMeasure (μ i))
        ((hf i).toLp (f i))
      rw [initialSquareSigmaComplexMeasure_variation_eq, hmass,
        one_mul] at hYoung
      simpa [T, probabilityConvolutionLpTwo] using hYoung
    have hleft : lpNorm (fun x => U x i) 2 volume = ‖T i‖ := by
      change lpNorm (T i : ℝ → ℂ) 2 volume = ‖T i‖
      exact (Lp.norm_def (T i)).symm
    have hright : lpNorm (fun x => F x i) 2 volume =
        ‖(hf i).toLp (f i)‖ := by
      change lpNorm (f i) 2 volume = ‖(hf i).toLp (f i)‖
      rw [Lp.norm_toLp]
      rfl
    rw [hleft, hright]
    exact hT
  exact ⟨U, hU, hraw, finiteEuclidean_two_norm_le_of_coord F U hF hU hcoord⟩

#print axioms finiteProbabilityConvolution_vector_two_bound

end

end FractionalPrimes.Literature.JSW

end
