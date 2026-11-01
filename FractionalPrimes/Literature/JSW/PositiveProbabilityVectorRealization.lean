module

public import FractionalPrimes.Literature.JSW.PositiveMaximalNuVectorBound
public import FractionalPrimes.Literature.JSW.PositiveRepresentativeTransfer
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Positive probability convolution of an arbitrary finite-vector `Lᵖ` input

The input vector may be only almost everywhere strongly measurable. A
measurable representative is used to define the `Lp` outputs, then the
checked translated-integral congruence returns to the raw coordinates.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A finite family of probability convolutions of a vector `Lᵖ`
function has a vector `Lᵖ` output with the exact raw coordinate
identity almost everywhere. -/
theorem finiteProbabilityConvolution_vector_realization
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (F : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume) :
    ∃ U : ℝ → EuclideanSpace ℂ ι,
      MemLp U (ENNReal.ofReal p) volume ∧
      ∀ i, (fun x => U x i) =ᵐ[volume]
        (fun x => jswConvolution (μ i) (fun y => F y i) x) := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hP1 : (1 : ℝ≥0∞) ≤ P := ENNReal.one_le_ofReal.mpr hp.le
  letI : Fact (1 ≤ P) := ⟨hP1⟩
  let F' : ℝ → EuclideanSpace ℂ ι := hF.aestronglyMeasurable.mk F
  have hFRep : F =ᵐ[volume] F' := hF.aestronglyMeasurable.ae_eq_mk
  have hF'Strong : StronglyMeasurable F' :=
    hF.aestronglyMeasurable.stronglyMeasurable_mk
  have hF'Mem : MemLp F' P volume :=
    hF.congr_norm hF'Strong.aestronglyMeasurable (by
      filter_upwards [hFRep] with x hx
      simp [hx])
  let f : ι → ℝ → ℂ := fun i x => F' x i
  have hf (i : ι) : MemLp (f i) P volume := hF'Mem.eval_piLp i
  have hstrong (i : ι) : StronglyMeasurable (f i) := by
    fun_prop
  let T : ι → Lp ℂ P volume := fun i => by
    letI : IsProbabilityMeasure (μ i) := hμ i
    have hvar : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μ i)).variation := by
      rw [initialSquareSigmaComplexMeasure_variation_eq]
      infer_instance
    letI : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μ i)).variation := hvar
    exact lpComplexMeasureConvolution P
      (initialSquareSigmaComplexMeasure (μ i)) ((hf i).toLp (f i))
  let U : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => (T i) x)
  have hU : MemLp U P volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (T i)
  have hraw (i : ι) : (fun x => U x i) =ᵐ[volume]
      (fun x => jswConvolution (μ i) (f i) x) := by
    letI : IsProbabilityMeasure (μ i) := hμ i
    change (fun x => (T i) x) =ᵐ[volume] _
    dsimp [T]
    exact lpComplexSigmaConvolution_ae_eq_jswConvolution hp (μ i)
      ((hf i).toLp (f i)) (f i) (hstrong i).measurable (hf i)
      (MemLp.coeFn_toLp (hf i))
  refine ⟨U, hU, ?_⟩
  intro i
  have hcoord : (fun x => F' x i) =ᵐ[volume] fun x => F x i := by
    filter_upwards [hFRep] with x hx
    rw [← hx]
  have htransfer := integral_sub_translation_congr_ae (μ i)
    (f i) (fun x => F x i) hcoord
  exact (hraw i).trans htransfer

#print axioms finiteProbabilityConvolution_vector_realization

/-- The positive finite-family upper-exponent estimate, packaged for an
arbitrary vector `MemLp` input and with raw convolution coordinates. -/
theorem finiteProbabilityConvolution_vector_lp_bound
    {ι : Type*} [Fintype ι] {p q : ℝ} (hp : 2 < p)
    (hrq : (p / 2).HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (F : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (B : ℝ) (hB : 0 ≤ B)
    (hMax : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume) :
    ∃ U : ℝ → EuclideanSpace ℂ ι,
      MemLp U (ENNReal.ofReal p) volume ∧
      (∀ i, (fun x => U x i) =ᵐ[volume]
        (fun x => jswConvolution (μ i) (fun y => F y i) x)) ∧
      lpNorm U (ENNReal.ofReal p) volume ≤
        Real.sqrt B * lpNorm F (ENNReal.ofReal p) volume := by
  classical
  let F' : ℝ → EuclideanSpace ℂ ι := hF.aestronglyMeasurable.mk F
  have hrep : F =ᵐ[volume] F' := hF.aestronglyMeasurable.ae_eq_mk
  have hF'Strong : StronglyMeasurable F' :=
    hF.aestronglyMeasurable.stronglyMeasurable_mk
  have hF'Mem : MemLp F' (ENNReal.ofReal p) volume :=
    hF.congr_norm hF'Strong.aestronglyMeasurable (by
      filter_upwards [hrep] with x hx
      simp [hx])
  let f : ι → ℝ → ℂ := fun i x => F' x i
  have hf (i : ι) : MemLp (f i) (ENNReal.ofReal p) volume :=
    hF'Mem.eval_piLp i
  have hstrong (i : ι) : StronglyMeasurable (f i) := by
    fun_prop
  obtain ⟨U, hU, hUraw⟩ :=
    finiteProbabilityConvolution_vector_realization (by linarith : 1 < p)
      μ hμ F' hF'Mem
  have hbound := finiteProbabilityConvolution_lp_bound hp hrq μ hμ
    f hf hstrong U hU hUraw B hB hMax
  have hnorm : lpNorm F' (ENNReal.ofReal p) volume =
      lpNorm F (ENNReal.ofReal p) volume := by
    unfold lpNorm
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hrep.symm)
  refine ⟨U, hU, ?_, ?_⟩
  · intro i
    have hcoord : (fun x => F' x i) =ᵐ[volume] fun x => F x i := by
      filter_upwards [hrep] with x hx
      rw [← hx]
    exact (hUraw i).trans
      (integral_sub_translation_congr_ae (μ i) (f i)
        (fun x => F x i) hcoord)
  · simpa [f, hnorm] using hbound

#print axioms finiteProbabilityConvolution_vector_lp_bound

end

end FractionalPrimes.Literature.JSW

end
