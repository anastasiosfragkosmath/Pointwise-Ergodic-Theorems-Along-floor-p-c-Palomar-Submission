module

public import FractionalPrimes.Literature.JSW.RoughSquareFiniteReconstruction

/-! Continuous finite assembly of scalar Lp outputs for the square-bound
density extension. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def finiteVectorScalarInjection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : ℂ →L[ℝ] EuclideanSpace ℂ ι :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (PiLp.single 2 i (1 : ℂ))).restrictScalars ℝ

def finiteVectorLpAssembly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (ι → Lp ℂ p (volume : Measure ℝ)) →L[ℝ]
      Lp (EuclideanSpace ℂ ι) p (volume : Measure ℝ) :=
  ∑ i : ι, ((finiteVectorScalarInjection i).compLpL p volume).comp
    (ContinuousLinearMap.proj i)

theorem finiteVectorLpAssembly_ae_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : ι → Lp ℂ p (volume : Measure ℝ)) :
    (finiteVectorLpAssembly p g : ℝ → EuclideanSpace ℂ ι) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun i => (g i : ℝ → ℂ) x)) := by
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : ι => (finiteVectorScalarInjection i).compLpL p volume (g i))
  have hcoord : ∀ i : ι, ∀ᵐ x ∂volume,
      ((finiteVectorScalarInjection i).compLpL p volume (g i) : ℝ → EuclideanSpace ℂ ι) x =
        finiteVectorScalarInjection i ((g i : ℝ → ℂ) x) :=
    fun i => (finiteVectorScalarInjection i).coeFn_compLpL (g i)
  have hpoint : ∀ᵐ x ∂volume,
      (∑ i : ι, (finiteVectorScalarInjection i).compLpL p volume (g i)) x =
        WithLp.toLp 2 (fun i => (g i : ℝ → ℂ) x) := by
    filter_upwards [hsum, ae_all_iff.mpr hcoord] with x hx hi
    rw [hx]
    simp only [Finset.sum_apply]
    simp_rw [hi]
    ext k
    simp [finiteVectorScalarInjection, Pi.single_apply, eq_comm]
  simpa only [finiteVectorLpAssembly, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Filter.EventuallyEq] using hpoint

def roughSquareNuLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (b : ℝ) (k : ℤ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let μ := initialSquareNuComplexMeasure σ
  letI : IsFiniteMeasure μ.variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  let μk := initialSquareDilateComplexMeasure μ (b^k)
  letI : IsFiniteMeasure μk.variation := by
    change IsFiniteMeasure (μ.map (fun x : ℝ => b^k*x)).variation
    infer_instance
  exact lpComplexMeasureConvolutionCLM (ENNReal.ofReal p) ENNReal.ofReal_ne_top μk

def roughSquareFiniteLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (b : ℝ) (F : Finset ℤ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp (EuclideanSpace ℂ {k : ℤ // k ∈ F}) (ENNReal.ofReal p) (volume : Measure ℝ) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  exact (finiteVectorLpAssembly (ENNReal.ofReal p)).comp
    (ContinuousLinearMap.pi (fun k : {k : ℤ // k ∈ F} => roughSquareNuLpOperator hSupp hp b k.1))

theorem roughSquareFiniteLpOperator_ae_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (b : ℝ) (F : Finset ℤ)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (roughSquareFiniteLpOperator hSupp hp b F f : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F})
      =ᵐ[volume] (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1 f : ℝ → ℂ) x)) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  change (finiteVectorLpAssembly (ENNReal.ofReal p)
    (fun k : {k : ℤ // k ∈ F} => localizedSquareNuLpConvolution hSupp p b hp k.1 f) :
      ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F}) =ᵐ[volume] _
  exact finiteVectorLpAssembly_ae_eq _ _

#print axioms roughSquareFiniteLpOperator_ae_eq
#print axioms finiteVectorLpAssembly_ae_eq
end
end FractionalPrimes.Literature.JSW
end
