module

public import FractionalPrimes.Literature.JSW.SmoothDyadicAlmostOrthogonal
public import FractionalPrimes.Literature.JSW.FiniteVectorLpAssembly

/-! Exponent-stable finite error operators for the source weak-CZ application. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicErrorOperatorAt
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (τ : ℝ) (m : ℤ) :
    Lp ℂ P (volume : Measure ℝ) →L[ℝ] Lp ℂ P (volume : Measure ℝ) := by
  subst P
  exact smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num) τ m

def smoothDyadicFiniteOperatorAt
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (a : ℝ) (ha : 0 < a) (K : Finset ℤ) :
    Lp ℂ P (volume : Measure ℝ) →L[ℝ]
      Lp (EuclideanSpace ℂ {k : ℤ // k ∈ K}) P (volume : Measure ℝ) := by
  classical
  exact (finiteVectorLpAssembly P).comp (ContinuousLinearMap.pi
    (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorOperatorAt hP hSupp
      (jswTau a ha k.1) (jswM a ha k.1)))

theorem smoothDyadicFiniteOperatorAt_norm_le
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ P (volume : Measure ℝ)) :
    ‖smoothDyadicFiniteOperatorAt hP hSupp a ha K F‖ ≤ smoothDyadicSquareConstant a ha*‖F‖ := by
  classical
  subst P
  let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
    (jswTau a ha k) (jswM a ha k) F
  have hAE : (smoothDyadicFiniteOperatorAt rfl hSupp a ha K F :
      ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ K} => (v k.1 : ℝ → ℂ) x)) :=
    finiteVectorLpAssembly_ae_eq _ _
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae hAE (p := ENNReal.ofReal (2 : ℝ)))
  rw [← Lp.norm_def] at hn
  change ‖smoothDyadicFiniteOperatorAt rfl hSupp a ha K F‖ = lpNorm _ _ _ at hn
  exact hn.le.trans (smoothDyadic_finite_vector_norm hSupp ha K F)

theorem smoothDyadicFiniteOperatorAt_opNorm_le
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {a : ℝ} (ha : 0 < a) (K : Finset ℤ) :
    ‖smoothDyadicFiniteOperatorAt hP hSupp a ha K‖ ≤ smoothDyadicSquareConstant a ha := by
  exact (smoothDyadicFiniteOperatorAt hP hSupp a ha K).opNorm_le_bound
    (smoothDyadicSquareConstant_nonneg ha)
    (fun F => smoothDyadicFiniteOperatorAt_norm_le hP hSupp ha K F)

theorem smoothDyadicFiniteOperatorAt_ae_eq
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ P (volume : Measure ℝ)) (g : ℝ → ℂ)
    (hg : MemLp g P volume) (hF : (F : ℝ → ℂ) =ᵐ[volume] g) :
    (smoothDyadicFiniteOperatorAt hP hSupp a ha K F : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ K} => smoothDyadicRawError σ a ha k.1 g x)) := by
  classical
  have hrep (k : {k : ℤ // k ∈ K}) :
      (smoothDyadicErrorOperatorAt hP hSupp (jswTau a ha k.1) (jswM a ha k.1) F : ℝ → ℂ) =ᵐ[volume]
        smoothDyadicRawError σ a ha k.1 g := by
    subst P
    exact smoothDyadicErrorLpOperator_ae_eq_of_memLp hSupp (p := 2) (by norm_num) _ _ F g hg hF
  have hvec := finiteVectorLpAssembly_ae_eq P
    (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorOperatorAt hP hSupp
      (jswTau a ha k.1) (jswM a ha k.1) F)
  filter_upwards [hvec, ae_all_iff.mpr hrep] with x hx hi
  change (finiteVectorLpAssembly P
    (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorOperatorAt hP hSupp
      (jswTau a ha k.1) (jswM a ha k.1) F) : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) x = _
  rw [hx]
  congr 1
  funext k
  exact hi k

#print axioms smoothDyadicFiniteOperatorAt_opNorm_le
#print axioms smoothDyadicFiniteOperatorAt_ae_eq
end
end FractionalPrimes.Literature.JSW
end
