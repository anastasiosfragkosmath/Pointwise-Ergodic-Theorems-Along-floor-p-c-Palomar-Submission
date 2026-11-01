module

public import FractionalPrimes.Literature.JSW.PositiveVectorL2

/-!
# The geometric cancellation vector at the Hilbert endpoint

The exact σ-minus-ψ complex-measure identity supplies the source ν
operator at exponent two, where each positive family is contractive.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The source geometric ν convolution as an `Lp ℂ 2` output. -/
noncomputable def geometricNuLpConvolutionTwo
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (b : ℝ) (k : ℤ) (F : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hbase : IsFiniteMeasure
      (initialSquareNuComplexMeasure σ).variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation := hbase
  have hscale : IsFiniteMeasure
      (initialSquareDilateComplexMeasure
        (initialSquareNuComplexMeasure σ) (b ^ k)).variation := by
    dsimp [initialSquareDilateComplexMeasure]
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure
        (initialSquareNuComplexMeasure σ) (b ^ k)).variation := hscale
  exact lpComplexMeasureConvolution 2
    (initialSquareDilateComplexMeasure
      (initialSquareNuComplexMeasure σ) (b ^ k)) F

/-- The exact Hilbert-endpoint source ν operator is the difference of
the two positive probability convolution operators. -/
theorem geometricNuLpConvolutionTwo_eq_positive_sub
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (b : ℝ) (k : ℤ) (F : Lp ℂ 2 (volume : Measure ℝ)) :
    geometricNuLpConvolutionTwo hSupp b k F =
      probabilityConvolutionLpTwo
          (Measure.map (fun y : ℝ => b ^ k * y) σ)
          (by infer_instance) F -
        probabilityConvolutionLpTwo
          (Measure.map (fun y : ℝ => b ^ k * y)
            (initialSquarePsiProbabilityMeasure σ))
          (by
            letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
              initialSquarePsiProbabilityMeasure_isProbability hSupp
            infer_instance) F := by
  let ψbase : Measure ℝ := initialSquarePsiProbabilityMeasure σ
  have hψprob : IsProbabilityMeasure ψbase :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  letI : IsProbabilityMeasure ψbase := hψprob
  let μσ : Measure ℝ := Measure.map (fun y : ℝ => b ^ k * y) σ
  let μψ : Measure ℝ := Measure.map (fun y : ℝ => b ^ k * y) ψbase
  haveI : IsFiniteMeasure μσ := by dsimp [μσ]; infer_instance
  haveI : IsFiniteMeasure μψ := by dsimp [μψ]; infer_instance
  have hσvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  have hψvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μψ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ).variation := hσvar
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μψ).variation := hψvar
  let ν : ComplexMeasure ℝ :=
    initialSquareDilateComplexMeasure
      (initialSquareNuComplexMeasure σ) (b ^ k)
  have hbase : IsFiniteMeasure
      (initialSquareNuComplexMeasure σ).variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation := hbase
  have hνvar : IsFiniteMeasure ν.variation := by
    dsimp [ν, initialSquareDilateComplexMeasure]
    infer_instance
  letI : IsFiniteMeasure ν.variation := hνvar
  have hmeasure : ν = initialSquareSigmaComplexMeasure μσ -
      initialSquareSigmaComplexMeasure μψ := by
    simpa [ν, μσ, μψ, ψbase] using
      initialSquareNuDilateComplexMeasure_eq_sigma_sub_psi hSupp
        (b ^ k) (inferInstance : IsFiniteMeasure ψbase)
        (inferInstance : IsFiniteMeasure μσ)
        (inferInstance : IsFiniteMeasure μψ)
  have hsubvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ -
        initialSquareSigmaComplexMeasure μψ).variation := by
    rw [← hmeasure]
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ -
        initialSquareSigmaComplexMeasure μψ).variation := hsubvar
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  change lpComplexMeasureConvolution 2 ν F =
    lpComplexMeasureConvolution 2 (initialSquareSigmaComplexMeasure μσ) F -
      lpComplexMeasureConvolution 2 (initialSquareSigmaComplexMeasure μψ) F
  rw [hmeasure]
  exact lpComplexMeasureConvolution_sub (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (initialSquareSigmaComplexMeasure μσ)
    (initialSquareSigmaComplexMeasure μψ) F

#print axioms geometricNuLpConvolutionTwo_eq_positive_sub

/-- The genuine geometric ν vector has the blueprint's `p=2`
bound by two probability contractions. -/
theorem finiteGeometricNuVector_two_bound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (b : ℝ) (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) 2 volume) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (geometricNuLpConvolutionTwo hSupp b (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x)) 2 volume ≤
      2 * lpNorm (fun x : ℝ => WithLp.toLp 2
        (fun i : ι => f i x)) 2 volume := by
  classical
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
  obtain ⟨Uσ, hUσ, hUσcoord, hUσbound⟩ :=
    finiteProbabilityConvolution_vector_two_bound μσ hμσ f hf
  obtain ⟨Uψ, hUψ, hUψcoord, hUψbound⟩ :=
    finiteProbabilityConvolution_vector_two_bound μψ hμψ f hf
  let Uν : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i =>
      (geometricNuLpConvolutionTwo hSupp b (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x)
  have hUν : MemLp Uν 2 volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp _
  have hcoord (i : ι) :
      (fun x => Uν x i) =ᵐ[volume]
        (fun x => Uσ x i - Uψ x i) := by
    have hνeq := geometricNuLpConvolutionTwo_eq_positive_sub
      hSupp b (κ i) ((hf i).toLp (f i))
    have hsub := Lp.coeFn_sub
      (probabilityConvolutionLpTwo (μσ i) (hμσ i) ((hf i).toLp (f i)))
      (probabilityConvolutionLpTwo (μψ i) (hμψ i) ((hf i).toLp (f i)))
    filter_upwards [hUσcoord i, hUψcoord i, hsub] with x hxσ hxψ hxsub
    change (geometricNuLpConvolutionTwo hSupp b (κ i)
      ((hf i).toLp (f i)) : ℝ → ℂ) x = Uσ x i - Uψ x i
    rw [hνeq, hxsub]
    change ((probabilityConvolutionLpTwo (μσ i) (hμσ i)
      ((hf i).toLp (f i)) : ℝ → ℂ) x -
      (probabilityConvolutionLpTwo (μψ i) (hμψ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x) = _
    rw [← hxσ, ← hxψ]
  have hUνeq : Uν =ᵐ[volume] fun x => Uσ x - Uψ x := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    ext i
    exact hx i
  have hnorm : lpNorm Uν 2 volume =
      lpNorm (fun x => Uσ x - Uψ x) 2 volume := by
    unfold lpNorm
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hUνeq)
  have hbound : lpNorm Uν 2 volume ≤
      lpNorm (fun x => WithLp.toLp 2 (fun i : ι => f i x)) 2 volume +
        lpNorm (fun x => WithLp.toLp 2 (fun i : ι => f i x)) 2 volume := by
    rw [hnorm]
    calc
      lpNorm (fun x => Uσ x - Uψ x) 2 volume ≤
          lpNorm Uσ 2 volume + lpNorm Uψ 2 volume :=
        lpNorm_sub_le hUσ (by norm_num)
      _ ≤ _ := add_le_add hUσbound hUψbound
  simpa [Uν, two_mul] using hbound

#print axioms finiteGeometricNuVector_two_bound

end

end FractionalPrimes.Literature.JSW

end
