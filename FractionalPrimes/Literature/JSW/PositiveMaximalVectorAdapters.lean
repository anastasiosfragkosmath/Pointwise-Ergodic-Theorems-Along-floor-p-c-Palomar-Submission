module

public import FractionalPrimes.Literature.JSW.PositiveMaximalVectorAssembly
public import FractionalPrimes.Literature.JSW.PositiveSquaredSliceIntegrable
public import FractionalPrimes.Literature.JSW.InitialSquareRawMaximal

/-!
# Adapters for the positive maximal vector estimate

This file connects the abstract energy estimate to finite families of the
paper's positive probability convolutions.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The reflected geometric-scale average is exactly the source average
controlled by the positive maximal operator. -/
theorem initialSquare_reflectedScale_integral_eq_rawPositiveScale
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (k : ℤ) (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ g x) (x : ℝ) :
    (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ k * y) σ) =
      initialSquareSigmaRawPositiveScale (Measure.map Neg.neg σ) b k
        (fun y => (g y : ℂ)) x := by
  have ht : b ^ k ≠ 0 := ne_of_gt (zpow_pos (by linarith) _)
  rw [(measurableEmbedding_mulLeft₀ ht).integral_map]
  unfold initialSquareSigmaRawPositiveScale
  rw [measurableEmbedding_neg.integral_map]
  congr 1
  funext y
  rw [mul_neg, sub_neg_eq_add]
  simp [Complex.norm_real, abs_of_nonneg (hg (x + b ^ k * y))]

/-- The pointwise probability Jensen inequality for a finite family gives
the AE coordinate-energy premise used by `finiteProbabilityVector_energy_bound`.
The explicit AE integrability conditions are the precise conditions needed
for raw representatives of general `Lᵖ` inputs. -/
theorem finiteProbabilityConvolution_jensen_ae
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (f : ι → ℝ → ℂ) (U : ℝ → EuclideanSpace ℂ ι)
    (hU : ∀ i, (fun x => U x i) =ᵐ[volume]
      (fun x => jswConvolution (μ i) (f i) x))
    (hInt : ∀ i, ∀ᵐ x ∂volume,
      Integrable (fun y => f i (x-y)) (μ i))
    (hSq : ∀ i, ∀ᵐ x ∂volume,
      Integrable (fun y => ‖f i (x-y)‖ ^ 2) (μ i)) :
    ∀ᵐ x ∂volume,
      (∑ i, ‖U x i‖ ^ 2) ≤
        ∑ i, ∫ y, ‖f i (x-y)‖ ^ 2 ∂(μ i) := by
  classical
  have hUall : ∀ᵐ x ∂volume, ∀ i, U x i = jswConvolution (μ i) (f i) x :=
    ae_all_iff.mpr hU
  have hIntall : ∀ᵐ x ∂volume, ∀ i,
      Integrable (fun y => f i (x-y)) (μ i) := ae_all_iff.mpr hInt
  have hSqall : ∀ᵐ x ∂volume, ∀ i,
      Integrable (fun y => ‖f i (x-y)‖ ^ 2) (μ i) := ae_all_iff.mpr hSq
  filter_upwards [hUall, hIntall, hSqall] with x hUx hIx hSx
  calc
    ∑ i, ‖U x i‖ ^ 2 =
        ∑ i, ‖jswConvolution (μ i) (f i) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hUx i]
    _ ≤ ∑ i, ∫ y, ‖f i (x-y)‖ ^ 2 ∂(μ i) :=
      finiteProbabilityConvolution_square_le μ hμ f x hIx hSx

/-- The translated input is integrable for almost every spatial point when
the measure is finite and the input belongs to `Lᵖ`, `p>2`. -/
theorem integrable_translation_ae_of_memLp
    {p : ℝ} (hp : 2 < p)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hstrong : StronglyMeasurable f) :
    ∀ᵐ x ∂volume, Integrable (fun y => f (x-y)) μ := by
  filter_upwards [integrable_sq_translation_ae_of_memLp hp μ f hf] with x hsquare
  have hsm : AEStronglyMeasurable (fun y => f (x-y)) μ :=
    (hstrong.comp_measurable (by fun_prop)).aestronglyMeasurable
  have hmem2 : MemLp (fun y => f (x-y)) (2 : ℝ≥0∞) μ :=
    (integrable_norm_rpow_iff hsm (by norm_num) (by norm_num)).mp (by simpa using hsquare)
  have hmem1 : MemLp (fun y => f (x-y)) 1 μ :=
    hmem2.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact memLp_one_iff_integrable.mp hmem1

/-- The paper's `p>2` finite-family vector estimate for raw convolution by
probability measures. The only nontrivial operator input is the reflected
maximal majorant with `Lᑫ` bound `B`. -/
theorem finiteProbabilityConvolution_lp_bound
    {ι : Type*} [Fintype ι] {p q : ℝ} (hp : 2 < p)
    (hrq : (p / 2).HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i))
    (U : ℝ → EuclideanSpace ℂ ι)
    (hU : MemLp U (ENNReal.ofReal p) volume)
    (hUraw : ∀ i, (fun x => U x i) =ᵐ[volume]
      (fun x => jswConvolution (μ i) (f i) x))
    (B : ℝ) (hB : 0 ≤ B)
    (hMax : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume) :
    lpNorm U (ENNReal.ofReal p) volume ≤
      Real.sqrt B * lpNorm
        (fun x => WithLp.toLp 2 (fun i => f i x))
        (ENNReal.ofReal p) volume := by
  let F : ℝ → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 (fun i => f i x)
  have hF : MemLp F (ENNReal.ofReal p) volume := by
    apply MemLp.of_eval_piLp
    intro i
    simpa [F] using hf i
  have hInt : ∀ i, ∀ᵐ x ∂volume,
      Integrable (fun y => f i (x-y)) (μ i) := by
    intro i
    exact integrable_translation_ae_of_memLp hp (μ i) (f i) (hf i) (hstrong i)
  have hSq : ∀ i, ∀ᵐ x ∂volume,
      Integrable (fun y => ‖f i (x-y)‖ ^ 2) (μ i) := by
    intro i
    exact integrable_sq_translation_ae_of_memLp hp (μ i) (f i) (hf i)
  have hJensen := finiteProbabilityConvolution_jensen_ae μ hμ f U hUraw hInt hSq
  exact finiteProbabilityVector_lp_bound hp hrq μ hμ F U hF hU
    (by simpa [F] using hJensen) B hB hMax

/-- A real-linear diagonal convolution operator inherits the upper-`p`
bound of its reflected adjoint. This is the lower-`p` transfer in
`lj:positivity`; the convolution-specific adjoint identity is supplied by
the Fubini pairing lemma. -/
theorem lpRealAdjoint_bound_transfer
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q C : ℝ} (hpq : p.HolderConjugate q) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
    ∀ (T : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp H (ENNReal.ofReal p) (volume : Measure ℝ))
      (S : Lp H (ENNReal.ofReal q) (volume : Measure ℝ) →L[ℝ]
        Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)),
      (∀ f g,
        (∫ x, inner ℂ
          ((T f : Lp H (ENNReal.ofReal p) (volume : Measure ℝ)) x)
          ((g : Lp H (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) =
        ∫ x, inner ℂ
          ((f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
          ((S g : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) x) ∂volume) →
      0 ≤ C → (∀ g, ‖S g‖ ≤ C * ‖g‖) → ∀ f, ‖T f‖ ≤ C * ‖f‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
  intro T S hAdj hC hS f
  have hnorm := lpRealAdjointOperator_norm_eq hpq T S hAdj
  have hSNorm : ‖S‖ ≤ C := S.opNorm_le_bound hC hS
  calc
    ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ = ‖S‖ * ‖f‖ := by rw [hnorm]
    _ ≤ C * ‖f‖ :=
      mul_le_mul_of_nonneg_right hSNorm (norm_nonneg f)

#print axioms finiteProbabilityConvolution_jensen_ae
#print axioms integrable_translation_ae_of_memLp
#print axioms finiteProbabilityConvolution_lp_bound
#print axioms lpRealAdjoint_bound_transfer

end

end FractionalPrimes.Literature.JSW

end
