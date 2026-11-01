module

public import FractionalPrimes.Literature.Ergodic.WeightedKernelTransference
public import FractionalPrimes.Literature.Variation.ScaleOrderedVariation

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Ergodic
open FractionalPrimes.Literature.Variation
noncomputable section

theorem extendedLpNorm_ennreal_eq_eLpNorm
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (F : X → ℝ≥0∞) (hF : AEStronglyMeasurable F μ) :
    extendedLpNorm μ p F = eLpNorm F p μ := by
  unfold extendedLpNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hF]
  simp only [enorm_eq_self, one_div]

theorem weightedFloorKernelFamily_discreteVariation
    (c r : ℝ) (w : Scale → ℕ → ℂ) (g : ℤ → ℂ) :
    finiteKernelDiscreteVariation r (fun N => weightedFloorKernelFinsupp c N (w N)) g =
      rVariationFun r (fun N => weightedAverage integerShiftSystem c (w N) g N) := by
  funext x
  change orderedRVariation r (fun N =>
    finiteKernelConvolution (weightedFloorKernelFinsupp c N (w N)) g x) = _
  have hfamily : (fun N => finiteKernelConvolution (weightedFloorKernelFinsupp c N (w N)) g x) =
      (fun N => weightedAverage integerShiftSystem c (w N) g N x) := by
    funext N
    rw [weightedFloorKernelFinsupp_convolution,
      ← weightedAverage_integerShift_eq_integerKernelConvolution]
  rw [hfamily, orderedRVariation_scale_eq_rVariation]
  rfl

theorem weightedFloorKernelFamily_systemVariation
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c r : ℝ) (w : Scale → ℕ → ℂ) (f : X → ℂ) :
    finiteKernelSystemVariation S r (fun N => weightedFloorKernelFinsupp c N (w N)) f =
      rVariationFun r (fun N => weightedAverage S c (w N) f N) := by
  funext x
  change orderedRVariation r (fun N =>
    finiteKernelSystemOperator S (weightedFloorKernelFinsupp c N (w N)) f x) = _
  have hfamily : (fun N => finiteKernelSystemOperator S (weightedFloorKernelFinsupp c N (w N)) f x) =
      (fun N => weightedAverage S c (w N) f N x) := by
    funext N
    rw [weightedFloorKernelFinsupp_systemOperator]
  rw [hfamily, orderedRVariation_scale_eq_rVariation]
  rfl

#print axioms weightedFloorKernelFamily_systemVariation

/-- Full-family weighted variation transfers from sequence lp to every
system, preserving the constant and the exact positive integer index set. -/
theorem transferWeightedFloorVariation
    {p r : ℝ} (hp : 1 < p) (hr : 1 ≤ r)
    (c : ℝ) (w : Scale → ℕ → ℂ) (C : NNReal)
    (hdisc : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ g : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
        eLpNorm (rVariationFun r
          (fun N => weightedAverage integerShiftSystem c (w N) (g : ℤ → ℂ) N))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofNNReal C * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) Measure.count)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (rVariationFun r (fun N => weightedAverage S c (w N) f N))
        (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofNNReal C * eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  let K := fun N => weightedFloorKernelFinsupp c N (w N)
  let Exh : Set.FiniteExhaustion (Set.univ : Set Scale) := Set.countable_univ.finiteExhaustion
  have htrunc (n : ℕ) (g : ℤ → ℂ) (x : ℤ) :
      finiteKernelDiscreteVariation r (fun i : Exh n => K i.val) g x ≤
        finiteKernelDiscreteVariation r K g x := by
    change orderedRVariation r (fun i : Exh n => finiteKernelConvolution (K i.val) g x) ≤
      orderedRVariation r (fun i => finiteKernelConvolution (K i) g x)
    rw [← orderedRVariationTrunc_eq_subtype Exh r
      (fun i => finiteKernelConvolution (K i) g x) n,
      orderedRVariation_eq_iSup_trunc Exh r (fun i => finiteKernelConvolution (K i) g x)]
    exact le_iSup (fun m => orderedRVariationTrunc Exh r
      (fun i => finiteKernelConvolution (K i) g x) m) n
  have hfinite (n : ℕ) (g : ℤ → ℂ) (hg : (Function.support g).Finite) :
      finiteKernelDiscreteVariationLpNorm (ENNReal.ofReal p) (ENNReal.ofReal r)
          (fun i : Exh n => K i.val) g ≤
        ENNReal.ofNNReal C * extendedLpNorm Measure.count (ENNReal.ofReal p)
          (fun j => ‖g j‖ₑ) := by
    let G : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
      ⟨g, (memℓp_zero hg).of_exponent_ge bot_le⟩
    rw [finiteKernelDiscreteVariationLpNorm, ENNReal.toReal_ofReal hr0,
      extendedLpNorm_ennreal_eq_eLpNorm _ _ hp0 ENNReal.ofReal_ne_top _
        (measurable_of_countable _).aestronglyMeasurable,
      extendedLpNorm_eq_eLpNorm _ _ _ hp0 ENNReal.ofReal_ne_top
        (measurable_of_countable _).aestronglyMeasurable]
    have hmono : eLpNorm (finiteKernelDiscreteVariation r (fun i : Exh n => K i.val) g)
        (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (finiteKernelDiscreteVariation r K g) (ENNReal.ofReal p) Measure.count := by
      apply eLpNorm_mono_enorm (measurable_of_countable _).aestronglyMeasurable
      intro x
      simpa only [enorm_eq_self] using htrunc n g x
    apply hmono.trans
    rw [weightedFloorKernelFamily_discreteVariation]
    exact hdisc G
  have hfull := transferCountableFiniteKernelVariation S (ENNReal.ofReal p) (ENNReal.ofReal r)
    (ENNReal.one_le_ofReal.mpr hp.le) ENNReal.ofReal_lt_top
    (ENNReal.one_le_ofReal.mpr hr) ENNReal.ofReal_lt_top K C Exh hfinite f hf
  rw [ENNReal.toReal_ofReal hr0,
    extendedLpNorm_ennreal_eq_eLpNorm _ _ hp0 ENNReal.ofReal_ne_top _
      (aemeasurable_finiteKernelSystemVariation S r K f hf.aestronglyMeasurable).aestronglyMeasurable,
    weightedFloorKernelFamily_systemVariation] at hfull
  exact hfull

#print axioms transferWeightedFloorVariation
end
end FractionalPrimes.Literature.Ergodic
