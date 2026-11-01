module

public import FractionalPrimes.Systems
public import FractionalPrimes.Literature.Variation.FiniteChainVariation
public import FractionalPrimes.Literature.Variation.FiniteOrderedVariationAttainment
public import FractionalPrimes.Literature.Variation.OrderedVariationExhaustion
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Finite-kernel transference

The finite-orbit cutoff proof of the approved finite-kernel transference
lemma.  The discrete convolution convention is `g (j - m)`, matching the
integer iterate convention in `FractionalPrimes.InvertibleSystem`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Ergodic

open MeasureTheory
open FractionalPrimes.Literature.Variation
open scoped ENNReal

noncomputable section

/-- Convolution by a finitely supported complex kernel on `ℤ`. -/
def finiteKernelConvolution (K : ℤ →₀ ℂ) (g : ℤ → ℂ) : ℤ → ℂ :=
  fun j => ∑ m ∈ K.support, K m * g (j - m)

/-- The system operator associated with a finitely supported complex kernel. -/
def finiteKernelSystemOperator {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (K : ℤ →₀ ℂ) (f : X → ℂ) : X → ℂ :=
  fun x => ∑ m ∈ K.support, K m * f (S.iterate m x)

/-- The cutoff-orbit identity at the center of finite-kernel transference. -/
theorem finiteKernelConvolution_orbit_eq_systemOperator_shift
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (K : ℤ →₀ ℂ) (f : X → ℂ) (j : ℤ) (x : X) :
    finiteKernelConvolution K (fun n => f (S.iterate (-n) x)) j =
      finiteKernelSystemOperator S K f (S.iterate (-j) x) := by
  classical
  unfold finiteKernelConvolution finiteKernelSystemOperator
  apply Finset.sum_congr rfl
  intro m hm
  congr 2
  apply congrArg f
  change (S.T.toEquiv ^ (-(j - m))) x =
    ((S.T.toEquiv ^ m * S.T.toEquiv ^ (-j)) x)
  rw [show -(j - m) = m + (-j) by omega, zpow_add, Equiv.Perm.mul_apply]

/-- A system operator of a finite kernel is a.e. measurable when its input
is a.e. strongly measurable. -/
theorem aemeasurable_finiteKernelSystemOperator
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (K : ℤ →₀ ℂ) (f : X → ℂ)
    (hf : AEStronglyMeasurable f S.μ) :
    AEMeasurable (finiteKernelSystemOperator S K f) S.μ := by
  classical
  unfold finiteKernelSystemOperator
  apply Finset.aemeasurable_fun_sum
  intro m hm
  exact ((hf.comp_measurePreserving (S.measurePreserving_integerIterate m)).const_mul (K m)).aemeasurable

/-- The `r`-variation of a finite chain of a.e. measurable functions is a.e.
measurable. -/
theorem aemeasurable_finiteChainVariationFun
    {I X : Type*} [LinearOrder I] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : I → X → ℂ)
    (hF : ∀ i, AEMeasurable (F i) μ) {length : ℕ}
    (chain : StrictOrderedChain I length) :
    AEMeasurable (finiteChainVariationFun r F chain) μ := by
  have hsum : AEMeasurable (fun x =>
      ∑ i : Fin length,
        (ENNReal.ofReal ‖F (chain.point i.succ) x -
          F (chain.point i.castSucc) x‖).rpow r) μ := by
    apply Finset.aemeasurable_fun_sum
    intro i hi
    convert ((ENNReal.continuous_rpow_const (y := r)).measurable.aemeasurable).comp_aemeasurable
      (AEMeasurable.ennreal_ofReal
        (((hF (chain.point i.succ)).sub (hF (chain.point i.castSucc))).norm)) using 1
    ext x
    simp only [Function.comp_apply, ENNReal.rpow_eq_pow, Pi.sub_apply]
  convert ((ENNReal.continuous_rpow_const (y := r⁻¹)).measurable.aemeasurable).comp_aemeasurable
    hsum using 1
  ext x
  simp only [Function.comp_apply, finiteChainVariationFun, finiteChainVariation,
    ENNReal.rpow_eq_pow]

/-- The ordered `r`-variation of a countable family of a.e. measurable
functions is a.e. measurable. -/
theorem aemeasurable_orderedRVariationFun
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : I → X → ℂ)
    (hF : ∀ i, AEMeasurable (F i) μ) :
    AEMeasurable (orderedRVariationFun r F) μ := by
  unfold orderedRVariationFun orderedRVariation
  apply AEMeasurable.iSup
  intro length
  let _ : Countable (StrictOrderedChain I length) :=
    (strictOrderedChainEmbedding length).countable
  apply AEMeasurable.iSup
  intro chain
  exact aemeasurable_finiteChainVariationFun μ r F hF chain

/-- The extended `Lᵖ` norm of a nonnegative extended-valued function. -/
def extendedLpNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    (F : X → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x, F x ^ p.toReal ∂μ) ^ (1 / p.toReal)

/-- Raising the extended `Lᵖ` norm to the exponent recovers its moment. -/
theorem extendedLpNorm_rpow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0∞)
    (F : X → ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    extendedLpNorm μ p F ^ p.toReal = ∫⁻ x, F x ^ p.toReal ∂μ := by
  unfold extendedLpNorm
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  rw [← ENNReal.rpow_mul]
  rw [one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The ordinary function `eLpNorm` is this extended norm of the pointwise
extended norm. -/
theorem extendedLpNorm_eq_eLpNorm {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → E)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    extendedLpNorm μ p (fun x => ‖f x‖ₑ) = eLpNorm f p μ := by
  unfold extendedLpNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf]

/-- The discrete `r`-variation of a finite family of kernel convolutions. -/
def finiteKernelDiscreteVariation {I : Type*} [LinearOrder I] (r : ℝ)
    (K : I → ℤ →₀ ℂ) (g : ℤ → ℂ) : ℤ → ℝ≥0∞ :=
  orderedRVariationFun r (fun i j => finiteKernelConvolution (K i) g j)

/-- The system `r`-variation of a finite family of kernel operators. -/
def finiteKernelSystemVariation {I X : Type*} [LinearOrder I]
    [MeasurableSpace X] (S : InvertibleSystem X) (r : ℝ)
    (K : I → ℤ →₀ ℂ) (f : X → ℂ) : X → ℝ≥0∞ :=
  orderedRVariationFun r (fun i => finiteKernelSystemOperator S (K i) f)

/-- The extended `Lᵖ` norm of the discrete variation in the finite-kernel
transference statement. -/
def finiteKernelDiscreteVariationLpNorm {I : Type*} [LinearOrder I]
    (p r : ℝ≥0∞) (K : I → ℤ →₀ ℂ) (g : ℤ → ℂ) : ℝ≥0∞ :=
  extendedLpNorm (Measure.count : Measure ℤ) p (finiteKernelDiscreteVariation r.toReal K g)

/-- The extended `Lᵖ` norm of the system variation in the finite-kernel
transference statement. -/
def finiteKernelSystemVariationLpNorm {I X : Type*} [LinearOrder I]
    [MeasurableSpace X] (S : InvertibleSystem X) (p r : ℝ≥0∞)
    (K : I → ℤ →₀ ℂ) (f : X → ℂ) : ℝ≥0∞ :=
  extendedLpNorm S.μ p (finiteKernelSystemVariation S r.toReal K f)

/-- Discrete convolution outputs are measurable because the integer domain
has its countable discrete measurable structure. -/
theorem measurable_finiteKernelDiscreteVariation
    {I : Type*} [LinearOrder I] [Countable I]
    (r : ℝ) (K : I → ℤ →₀ ℂ) (g : ℤ → ℂ) :
    Measurable (finiteKernelDiscreteVariation r K g) := by
  apply measurable_orderedRVariationFun
  intro i
  exact measurable_of_countable _

/-- System variation is a.e. measurable for an a.e. strongly measurable input. -/
theorem aemeasurable_finiteKernelSystemVariation
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (S : InvertibleSystem X) (r : ℝ) (K : I → ℤ →₀ ℂ) (f : X → ℂ)
    (hf : AEStronglyMeasurable f S.μ) :
    AEMeasurable (finiteKernelSystemVariation S r K f) S.μ := by
  apply aemeasurable_orderedRVariationFun S.μ r
  intro i
  exact aemeasurable_finiteKernelSystemOperator S (K i) f hf

/-- A common radius containing the supports of a finite family of kernels. -/
def finiteKernelSupportRadius {I : Type*} [Fintype I]
    (K : I → ℤ →₀ ℂ) : ℕ :=
  (Finset.univ.biUnion fun i => (K i).support).sup Int.natAbs

/-- The finite orbit segment used to localize the discrete hypothesis. -/
def finiteKernelOrbitCutoff {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (f : X → ℂ) (N : ℕ) (x : X) : ℤ → ℂ :=
  fun j => if j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then f (S.iterate (-j) x) else 0

/-- Every support point is within the common support radius. -/
theorem finiteKernel_mem_support_radius {I : Type*} [Fintype I]
    (K : I → ℤ →₀ ℂ) (i : I) {m : ℤ} (hm : m ∈ (K i).support) :
    m.natAbs ≤ finiteKernelSupportRadius K := by
  classical
  unfold finiteKernelSupportRadius
  apply Finset.le_sup
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hm⟩

/-- A cutoff orbit sequence has finite support. -/
theorem finiteKernelOrbitCutoff_support_finite
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (N : ℕ) (x : X) :
    (Function.support (finiteKernelOrbitCutoff S f N x)).Finite := by
  classical
  refine (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) (N : ℤ))).subset ?_
  intro j hj
  simp only [Function.mem_support, finiteKernelOrbitCutoff] at hj
  by_cases hmem : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
  · exact hmem
  · simp [hmem] at hj

/-- The localized convolution equals the system operator on the central
orbit segment whenever the kernel support lies in the chosen radius. -/
theorem finiteKernelConvolution_orbitCutoff_eq_systemOperator_shift
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : InvertibleSystem X) (K : I → ℤ →₀ ℂ) (f : X → ℂ)
    (R L : ℕ) (i : I) (j : ℤ) (x : X)
    (hL : ∀ m ∈ (K i).support, m.natAbs ≤ L)
    (hj : j ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)) :
    finiteKernelConvolution (K i) (finiteKernelOrbitCutoff S f (R + L) x) j =
      finiteKernelSystemOperator S (K i) f (S.iterate (-j) x) := by
  classical
  unfold finiteKernelConvolution finiteKernelSystemOperator
  apply Finset.sum_congr rfl
  intro m hm
  have hmabs : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
  have habsm : |m| ≤ (L : ℤ) := by
    rw [← hmabs]
    exact_mod_cast hL m hm
  have hml : -(L : ℤ) ≤ m := by
    exact (abs_le.mp habsm).1
  have hmu : m ≤ L := by
    exact (abs_le.mp habsm).2
  have hseg : j - m ∈ Finset.Icc (-((R + L : ℕ) : ℤ)) ((R + L : ℕ) : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor
    · have hj' := (Finset.mem_Icc.mp hj).1
      omega
    · have hj' := (Finset.mem_Icc.mp hj).2
      omega
  simp only [finiteKernelOrbitCutoff, hseg, ↓reduceIte]
  congr 2
  change (S.T.toEquiv ^ (-(j - m))) x =
    (S.T.toEquiv ^ m) ((S.T.toEquiv ^ (-j)) x)
  rw [show -(j - m) = m + (-j) by omega, zpow_add, Equiv.Perm.mul_apply]

/-- Equality of the corresponding variations along a localized orbit. -/
theorem finiteKernelVariation_orbitCutoff_eq
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : InvertibleSystem X) (r : ℝ) (K : I → ℤ →₀ ℂ) (f : X → ℂ)
    (R L : ℕ) (j : ℤ) (x : X)
    (hL : ∀ i m, m ∈ (K i).support → m.natAbs ≤ L)
    (hj : j ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)) :
    finiteKernelDiscreteVariation r K (finiteKernelOrbitCutoff S f (R + L) x) j =
      finiteKernelSystemVariation S r K f (S.iterate (-j) x) := by
  unfold finiteKernelDiscreteVariation finiteKernelSystemVariation
    orderedRVariationFun
  congr 1
  funext i
  exact finiteKernelConvolution_orbitCutoff_eq_systemOperator_shift
    S K f R L i j x (hL i) hj

/-- An a.e. measurable nonnegative function has invariant lower integral
under each integer iterate of a measure-preserving system. -/
theorem lintegral_comp_integerIterate_aemeasurable
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (m : ℤ)
    (F : X → ℝ≥0∞) (hF : AEMeasurable F S.μ) :
    ∫⁻ x, F (S.iterate m x) ∂S.μ = ∫⁻ x, F x ∂S.μ := by
  let hpres := S.measurePreserving_integerIterate m
  have hmap : AEMeasurable F (S.μ.map (S.iterate m)) := by
    rw [hpres.map_eq]
    exact hF
  change lintegral S.μ (F ∘ S.iterate m) = lintegral S.μ F
  rw [MeasureTheory.lintegral_comp' hmap hpres.measurable.aemeasurable, hpres.map_eq]

/-- Composition of an a.e. measurable function with an integer iterate is
a.e. measurable. -/
theorem aemeasurable_comp_integerIterate
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (m : ℤ)
    (F : X → ℝ≥0∞) (hF : AEMeasurable F S.μ) :
    AEMeasurable (fun x => F (S.iterate m x)) S.μ := by
  let hpres := S.measurePreserving_integerIterate m
  have hmap : AEMeasurable F (S.μ.map (S.iterate m)) := by
    rw [hpres.map_eq]
    exact hF
  exact hmap.comp_measurable hpres.measurable

/-- Counting measure integrates a function over a finite integer interval by
the corresponding finite sum. -/
theorem lintegral_count_Icc_eq_sum (a b : ℤ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ j in (Finset.Icc a b : Set ℤ), F j ∂(Measure.count : Measure ℤ) =
      ∑ j ∈ Finset.Icc a b, F j := by
  rw [MeasureTheory.lintegral_finset]
  simp

/-- The indicator of a finite integer interval has its expected counting
integral. -/
theorem lintegral_indicator_count_Icc_eq_sum (a b : ℤ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ j, (Finset.Icc a b : Set ℤ).indicator F j ∂(Measure.count : Measure ℤ) =
      ∑ j ∈ Finset.Icc a b, F j := by
  rw [MeasureTheory.lintegral_indicator (Finset.finite_toSet _).measurableSet,
    lintegral_count_Icc_eq_sum]

/-- Raising a discrete `Lᵖ`-variation estimate to the exponent yields its
moment estimate. -/
theorem finiteKernelDiscreteVariation_moment_le
    {I : Type*} [LinearOrder I] [Countable I]
    (p r : ℝ≥0∞) (K : I → ℤ →₀ ℂ) (C : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (g : ℤ → ℂ) (hvar :
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        C * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ)) :
    ∫⁻ j, finiteKernelDiscreteVariation r.toReal K g j ^ p.toReal
        ∂(Measure.count : Measure ℤ) ≤
      C ^ p.toReal * ∫⁻ j, ‖g j‖ₑ ^ p.toReal ∂(Measure.count : Measure ℤ) := by
  have hpnonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hpow := ENNReal.rpow_le_rpow hvar hpnonneg
  change extendedLpNorm (Measure.count : Measure ℤ) p
      (finiteKernelDiscreteVariation r.toReal K g) ^ p.toReal ≤ _ at hpow
  rw [extendedLpNorm_rpow (Measure.count : Measure ℤ) p
      (finiteKernelDiscreteVariation r.toReal K g) hp0 hptop] at hpow
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpnonneg] at hpow
  rw [extendedLpNorm_rpow (Measure.count : Measure ℤ) p
      (fun j => ‖g j‖ₑ) hp0 hptop] at hpow
  exact hpow

/-- The input moment of an orbit cutoff is exactly the finite sum over its
support interval. -/
theorem finiteKernelOrbitCutoff_moment_eq_sum
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (N : ℕ) (x : X) (q : ℝ) (hq : 0 < q) :
    ∫⁻ j, ‖finiteKernelOrbitCutoff S f N x j‖ₑ ^ q
        ∂(Measure.count : Measure ℤ) =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖f (S.iterate (-j) x)‖ₑ ^ q := by
  have hfun : (fun j : ℤ => ‖finiteKernelOrbitCutoff S f N x j‖ₑ ^ q) =
      (Finset.Icc (-(N : ℤ)) (N : ℤ) : Set ℤ).indicator
        (fun j => ‖f (S.iterate (-j) x)‖ₑ ^ q) := by
    funext j
    by_cases hj : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    · have hjS : j ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ) : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_mem hjS]
      simp [finiteKernelOrbitCutoff, hj]
    · have hjS : j ∉ (Finset.Icc (-(N : ℤ)) (N : ℤ) : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_notMem hjS]
      simp [finiteKernelOrbitCutoff, hj, hq]
  rw [hfun, lintegral_indicator_count_Icc_eq_sum]

/-- Pointwise moment domination on a finite central orbit segment, before
integrating over the system. -/
theorem finiteKernelOrbitCutoff_central_moment_le
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : InvertibleSystem X) (p r : ℝ≥0∞) (K : I → ℤ →₀ ℂ)
    (C : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        C * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (R L : ℕ) (x : X)
    (hL : ∀ i m, m ∈ (K i).support → m.natAbs ≤ L) :
    ∑ j ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        finiteKernelSystemVariation S r.toReal K f (S.iterate (-j) x) ^ p.toReal ≤
      C ^ p.toReal *
        ∑ j ∈ Finset.Icc (-((R + L : ℕ) : ℤ)) ((R + L : ℕ) : ℤ),
          ‖f (S.iterate (-j) x)‖ₑ ^ p.toReal := by
  let g := finiteKernelOrbitCutoff S f (R + L) x
  have hg : (Function.support g).Finite := by
    simpa [g] using finiteKernelOrbitCutoff_support_finite S f (R + L) x
  have hdiscMoment := finiteKernelDiscreteVariation_moment_le p r K C hp0 hptop
    g (hdisc g hg)
  have hpoint : ∀ j : ℤ,
      (Finset.Icc (-(R : ℤ)) (R : ℤ) : Set ℤ).indicator
        (fun j => finiteKernelSystemVariation S r.toReal K f
          (S.iterate (-j) x) ^ p.toReal) j ≤
        finiteKernelDiscreteVariation r.toReal K g j ^ p.toReal := by
    intro j
    by_cases hj : j ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)
    · have hjS : j ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ) : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_mem hjS]
      rw [← finiteKernelVariation_orbitCutoff_eq S r.toReal K f R L j x hL hj]
    · have hjS : j ∉ (Finset.Icc (-(R : ℤ)) (R : ℤ) : Set ℤ) := by simpa using hj
      rw [Set.indicator_of_notMem hjS]
      exact bot_le
  have hcentral := MeasureTheory.lintegral_mono
    (μ := (Measure.count : Measure ℤ)) hpoint
  rw [lintegral_indicator_count_Icc_eq_sum] at hcentral
  calc
    _ ≤ ∫⁻ j, finiteKernelDiscreteVariation r.toReal K g j ^ p.toReal
          ∂(Measure.count : Measure ℤ) := hcentral
    _ ≤ C ^ p.toReal * ∫⁻ j, ‖g j‖ₑ ^ p.toReal
          ∂(Measure.count : Measure ℤ) := hdiscMoment
    _ = _ := by
      change C ^ p.toReal *
        (∫⁻ j, ‖finiteKernelOrbitCutoff S f (R + L) x j‖ₑ ^ p.toReal
          ∂(Measure.count : Measure ℤ)) = _
      rw [finiteKernelOrbitCutoff_moment_eq_sum S f (R + L) x p.toReal
        (ENNReal.toReal_pos hp0 hptop)]

/-- Integrating the finite central estimate transfers its two moment sums to
the system measure. -/
theorem finiteKernelSystemVariation_moment_scaled
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : InvertibleSystem X) (p r : ℝ≥0∞) (K : I → ℤ →₀ ℂ)
    (C : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        C * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : AEStronglyMeasurable f S.μ) (R L : ℕ)
    (hL : ∀ i m, m ∈ (K i).support → m.natAbs ≤ L) :
    (Finset.Icc (-(R : ℤ)) (R : ℤ)).card *
        ∫⁻ x, finiteKernelSystemVariation S r.toReal K f x ^ p.toReal ∂S.μ ≤
      C ^ p.toReal *
        ((Finset.Icc (-((R + L : ℕ) : ℤ)) ((R + L : ℕ) : ℤ)).card *
          ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂S.μ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hptop : p ≠ ∞ := ne_of_lt hpTop
  let V := finiteKernelSystemVariation S r.toReal K f
  let vMoment : X → ℝ≥0∞ := fun x => V x ^ p.toReal
  let fMoment : X → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ p.toReal
  have hV : AEMeasurable V S.μ :=
    aemeasurable_finiteKernelSystemVariation S r.toReal K f hf
  have hvMoment : AEMeasurable vMoment S.μ := by
    exact AEMeasurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := p.toReal)).measurable.aemeasurable
      (by simpa [vMoment] using hV)
  have hnorm : AEMeasurable (fun x => ‖f x‖ₑ) S.μ := hf.enorm
  have hfMoment : AEMeasurable fMoment S.μ := by
    exact AEMeasurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := p.toReal)).measurable.aemeasurable
      (by simpa [fMoment] using hnorm)
  let center := Finset.Icc (-(R : ℤ)) (R : ℤ)
  let outer := Finset.Icc (-((R + L : ℕ) : ℤ)) ((R + L : ℕ) : ℤ)
  have hcenterComp : ∀ j ∈ center,
      AEMeasurable (fun x => vMoment (S.iterate (-j) x)) S.μ := by
    intro j hj
    exact aemeasurable_comp_integerIterate S (-j) vMoment hvMoment
  have houterComp : ∀ j ∈ outer,
      AEMeasurable (fun x => fMoment (S.iterate (-j) x)) S.μ := by
    intro j hj
    exact aemeasurable_comp_integerIterate S (-j) fMoment hfMoment
  have hcenterIntegral :
      ∫⁻ x, ∑ j ∈ center, vMoment (S.iterate (-j) x) ∂S.μ =
        (center.card : ℝ≥0∞) * ∫⁻ x, vMoment x ∂S.μ := by
    rw [MeasureTheory.lintegral_finsetSum' center hcenterComp]
    calc
      _ = ∑ j ∈ center, ∫⁻ x, vMoment x ∂S.μ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact lintegral_comp_integerIterate_aemeasurable S (-j) vMoment hvMoment
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have houterIntegral :
      ∫⁻ x, ∑ j ∈ outer, fMoment (S.iterate (-j) x) ∂S.μ =
        (outer.card : ℝ≥0∞) * ∫⁻ x, fMoment x ∂S.μ := by
    rw [MeasureTheory.lintegral_finsetSum' outer houterComp]
    calc
      _ = ∑ j ∈ outer, ∫⁻ x, fMoment x ∂S.μ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact lintegral_comp_integerIterate_aemeasurable S (-j) fMoment hfMoment
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hpoint : ∀ x,
      (∑ j ∈ center, vMoment (S.iterate (-j) x)) ≤
        C ^ p.toReal * ∑ j ∈ outer, fMoment (S.iterate (-j) x) := by
    intro x
    simpa [center, outer, V, vMoment, fMoment] using
      finiteKernelOrbitCutoff_central_moment_le S p r K C hp0 hptop hdisc
        f R L x hL
  have hIntegral := MeasureTheory.lintegral_mono (μ := S.μ) hpoint
  rw [hcenterIntegral, MeasureTheory.lintegral_const_mul'' _
    (by
      have hs : AEMeasurable (fun x => ∑ j ∈ outer, fMoment (S.iterate (-j) x)) S.μ :=
        Finset.aemeasurable_fun_sum outer fun j hj => houterComp j hj
      exact hs)] at hIntegral
  rw [houterIntegral] at hIntegral
  simpa [center, outer, V, vMoment, fMoment, mul_assoc] using hIntegral

/-- Exact real cardinality of a symmetric finite integer interval. -/
theorem finiteKernel_intIcc_card_real (A B : ℕ) :
    (Finset.Icc (-(A : ℤ)) (B : ℤ)).card = (A : ℕ) + B + 1 := by
  rw [Int.card_Icc]
  have hab : 0 ≤ (B : ℤ) + 1 - (-(A : ℤ)) := by omega
  apply (Nat.cast_inj (R := ℤ)).mp
  calc
    (((B : ℤ) + 1 - (-(A : ℤ))).toNat : ℤ) =
        (B : ℤ) + 1 - (-(A : ℤ)) := Int.toNat_of_nonneg hab
    _ = (A + B + 1 : ℕ) := by push_cast; omega

/-- Real version of the finite integer-interval cardinality. -/
theorem finiteKernel_intIcc_card_realCast (A B : ℕ) :
    ((Finset.Icc (-(A : ℤ)) (B : ℤ)).card : ℝ) =
      (A : ℝ) + B + 1 := by
  exact_mod_cast finiteKernel_intIcc_card_real A B

/-- Finite-family finite-kernel transference, with the same constant as the
counting-measure inequality. The displayed norms are expressed as extended
`Lᵖ` moments, so the variation may initially take the value `∞`. -/
theorem transferFiniteKernelVariation
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : InvertibleSystem X) (p r : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (_hr1 : 1 ≤ r) (_hrTop : r < ∞)
    (K : I → ℤ →₀ ℂ) (C : NNReal)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r K g ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    finiteKernelSystemVariationLpNorm S p r K f ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hptop : p ≠ ∞ := ne_of_lt hpTop
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  let L := finiteKernelSupportRadius K
  have hL : ∀ i m, m ∈ (K i).support → m.natAbs ≤ L := by
    intro i m hm
    exact finiteKernel_mem_support_radius K i hm
  let V := finiteKernelSystemVariation S r.toReal K f
  let A := ∫⁻ x, V x ^ p.toReal ∂S.μ
  let J := ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂S.μ
  let B := (C : ℝ≥0∞) ^ p.toReal
  have hJ_eq : J = eLpNorm f p S.μ ^ p.toReal := by
    calc
      J = extendedLpNorm S.μ p (fun x => ‖f x‖ₑ) ^ p.toReal := by
        dsimp [J]
        symm
        exact extendedLpNorm_rpow S.μ p (fun x => ‖f x‖ₑ) hp0 hptop
      _ = eLpNorm f p S.μ ^ p.toReal := by
        rw [extendedLpNorm_eq_eLpNorm S.μ p f hp0 hptop hf.aestronglyMeasurable]
  have hJne : J ≠ ∞ := by
    rw [hJ_eq]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hf.eLpNorm_ne_top
  have hBne : B ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  have hAne : A ≠ ∞ := by
    by_contra hAeq
    have hsmall := finiteKernelSystemVariation_moment_scaled S p r K
      (C : ℝ≥0∞) hp1 hpTop hdisc f hf.aestronglyMeasurable 1 L hL
    have hlefttop :
        ((Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).card : ℝ≥0∞) * A = ∞ := by
      simp [hAeq]
    have hrhsne : B *
        ((Finset.Icc (-((1 + L : ℕ) : ℤ)) ((1 + L : ℕ) : ℤ)).card * J) ≠ ∞ := by
      exact ENNReal.mul_ne_top hBne (ENNReal.mul_ne_top ENNReal.coe_ne_top hJne)
    rw [hlefttop] at hsmall
    exact (not_le_of_gt (lt_top_iff_ne_top.mpr hrhsne)) hsmall
  have hscaledReal (R : ℕ) :
      (2 * (R : ℝ) + 1) * A.toReal ≤
        B.toReal * ((2 * ((R + L : ℕ) : ℝ) + 1) * J.toReal) := by
    have hraw := finiteKernelSystemVariation_moment_scaled S p r K
      (C : ℝ≥0∞) hp1 hpTop hdisc f hf.aestronglyMeasurable R L hL
    rw [finiteKernel_intIcc_card_real R R,
      finiteKernel_intIcc_card_real (R + L) (R + L)] at hraw
    have hrhsne : B * ((((R + L) + (R + L) + 1 : ℕ) : ℝ≥0∞) * J) ≠ ∞ := by
      exact ENNReal.mul_ne_top hBne (ENNReal.mul_ne_top ENNReal.coe_ne_top hJne)
    have hreal := ENNReal.toReal_mono hrhsne hraw
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
    have hcardL :
        ((R + R + 1 : ℕ) : ℝ) = 2 * (R : ℝ) + 1 := by push_cast; ring
    have hcardR :
        ((R + L + (R + L) + 1 : ℕ) : ℝ) =
          2 * ((R + L : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcardL, hcardR] at hreal
    exact hreal
  have htargetMoment : A ≤ B * J := by
    by_contra hnot
    have hBJne : B * J ≠ ∞ := ENNReal.mul_ne_top hBne hJne
    have hlt : B * J < A := lt_of_not_ge hnot
    let Δ : ℝ := A.toReal - (B * J).toReal
    have hgap : 0 < A.toReal - (B * J).toReal := by
      have hltReal := (ENNReal.toReal_lt_toReal hBJne hAne).2 hlt
      linarith
    let D : ℝ := B.toReal * J.toReal
    have hD : D = (B * J).toReal := by
      simp [D, ENNReal.toReal_mul]
    let cutoff : ℝ := 2 * (L : ℝ) * D / Δ
    obtain ⟨R, hR⟩ := exists_nat_gt cutoff
    have hR' : 2 * (L : ℝ) * D / Δ < (R : ℝ) := by simpa [cutoff] using hR
    have hfinal := hscaledReal R
    have hBD : B.toReal * J.toReal = D := by
      simp [D]
    have hfinal' :
        (2 * (R : ℝ) + 1) * A.toReal ≤
          (2 * ((R + L : ℕ) : ℝ) + 1) * D := by
      calc
        _ ≤ B.toReal * ((2 * ((R + L : ℕ) : ℝ) + 1) * J.toReal) := hfinal
        _ = (2 * ((R + L : ℕ) : ℝ) + 1) * D := by rw [← hBD]; ring
    have hΔ : 0 < Δ := by simpa [Δ] using hgap
    have hfinal'' := hfinal'
    rw [hD] at hfinal''
    push_cast at hfinal''
    have hcontr : (2 * (R : ℝ) + 1) * Δ ≤ 2 * (L : ℝ) * D := by
      dsimp [Δ]
      rw [hD]
      nlinarith [hfinal'']
    have hRmul : 2 * (L : ℝ) * D < (R : ℝ) * Δ :=
      (div_lt_iff₀ hΔ).mp hR'
    have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    have hcoeff : (R : ℝ) * Δ ≤ (2 * (R : ℝ) + 1) * Δ := by
      nlinarith
    exact (not_lt_of_ge (le_trans hcoeff hcontr)) hRmul
  have hnormPow :
      finiteKernelSystemVariationLpNorm S p r K f ^ p.toReal ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    have hleft : finiteKernelSystemVariationLpNorm S p r K f ^ p.toReal = A := by
      simpa [finiteKernelSystemVariationLpNorm, V, A] using
        extendedLpNorm_rpow S.μ p V hp0 hptop
    rw [hleft]
    calc
      A ≤ B * J := htargetMoment
      _ = (B * eLpNorm f p S.μ ^ p.toReal) := by rw [hJ_eq]
      _ = ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
        simp [B, ENNReal.mul_rpow_of_nonneg]
  exact (ENNReal.rpow_le_rpow_iff hq).mp hnormPow

/-- Variation on a two-point index set is exactly the single increment. -/
theorem orderedRVariation_finTwo_eq
    (r : ℝ) (hr : 0 < r) (u : Fin 2 → ℂ) :
    orderedRVariation r u = ENNReal.ofReal ‖u 1 - u 0‖ := by
  classical
  let cap : ℝ≥0∞ := ENNReal.ofReal ‖u 1 - u 0‖
  have hcard : 2 ≤ Fintype.card (Fin 2) := by simp
  obtain ⟨length, chain, hmax⟩ :=
    orderedRVariation_isAttained_of_two_le_card r u hcard
  have twoChainValue (c : StrictOrderedChain (Fin 2) 1) :
      finiteChainVariation r u c = cap := by
    have hlt : (c.point (0 : Fin 2)).val < (c.point (1 : Fin 2)).val := by
      simpa using c.strictMono (show (0 : Fin 2) < 1 by decide)
    have h0val : (c.point (0 : Fin 2)).val = 0 := by
      have h0bound := (c.point (0 : Fin 2)).isLt
      have h1bound := (c.point (1 : Fin 2)).isLt
      omega
    have h1val : (c.point (1 : Fin 2)).val = 1 := by
      have h0bound := (c.point (0 : Fin 2)).isLt
      have h1bound := (c.point (1 : Fin 2)).isLt
      omega
    have h0 : c.point (0 : Fin 2) = 0 := Fin.ext h0val
    have h1 : c.point (1 : Fin 2) = 1 := Fin.ext h1val
    have hsum :
        (∑ i : Fin 1,
          (ENNReal.ofReal ‖u (c.point i.succ) -
            u (c.point i.castSucc)‖).rpow r) = cap.rpow r := by
      rw [Fin.sum_univ_succ]
      simp [cap, h0, h1]
    rw [finiteChainVariation, hsum]
    calc
      _ = cap.rpow (r * r⁻¹) := (ENNReal.rpow_mul cap r r⁻¹).symm
      _ = cap := by
        rw [mul_inv_cancel₀ hr.ne']
        exact ENNReal.rpow_one cap
  let c : StrictOrderedChain (Fin 2) 1 :=
    { point := fun i => i
      strictMono := strictMono_id }
  have hcvalue : finiteChainVariation r u c = cap := twoChainValue c
  have hlower : cap ≤ orderedRVariation r u := by
    rw [← hcvalue]
    exact finiteChainVariation_le_orderedRVariation r u c
  have hupper : orderedRVariation r u ≤ cap := by
    have hbound' := Fintype.card_le_of_injective chain.point chain.strictMono.injective
    have hbound : length + 1 ≤ 2 := by
      calc
        length + 1 = Fintype.card (Fin (length + 1)) := (Fintype.card_fin _).symm
        _ ≤ Fintype.card (Fin 2) := hbound'
        _ = 2 := Fintype.card_fin 2
    by_cases hlength : length = 1
    · subst length
      rw [hmax, twoChainValue]
    · have hzero : length = 0 := by omega
      have hchainzero : finiteChainVariation r u chain = 0 := by
        subst length
        unfold finiteChainVariation
        rw [Fin.sum_univ_zero]
        exact ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)
      have hvariationzero : orderedRVariation r u = 0 := hmax.trans hchainzero
      have hcapzero : cap = 0 := by
        apply le_antisymm
        · simpa [hvariationzero] using hlower
        · exact zero_le
      rw [hvariationzero, hcapzero]
  apply le_antisymm hupper hlower

/-- A single-operator `Lᵖ` estimate transfers with the same constant. -/
theorem transferFiniteKernelOperatorNorm
    {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (K : ℤ →₀ ℂ) (C : NNReal)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖finiteKernelConvolution K g j‖ₑ) ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    eLpNorm (finiteKernelSystemOperator S K f) p S.μ ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  classical
  let K₂ : Fin 2 → ℤ →₀ ℂ := fun i => if i = 0 then 0 else K
  have hK0 : K₂ 0 = 0 := by simp [K₂]
  have hK1 : K₂ 1 = K := by simp [K₂]
  have hrpos : 0 < (1 : ℝ) := by norm_num
  have hdiscVar : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p 1 K₂ g ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖g j‖ₑ) := by
    intro g hg
    have heq : finiteKernelDiscreteVariation 1 K₂ g =
        fun j => ENNReal.ofReal ‖finiteKernelConvolution K g j‖ := by
      funext j
      change orderedRVariation (1 : ℝ)
        (fun i : Fin 2 => finiteKernelConvolution (K₂ i) g j) = _
      rw [orderedRVariation_finTwo_eq 1 hrpos]
      simp [hK0, hK1, finiteKernelConvolution, ofReal_norm]
    simpa [finiteKernelDiscreteVariationLpNorm, heq] using hdisc g hg
  have hfinite := transferFiniteKernelVariation S p 1 hp1 hpTop (by norm_num) (by norm_num)
    K₂ C hdiscVar f hf
  have hsysVar : finiteKernelSystemVariation S 1 K₂ f =
      fun x => ENNReal.ofReal ‖finiteKernelSystemOperator S K f x‖ := by
    funext x
    change orderedRVariation (1 : ℝ)
      (fun i : Fin 2 => finiteKernelSystemOperator S (K₂ i) f x) = _
    rw [orderedRVariation_finTwo_eq 1 hrpos]
    simp [hK0, hK1, finiteKernelSystemOperator, ofReal_norm]
  have hsysMeas : AEStronglyMeasurable
      (finiteKernelSystemOperator S K f) S.μ := by
    exact aemeasurable_finiteKernelSystemOperator S K f hf.aestronglyMeasurable
      |>.aestronglyMeasurable
  have hnormEq := extendedLpNorm_eq_eLpNorm S.μ p
    (finiteKernelSystemOperator S K f)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)) (ne_of_lt hpTop) hsysMeas
  have hfinite' :
      extendedLpNorm S.μ p (finiteKernelSystemVariation S 1 K₂ f) ≤
        (C : ℝ≥0∞) * eLpNorm f p S.μ := by
    simpa [finiteKernelSystemVariationLpNorm] using hfinite
  rw [hsysVar] at hfinite'
  rw [← hnormEq]
  simpa [extendedLpNorm_eq_eLpNorm S.μ p f
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)) (ne_of_lt hpTop)
      hf.aestronglyMeasurable] using hfinite'

/-- The finite-exhaustion truncations are a.e. measurable when each member
of the family is a.e. measurable. -/
theorem aemeasurable_orderedRVariationTruncFun
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (Exh : Set.FiniteExhaustion (Set.univ : Set I))
    (μ : Measure X) (r : ℝ) (F : I → X → ℂ)
    (hF : ∀ i, AEMeasurable (F i) μ)
    (N : ℕ) :
    AEMeasurable (orderedRVariationTruncFun Exh r F N) μ := by
  classical
  unfold orderedRVariationTruncFun orderedRVariationTrunc
  apply AEMeasurable.iSup
  intro length
  let _ : Countable (StrictOrderedChain I length) :=
    (strictOrderedChainEmbedding length).countable
  apply AEMeasurable.iSup
  intro chain
  by_cases hchain : ∀ i, chain.point i ∈ Exh N
  · have hfun :
        (fun x => if ∀ i, chain.point i ∈ Exh N then
          finiteChainVariation r (fun i => F i x) chain else 0) =
          finiteChainVariationFun r F chain := by
      funext x
      simp [hchain, finiteChainVariationFun]
    rw [hfun]
    exact aemeasurable_finiteChainVariationFun μ r F hF chain
  · simp [hchain]

/-- Monotone convergence for positive powers of the finite-exhaustion
truncations, in the a.e.-measurable form needed for `MemLp` inputs. -/
theorem lintegral_orderedRVariationFun_rpow_eq_iSup_trunc_ae
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (Exh : Set.FiniteExhaustion (Set.univ : Set I))
    (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : I → X → ℂ) (hF : ∀ i, AEMeasurable (F i) μ) :
    ∫⁻ x, (orderedRVariationFun r F x) ^ p ∂μ =
      ⨆ N : ℕ,
        ∫⁻ x, (orderedRVariationTruncFun Exh r F N x) ^ p ∂μ := by
  have hrepr : (fun x => (orderedRVariationFun r F x) ^ p) =
      fun x => ⨆ N : ℕ, (orderedRVariationTruncFun Exh r F N x) ^ p := by
    funext x
    rw [orderedRVariationFun_eq_iSup_trunc Exh r F]
    change ENNReal.orderIsoRpow p hp
      (⨆ N : ℕ, orderedRVariationTruncFun Exh r F N x) = _
    rw [OrderIso.map_iSup]
    rfl
  rw [hrepr]
  apply lintegral_iSup'
  · intro N
    exact (ENNReal.continuous_rpow_const (y := p)).measurable.aemeasurable
      |>.comp_aemeasurable
        (aemeasurable_orderedRVariationTruncFun Exh μ r F hF N)
  · filter_upwards [] with x
    intro N M hNM
    exact (ENNReal.orderIsoRpow p hp).monotone
      (monotone_orderedRVariationTruncFun Exh r F hNM x)

/-- Countable-family finite-kernel transference. If one constant works for
every restriction to the members of a finite exhaustion, it works for the
full countable family. -/
theorem transferCountableFiniteKernelVariation
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (S : InvertibleSystem X) (p r : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (hr1 : 1 ≤ r) (hrTop : r < ∞)
    (K : I → ℤ →₀ ℂ) (C : NNReal)
    (Exh : Set.FiniteExhaustion (Set.univ : Set I))
    (hdisc : ∀ N : ℕ, ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p r
          (fun i : Exh N => K i.1) g ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    extendedLpNorm S.μ p
        (finiteKernelSystemVariation S r.toReal K f) ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hptop : p ≠ ∞ := ne_of_lt hpTop
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  let F : I → X → ℂ := fun i => finiteKernelSystemOperator S (K i) f
  have hF : ∀ i, AEMeasurable (F i) S.μ := by
    intro i
    exact aemeasurable_finiteKernelSystemOperator S (K i) f hf.aestronglyMeasurable
  have hmoment := lintegral_orderedRVariationFun_rpow_eq_iSup_trunc_ae
    Exh S.μ r.toReal p.toReal hq F hF
  have hN (N : ℕ) :
      extendedLpNorm S.μ p (orderedRVariationTruncFun Exh r.toReal F N) ≤
        (C : ℝ≥0∞) * eLpNorm f p S.μ := by
    letI : Fintype (Exh N) := Fintype.ofFinite (Exh N)
    let KN : (Exh N) → ℤ →₀ ℂ := fun i => K i.1
    have hfinite := transferFiniteKernelVariation S p r hp1 hpTop hr1 hrTop
      KN C (by
        intro g hg
        exact hdisc N g hg) f hf
    have hvariation :
        finiteKernelSystemVariation S r.toReal KN f =
          orderedRVariationTruncFun Exh r.toReal F N := by
      funext x
      change orderedRVariation r.toReal (fun i : Exh N => F i x) = _
      rw [← orderedRVariationTrunc_eq_subtype Exh r.toReal (fun i => F i x) N]
      rfl
    change extendedLpNorm S.μ p (finiteKernelSystemVariation S r.toReal KN f) ≤ _ at hfinite
    rw [hvariation] at hfinite
    exact hfinite
  have hmomentBound :
      (⨆ N : ℕ,
        ∫⁻ x, (orderedRVariationTruncFun Exh r.toReal F N x) ^ p.toReal ∂S.μ) ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    apply iSup_le
    intro N
    have hpow := ENNReal.rpow_le_rpow (hN N) hq.le
    have hnormEq := extendedLpNorm_rpow S.μ p
      (orderedRVariationTruncFun Exh r.toReal F N) hp0 hptop
    simpa only [hnormEq] using hpow
  have hfullMoment :
      ∫⁻ x, (finiteKernelSystemVariation S r.toReal K f x) ^ p.toReal ∂S.μ ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    have hfull :
        finiteKernelSystemVariation S r.toReal K f = orderedRVariationFun r.toReal F := by
      funext x
      rfl
    rw [hfull, hmoment]
    exact hmomentBound
  have hnormPow :
      extendedLpNorm S.μ p (finiteKernelSystemVariation S r.toReal K f) ^ p.toReal ≤
        ((C : ℝ≥0∞) * eLpNorm f p S.μ) ^ p.toReal := by
    rw [extendedLpNorm_rpow S.μ p _ hp0 hptop]
    exact hfullMoment
  exact (ENNReal.rpow_le_rpow_iff hq).mp hnormPow

end

end FractionalPrimes.Literature.Ergodic

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

/-- Public blueprint name for finite-kernel transference. -/
theorem transferFiniteKernels
    {I X : Type*} [Fintype I] [LinearOrder I] [MeasurableSpace X]
    (S : InvertibleSystem X) (p r : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (hr1 : 1 ≤ r) (hrTop : r < ∞)
    (K : I → ℤ →₀ ℂ) (C : NNReal)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      Literature.Ergodic.finiteKernelDiscreteVariationLpNorm p r K g ≤
        (C : ℝ≥0∞) * Literature.Ergodic.extendedLpNorm
          (Measure.count : Measure ℤ) p (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    Literature.Ergodic.finiteKernelSystemVariationLpNorm S p r K f ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  exact Literature.Ergodic.transferFiniteKernelVariation S p r hp1 hpTop
    hr1 hrTop K C hdisc f hf

end FractionalPrimes
