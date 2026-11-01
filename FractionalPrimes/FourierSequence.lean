module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

public import FractionalPrimes.Operators
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open Filter
open scoped Pointwise Topology

/-- Multiplication by an essentially bounded complex function is bounded on
every `Lᵖ` seminorm, with operator bound given by the pointwise bound. -/
theorem eLpNorm_mul_left_le_of_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℂ) (p : ENNReal) (C : NNReal)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hbound : ∀ᵐ x ∂μ, ‖g x‖₊ ≤ C) :
    eLpNorm (fun x => g x * f x) p μ ≤ (C : ENNReal) * eLpNorm f p μ := by
  calc
    eLpNorm (fun x => g x * f x) p μ ≤
        eLpNorm (fun x => (C : ℂ) * f x) p μ := by
      apply eLpNorm_mono_nnnorm_ae (hg.mul hf)
      filter_upwards [hbound] with x hx
      calc
        ‖g x * f x‖₊ = ‖g x‖₊ * ‖f x‖₊ := by simp
        _ ≤ C * ‖f x‖₊ := mul_le_mul_of_nonneg_right hx (by positivity)
        _ = ‖(C : ℂ) * f x‖₊ := by simp
    _ = (C : ENNReal) * eLpNorm f p μ := by
      have hfun : (fun x => (C : ℂ) * f x) = (C : ℂ) • f := by
        ext x
        simp [smul_eq_mul]
      rw [hfun, eLpNorm_const_smul]
      congr 1
      have hn : ‖(C : ℂ)‖₊ = C := by
        apply Subtype.ext
        change ‖(C : ℂ)‖ = (C : ℝ)
        rw [Complex.norm_real]
        exact abs_of_nonneg (by positivity)
      exact congrArg (fun x : NNReal => (x : ENNReal)) hn

theorem continuous_nnnorm_le_of_eLpNormEssSup_le
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [Measure.IsOpenPosMeasure μ]
    (f : α → ℂ) (hf : Continuous f) (C : NNReal)
    (hsup : eLpNormEssSup f μ ≤ (C : ENNReal)) :
    ∀ x, ‖f x‖₊ ≤ C := by
  have hbound : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f μ] with x hx
    exact ENNReal.coe_le_coe.mp (by simpa [enorm_eq_nnnorm] using hx.trans hsup)
  have hboundR : ∀ᵐ x ∂μ, ‖f x‖ ≤ (C : ℝ) :=
    hbound.mono fun x hx => NNReal.coe_le_coe.mp hx
  have hnull : μ {x | (C : ℝ) < ‖f x‖} = 0 := by
    have hgood : ∀ᵐ x ∂μ, ¬ (C : ℝ) < ‖f x‖ :=
      hboundR.mono fun x hx => not_lt.mpr hx
    simpa using (ae_iff.mp hgood)
  have hnorm : Continuous (fun x => ‖f x‖) := by fun_prop
  have hopen : IsOpen {x | (C : ℝ) < ‖f x‖} :=
    isOpen_lt continuous_const hnorm
  intro x
  by_contra hx
  have hxlt : (C : ℝ) < ‖f x‖ :=
    NNReal.coe_lt_coe.mp (lt_of_not_ge hx)
  have hpos : 0 < μ {x | (C : ℝ) < ‖f x‖} := hopen.measure_pos μ ⟨x, hxlt⟩
  rw [hnull] at hpos
  exact (lt_irrefl 0) hpos

/-- A finite trigonometric polynomial with coefficients indexed by the
integer frequencies in `s`. -/
noncomputable def integerFourierPolynomial
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑ n ∈ s, a n * fourier (T := (1 : ℝ)) n x

theorem integerFourierPolynomial_nnnorm_le_of_eLpNormEssSup_le
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ)
    (C : NNReal)
    (hsup : eLpNormEssSup (integerFourierPolynomial (hT := hT) s a)
      (@AddCircle.haarAddCircle (1 : ℝ) hT) ≤ (C : ENNReal)) :
    ∀ x, ‖integerFourierPolynomial (hT := hT) s a x‖₊ ≤ C := by
  have hcont : Continuous (integerFourierPolynomial (hT := hT) s a) := by
    unfold integerFourierPolynomial
    fun_prop
  exact continuous_nnnorm_le_of_eLpNormEssSup_le
    (integerFourierPolynomial (hT := hT) s a) hcont C hsup

theorem integerKernelFourierTransform_eq_integerFourierPolynomial_neg_of_finiteSupport
    (K : IntegerL1Kernel) (s : Finset ℤ)
    (hs : ∀ m ∉ s, K.coeff m = 0) (ξ : ℝ) :
    integerKernelFourierTransform K ξ =
      integerFourierPolynomial (hT := ⟨by norm_num⟩) s K.coeff
        ((-ξ : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  have hzero (m : ℤ) (hm : m ∉ s) :
      K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ)) = 0 := by
    rw [hs m hm]
    simp
  rw [integerKernelFourierTransform, tsum_eq_sum (s := s) hzero]
  unfold integerFourierPolynomial
  apply Finset.sum_congr rfl
  intro m hm
  have hphase :
      unitFrequencyPhase (-ξ * (m : ℝ)) =
        fourier (T := (1 : ℝ)) m ((-ξ : ℝ) : AddCircle (1 : ℝ)) := by
    calc
      unitFrequencyPhase (-ξ * (m : ℝ)) =
          unitFrequencyPhase ((m : ℝ) * (-ξ)) := by congr 1 <;> ring
      _ = fourier (T := (1 : ℝ)) m ((-ξ : ℝ) : AddCircle (1 : ℝ)) :=
        unitFrequencyPhase_int_mul_eq_addCircleFourier m (-ξ)
  rw [hphase]

theorem eLpNormEssSup_integerFourierPolynomial_neg
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    eLpNormEssSup
        (fun x : AddCircle (1 : ℝ) =>
          integerFourierPolynomial (hT := hT) s a (-x))
        (@AddCircle.haarAddCircle (1 : ℝ) hT) =
      eLpNormEssSup (integerFourierPolynomial (hT := hT) s a)
        (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
  let μ := @AddCircle.haarAddCircle (1 : ℝ) hT
  let P := integerFourierPolynomial (hT := hT) s a
  have hcont : Continuous P := by
    unfold P integerFourierPolynomial
    fun_prop
  have hpres : MeasurePreserving (fun x : AddCircle (1 : ℝ) => -x) μ μ :=
    Measure.measurePreserving_neg μ
  have hmap := eLpNormEssSup_map_measure
    (hcont.aestronglyMeasurable : AEStronglyMeasurable P
      (Measure.map (fun x : AddCircle (1 : ℝ) => -x) μ))
    hpres.measurable.aemeasurable
  rw [hpres.map_eq] at hmap
  exact hmap.symm

noncomputable def finiteIntegerKernelFourierSymbol
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    AddCircle (1 : ℝ) → ℂ :=
  fun x => integerFourierPolynomial (hT := hT) s a (-x)

theorem eLpNormEssSup_finiteIntegerKernelFourierSymbol
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    eLpNormEssSup (finiteIntegerKernelFourierSymbol (hT := hT) s a)
        (@AddCircle.haarAddCircle (1 : ℝ) hT) =
      eLpNormEssSup (integerFourierPolynomial (hT := hT) s a)
        (@AddCircle.haarAddCircle (1 : ℝ) hT) :=
  eLpNormEssSup_integerFourierPolynomial_neg (hT := hT) s a

theorem integerKernelFourierTransform_eq_finiteSymbol_of_finiteSupport
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel) (s : Finset ℤ)
    (hs : ∀ m ∉ s, K.coeff m = 0) (ξ : ℝ) :
    integerKernelFourierTransform K ξ =
      finiteIntegerKernelFourierSymbol (hT := hT) s K.coeff
        ((ξ : ℝ) : AddCircle (1 : ℝ)) := by
  simpa [finiteIntegerKernelFourierSymbol, AddCircle.coe_neg] using
    integerKernelFourierTransform_eq_integerFourierPolynomial_neg_of_finiteSupport
      K s hs ξ

theorem integerFourierPolynomial_norm_le
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ)
    (x : AddCircle (1 : ℝ)) :
    ‖integerFourierPolynomial (hT := hT) s a x‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  unfold integerFourierPolynomial
  calc
    ‖∑ n ∈ s, a n * fourier (T := (1 : ℝ)) n x‖ ≤
        ∑ n ∈ s, ‖a n * fourier (T := (1 : ℝ)) n x‖ := norm_sum_le _ _
    _ = ∑ n ∈ s, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul]
      have hnorm : ‖fourier (T := (1 : ℝ)) n x‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      rw [hnorm, mul_one]

theorem integerFourierPolynomial_memLp
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    MemLp (integerFourierPolynomial (hT := hT) s a) 2
      (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
  have hmeas : AEStronglyMeasurable
      (integerFourierPolynomial (hT := hT) s a)
      (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
    unfold integerFourierPolynomial
    fun_prop
  apply MemLp.of_bound hmeas (∑ n ∈ s, ‖a n‖)
  filter_upwards with x
  exact integerFourierPolynomial_norm_le (hT := hT) s a x

theorem integerFourierPolynomial_memLp_top
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    MemLp (integerFourierPolynomial (hT := hT) s a) ⊤
      (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
  have hmeas : AEStronglyMeasurable
      (integerFourierPolynomial (hT := hT) s a)
      (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
    unfold integerFourierPolynomial
    fun_prop
  apply MemLp.of_bound hmeas (∑ n ∈ s, ‖a n‖)
  filter_upwards with x
  exact integerFourierPolynomial_norm_le (hT := hT) s a x

theorem integerFourierPolynomial_mul_memLp
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) :
    MemLp
      (fun x : AddCircle (1 : ℝ) =>
        integerFourierPolynomial (hT := hT) s a x *
          integerFourierPolynomial (hT := hT) t b x)
      2 (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
  exact (integerFourierPolynomial_memLp_top (hT := hT) s a).mul
    (integerFourierPolynomial_memLp (hT := hT) t b)

noncomputable def integerFourierPolynomialL2
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) hT) :=
  (integerFourierPolynomial_memLp (hT := hT) s a).toLp
    (integerFourierPolynomial (hT := hT) s a)

/-- The Fourier coefficients of a finite trigonometric polynomial recover
its coefficients, with zero extension outside its frequency set. -/
theorem fourierCoeff_integerFourierPolynomial
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) :
    fourierCoeff (integerFourierPolynomial (hT := hT) s a) k =
      ∑ n ∈ s, if n = k then a n else 0 := by
  classical
  unfold integerFourierPolynomial
  have hterm (n : ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) =>
        a n * fourier (T := (1 : ℝ)) n x)
        (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
    apply Integrable.of_bound (by fun_prop) ‖a n‖
    filter_upwards with x
    rw [norm_mul]
    have hnorm : ‖fourier (T := (1 : ℝ)) n x‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    rw [hnorm, mul_one]
  have hsumfun :
      (fun x : AddCircle (1 : ℝ) =>
        ∑ n ∈ s, a n * fourier (T := (1 : ℝ)) n x) =
      ∑ n ∈ s, (fun x : AddCircle (1 : ℝ) =>
        a n * fourier (T := (1 : ℝ)) n x) := by
    funext x
    simp
  rw [hsumfun]
  have hcoeffsum := fourierCoeff.sum s
    (fun n x => a n * fourier (T := (1 : ℝ)) n x)
    (fun n hn => hterm n)
  calc
    (fourierCoeff
        (∑ n ∈ s, fun x : AddCircle (1 : ℝ) =>
          a n * fourier (T := (1 : ℝ)) n x)) k =
      (∑ n ∈ s, fourierCoeff
        (fun x : AddCircle (1 : ℝ) =>
          a n * fourier (T := (1 : ℝ)) n x)) k := congrFun hcoeffsum k
    _ = ∑ n ∈ s, fourierCoeff
        (fun x : AddCircle (1 : ℝ) =>
          a n * fourier (T := (1 : ℝ)) n x) k := by simp
    _ = ∑ n ∈ s, if n = k then a n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [fourierCoeff.const_mul, fourierCoeff_fourier]
      simp [Pi.single_apply, eq_comm]

theorem fourierBasis_repr_integerFourierPolynomialL2
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) :
    (fourierBasis (T := (1 : ℝ))).repr
        (integerFourierPolynomialL2 (hT := hT) s a) k =
      ∑ n ∈ s, if n = k then a n else 0 := by
  rw [fourierBasis_repr]
  have hae := MemLp.coeFn_toLp
    (integerFourierPolynomial_memLp (hT := hT) s a)
  change fourierCoeff
    ((integerFourierPolynomial_memLp (hT := hT) s a).toLp
      (integerFourierPolynomial (hT := hT) s a) :
        AddCircle (1 : ℝ) → ℂ) k = _
  rw [fourierCoeff_congr_ae hae]
  exact fourierCoeff_integerFourierPolynomial (hT := hT) s a k

/-- Multiplication of finite Fourier polynomials induces finite convolution
of their coefficient families. -/
theorem fourierCoeff_mul_integerFourierPolynomial
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (k : ℤ) :
    fourierCoeff
      (fun x : AddCircle (1 : ℝ) =>
        integerFourierPolynomial (hT := hT) s a x *
          integerFourierPolynomial (hT := hT) t b x) k =
      ∑ i ∈ s, ∑ j ∈ t,
        if i + j = k then a i * b j else 0 := by
  classical
  have hprod :
      (fun x : AddCircle (1 : ℝ) =>
        integerFourierPolynomial (hT := hT) s a x *
          integerFourierPolynomial (hT := hT) t b x) =
      ∑ i ∈ s, ∑ j ∈ t,
        (fun x : AddCircle (1 : ℝ) =>
          (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) := by
    funext x
    simp only [integerFourierPolynomial]
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (a i * fourier (T := (1 : ℝ)) i x) *
          (b j * fourier (T := (1 : ℝ)) j x) =
        (a i * b j) *
          (fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) j x) := by ring
      _ = (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x := by
        rw [← fourier_add]
  rw [hprod]
  have hterm (i j : ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) =>
        (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)
        (@AddCircle.haarAddCircle (1 : ℝ) hT) := by
    apply Integrable.of_bound (by fun_prop) ‖a i * b j‖
    filter_upwards with x
    rw [norm_mul]
    have hnorm : ‖fourier (T := (1 : ℝ)) (i + j) x‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    rw [hnorm, mul_one]
  have houterFun :
      (∑ i ∈ s, ∑ j ∈ t,
        (fun x : AddCircle (1 : ℝ) =>
          (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)) =
      ∑ i ∈ s, (fun x : AddCircle (1 : ℝ) =>
        ∑ j ∈ t,
          (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) := by
    apply Finset.sum_congr rfl
    intro i hi
    funext x
    simp
  rw [houterFun]
  have hcoeffsum := fourierCoeff.sum s
    (fun i x => ∑ j ∈ t,
      (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)
    (fun i hi => by
      have hinnerFun :
          (fun x : AddCircle (1 : ℝ) =>
            ∑ j ∈ t,
              (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) =
          ∑ j ∈ t, (fun x : AddCircle (1 : ℝ) =>
            (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) := by
        funext x
        simp
      rw [hinnerFun]
      apply integrable_finsetSum'
      intro j hj
      exact hterm i j)
  calc
      (fourierCoeff
        (∑ i ∈ s, fun x : AddCircle (1 : ℝ) =>
          ∑ j ∈ t,
            (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)) k =
      (∑ i ∈ s, fourierCoeff
        (fun x : AddCircle (1 : ℝ) =>
          ∑ j ∈ t,
            (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)) k :=
      congrFun hcoeffsum k
    _ = ∑ i ∈ s, fourierCoeff
        (fun x : AddCircle (1 : ℝ) =>
          ∑ j ∈ t,
            (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) k := by simp
    _ = ∑ i ∈ s, ∑ j ∈ t,
        if i + j = k then a i * b j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hinnerFun :
          (fun x : AddCircle (1 : ℝ) =>
            ∑ j ∈ t,
              (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) =
          ∑ j ∈ t, (fun x : AddCircle (1 : ℝ) =>
            (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) := by
        funext x
        simp
      rw [hinnerFun]
      have hinner := fourierCoeff.sum t
        (fun j x => (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)
        (fun j hj => hterm i j)
      calc
        fourierCoeff
            (∑ j ∈ t, (fun x : AddCircle (1 : ℝ) =>
              (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)) k =
          (∑ j ∈ t, fourierCoeff
            (fun x : AddCircle (1 : ℝ) =>
              (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x)) k :=
          congrFun hinner k
        _ = ∑ j ∈ t, fourierCoeff
            (fun x : AddCircle (1 : ℝ) =>
              (a i * b j) * fourier (T := (1 : ℝ)) (i + j) x) k := by simp
        _ = ∑ j ∈ t, if i + j = k then a i * b j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [fourierCoeff.const_mul, fourierCoeff_fourier]
          simp [Pi.single_apply, eq_comm]

noncomputable def integerFourierPolynomialProductL2
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) hT) :=
  (integerFourierPolynomial_mul_memLp (hT := hT) s t a b).toLp
    (fun x : AddCircle (1 : ℝ) =>
      integerFourierPolynomial (hT := hT) s a x *
        integerFourierPolynomial (hT := hT) t b x)

theorem integerFourierPolynomialProductL2_enorm_le
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (C : NNReal)
    (hbound : ∀ x : AddCircle (1 : ℝ),
      ‖integerFourierPolynomial (hT := hT) s a x‖₊ ≤ C) :
    ‖integerFourierPolynomialProductL2 (hT := hT) s t a b‖ₑ ≤
      (C : ENNReal) * ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ := by
  rw [integerFourierPolynomialProductL2, Lp.enorm_toLp,
    integerFourierPolynomialL2, Lp.enorm_toLp]
  exact eLpNorm_mul_left_le_of_bound
    (@AddCircle.haarAddCircle (1 : ℝ) hT)
    (integerFourierPolynomial (hT := hT) t b)
    (integerFourierPolynomial (hT := hT) s a) 2 C
    (integerFourierPolynomial_memLp (hT := hT) t b).aestronglyMeasurable
    (integerFourierPolynomial_memLp_top (hT := hT) s a).aestronglyMeasurable
    (by filter_upwards with x; exact hbound x)

/-- The finite Fourier multiplier estimate with its exact essential-supremum
constant, expressed in `ENNReal` so it passes directly to limits. -/
theorem integerFourierPolynomialProductL2_enorm_le_of_essSup
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) :
    ‖integerFourierPolynomialProductL2 (hT := hT) s t a b‖ₑ ≤
      eLpNormEssSup (integerFourierPolynomial (hT := hT) s a)
          (@AddCircle.haarAddCircle (1 : ℝ) hT) *
        ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ := by
  let μ := @AddCircle.haarAddCircle (1 : ℝ) hT
  let P := integerFourierPolynomial (hT := hT) s a
  let Q := integerFourierPolynomial (hT := hT) t b
  have hraw := eLpNorm_le_eLpNorm_mul_eLpNorm_top_of_pos
      (μ := μ) (f := Q) (g := P) (p := 2)
      (b := fun z w : ℂ => w * z) 1 (by fun_prop)
      (by filter_upwards with x; simp [mul_assoc, mul_comm]) (by norm_num)
  have htop := eLpNorm_exponent_top
    (integerFourierPolynomial_memLp_top (hT := hT) s a).aestronglyMeasurable
  rw [htop] at hraw
  have hmul :
      eLpNorm (fun x => P x * Q x) 2 μ ≤
        eLpNorm Q 2 μ * eLpNormEssSup P μ := by
    simpa [P, Q, one_mul, mul_assoc] using hraw
  rw [integerFourierPolynomialProductL2, Lp.enorm_toLp]
  have hinputNorm : eLpNorm Q 2 μ =
      ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ := by
    rw [integerFourierPolynomialL2, Lp.enorm_toLp]
  calc
    eLpNorm (fun x => P x * Q x) 2 μ ≤ eLpNorm Q 2 μ * eLpNormEssSup P μ := hmul
    _ = eLpNormEssSup P μ * eLpNorm Q 2 μ := by ac_rfl
    _ = eLpNormEssSup (integerFourierPolynomial (hT := hT) s a) μ *
        ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ := by
      rw [hinputNorm]

theorem fourierBasis_repr_integerFourierPolynomialProductL2
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (k : ℤ) :
    (fourierBasis (T := (1 : ℝ))).repr
        (integerFourierPolynomialProductL2 (hT := hT) s t a b) k =
      ∑ i ∈ s, ∑ j ∈ t,
        if i + j = k then a i * b j else 0 := by
  rw [fourierBasis_repr]
  have hmem := integerFourierPolynomial_mul_memLp
    (hT := hT) s t a b
  have hae := MemLp.coeFn_toLp hmem
  change fourierCoeff
    (hmem.toLp (fun x : AddCircle (1 : ℝ) =>
      integerFourierPolynomial (hT := hT) s a x *
        integerFourierPolynomial (hT := hT) t b x) :
        AddCircle (1 : ℝ) → ℂ) k = _
  rw [fourierCoeff_congr_ae hae]
  exact fourierCoeff_mul_integerFourierPolynomial (hT := hT) s t a b k

/-- The pair-sum coefficient formula for a product of finite Fourier
polynomials is the usual shifted finite convolution formula. -/
theorem finite_frequency_pair_sum_eq_shifted_convolution
    (s t : Finset ℤ) (a b : ℤ → ℂ) (k : ℤ) :
    (∑ i ∈ s, ∑ j ∈ t, if i + j = k then a i * b j else 0) =
      ∑ i ∈ s, if k - i ∈ t then a i * b (k - i) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  have hinner :
      (∑ j ∈ t, if i + j = k then a i * b j else 0) =
        if k - i ∈ t then a i * b (k - i) else 0 := by
    have hiff : ∀ j : ℤ, (i + j = k) ↔ j = k - i := by
      intro j
      omega
    simp_rw [hiff]
    simp
  exact hinner

theorem fourierBasis_repr_integerFourierPolynomialProductL2_eq_shiftedConvolution
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (k : ℤ) :
    (fourierBasis (T := (1 : ℝ))).repr
        (integerFourierPolynomialProductL2 (hT := hT) s t a b) k =
      ∑ i ∈ s, if k - i ∈ t then a i * b (k - i) else 0 := by
  rw [fourierBasis_repr_integerFourierPolynomialProductL2]
  exact finite_frequency_pair_sum_eq_shifted_convolution s t a b k

noncomputable def integerSequenceToCircleL2
    {hT : Fact (0 < (1 : ℝ))} (c : lp (fun _ : ℤ => ℂ) 2) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) hT) :=
  (fourierBasis (T := (1 : ℝ))).repr.symm c

theorem norm_integerSequenceToCircleL2
    {hT : Fact (0 < (1 : ℝ))} (c : lp (fun _ : ℤ => ℂ) 2) :
    ‖integerSequenceToCircleL2 (hT := hT) c‖ = ‖c‖ := by
  exact (fourierBasis (T := (1 : ℝ))).repr.symm.norm_map c

theorem enorm_integerSequenceToCircleL2
    {hT : Fact (0 < (1 : ℝ))} (c : lp (fun _ : ℤ => ℂ) 2) :
    ‖integerSequenceToCircleL2 (hT := hT) c‖ₑ = ‖c‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact congrArg (fun x : NNReal => (x : ENNReal))
    (NNReal.eq (norm_integerSequenceToCircleL2 (hT := hT) c))

theorem fourierCoeff_integerSequenceToCircleL2
    {hT : Fact (0 < (1 : ℝ))} (c : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    fourierCoeff (integerSequenceToCircleL2 (hT := hT) c) n = c n := by
  change fourierCoeff ((fourierBasis (T := (1 : ℝ))).repr.symm c) n = c n
  rw [← fourierBasis_repr (T := (1 : ℝ))]
  simp

noncomputable def finiteIntegerSequenceL2
    (s : Finset ℤ) (a : ℤ → ℂ) : lp (fun _ : ℤ => ℂ) 2 := by
  let c : ℤ → ℂ := fun n => if n ∈ s then a n else 0
  have hsupp : {n | c n ≠ 0} ⊆ (s : Set ℤ) := by
    intro n hn
    by_contra hnot
    have hmem : n ∈ s ∧ a n ≠ 0 := by simpa [c] using hn
    exact hnot hmem.1
  have hmem0 : Memℓp c 0 :=
    memℓp_zero (s.finite_toSet.subset hsupp)
  exact ⟨c, hmem0.of_exponent_ge zero_le⟩

theorem finiteIntegerSequenceL2_apply
    (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) :
    finiteIntegerSequenceL2 s a k = if k ∈ s then a k else 0 := by
  classical
  simp [finiteIntegerSequenceL2]

theorem finiteIntegerSequenceL2_eq_sum_single
    (s : Finset ℤ) (f : lp (fun _ : ℤ => ℂ) 2) :
    finiteIntegerSequenceL2 s f =
      ∑ i ∈ s, lp.single (2 : ENNReal) i (f i) := by
  classical
  apply lp.ext
  funext k
  rw [finiteIntegerSequenceL2_apply, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

theorem finiteIntegerSequenceL2_sub
    (s : Finset ℤ) (b c : ℤ → ℂ) :
    finiteIntegerSequenceL2 s (fun k => b k - c k) =
      finiteIntegerSequenceL2 s b - finiteIntegerSequenceL2 s c := by
  apply lp.ext
  funext k
  by_cases hk : k ∈ s <;> simp [finiteIntegerSequenceL2_apply, hk]

/-- Enlarging the finite support set does not change a sequence when the
coefficient function is taken to be the original truncated sequence. -/
theorem finiteIntegerSequenceL2_truncate_of_subset
    (s u : Finset ℤ) (b : ℤ → ℂ) (hsu : s ⊆ u) :
    finiteIntegerSequenceL2 u
        (fun k => finiteIntegerSequenceL2 s b k) =
      finiteIntegerSequenceL2 s b := by
  apply lp.ext
  funext k
  by_cases hks : k ∈ s
  · have hku : k ∈ u := hsu hks
    simp [finiteIntegerSequenceL2_apply, hks, hku]
  · by_cases hku : k ∈ u
    · simp [finiteIntegerSequenceL2_apply, hks, hku]
    · simp [finiteIntegerSequenceL2_apply, hks, hku]

/-- Symmetric finite truncations converge in `ℓ²` to an arbitrary element.
This is Mathlib's `lp.hasSum_single` along the cofinal symmetric-interval
filter. -/
theorem finiteIntegerSequenceL2_Icc_tendsto
    (f : lp (fun _ : ℤ => ℂ) 2) :
    Tendsto (fun N : ℕ =>
      finiteIntegerSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ)) f) atTop
      (𝓝 f) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hsum := lp.hasSum_single (p := (2 : ENNReal))
    (by norm_num : (2 : ENNReal) ≠ ⊤) f
  have hmono : Monotone
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro n k hnk
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hnk)
    · exact Int.ofNat_le.mpr hnk
  have hcofinal : ∀ z : ℤ, ∃ N : ℕ,
      z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro z
    refine ⟨z.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    have habs := abs_le.mp (le_rfl : |z| ≤ |z|)
    rw [Int.abs_eq_natAbs] at habs
    exact habs
  have hfilter : Tendsto
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    hmono.tendsto_atTop_finset hcofinal
  have hsumFilter : Tendsto
      (fun s : Finset ℤ => ∑ i ∈ s, lp.single (2 : ENNReal) i (f i))
      atTop (𝓝 f) := hsum
  have hcomp := hsumFilter.comp hfilter
  apply hcomp.congr'
  filter_upwards with N
  exact (finiteIntegerSequenceL2_eq_sum_single
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) f).symm

theorem integerSequenceToCircleL2_finite_eq_polynomialL2
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ) :
    integerSequenceToCircleL2 (hT := hT) (finiteIntegerSequenceL2 s a) =
      integerFourierPolynomialL2 (hT := hT) s a := by
  apply (fourierBasis (T := (1 : ℝ))).repr.injective
  ext k
  rw [fourierBasis_repr, fourierCoeff_integerSequenceToCircleL2,
    fourierBasis_repr_integerFourierPolynomialL2]
  simp [finiteIntegerSequenceL2]

/-- The finite discrete convolution of two coefficient families supported on
`s` and `t`, respectively. -/
noncomputable def finiteDiscreteConvolutionCoefficient
    (s t : Finset ℤ) (a b : ℤ → ℂ) (k : ℤ) : ℂ :=
  ∑ i ∈ s, if k - i ∈ t then a i * b (k - i) else 0

theorem finiteDiscreteConvolutionCoefficient_eq_zero_of_not_mem
    (s t : Finset ℤ) (a b : ℤ → ℂ) {k : ℤ}
    (hk : k ∉ s + t) :
    finiteDiscreteConvolutionCoefficient s t a b k = 0 := by
  classical
  unfold finiteDiscreteConvolutionCoefficient
  apply Finset.sum_eq_zero
  intro i hi
  have hki : k - i ∉ t := by
    intro hki
    apply hk
    rw [Finset.mem_add]
    exact ⟨i, hi, k - i, hki, by omega⟩
  simp [hki]

theorem finiteDiscreteConvolutionCoefficient_eq_add_sdiff
    (s u t : Finset ℤ) (a b : ℤ → ℂ) (hs : s ⊆ u) (k : ℤ) :
    finiteDiscreteConvolutionCoefficient u t a b k =
      finiteDiscreteConvolutionCoefficient s t a b k +
        finiteDiscreteConvolutionCoefficient (u \ s) t a b k := by
  unfold finiteDiscreteConvolutionCoefficient
  rw [← Finset.sum_sdiff hs]
  exact add_comm _ _

noncomputable def finiteDiscreteConvolutionSequenceL2
    (s t : Finset ℤ) (a b : ℤ → ℂ) : lp (fun _ : ℤ => ℂ) 2 :=
  finiteIntegerSequenceL2 (s + t)
    (finiteDiscreteConvolutionCoefficient s t a b)

theorem finiteDiscreteConvolutionSequenceL2_apply
    (s t : Finset ℤ) (a b : ℤ → ℂ) (k : ℤ) :
    finiteDiscreteConvolutionSequenceL2 s t a b k =
      finiteDiscreteConvolutionCoefficient s t a b k := by
  by_cases hk : k ∈ s + t
  · simp [finiteDiscreteConvolutionSequenceL2, finiteIntegerSequenceL2, hk]
  · rw [finiteDiscreteConvolutionSequenceL2, finiteIntegerSequenceL2]
    simp [hk, finiteDiscreteConvolutionCoefficient_eq_zero_of_not_mem s t a b hk]

theorem finiteDiscreteConvolutionSequenceL2_apply_eq_sum
    (s t : Finset ℤ) (a b : ℤ → ℂ) (k : ℤ) :
    finiteDiscreteConvolutionSequenceL2 s t a b k =
      ∑ i ∈ s, a i * finiteIntegerSequenceL2 t b (k - i) := by
  rw [finiteDiscreteConvolutionSequenceL2_apply]
  unfold finiteDiscreteConvolutionCoefficient
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : k - i ∈ t
  · simp [hik, finiteIntegerSequenceL2_apply]
  · simp [hik, finiteIntegerSequenceL2_apply]

theorem finiteDiscreteConvolutionSequenceL2_sub_input
    (s t : Finset ℤ) (a b c : ℤ → ℂ) :
    finiteDiscreteConvolutionSequenceL2 s t a (fun k => b k - c k) =
      finiteDiscreteConvolutionSequenceL2 s t a b -
        finiteDiscreteConvolutionSequenceL2 s t a c := by
  apply lp.ext
  funext k
  change finiteDiscreteConvolutionSequenceL2 s t a (fun k => b k - c k) k =
    finiteDiscreteConvolutionSequenceL2 s t a b k -
      finiteDiscreteConvolutionSequenceL2 s t a c k
  rw [finiteDiscreteConvolutionSequenceL2_apply_eq_sum,
    finiteDiscreteConvolutionSequenceL2_apply_eq_sum,
    finiteDiscreteConvolutionSequenceL2_apply_eq_sum]
  rw [finiteIntegerSequenceL2_sub t b c]
  rw [lp.coeFn_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.sub_apply, mul_sub]

theorem finiteDiscreteConvolutionSequenceL2_sub_eq_sdiff
    (s u t : Finset ℤ) (a b : ℤ → ℂ) (hs : s ⊆ u) :
    finiteDiscreteConvolutionSequenceL2 u t a b -
        finiteDiscreteConvolutionSequenceL2 s t a b =
      finiteDiscreteConvolutionSequenceL2 (u \ s) t a b := by
  apply lp.ext
  funext k
  change finiteDiscreteConvolutionSequenceL2 u t a b k -
      finiteDiscreteConvolutionSequenceL2 s t a b k =
    finiteDiscreteConvolutionSequenceL2 (u \ s) t a b k
  simp only [finiteDiscreteConvolutionSequenceL2_apply]
  rw [finiteDiscreteConvolutionCoefficient_eq_add_sdiff s u t a b hs k]
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem integerSequenceToCircleL2_finiteConvolution_eq_productL2
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) :
    integerSequenceToCircleL2 (hT := hT)
        (finiteDiscreteConvolutionSequenceL2 s t a b) =
      integerFourierPolynomialProductL2 (hT := hT) s t a b := by
  apply (fourierBasis (T := (1 : ℝ))).repr.injective
  ext k
  rw [fourierBasis_repr, fourierCoeff_integerSequenceToCircleL2,
    fourierBasis_repr_integerFourierPolynomialProductL2_eq_shiftedConvolution]
  by_cases hk : k ∈ s + t
  · simp [finiteDiscreteConvolutionSequenceL2, finiteIntegerSequenceL2, hk]
    rfl
  · simp [finiteDiscreteConvolutionSequenceL2, finiteIntegerSequenceL2, hk]
    exact (finiteDiscreteConvolutionCoefficient_eq_zero_of_not_mem
      s t a b hk).symm

theorem finiteDiscreteConvolutionSequenceL2_enorm_le_of_symbol_bound
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (C : NNReal)
    (hbound : ∀ x : AddCircle (1 : ℝ),
      ‖integerFourierPolynomial (hT := hT) s a x‖₊ ≤ C) :
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ ≤
      (C : ENNReal) * ‖finiteIntegerSequenceL2 t b‖ₑ := by
  calc
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ =
        ‖integerSequenceToCircleL2 (hT := hT)
          (finiteDiscreteConvolutionSequenceL2 s t a b)‖ₑ :=
      (enorm_integerSequenceToCircleL2 (hT := hT) _).symm
    _ = ‖integerFourierPolynomialProductL2 (hT := hT) s t a b‖ₑ :=
      congrArg (fun f : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) hT) => ‖f‖ₑ)
        (integerSequenceToCircleL2_finiteConvolution_eq_productL2
          (hT := hT) s t a b)
    _ ≤ (C : ENNReal) * ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ :=
      integerFourierPolynomialProductL2_enorm_le (hT := hT) s t a b C hbound
    _ = (C : ENNReal) *
        ‖integerSequenceToCircleL2 (hT := hT) (finiteIntegerSequenceL2 t b)‖ₑ := by
      rw [integerSequenceToCircleL2_finite_eq_polynomialL2]
    _ = (C : ENNReal) * ‖finiteIntegerSequenceL2 t b‖ₑ := by
      rw [enorm_integerSequenceToCircleL2]

theorem finiteDiscreteConvolutionSequenceL2_enorm_le_of_eLpNormEssSup_bound
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (C : NNReal)
    (hsup : eLpNormEssSup (integerFourierPolynomial (hT := hT) s a)
      (@AddCircle.haarAddCircle (1 : ℝ) hT) ≤ (C : ENNReal)) :
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ ≤
      (C : ENNReal) * ‖finiteIntegerSequenceL2 t b‖ₑ :=
  finiteDiscreteConvolutionSequenceL2_enorm_le_of_symbol_bound
    (hT := hT) s t a b C
    (integerFourierPolynomial_nnnorm_le_of_eLpNormEssSup_le
      (hT := hT) s a C hsup)

theorem finiteDiscreteConvolutionSequenceL2_enorm_le_of_finiteSymbol_bound
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) (C : NNReal)
    (hsup : eLpNormEssSup (finiteIntegerKernelFourierSymbol (hT := hT) s a)
      (@AddCircle.haarAddCircle (1 : ℝ) hT) ≤ (C : ENNReal)) :
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ ≤
      (C : ENNReal) * ‖finiteIntegerSequenceL2 t b‖ₑ := by
  apply finiteDiscreteConvolutionSequenceL2_enorm_le_of_eLpNormEssSup_bound
    (hT := hT) s t a b C
  rw [← eLpNormEssSup_finiteIntegerKernelFourierSymbol (hT := hT) s a]
  exact hsup

/-- Finite convolution obeys the exact Fourier multiplier bound, with the
essential supremum retained as an `ENNReal` constant. -/
theorem finiteDiscreteConvolutionSequenceL2_enorm_le_of_finiteSymbol_essSup
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ)
    (a b : ℤ → ℂ) :
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ ≤
      eLpNormEssSup (finiteIntegerKernelFourierSymbol (hT := hT) s a)
        (@AddCircle.haarAddCircle (1 : ℝ) hT) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
  calc
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ =
        ‖integerSequenceToCircleL2 (hT := hT)
          (finiteDiscreteConvolutionSequenceL2 s t a b)‖ₑ :=
      (enorm_integerSequenceToCircleL2 (hT := hT) _).symm
    _ = ‖integerFourierPolynomialProductL2 (hT := hT) s t a b‖ₑ :=
      congrArg (fun f : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) hT) => ‖f‖ₑ)
        (integerSequenceToCircleL2_finiteConvolution_eq_productL2
          (hT := hT) s t a b)
    _ ≤ eLpNormEssSup (integerFourierPolynomial (hT := hT) s a)
          (@AddCircle.haarAddCircle (1 : ℝ) hT) *
        ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ :=
      integerFourierPolynomialProductL2_enorm_le_of_essSup
        (hT := hT) s t a b
    _ = eLpNormEssSup (finiteIntegerKernelFourierSymbol (hT := hT) s a)
          (@AddCircle.haarAddCircle (1 : ℝ) hT) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
      rw [eLpNormEssSup_finiteIntegerKernelFourierSymbol (hT := hT) s a]
      have hinput :
          ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ =
            ‖finiteIntegerSequenceL2 t b‖ₑ := by
        calc
          ‖integerFourierPolynomialL2 (hT := hT) t b‖ₑ =
              ‖integerSequenceToCircleL2 (hT := hT)
                (finiteIntegerSequenceL2 t b)‖ₑ := by
            rw [integerSequenceToCircleL2_finite_eq_polynomialL2]
          _ = ‖finiteIntegerSequenceL2 t b‖ₑ :=
            enorm_integerSequenceToCircleL2 (hT := hT) _
      rw [hinput]

/-- Finite convolution is bounded by the `ℓ¹` norm of the kernel
coefficients. This is the Young-type stability estimate used to compare
finite truncations of an absolutely summable kernel. -/
theorem finiteDiscreteConvolutionSequenceL2_enorm_le_of_coeff_norm_sum
    {hT : Fact (0 < (1 : ℝ))} (s t : Finset ℤ) (a b : ℤ → ℂ) :
    ‖finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ ≤
      (∑ n ∈ s, ‖a n‖₊ : NNReal) * ‖finiteIntegerSequenceL2 t b‖ₑ := by
  apply finiteDiscreteConvolutionSequenceL2_enorm_le_of_symbol_bound
    (hT := hT) s t a b (∑ n ∈ s, ‖a n‖₊)
  intro x
  have hnorm := integerFourierPolynomial_norm_le (hT := hT) s a x
  exact NNReal.coe_le_coe.mp (by
    simpa only [← NNReal.coe_sum, ← coe_nnnorm] using hnorm)

theorem finiteDiscreteConvolutionSequenceL2_sub_enorm_le_of_coeff_norm_sum
    {hT : Fact (0 < (1 : ℝ))} (s u t : Finset ℤ)
    (a b : ℤ → ℂ) (hs : s ⊆ u) :
    ‖finiteDiscreteConvolutionSequenceL2 u t a b -
        finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ ≤
      (∑ n ∈ u \ s, ‖a n‖₊) * ‖finiteIntegerSequenceL2 t b‖ₑ := by
  calc
    ‖finiteDiscreteConvolutionSequenceL2 u t a b -
        finiteDiscreteConvolutionSequenceL2 s t a b‖ₑ =
      ‖finiteDiscreteConvolutionSequenceL2 (u \ s) t a b‖ₑ := by
        rw [finiteDiscreteConvolutionSequenceL2_sub_eq_sdiff s u t a b hs]
    _ ≤ (∑ n ∈ u \ s, ‖a n‖₊) *
        ‖finiteIntegerSequenceL2 t b‖ₑ :=
      finiteDiscreteConvolutionSequenceL2_enorm_le_of_coeff_norm_sum
        (hT := hT) (u \ s) t a b

/-- The symmetric finite truncations of an absolutely summable integer
kernel capture its full coefficient `ℓ¹` mass in the limit. -/
theorem integerKernel_norm_sum_Icc_tendsto (K : IntegerL1Kernel) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖K.coeff m‖)
      atTop (𝓝 (∑' m : ℤ, ‖K.coeff m‖)) := by
  have hmono : Monotone
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro n k hnk
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hnk)
    · exact Int.ofNat_le.mpr hnk
  have hcofinal : ∀ z : ℤ, ∃ N : ℕ, z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro z
    refine ⟨z.natAbs, ?_⟩
    have hz : |z| = (z.natAbs : ℤ) := Int.abs_eq_natAbs z
    rw [Finset.mem_Icc]
    have habs := abs_le.mp (le_rfl : |z| ≤ |z|)
    rw [hz] at habs
    exact habs
  have hfilter : Tendsto
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    hmono.tendsto_atTop_finset hcofinal
  have hsum : HasSum (fun m : ℤ => ‖K.coeff m‖) (∑' m : ℤ, ‖K.coeff m‖) :=
    K.summable_norm.hasSum
  have hsumFilter : Tendsto
      (fun s : Finset ℤ => ∑ m ∈ s, ‖K.coeff m‖) atTop
      (𝓝 (∑' m : ℤ, ‖K.coeff m‖)) := hsum
  exact hsumFilter.comp hfilter

/-- The coefficient `ℓ¹` mass outside symmetric finite truncations tends to
zero. -/
theorem integerKernel_norm_tail_Icc_tendsto_zero (K : IntegerL1Kernel) :
    Tendsto
      (fun N : ℕ => ∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
        ‖K.coeff m‖)
      atTop (𝓝 0) := by
  let total : ℝ := ∑' m : ℤ, ‖K.coeff m‖
  let partialSum : ℕ → ℝ := fun N =>
    ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖K.coeff m‖
  have hidentity (N : ℕ) :
      (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
        ‖K.coeff m‖) = total - partialSum N := by
    have hsplit := K.summable_norm.sum_add_tsum_compl
      (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    dsimp [total, partialSum]
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsplit)
  have hdiff : Tendsto (fun N : ℕ => total - partialSum N) atTop (𝓝 0) := by
    have hpartial := integerKernel_norm_sum_Icc_tendsto K
    change Tendsto partialSum atTop (𝓝 total) at hpartial
    convert tendsto_const_nhds.sub hpartial using 1 <;> simp [total]
  apply hdiff.congr'
  filter_upwards with N
  exact (hidentity N).symm

theorem integerKernel_norm_sum_le_tail_of_subset_compl
    (K : IntegerL1Kernel) (s A : Finset ℤ)
    (hA : (A : Set ℤ) ⊆ (s : Set ℤ)ᶜ) :
    (∑ m ∈ A, ‖K.coeff m‖) ≤
      ∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖ := by
  let T := ↥((s : Set ℤ)ᶜ)
  let f : T → ℝ := fun m => ‖K.coeff m.1‖
  let A' : Finset T := A.attach.image fun m => (⟨m.1, hA m.2⟩ : T)
  have hsum :
      (∑ m ∈ A, ‖K.coeff m‖) = ∑ m ∈ A', f m := by
    calc
      (∑ m ∈ A, ‖K.coeff m‖) =
          ∑ m ∈ A.attach, ‖K.coeff m.1‖ := by
        rw [← Finset.sum_attach]
      _ = ∑ m ∈ A', f m := by
        dsimp [A', f]
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact Subtype.ext (congrArg (fun z : T => z.1) hxy)
  rw [hsum]
  refine (K.summable_norm.comp_injective Subtype.val_injective).sum_le_tsum
    A' (fun m hm => norm_nonneg _)

theorem integerKernel_norm_sum_Icc_sdiff_le_tail
    (K : IntegerL1Kernel) (N M : ℕ) :
    (∑ m ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ)),
      ‖K.coeff m‖) ≤
      ∑' m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
        ‖K.coeff m‖ := by
  apply integerKernel_norm_sum_le_tail_of_subset_compl
  intro m hm
  have hm' : m ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) :=
    (Finset.mem_sdiff.mp hm).2
  simpa using hm'

theorem exists_nat_symmetric_Icc_superset (s : Finset ℤ) :
    ∃ N : ℕ, (s : Set ℤ) ⊆ Set.Icc (-(N : ℤ)) (N : ℤ) := by
  let N := s.sup fun z => z.natAbs
  refine ⟨N, ?_⟩
  intro z hz
  have hnat : z.natAbs ≤ N := Finset.le_sup (f := fun z => z.natAbs) hz
  have habs : |z| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat
  exact abs_le.mp habs

/-- The convolution of a finitely supported input is the finite sum over the
indices that can contribute at a fixed output coordinate. -/
theorem integerKernelConvolution_eq_sum_finiteInputSupport
    (K : IntegerL1Kernel) (t : Finset ℤ) (b : ℤ → ℂ) (k : ℤ) :
    integerKernelConvolution K (finiteIntegerSequenceL2 t b) k =
      ∑ i ∈ t.image (fun j : ℤ => k - j),
        K.coeff i * finiteIntegerSequenceL2 t b (k - i) := by
  classical
  let A := t.image (fun j : ℤ => k - j)
  have hinput (j : ℤ) (hj : j ∉ t) :
      finiteIntegerSequenceL2 t b j = 0 := by
    simp [finiteIntegerSequenceL2_apply, hj]
  have hzero (i : ℤ) (hi : i ∉ A) :
      K.coeff i * finiteIntegerSequenceL2 t b (k - i) = 0 := by
    have hki : k - i ∉ t := by
      intro hmem
      apply hi
      simp only [A, Finset.mem_image]
      exact ⟨k - i, hmem, by omega⟩
    rw [hinput (k - i) hki]
    simp
  have hexists := integerKernelConvolutionExistsAt_of_finiteInputSupport
    K (finiteIntegerSequenceL2 t b) k t hinput
  rw [integerKernelConvolution_eq_tsum K _ _ hexists]
  simpa [A] using (tsum_eq_sum (s := A) hzero)

/-- Once a symmetric kernel truncation contains all indices that can meet a
fixed finite-support input at a given output coordinate, its coordinate is
exactly the Mathlib convolution value there. -/
theorem finiteDiscreteConvolutionSequenceL2_apply_eventually_eq_convolution
    (K : IntegerL1Kernel) (t : Finset ℤ) (b : ℤ → ℂ) (k : ℤ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      finiteDiscreteConvolutionSequenceL2
          (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b k =
        integerKernelConvolution K (finiteIntegerSequenceL2 t b) k := by
  classical
  let A := t.image (fun j : ℤ => k - j)
  have hzero (i : ℤ) (hi : i ∉ A) :
      K.coeff i * finiteIntegerSequenceL2 t b (k - i) = 0 := by
    have hki : k - i ∉ t := by
      intro hmem
      apply hi
      simp only [A, Finset.mem_image]
      exact ⟨k - i, hmem, by omega⟩
    rw [finiteIntegerSequenceL2_apply]
    simp [hki]
  have hconvSum := integerKernelConvolution_eq_sum_finiteInputSupport K t b k
  obtain ⟨N₀, hA₀⟩ := exists_nat_symmetric_Icc_superset A
  refine ⟨N₀, ?_⟩
  intro N hN
  have hbase : A ⊆ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) := by
    intro i hi
    have hi' := hA₀ hi
    simpa [Set.mem_Icc] using hi'
  have hmono : Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hN)
    · exact Int.ofNat_le.mpr hN
  have hsub := Finset.Subset.trans hbase hmono
  have hsum :
      (∑ i ∈ A, K.coeff i * finiteIntegerSequenceL2 t b (k - i)) =
        ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          K.coeff i * finiteIntegerSequenceL2 t b (k - i) :=
    Finset.sum_subset hsub (by
      intro i hi hnot
      exact hzero i hnot)
  calc
    finiteDiscreteConvolutionSequenceL2
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b k =
      ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        K.coeff i * finiteIntegerSequenceL2 t b (k - i) :=
      finiteDiscreteConvolutionSequenceL2_apply_eq_sum
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b k
    _ = ∑ i ∈ A, K.coeff i * finiteIntegerSequenceL2 t b (k - i) := hsum.symm
    _ = integerKernelConvolution K (finiteIntegerSequenceL2 t b) k := by
      exact hconvSum.symm

theorem integerKernel_nnnorm_sum_Icc_sdiff_le_toNNReal_tail
    (K : IntegerL1Kernel) (N M : ℕ) :
    (∑ m ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ) \
        Finset.Icc (-(N : ℤ)) (N : ℤ)), ‖K.coeff m‖₊) ≤
      Real.toNNReal
        (∑' m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
          ‖K.coeff m‖) := by
  have hreal := integerKernel_norm_sum_Icc_sdiff_le_tail K N M
  have htail_nonneg :
      0 ≤ ∑' m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
        ‖K.coeff m‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ htail_nonneg]
  simpa only [← NNReal.coe_sum, ← coe_nnnorm] using hreal

theorem integerKernel_nnnorm_sum_le_toNNReal_tail_of_subset_compl
    (K : IntegerL1Kernel) (s A : Finset ℤ)
    (hA : (A : Set ℤ) ⊆ (s : Set ℤ)ᶜ) :
    (∑ m ∈ A, ‖K.coeff m‖₊) ≤
      Real.toNNReal (∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖) := by
  have hreal := integerKernel_norm_sum_le_tail_of_subset_compl K s A hA
  have htail_nonneg :
      0 ≤ ∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ htail_nonneg]
  simpa only [← NNReal.coe_sum, ← coe_nnnorm] using hreal

theorem finiteDiscreteConvolutionSequenceL2_sub_enorm_le_of_kernel_tail_subset
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (s u base : Finset ℤ) (hs : s ⊆ u)
    (hA : ((u \ s : Finset ℤ) : Set ℤ) ⊆ (base : Set ℤ)ᶜ)
    (t : Finset ℤ) (b : ℤ → ℂ) :
    ‖finiteDiscreteConvolutionSequenceL2 u t K.coeff b -
        finiteDiscreteConvolutionSequenceL2 s t K.coeff b‖ₑ ≤
      ENNReal.ofReal (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
  have hmassNN :
      (∑ m ∈ u \ s, ‖K.coeff m‖₊) ≤
        Real.toNNReal (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) :=
    integerKernel_nnnorm_sum_le_toNNReal_tail_of_subset_compl K base (u \ s) hA
  have hmassENN :
      (∑ m ∈ u \ s, (‖K.coeff m‖₊ : ENNReal)) ≤
        ENNReal.ofReal (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) := by
    calc
      (∑ m ∈ u \ s, (‖K.coeff m‖₊ : ENNReal)) =
          ↑(∑ m ∈ u \ s, ‖K.coeff m‖₊) := by
        rw [ENNReal.ofNNReal_finsetSum]
      _ ≤ ↑(Real.toNNReal (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖)) :=
        ENNReal.coe_le_coe.mpr hmassNN
      _ = ENNReal.ofReal (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) :=
        ENNReal.ofNNReal_toNNReal _
  calc
    ‖finiteDiscreteConvolutionSequenceL2 u t K.coeff b -
        finiteDiscreteConvolutionSequenceL2 s t K.coeff b‖ₑ ≤
      (∑ m ∈ u \ s, ‖K.coeff m‖₊) *
        ‖finiteIntegerSequenceL2 t b‖ₑ :=
      finiteDiscreteConvolutionSequenceL2_sub_enorm_le_of_coeff_norm_sum
        (hT := hT) s u t K.coeff b hs
    _ ≤ ENNReal.ofReal (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
      gcongr <;> simpa only [← ENNReal.ofNNReal_finsetSum] using hmassENN

theorem finiteDiscreteConvolutionSequenceL2_dist_le_of_kernel_tail_subset
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (s u base : Finset ℤ) (hs : s ⊆ u)
    (hA : ((u \ s : Finset ℤ) : Set ℤ) ⊆ (base : Set ℤ)ᶜ)
    (t : Finset ℤ) (b : ℤ → ℂ) :
    dist (finiteDiscreteConvolutionSequenceL2 u t K.coeff b)
        (finiteDiscreteConvolutionSequenceL2 s t K.coeff b) ≤
      (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) *
        ‖finiteIntegerSequenceL2 t b‖ := by
  have htail_nonneg :
      0 ≤ ∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  have hENN :=
    finiteDiscreteConvolutionSequenceL2_sub_enorm_le_of_kernel_tail_subset
      (hT := hT) K s u base hs hA t b
  have henorm (x : lp (fun _ : ℤ => ℂ) 2) :
      ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
    simp only [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ← coe_nnnorm]
  rw [henorm, henorm, ← ENNReal.ofReal_mul htail_nonneg] at hENN
  have hreal :
      ‖finiteDiscreteConvolutionSequenceL2 u t K.coeff b -
          finiteDiscreteConvolutionSequenceL2 s t K.coeff b‖ ≤
        (∑' m : ↥((base : Set ℤ)ᶜ), ‖K.coeff m‖) *
          ‖finiteIntegerSequenceL2 t b‖ :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg htail_nonneg (norm_nonneg _))).mp hENN
  simpa only [dist_eq_norm] using hreal

theorem integerKernelFiniteConvolutionTruncations_cauchy
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b : ℤ → ℂ) :
    CauchySeq (fun N : ℕ =>
      finiteDiscreteConvolutionSequenceL2
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b) := by
  let tail : ℕ → ℝ := fun N =>
    ∑' m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
      ‖K.coeff m‖
  let bound : ℕ → ℝ := fun N => tail N * ‖finiteIntegerSequenceL2 t b‖
  have htail : Tendsto tail atTop (𝓝 0) :=
    integerKernel_norm_tail_Icc_tendsto_zero K
  have hbound : Tendsto bound atTop (𝓝 0) := by
    simpa [bound, mul_zero] using
      htail.mul_const ‖finiteIntegerSequenceL2 t b‖
  apply cauchySeq_of_le_tendsto_0' bound
  · intro n m hnm
    have hs : Finset.Icc (-(n : ℤ)) (n : ℤ) ⊆
        Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      apply Finset.Icc_subset_Icc
      · exact neg_le_neg (Int.ofNat_le.mpr hnm)
      · exact Int.ofNat_le.mpr hnm
    have hA :
        ((Finset.Icc (-(m : ℤ)) (m : ℤ) \
          Finset.Icc (-(n : ℤ)) (n : ℤ) : Finset ℤ) : Set ℤ) ⊆
          ((Finset.Icc (-(n : ℤ)) (n : ℤ) : Finset ℤ) : Set ℤ)ᶜ := by
      intro z hz
      change z ∉ Finset.Icc (-(n : ℤ)) (n : ℤ)
      exact (Finset.mem_sdiff.mp hz).2
    have hdist :=
      finiteDiscreteConvolutionSequenceL2_dist_le_of_kernel_tail_subset
        (hT := hT) K
        (Finset.Icc (-(n : ℤ)) (n : ℤ))
        (Finset.Icc (-(m : ℤ)) (m : ℤ))
        (Finset.Icc (-(n : ℤ)) (n : ℤ)) hs hA t b
    calc
      dist
          (finiteDiscreteConvolutionSequenceL2
            (Finset.Icc (-(n : ℤ)) (n : ℤ)) t K.coeff b)
          (finiteDiscreteConvolutionSequenceL2
            (Finset.Icc (-(m : ℤ)) (m : ℤ)) t K.coeff b) =
        dist
          (finiteDiscreteConvolutionSequenceL2
            (Finset.Icc (-(m : ℤ)) (m : ℤ)) t K.coeff b)
          (finiteDiscreteConvolutionSequenceL2
            (Finset.Icc (-(n : ℤ)) (n : ℤ)) t K.coeff b) :=
        dist_comm _ _
      _ ≤
        (∑' z : ↥(((Finset.Icc (-(n : ℤ)) (n : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
          ‖K.coeff z‖) * ‖finiteIntegerSequenceL2 t b‖ := hdist
      _ = bound n := by rfl
  · exact hbound

/-- The complete `ℓ²` limit of the symmetric truncations applied to a
finite-support input. -/
noncomputable def integerKernelFiniteConvolutionLimitL2
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b : ℤ → ℂ) : lp (fun _ : ℤ => ℂ) 2 :=
  Filter.limUnder atTop (fun N : ℕ =>
    finiteDiscreteConvolutionSequenceL2
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b)

theorem integerKernelFiniteConvolutionTruncations_tendsto_limitL2
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b : ℤ → ℂ) :
    Tendsto (fun N : ℕ => finiteDiscreteConvolutionSequenceL2
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b) atTop
      (𝓝 (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b)) := by
  exact (integerKernelFiniteConvolutionTruncations_cauchy
    (hT := hT) K t b).tendsto_limUnder

/-- The coordinates of the completed `ℓ²` limit agree with the absolutely
convergent Mathlib convolution at every integer. -/
theorem integerKernelFiniteConvolutionLimitL2_apply
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b : ℤ → ℂ) (k : ℤ) :
    integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b k =
      integerKernelConvolution K (finiteIntegerSequenceL2 t b) k := by
  let seq : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteDiscreteConvolutionSequenceL2
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hseq : Tendsto seq atTop
      (𝓝 (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b)) := by
    simpa [seq] using integerKernelFiniteConvolutionTruncations_tendsto_limitL2
      (hT := hT) K t b
  have hfun : Tendsto (fun N => (seq N : ℤ → ℂ)) atTop
      (𝓝 (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b : ℤ → ℂ)) :=
    (lp.uniformContinuous_coe (p := (2 : ENNReal))).continuous.continuousAt.tendsto.comp hseq
  have hlimitCoord : Tendsto (fun N => (seq N : ℤ → ℂ) k) atTop
      (𝓝 ((integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b : ℤ → ℂ) k)) :=
    (continuous_apply k).continuousAt.tendsto.comp hfun
  obtain ⟨N₀, hN₀⟩ :=
    finiteDiscreteConvolutionSequenceL2_apply_eventually_eq_convolution K t b k
  have heq : ∀ᶠ N : ℕ in atTop,
      (seq N : ℤ → ℂ) k = integerKernelConvolution K
        (finiteIntegerSequenceL2 t b) k := by
    filter_upwards [eventually_atTop.2 ⟨N₀, hN₀⟩] with N hN
    exact hN
  have hconvCoord : Tendsto (fun N => (seq N : ℤ → ℂ) k) atTop
      (𝓝 (integerKernelConvolution K (finiteIntegerSequenceL2 t b) k)) :=
    (Filter.tendsto_congr' heq).2 tendsto_const_nhds
  exact tendsto_nhds_unique hlimitCoord hconvCoord

/-- The completed output depends only on the represented finite-support
`lp` input, not on its chosen finite set of indices. -/
theorem integerKernelFiniteConvolutionLimitL2_congr
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (s t : Finset ℤ) (b c : ℤ → ℂ)
    (h : finiteIntegerSequenceL2 s b = finiteIntegerSequenceL2 t c) :
    integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b =
      integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c := by
  have hfun : (finiteIntegerSequenceL2 s b : ℤ → ℂ) =
      finiteIntegerSequenceL2 t c := congrArg (fun f : lp (fun _ : ℤ => ℂ) 2 =>
        (f : ℤ → ℂ)) h
  apply lp.ext
  funext k
  change integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b k =
    integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c k
  rw [integerKernelFiniteConvolutionLimitL2_apply,
    integerKernelFiniteConvolutionLimitL2_apply, hfun]

/-- The completed convolution limit is linear in finite-support inputs when
they are represented on the same finite support. -/
theorem integerKernelFiniteConvolutionLimitL2_sub
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b c : ℤ → ℂ) :
    integerKernelFiniteConvolutionLimitL2 (hT := hT) K t
        (fun k => b k - c k) =
      integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b -
        integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c := by
  apply lp.ext
  funext k
  change integerKernelFiniteConvolutionLimitL2 (hT := hT) K t
      (fun j => b j - c j) k =
    integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b k -
      integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c k
  rw [integerKernelFiniteConvolutionLimitL2_apply,
    integerKernelFiniteConvolutionLimitL2_apply,
    integerKernelFiniteConvolutionLimitL2_apply]
  rw [integerKernelConvolution_eq_sum_finiteInputSupport,
    integerKernelConvolution_eq_sum_finiteInputSupport,
    integerKernelConvolution_eq_sum_finiteInputSupport]
  rw [finiteIntegerSequenceL2_sub t b c, lp.coeFn_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.sub_apply, mul_sub]

theorem finiteDiscreteConvolutionSequenceL2_sub_enorm_le_of_kernel_tail
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel) (N M : ℕ)
    (hNM : N ≤ M) (t : Finset ℤ) (b : ℤ → ℂ) :
    ‖finiteDiscreteConvolutionSequenceL2 (Finset.Icc (-(M : ℤ)) (M : ℤ))
          t K.coeff b -
        finiteDiscreteConvolutionSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ))
          t K.coeff b‖ₑ ≤
      ENNReal.ofReal
          (∑' m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
            ‖K.coeff m‖) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let u := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hs : s ⊆ u := by
    dsimp [s, u]
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hNM)
    · exact Int.ofNat_le.mpr hNM
  let annulus := u \ s
  have hmassNN :
      (∑ m ∈ annulus, ‖K.coeff m‖₊) ≤
        Real.toNNReal
          (∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖) := by
    simpa [annulus, u, s] using
      integerKernel_nnnorm_sum_Icc_sdiff_le_toNNReal_tail K N M
  have hmassENN :
      (∑ m ∈ annulus, (‖K.coeff m‖₊ : ENNReal)) ≤
        ENNReal.ofReal (∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖) := by
    calc
      (∑ m ∈ annulus, (‖K.coeff m‖₊ : ENNReal)) =
          ↑(∑ m ∈ annulus, ‖K.coeff m‖₊) := by
        rw [ENNReal.ofNNReal_finsetSum]
      _ ≤ ↑(Real.toNNReal (∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖)) :=
        ENNReal.coe_le_coe.mpr hmassNN
      _ = ENNReal.ofReal (∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖) :=
        ENNReal.ofNNReal_toNNReal _
  calc
    ‖finiteDiscreteConvolutionSequenceL2 u t K.coeff b -
        finiteDiscreteConvolutionSequenceL2 s t K.coeff b‖ₑ ≤
      (∑ m ∈ annulus, ‖K.coeff m‖₊) *
        ‖finiteIntegerSequenceL2 t b‖ₑ :=
      finiteDiscreteConvolutionSequenceL2_sub_enorm_le_of_coeff_norm_sum
        (hT := hT) s u t K.coeff b hs
    _ ≤ ENNReal.ofReal (∑' m : ↥((s : Set ℤ)ᶜ), ‖K.coeff m‖) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
      gcongr <;> simpa [annulus] using hmassENN

/-- The Fourier transform of an absolutely summable kernel is uniformly
approximated by the symmetric finite coefficient sums, with error at most
the omitted coefficient mass. -/
theorem integerKernelFourierTransform_sub_Icc_sum_norm_le
    (K : IntegerL1Kernel) (ξ : ℝ) (N : ℕ) :
    ‖integerKernelFourierTransform K ξ -
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))‖ ≤
      ∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
        ‖K.coeff m‖ := by
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hsum := summable_integerKernelFourier_terms K ξ
  have hsplit := hsum.sum_add_tsum_compl (s := s)
  have htransform : integerKernelFourierTransform K ξ =
      (∑ m ∈ s, K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))) +
        ∑' (m : ↥((s : Set ℤ)ᶜ)),
          K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ)) := by
    unfold integerKernelFourierTransform
    exact hsplit.symm
  have htailNormSummable : Summable (fun m : ↥((s : Set ℤ)ᶜ) =>
      ‖K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))‖) := by
    apply (K.summable_norm.subtype (s : Set ℤ)ᶜ).congr
    intro m
    simp [norm_unitFrequencyPhase]
  calc
    _ = ‖∑' (m : ↥((s : Set ℤ)ᶜ)),
          K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))‖ := by
      rw [htransform]
      simp [s, add_comm]
    _ ≤ ∑' (m : ↥((s : Set ℤ)ᶜ)),
          ‖K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))‖ :=
      norm_tsum_le_tsum_norm htailNormSummable
    _ = ∑' (m : ↥((s : Set ℤ)ᶜ)), ‖K.coeff m‖ := by
      congr 1
      funext m
      rw [norm_mul, norm_unitFrequencyPhase, mul_one]
    _ = ∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
          ‖K.coeff m‖ := by rfl

/-- The absolutely convergent kernel Fourier transform is periodic with
period one, so it descends to the normalized additive circle. -/
theorem integerKernelFourierTransform_add_one (K : IntegerL1Kernel) (ξ : ℝ) :
    integerKernelFourierTransform K (ξ + 1) =
      integerKernelFourierTransform K ξ := by
  unfold integerKernelFourierTransform
  apply tsum_congr
  intro m
  have harg : -(ξ + 1) * (m : ℝ) = (-ξ * (m : ℝ)) + (-(m : ℝ)) := by ring
  have hphase : unitFrequencyPhase (-(m : ℝ)) = 1 := by
    convert unitFrequencyPhase_int (-m) using 1 <;> simp
  rw [harg, unitFrequencyPhase_add, hphase, mul_one]

/-- The symmetric finite Fourier sums converge uniformly on the real
frequency line to the full kernel transform. -/
theorem integerKernelFourierTransform_tendstoUniformly_Icc
    (K : IntegerL1Kernel) :
    TendstoUniformly
      (fun N : ℕ => fun ξ : ℝ =>
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ)))
      (integerKernelFourierTransform K) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
        ‖K.coeff m‖) < ε :=
    (integerKernel_norm_tail_Icc_tendsto_zero K) (Iio_mem_nhds hε)
  filter_upwards [hsmall] with N hN
  intro ξ
  rw [dist_eq_norm]
  exact (integerKernelFourierTransform_sub_Icc_sum_norm_le K ξ N).trans_lt hN

/-- The Fourier transform of an `ℓ¹` integer kernel is continuous, as a
uniform limit of its finite Fourier sums. -/
theorem integerKernelFourierTransform_continuous (K : IntegerL1Kernel) :
    Continuous (integerKernelFourierTransform K) := by
  apply (integerKernelFourierTransform_tendstoUniformly_Icc K).continuous
  apply Eventually.frequently
  filter_upwards with N
  unfold unitFrequencyPhase
  fun_prop

/-- The period-one Fourier transform, lifted from the canonical interval to
the normalized additive circle. -/
noncomputable def integerKernelFourierSymbol (K : IntegerL1Kernel) :
    AddCircle (1 : ℝ) → ℂ := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  exact AddCircle.liftIco (1 : ℝ) 0 (integerKernelFourierTransform K)

theorem continuous_integerKernelFourierSymbol (K : IntegerL1Kernel) :
    Continuous (integerKernelFourierSymbol K) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  unfold integerKernelFourierSymbol
  apply AddCircle.liftIco_zero_continuous
  · simpa using (integerKernelFourierTransform_add_one K 0).symm
  · exact (integerKernelFourierTransform_continuous K).continuousOn

theorem integerKernelFourierSymbol_coe_Ico
    (K : IntegerL1Kernel) (ξ : ℝ) (hξ : ξ ∈ Set.Ico 0 1) :
    integerKernelFourierSymbol K (ξ : AddCircle (1 : ℝ)) =
      integerKernelFourierTransform K ξ := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [integerKernelFourierSymbol, AddCircle.liftIco_zero_coe_apply hξ]

/-- Pointwise absolute convergence bounds the circle Fourier symbol by the
`ℓ¹` coefficient norm. -/
theorem integerKernelFourierSymbol_norm_le_tsum
    (K : IntegerL1Kernel) (x : AddCircle (1 : ℝ)) :
    ‖integerKernelFourierSymbol K x‖ ≤ ∑' m : ℤ, ‖K.coeff m‖ := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hxmem : x ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ico 0 (0 + (1 : ℝ)) := by
    rw [AddCircle.coe_image_Ico_eq]
    exact Set.mem_univ x
  rcases hxmem with ⟨ξ, hξ, rfl⟩
  have hξ' : ξ ∈ Set.Ico 0 1 := by simpa using hξ
  rw [integerKernelFourierSymbol_coe_Ico K ξ hξ']
  exact integerKernelFourierTransform_norm_le K ξ

/-- The full Fourier symbol has finite essential supremum, bounded by the
absolute coefficient sum of the kernel. -/
theorem eLpNormEssSup_integerKernelFourierSymbol_le_tsum
    (K : IntegerL1Kernel) :
    eLpNormEssSup (integerKernelFourierSymbol K)
        (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
      ENNReal.ofReal (∑' m : ℤ, ‖K.coeff m‖) := by
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with x
  exact integerKernelFourierSymbol_norm_le_tsum K x

theorem finiteIntegerKernelFourierSymbol_coe_Ico
    {hT : Fact (0 < (1 : ℝ))} (s : Finset ℤ) (a : ℤ → ℂ)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ico 0 1) :
    finiteIntegerKernelFourierSymbol (hT := hT) s a
        (ξ : AddCircle (1 : ℝ)) =
      ∑ m ∈ s, a m * unitFrequencyPhase (-ξ * (m : ℝ)) := by
  unfold finiteIntegerKernelFourierSymbol integerFourierPolynomial
  apply Finset.sum_congr rfl
  intro m hm
  rw [← AddCircle.coe_neg, ← unitFrequencyPhase_int_mul_eq_addCircleFourier m (-ξ)]
  congr 2
  ring

theorem integerKernelFourierSymbol_sub_finiteSymbol_norm_le
    (K : IntegerL1Kernel) (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ‖integerKernelFourierSymbol K x -
        finiteIntegerKernelFourierSymbol (hT := ⟨by norm_num⟩)
          (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff x‖ ≤
      ∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
        ‖K.coeff m‖ := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hxmem : x ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ico 0 (0 + (1 : ℝ)) := by
    rw [AddCircle.coe_image_Ico_eq]
    exact Set.mem_univ x
  rcases hxmem with ⟨ξ, hξ, rfl⟩
  have hξ' : ξ ∈ Set.Ico 0 1 := by simpa using hξ
  rw [integerKernelFourierSymbol_coe_Ico K ξ hξ',
    finiteIntegerKernelFourierSymbol_coe_Ico
      (hT := ⟨by norm_num⟩) (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff ξ hξ']
  exact integerKernelFourierTransform_sub_Icc_sum_norm_le K ξ N

theorem eLpNormEssSup_integerKernelFourierSymbol_sub_finiteSymbol_le
    (K : IntegerL1Kernel) (N : ℕ) :
    eLpNormEssSup
      (fun x : AddCircle (1 : ℝ) => integerKernelFourierSymbol K x -
        finiteIntegerKernelFourierSymbol (hT := ⟨by norm_num⟩)
          (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff x)
      (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
        ENNReal.ofReal
          (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
            ‖K.coeff m‖) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with x
  exact integerKernelFourierSymbol_sub_finiteSymbol_norm_le K N x

theorem eLpNormEssSup_integerKernelFourierSymbol_sub_finiteSymbol_tendsto_zero
    (K : IntegerL1Kernel) :
    Tendsto
      (fun N : ℕ => eLpNormEssSup
        (fun x : AddCircle (1 : ℝ) => integerKernelFourierSymbol K x -
          finiteIntegerKernelFourierSymbol (hT := ⟨by norm_num⟩)
            (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff x)
        (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun N : ℕ => ENNReal.ofReal
        (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
          ‖K.coeff m‖)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (integerKernel_norm_tail_Icc_tendsto_zero K)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hupper ε hε] with N hN
  exact (eLpNormEssSup_integerKernelFourierSymbol_sub_finiteSymbol_le K N).trans hN

theorem eLpNormEssSup_finiteIntegerKernelFourierSymbol_le_full_add_tail
    (K : IntegerL1Kernel) (N : ℕ) :
    eLpNormEssSup
      (finiteIntegerKernelFourierSymbol (hT := ⟨by norm_num⟩)
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff)
      (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
        eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) +
        ENNReal.ofReal
          (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
            ‖K.coeff m‖) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let μ := @AddCircle.haarAddCircle (1 : ℝ) ‹Fact (0 < (1 : ℝ))›
  let P := integerKernelFourierSymbol K
  let Q := finiteIntegerKernelFourierSymbol (hT := ‹Fact (0 < (1 : ℝ))›)
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff
  have herror : eLpNormEssSup (fun x => Q x - P x) μ ≤
      ENNReal.ofReal
        (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
          ‖K.coeff m‖) := by
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    calc
      ‖Q x - P x‖ = ‖P x - Q x‖ := norm_sub_rev _ _
      _ ≤ ∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
            ‖K.coeff m‖ := integerKernelFourierSymbol_sub_finiteSymbol_norm_le K N x
  have hdecomp : Q = fun x => P x + (Q x - P x) := by
    funext x
    ring
  rw [show eLpNormEssSup Q μ =
      eLpNormEssSup (fun x => P x + (Q x - P x)) μ by rw [← hdecomp]]
  calc
    eLpNormEssSup (fun x => P x + (Q x - P x)) μ ≤
        eLpNormEssSup P μ + eLpNormEssSup (fun x => Q x - P x) μ :=
      eLpNormEssSup_add_le
    _ ≤ eLpNormEssSup P μ + ENNReal.ofReal
        (∑' (m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ)),
          ‖K.coeff m‖) := add_le_add_right herror (eLpNormEssSup P μ)

/-- The completed finite-input convolution has the exact `ℓ²` Fourier
multiplier bound. -/
theorem integerKernelFiniteConvolutionLimitL2_enorm_le
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b : ℤ → ℂ) :
    ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b‖ₑ ≤
      eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖finiteIntegerSequenceL2 t b‖ₑ := by
  let seq : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteDiscreteConvolutionSequenceL2
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b
  let tail : ℕ → ℝ := fun N =>
    ∑' m : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ),
      ‖K.coeff m‖
  let μ := @AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩
  let S := eLpNormEssSup (integerKernelFourierSymbol K) μ
  let B := ‖finiteIntegerSequenceL2 t b‖ₑ
  have hseq : Tendsto seq atTop
      (𝓝 (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b)) := by
    simpa [seq] using integerKernelFiniteConvolutionTruncations_tendsto_limitL2
      (hT := hT) K t b
  have htail : Tendsto tail atTop (𝓝 0) :=
    integerKernel_norm_tail_Icc_tendsto_zero K
  have htailENN : Tendsto (fun N => ENNReal.ofReal (tail N)) atTop (𝓝 0) := by
    simpa [tail] using ENNReal.tendsto_ofReal htail
  have hbound (N : ℕ) : ‖seq N‖ₑ ≤ (S + ENNReal.ofReal (tail N)) * B := by
    calc
      ‖seq N‖ₑ ≤
          eLpNormEssSup
            (finiteIntegerKernelFourierSymbol (hT := ⟨by norm_num⟩)
              (Finset.Icc (-(N : ℤ)) (N : ℤ)) K.coeff) μ * B :=
        finiteDiscreteConvolutionSequenceL2_enorm_le_of_finiteSymbol_essSup
          (hT := hT) (Finset.Icc (-(N : ℤ)) (N : ℤ)) t K.coeff b
      _ ≤ (S + ENNReal.ofReal (tail N)) * B := by
        gcongr
        simpa [S, μ, tail] using
          eLpNormEssSup_finiteIntegerKernelFourierSymbol_le_full_add_tail K N
  have hright : Tendsto (fun N => (S + ENNReal.ofReal (tail N)) * B)
      atTop (𝓝 (S * B)) := by
    have hadd : Tendsto (fun N => S + ENNReal.ofReal (tail N)) atTop (𝓝 S) := by
      simpa using tendsto_const_nhds.add htailENN
    by_cases hB0 : B = 0
    · simp [hB0]
    · have hBtop : B ≠ ⊤ := by
        dsimp [B]
        exact enorm_ne_top
      simpa using ENNReal.Tendsto.mul hadd (Or.inr hBtop)
        tendsto_const_nhds (Or.inl hB0)
  have hnorm : Tendsto (fun N => ‖seq N‖ₑ) atTop
      (𝓝 ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b‖ₑ) :=
    continuous_enorm.continuousAt.tendsto.comp hseq
  have hle := le_of_tendsto_of_tendsto hnorm hright
    (Filter.Eventually.of_forall hbound)
  simpa [S, B, μ] using hle

/-- The finite-support completed convolution is Lipschitz in the input, with
the exact Fourier multiplier norm, on any fixed support representation. -/
theorem integerKernelFiniteConvolutionLimitL2_dist_le
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (t : Finset ℤ) (b c : ℤ → ℂ) :
    ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K t b -
      integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c‖ₑ ≤
      eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖finiteIntegerSequenceL2 t b - finiteIntegerSequenceL2 t c‖ₑ := by
  rw [← integerKernelFiniteConvolutionLimitL2_sub (hT := hT) K t b c]
  calc
    ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K t (fun k => b k - c k)‖ₑ ≤
        eLpNormEssSup (integerKernelFourierSymbol K)
            (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
          ‖finiteIntegerSequenceL2 t (fun k => b k - c k)‖ₑ :=
      integerKernelFiniteConvolutionLimitL2_enorm_le (hT := hT) K t
        (fun k => b k - c k)
    _ = eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖finiteIntegerSequenceL2 t b - finiteIntegerSequenceL2 t c‖ₑ := by
      rw [finiteIntegerSequenceL2_sub]

/-- The sharp Lipschitz estimate is independent of the finite support
representations chosen for the two inputs. -/
theorem integerKernelFiniteConvolutionLimitL2_dist_le_of_representations
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (s t : Finset ℤ) (b c : ℤ → ℂ) :
    ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b -
      integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c‖ₑ ≤
      eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖finiteIntegerSequenceL2 s b - finiteIntegerSequenceL2 t c‖ₑ := by
  let u := s ∪ t
  let f : ℤ → ℂ := finiteIntegerSequenceL2 s b
  let g : ℤ → ℂ := finiteIntegerSequenceL2 t c
  have hsu : s ⊆ u := Finset.subset_union_left
  have htu : t ⊆ u := Finset.subset_union_right
  have hfs : finiteIntegerSequenceL2 u f = finiteIntegerSequenceL2 s b := by
    exact finiteIntegerSequenceL2_truncate_of_subset s u b hsu
  have hgt : finiteIntegerSequenceL2 u g = finiteIntegerSequenceL2 t c := by
    exact finiteIntegerSequenceL2_truncate_of_subset t u c htu
  have hLs := integerKernelFiniteConvolutionLimitL2_congr
    (hT := hT) K u s f b hfs
  have hLt := integerKernelFiniteConvolutionLimitL2_congr
    (hT := hT) K u t g c hgt
  calc
    ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b -
        integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c‖ₑ =
      ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K u f -
        integerKernelFiniteConvolutionLimitL2 (hT := hT) K u g‖ₑ := by
      rw [← hLs, ← hLt]
    _ ≤ eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖finiteIntegerSequenceL2 u f - finiteIntegerSequenceL2 u g‖ₑ :=
      integerKernelFiniteConvolutionLimitL2_dist_le (hT := hT) K u f g
    _ = eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖finiteIntegerSequenceL2 s b - finiteIntegerSequenceL2 t c‖ₑ := by
      rw [hfs, hgt]

/-- Real-metric form of the representation-independent sharp Lipschitz
estimate. -/
theorem integerKernelFiniteConvolutionLimitL2_dist_le_real
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (s t : Finset ℤ) (b c : ℤ → ℂ) :
    dist (integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b)
      (integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c) ≤
      (∑' m : ℤ, ‖K.coeff m‖) *
        dist (finiteIntegerSequenceL2 s b) (finiteIntegerSequenceL2 t c) := by
  let C : ℝ := ∑' m : ℤ, ‖K.coeff m‖
  have hC : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  have hS := eLpNormEssSup_integerKernelFourierSymbol_le_tsum K
  have hbound := integerKernelFiniteConvolutionLimitL2_dist_le_of_representations
    (hT := hT) K s t b c
  have henorm (x : lp (fun _ : ℤ => ℂ) 2) :
      ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
    simp only [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ← coe_nnnorm]
  have hrealENN : ENNReal.ofReal
        ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b -
          integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c‖ ≤
      ENNReal.ofReal (C * ‖finiteIntegerSequenceL2 s b -
        finiteIntegerSequenceL2 t c‖) := by
    calc
      _ = ‖integerKernelFiniteConvolutionLimitL2 (hT := hT) K s b -
          integerKernelFiniteConvolutionLimitL2 (hT := hT) K t c‖ₑ :=
        (henorm _).symm
      _ ≤ eLpNormEssSup (integerKernelFourierSymbol K)
            (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
          ‖finiteIntegerSequenceL2 s b - finiteIntegerSequenceL2 t c‖ₑ := hbound
      _ ≤ ENNReal.ofReal C *
          ‖finiteIntegerSequenceL2 s b - finiteIntegerSequenceL2 t c‖ₑ :=
        mul_le_mul_of_nonneg_right hS (zero_le)
      _ = ENNReal.ofReal (C * ‖finiteIntegerSequenceL2 s b -
          finiteIntegerSequenceL2 t c‖) := by
        rw [henorm, ENNReal.ofReal_mul hC]
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (norm_nonneg _))).mp hrealENN
  simpa only [dist_eq_norm] using hreal

/-- For any `ℓ²` input, applying the completed finite-support convolution
operator to its symmetric truncations gives a Cauchy sequence in `ℓ²`. -/
theorem integerKernelInputTruncationOutputs_cauchy
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    CauchySeq (fun N : ℕ => integerKernelFiniteConvolutionLimitL2
      (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f) := by
  let x : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteIntegerSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let y : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    integerKernelFiniteConvolutionLimitL2
      (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let C : ℝ := ∑' m : ℤ, ‖K.coeff m‖
  have hC : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  have hx : Tendsto x atTop (𝓝 f) := by
    simpa [x] using finiteIntegerSequenceL2_Icc_tendsto f
  have hxc : CauchySeq x := hx.cauchySeq
  by_cases hC0 : C = 0
  · rw [Metric.cauchySeq_iff]
    intro ε hε
    refine ⟨0, ?_⟩
    intro m hm n hn
    have hLip := integerKernelFiniteConvolutionLimitL2_dist_le_real
      (hT := hT) K (Finset.Icc (-(m : ℤ)) (m : ℤ))
        (Finset.Icc (-(n : ℤ)) (n : ℤ)) f f
    have hzero : dist (y m) (y n) ≤ 0 := by
      simpa [y, C, hC0] using hLip
    exact lt_of_le_of_lt hzero hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hεC : 0 < ε / C := div_pos hε hCpos
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hxc) (ε / C) hεC
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hLip := integerKernelFiniteConvolutionLimitL2_dist_le_real
      (hT := hT) K (Finset.Icc (-(m : ℤ)) (m : ℤ))
        (Finset.Icc (-(n : ℤ)) (n : ℤ)) f f
    calc
      dist (y m) (y n) ≤ C * dist (x m) (x n) := by
        simpa [x, y, C] using hLip
      _ < C * (ε / C) := mul_lt_mul_of_pos_left (hN m hm n hn) hCpos
      _ = ε := by field_simp [ne_of_gt hCpos]

/-- The extension of an absolutely summable integer kernel's convolution to
arbitrary `ℓ²` inputs, defined as the limit of its finite-input truncations. -/
noncomputable def integerKernelConvolutionL2
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  Filter.limUnder atTop (fun N : ℕ => integerKernelFiniteConvolutionLimitL2
    (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f)

theorem integerKernelInputTruncationOutputs_tendsto
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    Tendsto (fun N : ℕ => integerKernelFiniteConvolutionLimitL2
      (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f) atTop
      (𝓝 (integerKernelConvolutionL2 (hT := hT) K f)) := by
  exact (integerKernelInputTruncationOutputs_cauchy (hT := hT) K f).tendsto_limUnder

/-- The arbitrary-input completed convolution obeys the sharp Fourier
multiplier norm estimate. -/
theorem integerKernelConvolutionL2_enorm_le
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖integerKernelConvolutionL2 (hT := hT) K f‖ₑ ≤
      eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) * ‖f‖ₑ := by
  let x : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteIntegerSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let y : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    integerKernelFiniteConvolutionLimitL2
      (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let S := eLpNormEssSup (integerKernelFourierSymbol K)
      (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩)
  have hS := eLpNormEssSup_integerKernelFourierSymbol_le_tsum K
  have hStop : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS
  have hx : Tendsto x atTop (𝓝 f) := by
    simpa [x] using finiteIntegerSequenceL2_Icc_tendsto f
  have hnorm : Tendsto (fun N => ‖x N‖ₑ) atTop (𝓝 ‖f‖ₑ) :=
    continuous_enorm.continuousAt.tendsto.comp hx
  have hright : Tendsto (fun N => S * ‖x N‖ₑ) atTop (𝓝 (S * ‖f‖ₑ)) := by
    simpa [mul_comm] using ENNReal.Tendsto.mul_const hnorm (Or.inr hStop)
  have hseq : Tendsto y atTop
      (𝓝 (integerKernelConvolutionL2 (hT := hT) K f)) := by
    simpa [y] using integerKernelInputTruncationOutputs_tendsto
      (hT := hT) K f
  have hnormSeq : Tendsto (fun N => ‖y N‖ₑ) atTop
      (𝓝 ‖integerKernelConvolutionL2 (hT := hT) K f‖ₑ) :=
    continuous_enorm.continuousAt.tendsto.comp hseq
  have hbound (N : ℕ) : ‖y N‖ₑ ≤ S * ‖x N‖ₑ := by
    simpa [x, y, S] using integerKernelFiniteConvolutionLimitL2_enorm_le
      (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  exact le_of_tendsto_of_tendsto hnormSeq hright
    (Filter.Eventually.of_forall hbound)

/-- The arbitrary-input `ℓ²` extension agrees coordinatewise with the
counting-measure convolution. -/
theorem integerKernelConvolutionL2_apply
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) 2) (k : ℤ) :
    integerKernelConvolutionL2 (hT := hT) K f k =
      integerKernelConvolution K (f : ℤ → ℂ) k := by
  let seqIn : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    finiteIntegerSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let seqOut : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun N =>
    integerKernelFiniteConvolutionLimitL2
      (hT := hT) K (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let bound : ℤ → ℝ := fun m => ‖K.coeff m‖ * ‖f‖
  let summand : ℕ → ℤ → ℂ := fun N m => K.coeff m * seqIn N (k - m)
  let limitSummand : ℤ → ℂ := fun m => K.coeff m * f (k - m)
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hIn : Tendsto seqIn atTop (𝓝 f) := by
    simpa [seqIn] using finiteIntegerSequenceL2_Icc_tendsto f
  have hfun : Tendsto (fun N => (seqIn N : ℤ → ℂ)) atTop
      (𝓝 (f : ℤ → ℂ)) :=
    (lp.uniformContinuous_coe (p := (2 : ENNReal))).continuous.continuousAt.tendsto.comp hIn
  have hbound : Summable bound := by
    simpa [bound] using K.summable_norm.mul_right ‖f‖
  have hterm (m : ℤ) : Tendsto (fun N => summand N m) atTop
      (𝓝 (limitSummand m)) := by
    have hcoord : Tendsto (fun N => (seqIn N : ℤ → ℂ) (k - m)) atTop
        (𝓝 ((f : ℤ → ℂ) (k - m))) :=
      (continuous_apply (k - m)).continuousAt.tendsto.comp hfun
    simpa [summand, limitSummand] using tendsto_const_nhds.mul hcoord
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ m : ℤ,
      ‖summand N m‖ ≤ bound m := Filter.Eventually.of_forall fun N m => by
    have hcoord : ‖seqIn N (k - m)‖ ≤ ‖f‖ := by
      simp only [seqIn, finiteIntegerSequenceL2_apply]
      split_ifs
      · exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f (k - m)
      · simpa using norm_nonneg f
    calc
      ‖summand N m‖ = ‖K.coeff m‖ * ‖seqIn N (k - m)‖ := norm_mul _ _
      _ ≤ bound m := by
        dsimp [bound]
        exact mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)
  have hsum : Tendsto (fun N => ∑' m : ℤ, summand N m) atTop
      (𝓝 (∑' m : ℤ, limitSummand m)) :=
    tendsto_tsum_of_dominated_convergence hbound hterm hdom
  have hconvExists : IntegerKernelConvolutionExistsAt K (f : ℤ → ℂ) k :=
    integerKernelConvolutionExistsAt_of_lpL2 K f k
  have hconv : integerKernelConvolution K (f : ℤ → ℂ) k =
      ∑' m : ℤ, limitSummand m := by
    exact integerKernelConvolution_eq_tsum K (f : ℤ → ℂ) k hconvExists
  have hseq : Tendsto seqOut atTop
      (𝓝 (integerKernelConvolutionL2 (hT := hT) K f)) := by
    simpa [seqOut] using integerKernelInputTruncationOutputs_tendsto
      (hT := hT) K f
  have hfunOut : Tendsto (fun N => (seqOut N : ℤ → ℂ)) atTop
      (𝓝 (integerKernelConvolutionL2 (hT := hT) K f : ℤ → ℂ)) :=
    (lp.uniformContinuous_coe (p := (2 : ENNReal))).continuous.continuousAt.tendsto.comp hseq
  have hcoordOut : Tendsto (fun N => (seqOut N : ℤ → ℂ) k) atTop
      (𝓝 ((integerKernelConvolutionL2 (hT := hT) K f : ℤ → ℂ) k)) :=
    (continuous_apply k).continuousAt.tendsto.comp hfunOut
  have hcoords : ∀ N : ℕ,
      (seqOut N : ℤ → ℂ) k = ∑' m : ℤ, summand N m := by
    intro N
    change integerKernelFiniteConvolutionLimitL2 (hT := hT) K
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) f k =
      ∑' m : ℤ, K.coeff m *
        finiteIntegerSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ)) f (k - m)
    rw [integerKernelFiniteConvolutionLimitL2_apply]
    rw [integerKernelConvolution_eq_tsum K _ k
      (integerKernelConvolutionExistsAt_of_finiteInputSupport K
        (finiteIntegerSequenceL2 (Finset.Icc (-(N : ℤ)) (N : ℤ)) f) k
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) (by
          intro j hj
          simp [finiteIntegerSequenceL2_apply, hj]))]
  have hsumCoord : Tendsto (fun N => (seqOut N : ℤ → ℂ) k) atTop
      (𝓝 (integerKernelConvolution K (f : ℤ → ℂ) k)) := by
    rw [hconv]
    exact (Filter.tendsto_congr' (Filter.Eventually.of_forall hcoords)).2 hsum
  have hcoordValue : (integerKernelConvolutionL2 (hT := hT) K f : ℤ → ℂ) k =
      integerKernelConvolution K (f : ℤ → ℂ) k :=
    tendsto_nhds_unique hcoordOut hsumCoord
  exact hcoordValue

/-- The product of two period-one Fourier monomials has the expected
frequency-sum coefficient. -/
theorem fourierCoeff_product_fourier_monomials
    {hT : Fact (0 < (1 : ℝ))} (m n : ℤ) :
    fourierCoeff
      (fun x : AddCircle (1 : ℝ) => fourier (T := (1 : ℝ)) m x *
        fourier (T := (1 : ℝ)) n x) = Pi.single (m + n) 1 := by
  have hfun :
      (fun x : AddCircle (1 : ℝ) => fourier (T := (1 : ℝ)) m x *
        fourier (T := (1 : ℝ)) n x) =
      (fourier (T := (1 : ℝ)) (m + n) : AddCircle (1 : ℝ) → ℂ) := by
    funext x
    rw [fourier_add]
  rw [hfun]
  exact fourierCoeff_fourier (T := (1 : ℝ)) (m + n)

end FractionalPrimes
