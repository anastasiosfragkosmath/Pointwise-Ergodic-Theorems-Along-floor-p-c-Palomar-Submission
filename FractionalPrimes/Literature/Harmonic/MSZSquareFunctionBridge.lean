module

public import FractionalPrimes.Literature.Harmonic.MSZProjectionBridge

/-! Adapter from the checked Fourier square-function theorem to the
common-domain signed projection family used by MSZ. -/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier
open FractionalPrimes.Literature.MSZ

noncomputable section

/-- Counting-measure convolution transported to the exact `ofReal p`
sequence exponent of the Mikhlin multiplier theorem. -/
noncomputable def integerKernelConvolutionRealExponentCLM
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (K : IntegerL1Kernel) :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hpTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  let e₁ : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
    (generalLpToCountLp (p := ENNReal.ofReal p)
      hp0 hpTop).mkContinuous 1 (by
        intro f
        rw [generalLpToCountLp_norm]
        simp)
  let e₂ : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) :=
    (countLpToGeneralLp (p := ENNReal.ofReal p)
      hp0 hpTop).mkContinuous 1 (by
        intro f
        rw [countLpToGeneralLp_norm]
        simp)
  exact e₂.comp ((integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K).comp e₁)

/-- Pointwise action of the generic real-exponent convolution operator. -/
theorem integerKernelConvolutionRealExponentCLM_apply
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    integerKernelConvolutionRealExponentCLM p hp K f x =
      integerKernelConvolution K (f : ℤ → ℂ) x := by
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hpTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  change countLpToGeneralLp hp0 hpTop
    (integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K
      (generalLpToCountLp hp0 hpTop f)) x = _
  rw [countLpToGeneralLp_apply, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  congr 1
  funext n
  exact generalLpToCountLp_apply hp0 hpTop f n

/-- Every source Fourier projection equals convolution by its summable
kernel at every real exponent `p>1`. -/
theorem frequencyProjectionLpProjection_eq_kernelCLM_all
    (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (h : ℕ) :
    frequencyProjectionLpProjection c hc hp h =
      integerKernelConvolutionRealExponentCLM p hp
        (frequencyProjectionIntegerKernel c hc h) := by
  let e := finiteSupportLpInclusion (P := ENNReal.ofReal p)
  let U := frequencyProjectionLpProjection c hc hp h
  let V := integerKernelConvolutionRealExponentCLM p hp
    (frequencyProjectionIntegerKernel c hc h)
  have hdense : DenseRange e :=
    finiteSupportLpInclusion_denseRange (P := ENNReal.ofReal p)
      ENNReal.ofReal_ne_top
  have hcompose : U ∘ e = V ∘ e := by
    funext f
    apply lp.ext
    funext x
    change (frequencyProjectionLpProjection c hc hp h
      (finiteSupportLpInclusion (P := ENNReal.ofReal p) f)) x =
      (integerKernelConvolutionRealExponentCLM p hp
        (frequencyProjectionIntegerKernel c hc h)
        (finiteSupportLpInclusion (P := ENNReal.ofReal p) f)) x
    rw [integerKernelConvolutionRealExponentCLM_apply]
    rw [frequencyProjectionLpProjection_apply_finite c hc hp h f x]
    have hfun :
        (finiteSupportLpInclusion (P := ENNReal.ofReal p) f : ℤ → ℂ) =
          (f : ℤ → ℂ) := by
      funext n
      exact finiteSupportLpInclusion_apply f n
    rw [hfun, integerKernelConvolution_eq_finsupp_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  apply ContinuousLinearMap.ext
  intro f
  exact congrFun
    (DenseRange.equalizer hdense U.continuous V.continuous hcompose) f

#print axioms frequencyProjectionLpProjection_eq_kernelCLM_all

/-- On every `ℓ^p` input, the common-domain positive-index projection
agrees pointwise with the checked Fourier multiplier projection. -/
theorem mszFrequencyProjection_apply_eq_lpProjection
    (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (h : ℕ) (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (x : ℤ) :
    mszFrequencyProjection c hc (h : ℤ) (f : ℤ → ℂ) x =
      (frequencyProjectionLpProjection c hc hp h f) x := by
  have hf : MemL1PlusLInfty (f : ℤ → ℂ) :=
    memL1PlusLInfty_iff_memℓp_infty.mpr
      ((lp.memℓp f).of_exponent_ge (by simp : ENNReal.ofReal p ≤ ⊤))
  rw [mszFrequencyProjection, dif_pos (Int.natCast_nonneg h),
    integerKernelConvolutionAmbientLinearMap_apply _ hf]
  simp only [Int.toNat_natCast]
  rw [frequencyProjectionLpProjection_eq_kernelCLM_all c hc p hp h,
    integerKernelConvolutionRealExponentCLM_apply]

#print axioms mszFrequencyProjection_apply_eq_lpProjection

/-- The square coefficients of the source's natural-index resolution
are summable at each integer coordinate. -/
theorem frequencyProjectionLpProjection_square_summable
    (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    Summable (fun h : ℕ =>
      ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2) := by
  let B := frequencyProjectionFiniteSquareFunctionBound p * ‖f‖
  have hBnonneg : 0 ≤ B := by
    dsimp [B, frequencyProjectionFiniteSquareFunctionBound]
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
        (frequencyProjectionSignedLpBound_nonneg hp)
    · exact norm_nonneg _
  have hbound (N : ℕ) :
      ∑ h ∈ Finset.range N,
        ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2 ≤ B ^ 2 := by
    obtain ⟨g, hg, hnorm⟩ :=
      frequencyProjectionFiniteSquareFunction_memLp_norm_le hp c hc N f
    have hcoord : g x = Real.sqrt
        (∑ h ∈ Finset.range (N + 1),
          ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2) := by
      rw [hg x]
      exact finiteProjectionSquareFunction_eq_range c hc hp N f x
    have hsumNonneg : 0 ≤ ∑ h ∈ Finset.range (N + 1),
        ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2 :=
      Finset.sum_nonneg (by intro h hh; exact sq_nonneg _)
    have hgnonneg : 0 ≤ g x := by rw [hcoord]; exact Real.sqrt_nonneg _
    have hgBound : g x ≤ B := by
      calc
        g x = ‖g x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hgnonneg]
        _ ≤ ‖g‖ := lp.norm_apply_le_norm
          (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)) g x
        _ ≤ B := hnorm
    have hsumSq : (g x) ^ 2 =
        ∑ h ∈ Finset.range (N + 1),
          ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2 := by
      rw [hcoord, Real.sq_sqrt hsumNonneg]
    calc
      ∑ h ∈ Finset.range N,
          ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2 ≤
        ∑ h ∈ Finset.range (N + 1),
          ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_succ N))
          (by intro h hh hnot; exact sq_nonneg _)
      _ = (g x) ^ 2 := hsumSq.symm
      _ ≤ B ^ 2 := by nlinarith
  exact summable_of_sum_range_le (by intro h; exact sq_nonneg _) hbound

#print axioms frequencyProjectionLpProjection_square_summable

/-- The actual signed `MSZ.AdmissibleData` square coefficients are
summable; all strictly negative terms vanish. -/
theorem mszFrequencyProjection_square_summable
    (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    Summable (fun h : ℤ =>
      ‖mszFrequencyProjection c hc h (f : ℤ → ℂ) x‖ ^ 2) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · have hnat := frequencyProjectionLpProjection_square_summable
      c hc p hp f x
    convert hnat using 1
    funext h
    rw [mszFrequencyProjection_apply_eq_lpProjection c hc p hp h f x]
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    have hlt : -(n : ℤ) < 0 := by omega
    simp [mszFrequencyProjection, hn0]

#print axioms mszFrequencyProjection_square_summable

/-- The signed integer-index square sum is exactly the source's
natural-index Fourier square sum. -/
theorem mszFrequencyProjection_square_tsum_eq
    (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    (∑' h : ℤ,
      ‖mszFrequencyProjection c hc h (f : ℤ → ℂ) x‖ ^ 2) =
      ∑' h : ℕ, ‖frequencyProjectionLpProjection c hc hp h f x‖ ^ 2 := by
  let a : ℤ → ℝ := fun h =>
    ‖mszFrequencyProjection c hc h (f : ℤ → ℂ) x‖ ^ 2
  have hnat : Summable (fun h : ℕ => a h) := by
    change Summable (fun h : ℕ =>
      ‖mszFrequencyProjection c hc h (f : ℤ → ℂ) x‖ ^ 2)
    convert frequencyProjectionLpProjection_square_summable
      c hc p hp f x using 1
    funext h
    rw [mszFrequencyProjection_apply_eq_lpProjection c hc p hp h f x]
  have hnegZero (n : ℕ) : a (-(↑n + 1)) = 0 := by
    have hlt : -(↑n + 1 : ℤ) < 0 := by omega
    have hzero : mszFrequencyProjection c hc (-(↑n + 1 : ℤ))
        (f : ℤ → ℂ) x = 0 := by
      rw [mszFrequencyProjection, dif_neg (not_le.mpr hlt)]
      rfl
    change ‖mszFrequencyProjection c hc (-(↑n + 1 : ℤ))
      (f : ℤ → ℂ) x‖ ^ 2 = 0
    rw [hzero]
    simp
  have hneg : Summable (fun n : ℕ => a (-(↑n + 1))) := by
    simp only [hnegZero]
    exact summable_zero
  rw [show (∑' h : ℤ,
      ‖mszFrequencyProjection c hc h (f : ℤ → ℂ) x‖ ^ 2) =
      ∑' h : ℤ, a h from rfl,
    tsum_of_nat_of_neg_add_one hnat hneg]
  simp only [hnegZero, tsum_zero, add_zero]
  congr 1
  funext h
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (mszFrequencyProjection_apply_eq_lpProjection c hc p hp h f x)

#print axioms mszFrequencyProjection_square_tsum_eq

/-- The common-domain signed projections satisfy the exact
`MSZ.AdmissibleData.square_function_bound` field at every `p>1`. -/
theorem mszFrequencyProjection_squareFunction_bound
    (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, g x = projectionSquareFunction
        (mszFrequencyProjection c hc) f x) ∧
      ‖g‖ ≤ frequencyProjectionFiniteSquareFunctionBound p * ‖f‖ := by
  obtain ⟨g, hg, hnorm⟩ :=
    frequencyProjectionSquareFunction_memLp_norm_le hp c hc f
  refine ⟨g, ?_, hnorm⟩
  intro x
  rw [hg x]
  unfold frequencyProjectionSquareFunction projectionSquareFunction
  rw [mszFrequencyProjection_square_tsum_eq c hc p hp f x]

#print axioms mszFrequencyProjection_squareFunction_bound

/-- The localized grid increment built from the common-domain
projection is the already checked concrete localized increment. -/
theorem mszGridIncrement_commonProjection_eq_localizedFamily
    (c : ℝ) (hc : 1 < c) (j : ℤ) (l : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2)
    (i : ℤ × Fin (2 ^ l)) (x : ℤ) :
    mszGridIncrement (interpolatedFloorPowerMSZKernel c)
      i.1 l i.2.val
      (mszFrequencyProjection c hc (j + i.1) (f : ℤ → ℂ)) x =
      localizedIncrementFamily c hc j l f i x := by
  have hfun : mszFrequencyProjection c hc (j + i.1) (f : ℤ → ℂ) =
      (localizedSignedFrequencyProjectionL2 c hc (j + i.1) f : ℤ → ℂ) := by
    funext y
    rw [← mszFrequencyProjectionL2_agree c hc (j + i.1) f y,
      mszFrequencyProjectionL2_eq_localizedSigned]
  rw [hfun]
  exact mszGridIncrement_projected_eq_localizedFamily c hc j l f i x

#print axioms mszGridIncrement_commonProjection_eq_localizedFamily

/-- Exact summability for the common-domain localized grid increments. -/
theorem mszGridIncrement_commonProjection_square_summable
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    Summable (fun i : ℤ × Fin (2 ^ l) =>
      ‖mszGridIncrement (interpolatedFloorPowerMSZKernel c)
        i.1 l i.2.val
        (mszFrequencyProjection c hc (j + i.1) (f : ℤ → ℂ)) x‖ ^ 2) := by
  convert mszGridIncrement_projected_square_summable
    c hc hcNon j l f x using 1
  funext i
  rw [mszGridIncrement_commonProjection_eq_localizedFamily,
    ← mszGridIncrement_projected_eq_localizedFamily c hc j l f i x]

/-- Exact pointwise agreement of the abstract localized square function
with the already checked concrete one. -/
theorem mszLocalizedIncrementSquareFunction_eq
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    localizedIncrementSquareFunction (interpolatedFloorPowerMSZKernel c)
      (mszFrequencyProjection c hc) j l f x =
      localizedUnweightedIncrementSquareFunction c hc hcNon j l f x := by
  unfold localizedIncrementSquareFunction
    localizedUnweightedIncrementSquareFunction
  congr 1
  apply tsum_congr
  intro i
  rw [mszGridIncrement_commonProjection_eq_localizedFamily]
  rfl

#print axioms mszGridIncrement_commonProjection_square_summable
#print axioms mszLocalizedIncrementSquareFunction_eq

/-- The common-domain projections and interpolated kernel meet the
localized increment bound in `MSZ.AdmissibleData` with the exact
coefficient from `ha:square`. -/
theorem mszLocalizedIncrementSquareFunction_bound
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    ∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x, G x = localizedIncrementSquareFunction
        (interpolatedFloorPowerMSZKernel c)
        (mszFrequencyProjection c hc) j l f x) ∧
      ‖G‖ ≤ (2 : ℝ) ^ (-(l : ℝ) / 2) *
        localizedSquareCoefficient c hc hcNon j l * ‖f‖ := by
  obtain ⟨G, hGpoint, hGbound⟩ :=
    localizedSquareEstimate c hc hcNon j l f
  refine ⟨G, ?_, hGbound⟩
  intro x
  rw [hGpoint x, mszLocalizedIncrementSquareFunction_eq]

#print axioms mszLocalizedIncrementSquareFunction_bound

/-- The exact `ha:square` coefficient used in the MSZ data is nonnegative. -/
theorem mszLocalizedSquareCoefficient_nonneg
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j : ℤ) (l : ℕ) :
    0 ≤ localizedSquareCoefficient c hc hcNon j l := by
  unfold localizedSquareCoefficient
  have hD : 0 ≤ localizedUnweightedIncrementConstant c hc hcNon := by
    unfold localizedUnweightedIncrementConstant
    exact le_trans (by norm_num : (0 : ℝ) ≤ 4) (le_max_left _ _)
  have hL : 0 ≤ frequencyProjectionFiniteSquareFunctionBound 2 := by
    unfold frequencyProjectionFiniteSquareFunctionBound
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (frequencyProjectionSignedLpBound_nonneg (by norm_num))
  have hM : 0 ≤ min (1 : ℝ)
      (Real.rpow 2 ((l : ℝ) - localizedIncrementSigma c * |(j : ℝ)|)) :=
    le_min (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  exact mul_nonneg (mul_nonneg hD hL) hM

#print axioms mszLocalizedSquareCoefficient_nonneg

