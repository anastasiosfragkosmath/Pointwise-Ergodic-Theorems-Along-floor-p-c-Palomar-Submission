module

public import FractionalPrimes.Literature.Harmonic.MSZKernelBridge
public import FractionalPrimes.Literature.Harmonic.FrequencyResolutionLp
public import FractionalPrimes.GeneralDiscreteLpBridge

/-! The common sequence domain of the paper's Fourier projections. -/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.MSZ
open FractionalPrimes.Literature.Multiplier

noncomputable section

local instance : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩

/-- The source projection domain `ℓ¹+ℓ∞` is closed under addition. -/
theorem memL1PlusLInfty_add {f g : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) (hg : MemL1PlusLInfty g) :
    MemL1PlusLInfty (f + g) := by
  obtain ⟨f₁, fInf, hf₁, hfInf, rfl⟩ := hf
  obtain ⟨g₁, gInf, hg₁, hgInf, rfl⟩ := hg
  refine ⟨f₁ + g₁, fInf + gInf, hf₁.add hg₁, hfInf.add hgInf, ?_⟩
  ext x
  simp only [Pi.add_apply]
  abel

/-- The source projection domain `ℓ¹+ℓ∞` is closed under complex scalars. -/
theorem memL1PlusLInfty_smul (a : ℂ) {f : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) :
    MemL1PlusLInfty (a • f) := by
  obtain ⟨f₁, fInf, hf₁, hfInf, rfl⟩ := hf
  refine ⟨a • f₁, a • fInf, ?_, ?_, ?_⟩
  · exact hf₁.const_smul a
  · exact hfInf.const_smul a
  · ext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_add]

/-- The exact `ℓ¹+ℓ∞` common domain is a complex vector subspace of
all sequences, so a linear projection action can be extended from it. -/
def l1PlusLInftySubmodule : Submodule ℂ (ℤ → ℂ) where
  carrier := {f | MemL1PlusLInfty f}
  zero_mem' := by
    refine ⟨0, 0, zero_memℓp, zero_memℓp, ?_⟩
    simp
  add_mem' := by
    intro f g hf hg
    exact memL1PlusLInfty_add hf hg
  smul_mem' := by
    intro a f hf
    exact memL1PlusLInfty_smul a hf

#print axioms l1PlusLInftySubmodule

/-- On counting-measure sequences, `ℓ¹` is contained in `ℓ∞`, so the
source's algebraic sum domain is exactly the bounded sequences. -/
theorem memL1PlusLInfty_iff_memℓp_infty {f : ℤ → ℂ} :
    MemL1PlusLInfty f ↔ Memℓp f ⊤ := by
  constructor
  · rintro ⟨f₁, fInf, hf₁, hfInf, rfl⟩
    exact (hf₁.of_exponent_ge (by simp : (1 : ℝ≥0∞) ≤ ⊤)).add hfInf
  · intro hf
    refine ⟨0, f, zero_memℓp, hf, ?_⟩
    simp

#print axioms memL1PlusLInfty_iff_memℓp_infty

/-- An absolutely summable Fourier projection kernel convolves pointwise
with every source-domain sequence, including its `ℓ∞` component. -/
theorem integerKernelConvolutionExistsAt_of_memL1PlusLInfty
    (K : IntegerL1Kernel) {f : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) (x : ℤ) :
    IntegerKernelConvolutionExistsAt K f x := by
  let F : lp (fun _ : ℤ => ℂ) ⊤ :=
    ⟨f, memL1PlusLInfty_iff_memℓp_infty.mp hf⟩
  have hbound : Summable (fun m : ℤ => ‖K.coeff m‖ * ‖F‖) :=
    K.summable_norm.mul_right ‖F‖
  have hnorm : Summable (fun m : ℤ => ‖K.coeff m * f (x - m)‖) :=
    hbound.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm ENNReal.top_ne_zero F (x - m))
        (norm_nonneg _))
  change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
  rw [MeasureTheory.integrable_count_iff]
  exact hnorm

#print axioms integerKernelConvolutionExistsAt_of_memL1PlusLInfty

/-- Absolute convergence makes convolution additive on the exact
`ℓ¹+ℓ∞` domain. -/
theorem integerKernelConvolution_add_of_memL1PlusLInfty
    (K : IntegerL1Kernel) {f g : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) (hg : MemL1PlusLInfty g) (x : ℤ) :
    integerKernelConvolution K (f + g) x =
      integerKernelConvolution K f x + integerKernelConvolution K g x := by
  have hfg := integerKernelConvolutionExistsAt_of_memL1PlusLInfty
    K (memL1PlusLInfty_add hf hg) x
  have hf' := integerKernelConvolutionExistsAt_of_memL1PlusLInfty K hf x
  have hg' := integerKernelConvolutionExistsAt_of_memL1PlusLInfty K hg x
  have hfs : Summable (fun m : ℤ => K.coeff m * f (x - m)) :=
    (MeasureTheory.integrable_count_iff.mp hf').of_norm
  have hgs : Summable (fun m : ℤ => K.coeff m * g (x - m)) :=
    (MeasureTheory.integrable_count_iff.mp hg').of_norm
  rw [integerKernelConvolution_eq_tsum K _ x hfg,
    integerKernelConvolution_eq_tsum K _ x hf',
    integerKernelConvolution_eq_tsum K _ x hg']
  simp only [Pi.add_apply, mul_add]
  exact Summable.tsum_add hfs hgs

/-- Absolute convergence makes convolution complex-linear in the input
on the source's `ℓ¹+ℓ∞` domain. -/
theorem integerKernelConvolution_smul_of_memL1PlusLInfty
    (K : IntegerL1Kernel) (a : ℂ) {f : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) (x : ℤ) :
    integerKernelConvolution K (a • f) x =
      a • integerKernelConvolution K f x := by
  have haf := integerKernelConvolutionExistsAt_of_memL1PlusLInfty
    K (memL1PlusLInfty_smul a hf) x
  have hf' := integerKernelConvolutionExistsAt_of_memL1PlusLInfty K hf x
  have hfs : Summable (fun m : ℤ => K.coeff m * f (x - m)) :=
    (MeasureTheory.integrable_count_iff.mp hf').of_norm
  rw [integerKernelConvolution_eq_tsum K _ x haf,
    integerKernelConvolution_eq_tsum K _ x hf']
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑' m : ℤ, K.coeff m * (a * f (x - m))) =
        ∑' m : ℤ, a * (K.coeff m * f (x - m)) := by
      apply tsum_congr
      intro m
      ring
    _ = a * ∑' m : ℤ, K.coeff m * f (x - m) := by
      rw [tsum_mul_left]

#print axioms integerKernelConvolution_add_of_memL1PlusLInfty
#print axioms integerKernelConvolution_smul_of_memL1PlusLInfty

/-- Convolution by an absolutely summable kernel is a genuine linear
operator on the source's common projection domain. -/
noncomputable def integerKernelConvolutionL1PlusLInftyLinearMap
    (K : IntegerL1Kernel) :
    l1PlusLInftySubmodule →ₗ[ℂ] (ℤ → ℂ) where
  toFun f := integerKernelConvolution K f.val
  map_add' f g := by
    funext x
    exact integerKernelConvolution_add_of_memL1PlusLInfty K
      f.property g.property x
  map_smul' a f := by
    funext x
    exact integerKernelConvolution_smul_of_memL1PlusLInfty K a
      f.property x

/-- Extend the source-domain convolution action to the ambient sequence
vector space, as required by the generic MSZ projection interface. -/
noncomputable def integerKernelConvolutionAmbientLinearMap
    (K : IntegerL1Kernel) : (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  Classical.choose (LinearMap.exists_extend
    (integerKernelConvolutionL1PlusLInftyLinearMap K))

/-- The ambient extension agrees with the actual convolution on every
`ℓ¹+ℓ∞` input; its values elsewhere are irrelevant to the MSZ theorem. -/
theorem integerKernelConvolutionAmbientLinearMap_apply
    (K : IntegerL1Kernel) {f : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) :
    integerKernelConvolutionAmbientLinearMap K f =
      integerKernelConvolution K f := by
  have h := Classical.choose_spec (LinearMap.exists_extend
    (integerKernelConvolutionL1PlusLInftyLinearMap K))
  have hfun := congrArg
    (fun T : l1PlusLInftySubmodule →ₗ[ℂ] (ℤ → ℂ) => T ⟨f, hf⟩) h
  simpa [integerKernelConvolutionAmbientLinearMap,
    integerKernelConvolutionL1PlusLInftyLinearMap] using hfun

#print axioms integerKernelConvolutionAmbientLinearMap_apply

/-- Absolutely summable convolution preserves bounded sequences, hence
the source's `ℓ¹+ℓ∞` projection domain. -/
theorem integerKernelConvolution_memL1PlusLInfty
    (K : IntegerL1Kernel) {f : ℤ → ℂ}
    (hf : MemL1PlusLInfty f) :
    MemL1PlusLInfty (integerKernelConvolution K f) := by
  let F : lp (fun _ : ℤ => ℂ) ⊤ :=
    ⟨f, memL1PlusLInfty_iff_memℓp_infty.mp hf⟩
  have hbound (x : ℤ) :
      ‖integerKernelConvolution K f x‖ ≤
        (∑' m : ℤ, ‖K.coeff m‖) * ‖F‖ := by
    have hexists := integerKernelConvolutionExistsAt_of_memL1PlusLInfty K hf x
    have hterm : Summable (fun m : ℤ => K.coeff m * f (x - m)) :=
      (MeasureTheory.integrable_count_iff.mp hexists).of_norm
    have hnorm : Summable (fun m : ℤ => ‖K.coeff m * f (x - m)‖) :=
      MeasureTheory.integrable_count_iff.mp hexists
    calc
      ‖integerKernelConvolution K f x‖ =
          ‖∑' m : ℤ, K.coeff m * f (x - m)‖ := by
        rw [integerKernelConvolution_eq_tsum K f x hexists]
      _ ≤ ∑' m : ℤ, ‖K.coeff m * f (x - m)‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' m : ℤ, ‖K.coeff m‖ * ‖F‖ := by
        apply Summable.tsum_le_tsum (fun m => ?_) hnorm
          (K.summable_norm.mul_right ‖F‖)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero F (x - m))
          (norm_nonneg _)
      _ = (∑' m : ℤ, ‖K.coeff m‖) * ‖F‖ := by
        rw [tsum_mul_right]
  apply memL1PlusLInfty_iff_memℓp_infty.mpr
  apply memℓp_infty
  exact ⟨(∑' m : ℤ, ‖K.coeff m‖) * ‖F‖, by
    rintro y ⟨x, rfl⟩
    exact hbound x⟩

#print axioms integerKernelConvolution_memL1PlusLInfty

/-- The source Fourier projection and its summable-kernel convolution
agree exactly on finite sequences at exponent two. -/
theorem frequencyProjectionIntegerKernel_apply_finite
    (c : ℝ) (hc : 1 < c) (h : ℕ)
    (f : ℤ →₀ ℂ) (x : ℤ) :
    integerKernelConvolution (frequencyProjectionIntegerKernel c hc h)
      (f : ℤ → ℂ) x =
      (frequencyProjectionLpProjection c hc (by norm_num : 1 < (2 : ℝ)) h
        (finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f)) x := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  rw [integerKernelConvolution_eq_finsupp_sum,
    frequencyProjectionLpProjection_apply_finite c hc (by norm_num) h f x]
  apply Finset.sum_congr rfl
  intro n hn
  ring

#print axioms frequencyProjectionIntegerKernel_apply_finite

/-- The sequence-space continuous `ℓ²` action of an absolutely summable
kernel, transported through the exact counting-measure isometry. -/
noncomputable def integerKernelConvolutionSequenceCLM
    (K : IntegerL1Kernel) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  countLpToLpIsometry.toContinuousLinearMap.comp
    ((integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K).comp
      lpToCountLpIsometry.toContinuousLinearMap)

theorem integerKernelConvolutionSequenceCLM_apply
    (K : IntegerL1Kernel) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    integerKernelConvolutionSequenceCLM K f x =
      integerKernelConvolution K (f : ℤ → ℂ) x := by
  change countLpToLp
    (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K
      (lpToCountLp f)) x = _
  rw [countLpToLp_apply, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  congr 1
  funext n
  exact lpToCountLp_apply f n

#print axioms integerKernelConvolutionSequenceCLM_apply

/-- The existing counting-measure to sequence bridge is continuous at
the multiplier's exact `ofReal 2` exponent. -/
noncomputable def countLpToMultiplierExponentCLM :
    Lp ℂ (ENNReal.ofReal (2 : ℝ)) (Measure.count : Measure ℤ) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)) :=
  (countLpToGeneralLp (p := ENNReal.ofReal (2 : ℝ))
    (by norm_num) (by simp)).mkContinuous 1 (by
    intro f
    rw [countLpToGeneralLp_norm]
    simp)

/-- The reverse bridge is continuous at the same exponent. -/
noncomputable def multiplierExponentToCountLpCLM :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)) →L[ℂ]
      Lp ℂ (ENNReal.ofReal (2 : ℝ)) (Measure.count : Measure ℤ) :=
  (generalLpToCountLp (p := ENNReal.ofReal (2 : ℝ))
    (by norm_num) (by simp)).mkContinuous 1 (by
    intro f
    rw [generalLpToCountLp_norm]
    simp)

#print axioms countLpToMultiplierExponentCLM
#print axioms multiplierExponentToCountLpCLM

/-- Continuous convolution on the multiplier's exact exponent presentation,
constructed directly from the general counting-measure bridges. -/
noncomputable def integerKernelConvolutionMultiplierCLM
    (K : IntegerL1Kernel) :
    lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)) →L[ℂ]
      lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)) :=
  countLpToMultiplierExponentCLM.comp
    ((integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ)) K).comp
      multiplierExponentToCountLpCLM)

theorem integerKernelConvolutionMultiplierCLM_apply
    (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal (2 : ℝ)))
    (x : ℤ) :
    integerKernelConvolutionMultiplierCLM K f x =
      integerKernelConvolution K (f : ℤ → ℂ) x := by
  change countLpToGeneralLp (by norm_num) (by simp)
    (integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ)) K
      (generalLpToCountLp (by norm_num) (by simp) f)) x = _
  rw [countLpToGeneralLp_apply, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  congr 1
  funext n
  exact generalLpToCountLp_apply (by norm_num) (by simp) f n

#print axioms integerKernelConvolutionMultiplierCLM_apply

/-- The Fourier projection is convolution by its absolutely summable
coefficient kernel on every sequence at the source multiplier exponent. -/
theorem frequencyProjectionLpProjection_eq_kernelCLM
    (c : ℝ) (hc : 1 < c) (h : ℕ) :
    frequencyProjectionLpProjection c hc (by norm_num : 1 < (2 : ℝ)) h =
      integerKernelConvolutionMultiplierCLM
        (frequencyProjectionIntegerKernel c hc h) := by
  let e := finiteSupportLpInclusion
    (P := ENNReal.ofReal (2 : ℝ))
  let U := frequencyProjectionLpProjection c hc
    (by norm_num : 1 < (2 : ℝ)) h
  let V := integerKernelConvolutionMultiplierCLM
    (frequencyProjectionIntegerKernel c hc h)
  have hdense : DenseRange e :=
    finiteSupportLpInclusion_denseRange (P := ENNReal.ofReal (2 : ℝ))
      ENNReal.ofReal_ne_top
  have hcompose : U ∘ e = V ∘ e := by
    funext f
    apply lp.ext
    funext x
    change (frequencyProjectionLpProjection c hc
      (by norm_num : 1 < (2 : ℝ)) h
      (finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f)) x =
      (integerKernelConvolutionMultiplierCLM
        (frequencyProjectionIntegerKernel c hc h)
        (finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f)) x
    rw [integerKernelConvolutionMultiplierCLM_apply]
    rw [← frequencyProjectionIntegerKernel_apply_finite c hc h f x]
    congr 1
  have hoperator : U = V := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrFun
      (DenseRange.equalizer hdense U.continuous V.continuous hcompose) f
  exact hoperator

#print axioms frequencyProjectionLpProjection_eq_kernelCLM

private theorem lpExponentCast_apply {p q : ℝ≥0∞} (hpq : p = q)
    (f : lp (fun _ : ℤ => ℂ) p) (x : ℤ) :
    (hpq ▸ f) x = f x := by
  cases hpq
  rfl

/-- The source's literal-`2` localized projection has the same pointwise
action as its `ofReal 2` multiplier presentation. -/
theorem localizedFrequencyProjectionL2_apply_eq_multiplier
    (c : ℝ) (hc : 1 < c) (h : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    localizedFrequencyProjectionL2 c hc h f x =
      (frequencyProjectionLpProjection c hc
        (by norm_num : 1 < (2 : ℝ)) h
        (frequencyProjectionLpTwoToMultiplier f)) x := by
  by_cases hh : h = 0
  · subst h
    simp [localizedFrequencyProjectionL2, frequencyProjectionLpProjection,
      frequencyProjectionPartialLpOperatorL2, lpExponentCast_apply]
  · simp [localizedFrequencyProjectionL2, frequencyProjectionLpProjection, hh,
      frequencyProjectionPartialLpOperatorL2, lp.coeFn_sub, Pi.sub_apply,
      lpExponentCast_apply]

#print axioms localizedFrequencyProjectionL2_apply_eq_multiplier

/-- Exact arbitrary-input `ℓ²` agreement of the paper's Fourier
projection with convolution by its summable coefficient kernel. -/
theorem localizedFrequencyProjectionL2_eq_kernelConvolution
    (c : ℝ) (hc : 1 < c) (h : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    localizedFrequencyProjectionL2 c hc h f x =
      integerKernelConvolution
        (frequencyProjectionIntegerKernel c hc h) (f : ℤ → ℂ) x := by
  rw [localizedFrequencyProjectionL2_apply_eq_multiplier,
    frequencyProjectionLpProjection_eq_kernelCLM,
    integerKernelConvolutionMultiplierCLM_apply]
  congr 1
  funext n
  exact lpExponentCast_apply frequencyProjectionLpTwoExponent.symm f n

#print axioms localizedFrequencyProjectionL2_eq_kernelConvolution

/-- The source's signed Fourier projections as common linear maps on
all complex sequences. Negative indices are exactly zero. -/
noncomputable def mszFrequencyProjection
    (c : ℝ) (hc : 1 < c) (h : ℤ) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  if hh : 0 ≤ h then
    integerKernelConvolutionAmbientLinearMap
      (frequencyProjectionIntegerKernel c hc h.toNat)
  else 0

/-- The matching signed projection action on `ℓ²`. -/
noncomputable def mszFrequencyProjectionL2
    (c : ℝ) (hc : 1 < c) (h : ℤ) :
    lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  if hh : 0 ≤ h then
    (integerKernelConvolutionSequenceCLM
      (frequencyProjectionIntegerKernel c hc h.toNat)).toLinearMap
  else 0

/-- The common-domain projection preserves `ℓ¹+ℓ∞`. -/
theorem mszFrequencyProjection_preserve_l1_add_linf
    (c : ℝ) (hc : 1 < c) (h : ℤ)
    {f : ℤ → ℂ} (hf : MemL1PlusLInfty f) :
    MemL1PlusLInfty (mszFrequencyProjection c hc h f) := by
  by_cases hh : 0 ≤ h
  · rw [mszFrequencyProjection, dif_pos hh,
      integerKernelConvolutionAmbientLinearMap_apply _ hf]
    exact integerKernelConvolution_memL1PlusLInfty _ hf
  · simp only [mszFrequencyProjection, dif_neg hh, LinearMap.zero_apply]
    exact ⟨0, 0, zero_memℓp, zero_memℓp, by simp⟩

/-- Exact pointwise agreement between the two signed projection
representations on every `ℓ²` input. -/
theorem mszFrequencyProjectionL2_agree
    (c : ℝ) (hc : 1 < c) (h : ℤ)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    mszFrequencyProjectionL2 c hc h f x =
      mszFrequencyProjection c hc h (f : ℤ → ℂ) x := by
  have hf : MemL1PlusLInfty (f : ℤ → ℂ) :=
    memL1PlusLInfty_iff_memℓp_infty.mpr
      ((lp.memℓp f).of_exponent_ge (by simp : (2 : ℝ≥0∞) ≤ ⊤))
  by_cases hh : 0 ≤ h
  · rw [mszFrequencyProjectionL2, dif_pos hh,
      mszFrequencyProjection, dif_pos hh,
      integerKernelConvolutionAmbientLinearMap_apply _ hf]
    exact integerKernelConvolutionSequenceCLM_apply _ f x
  · simp [mszFrequencyProjectionL2, mszFrequencyProjection, hh]

#print axioms mszFrequencyProjection_preserve_l1_add_linf
#print axioms mszFrequencyProjectionL2_agree

/-- The MSZ signed projection family is exactly the paper's checked
signed Fourier resolution on `ℓ²`. -/
theorem mszFrequencyProjectionL2_eq_localizedSigned
    (c : ℝ) (hc : 1 < c) (h : ℤ)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    mszFrequencyProjectionL2 c hc h f =
      localizedSignedFrequencyProjectionL2 c hc h f := by
  by_cases hh : 0 ≤ h
  · apply lp.ext
    funext x
    rw [mszFrequencyProjectionL2, dif_pos hh,
      localizedSignedFrequencyProjectionL2_of_nonneg c hc h hh]
    change (integerKernelConvolutionSequenceCLM
      (frequencyProjectionIntegerKernel c hc h.toNat) f) x =
        localizedFrequencyProjectionL2 c hc h.toNat f x
    rw [integerKernelConvolutionSequenceCLM_apply,
      localizedFrequencyProjectionL2_eq_kernelConvolution]
  · have hneg : h < 0 := lt_of_not_ge hh
    simp [mszFrequencyProjectionL2, hh,
      localizedSignedFrequencyProjectionL2_of_neg c hc h hneg]

#print axioms mszFrequencyProjectionL2_eq_localizedSigned

/-- Adding one symmetric shell contributes only its positive-index projection:
the negative-index projection is zero. -/
private theorem symmetricSum_succ {α : Type*} [AddCommMonoid α]
    (g : ℤ → α) (hg : ∀ h : ℤ, h < 0 → g h = 0) (J : ℕ) :
    (∑ h ∈ Finset.Icc (-(↑(J + 1) : ℤ)) (↑(J + 1) : ℤ), g h) =
      (∑ h ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), g h) + g (↑(J + 1) : ℤ) := by
  have hset : Finset.Icc (-(↑(J + 1) : ℤ)) (↑(J + 1) : ℤ) =
      insert (-(↑(J + 1) : ℤ))
        (insert (↑(J + 1) : ℤ) (Finset.Icc (-(J : ℤ)) (J : ℤ))) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert, Finset.sum_insert]
  · have hneg : g (-(↑(J + 1) : ℤ)) = 0 := hg _ (by omega)
    simp only [hneg, zero_add, add_comm]
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

/-- The symmetric finite sum of signed projections is exactly the
partial Fourier resolution at the same scale. -/
theorem mszFrequencyProjectionL2_symmetricSum
    (c : ℝ) (hc : 1 < c) (f : lp (fun _ : ℤ => ℂ) 2) (J : ℕ) :
    (∑ h ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
      mszFrequencyProjectionL2 c hc h f) =
      frequencyProjectionPartialLpOperatorL2 c hc J f := by
  have hlocalized :
      (∑ h ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
        localizedSignedFrequencyProjectionL2 c hc h f) =
        frequencyProjectionPartialLpOperatorL2 c hc J f := by
    induction J with
    | zero =>
        simp [localizedSignedFrequencyProjectionL2,
          localizedFrequencyProjectionL2]
    | succ J ih =>
        rw [symmetricSum_succ
          (localizedSignedFrequencyProjectionL2 c hc · f)
          (by intro h hh; exact localizedSignedFrequencyProjectionL2_of_neg c hc h hh f) J,
          ih]
        rw [localizedSignedFrequencyProjectionL2_of_nonneg c hc _ (by omega)]
        simp [localizedFrequencyProjectionL2]
  simp_rw [mszFrequencyProjectionL2_eq_localizedSigned]
  exact hlocalized

/-- The signed common-domain Fourier projections satisfy the exact
`MSZ.AdmissibleData.symmetric_resolution` field. -/
theorem mszFrequencyProjectionL2_symmetricResolution
    (c : ℝ) (hc : 1 < c) (f : lp (fun _ : ℤ => ℂ) 2) :
    Filter.Tendsto (fun J : ℕ =>
      ‖(∑ h ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          mszFrequencyProjectionL2 c hc h f) - f‖)
      Filter.atTop (nhds 0) := by
  simp_rw [mszFrequencyProjectionL2_symmetricSum c hc f]
  exact tendsto_iff_norm_sub_tendsto_zero.mp
    (frequencyProjectionPartialLpOperator_tendsto_L2 c hc f)

#print axioms mszFrequencyProjectionL2_symmetricSum
#print axioms mszFrequencyProjectionL2_symmetricResolution

end

end FractionalPrimes.Literature.Harmonic

end
