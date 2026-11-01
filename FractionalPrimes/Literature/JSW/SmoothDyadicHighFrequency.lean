module

public import FractionalPrimes.Literature.JSW.SmoothDyadicConvolutionEnergy
public import FractionalPrimes.Literature.JSW.SmoothDyadicFirstMoment
public import FractionalPrimes.Literature.JSW.DyadicAverageL2Expansion

/-! The actual smooth/dyadic high-frequency branch, with its source scale ratio. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem dyadicStepPsiSmoothing_energy_le
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ h : ℝ} (hτ : 0 < τ) (hh : 0 < h)
    {g : ℝ → ℂ} (hg : MemLp g 2 volume) (hgmeas : Measurable g)
    (hstep : ∀ j : ℤ, ∃ c : ℂ, ∀ x,
      x ∈ Set.Ico ((j : ℝ)*h) (((j+1 : ℤ) : ℝ)*h) → g x = c) :
    let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
    MemLp (fun x : ℝ => jswConvolution μ g x-g x) 2 volume ∧
    lpNorm (fun x : ℝ => jswConvolution μ g x-g x) 2 volume ^ 2 ≤
      (8*τ/h) * lpNorm g 2 volume ^ 2 := by
  let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
  letI : IsProbabilityMeasure μ := initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  obtain ⟨hmoment, hbound⟩ := initialSquarePsiDilate_firstMoment hSupp hτ
  obtain ⟨hmem, he⟩ := dyadicStepProbabilitySmoothing_energy_le μ hmoment hh hg hgmeas hstep
  refine ⟨hmem, he.trans ?_⟩
  calc
    _ ≤ (4/h * lpNorm g 2 volume ^ 2) * (2*τ) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (div_nonneg (by norm_num) hh.le) (sq_nonneg _))
    _ = _ := by ring

theorem dyadicDifference_fine_average
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {m j : ℤ} (hmj : m < j) (x : ℝ) :
    dyadicAverage m (dyadicDifference j f) x = dyadicDifference j f x := by
  change dyadicAverage m (dyadicAverage (j-1) f - dyadicAverage j f) x = _
  rw [dyadicAverage_sub_of_memLp_two
    (memLp_dyadicAverage_two_of_memLp hf (j-1)) (memLp_dyadicAverage_two_of_memLp hf j)]
  rw [dyadicAverage_comp_of_le (by omega : m ≤ j-1), dyadicAverage_comp_of_le (by omega : m ≤ j)]
  rfl

theorem smoothDyadic_highFrequency_energy
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) {m j : ℤ} (hmj : m < j)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
    let g := dyadicDifference j f
    MemLp (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ∧
    lpNorm (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ^ 2 ≤
      (8*τ/(2 : ℝ)^(j-1)) * lpNorm g 2 volume ^ 2 := by
  have hh : 0 < (2 : ℝ)^(j-1) := zpow_pos (by norm_num) _
  have hg := memLp_dyadicDifference_two_of_memLp hf j
  have hgmeas : Measurable (dyadicDifference j f) :=
    (measurable_dyadicAverage (j-1) f).sub (measurable_dyadicAverage j f)
  have hstep : ∀ l : ℤ, ∃ c : ℂ, ∀ x,
      x ∈ Set.Ico ((l : ℝ)*(2 : ℝ)^(j-1))
        (((l+1 : ℤ) : ℝ)*(2 : ℝ)^(j-1)) → dyadicDifference j f x = c := by
    intro l
    refine ⟨dyadicDifference j f ((l : ℝ)*(2 : ℝ)^(j-1)), ?_⟩
    intro x hx
    apply dyadicDifference_eq_of_mem_same_fine_cell j l f hx
    change (l : ℝ)*(2 : ℝ)^(j-1) ∈ Set.Ico _ _
    constructor
    · exact le_rfl
    · push_cast
      nlinarith
  have hE : dyadicAverage m (dyadicDifference j f) = dyadicDifference j f :=
    funext (dyadicDifference_fine_average hf hmj)
  dsimp only
  rw [hE]
  exact dyadicStepPsiSmoothing_energy_le hSupp hτ hh hg hgmeas hstep

def smoothDyadicAmplitude : ℝ :=
  16 * (1 + lpNorm (deriv φ) 1 volume + lpNorm (deriv φ) ∞ volume + Real.sqrt 2)

theorem smoothDyadicAmplitude_eight_le : 8 ≤ smoothDyadicAmplitude := by
  unfold smoothDyadicAmplitude
  nlinarith [lpNorm_nonneg (f := deriv φ) (p := 1) (μ := volume),
    lpNorm_nonneg (f := deriv φ) (p := ∞) (μ := volume), Real.sqrt_nonneg 2]

theorem smoothDyadic_highFrequency_decay
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) {m j : ℤ} (hmj : m < j) (hupper : τ ≤ (2 : ℝ)^(m+1))
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
    let g := dyadicDifference j f
    lpNorm (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ≤
      smoothDyadicAmplitude * (2 : ℝ)^(-|((m-j : ℤ) : ℝ)|/2) * lpNorm g 2 volume := by
  let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
  let g := dyadicDifference j f
  let L := lpNorm g 2 volume
  let w : ℝ := (2 : ℝ)^(-|((m-j : ℤ) : ℝ)|/2)
  have hw : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hz : 0 < (2 : ℝ)^(m-j) := zpow_pos (by norm_num) _
  have hw2 : w^2 = (2 : ℝ)^(m-j) := by
    dsimp [w]
    calc
      _ = (2 : ℝ)^((-|((m-j : ℤ) : ℝ)|/2)*2) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_two]
      _ = (2 : ℝ)^(((m-j : ℤ) : ℝ)) := by
        congr 1
        rw [abs_of_nonpos (by exact_mod_cast (show m-j ≤ 0 by omega))]
        ring
      _ = _ := Real.rpow_intCast _ _
  have hratio : (2 : ℝ)^(m+1)/(2 : ℝ)^(j-1) = 4*(2 : ℝ)^(m-j) := by
    rw [← zpow_sub₀ (by norm_num)]
    rw [show m+1-(j-1) = (m-j)+2 by omega, zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hscale : 8*τ/(2 : ℝ)^(j-1) ≤ 32*(2 : ℝ)^(m-j) := by
    calc
      _ ≤ 8*((2 : ℝ)^(m+1)/(2 : ℝ)^(j-1)) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hupper
          (le_of_lt (zpow_pos (by norm_num) _))) (by norm_num)
      _ = _ := by rw [hratio]; ring
  have henergy := (smoothDyadic_highFrequency_energy hSupp hτ hmj hf).2
  have hsmall : lpNorm (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ≤
      8*w*L := by
    apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (mul_nonneg (by norm_num) hw) lpNorm_nonneg)).1
    calc
      _ ≤ (8*τ/(2 : ℝ)^(j-1))*L^2 := henergy
      _ ≤ (32*(2 : ℝ)^(m-j))*L^2 := mul_le_mul_of_nonneg_right hscale (sq_nonneg _)
      _ ≤ (8*w*L)^2 := by
        rw [mul_pow, mul_pow, hw2]
        nlinarith [mul_nonneg hz.le (sq_nonneg L)]
  exact hsmall.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right smoothDyadicAmplitude_eight_le hw) lpNorm_nonneg)

#print axioms smoothDyadic_highFrequency_decay
#print axioms smoothDyadic_highFrequency_energy
#print axioms dyadicStepPsiSmoothing_energy_le
end
end FractionalPrimes.Literature.JSW
end
