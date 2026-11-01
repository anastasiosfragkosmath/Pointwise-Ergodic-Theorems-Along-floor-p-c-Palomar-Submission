module

public import FractionalPrimes.Literature.JSW.SmoothDyadicDensityIdentity
public import FractionalPrimes.Literature.JSW.SmoothDyadicHighFrequency

/-! The exact source almost-orthogonal block estimate, in both frequency ranges. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem dyadicDifference_coarse_average
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {m j : ℤ} (hjm : j ≤ m) (x : ℝ) :
    dyadicAverage m (dyadicDifference j f) x = 0 := by
  have hloc := hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  change dyadicAverage m (dyadicAverage (j-1) f-dyadicAverage j f) x = 0
  rw [dyadicAverage_sub_of_memLp_two
    (memLp_dyadicAverage_two_of_memLp hf (j-1)) (memLp_dyadicAverage_two_of_memLp hf j),
    dyadicAverage_reverse_comp_of_le (by omega : j-1 ≤ m) hloc,
    dyadicAverage_reverse_comp_of_le hjm hloc, sub_self]

theorem smoothDyadic_lowFrequency_decay
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) {m j : ℤ} (hjm : j ≤ m) (hlower : (2 : ℝ)^m ≤ τ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
    let g := dyadicDifference j f
    MemLp (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ∧
    lpNorm (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ≤
      smoothDyadicAmplitude * (2 : ℝ)^(-|((m-j : ℤ) : ℝ)|/2) * lpNorm g 2 volume := by
  let g := dyadicDifference j f
  let w : ℝ := (2 : ℝ)^(-|((m-j : ℤ) : ℝ)|/2)
  have hgmeas : Measurable g :=
    (measurable_dyadicAverage (j-1) f).sub (measurable_dyadicAverage j f)
  have hscale : (2 : ℝ)^j ≤ τ :=
    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjm).trans hlower
  have heq : (fun x : ℝ => jswConvolution
      (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) g x-
      dyadicAverage m g x) = smoothPsiDensityConvolution σ τ g := by
    funext x
    rw [dyadicDifference_coarse_average hf hjm x, sub_zero]
    exact (smoothPsiDensityConvolution_eq_probability hτ hgmeas x).symm
  obtain ⟨hmem,hbound⟩ := smoothDyadic_lowFrequency_density_bound hSupp hτ j hscale hf
  have hratio : (2 : ℝ)^j/τ ≤ w := by
    calc
      _ ≤ (2 : ℝ)^j/(2 : ℝ)^m := div_le_div_of_nonneg_left
        (le_of_lt (zpow_pos (by norm_num) _)) (zpow_pos (by norm_num) _) hlower
      _ = (2 : ℝ)^(((j-m : ℤ) : ℝ)) := by rw [Real.rpow_intCast, zpow_sub₀ (by norm_num)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ m-j by omega))]
        push_cast
        have hh : (j : ℝ) ≤ m := by exact_mod_cast hjm
        linarith
  have hA : 8*lpNorm (deriv φ) ∞ volume ≤ smoothDyadicAmplitude := by
    unfold smoothDyadicAmplitude
    nlinarith [lpNorm_nonneg (f := deriv φ) (p := 1) (μ := volume),
      lpNorm_nonneg (f := deriv φ) (p := ∞) (μ := volume), Real.sqrt_nonneg 2]
  dsimp only
  rw [heq]
  refine ⟨hmem, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ lpNorm_nonneg
  calc
    _ = (8*lpNorm (deriv φ) ∞ volume)*((2 : ℝ)^j/τ) := by ring
    _ ≤ (8*lpNorm (deriv φ) ∞ volume)*w := mul_le_mul_of_nonneg_left hratio
      (mul_nonneg (by norm_num) lpNorm_nonneg)
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (by norm_num) _)

theorem smoothDyadic_block_decay
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) {m : ℤ} (hlower : (2 : ℝ)^m ≤ τ) (hupper : τ ≤ (2 : ℝ)^(m+1))
    (j : ℤ) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
    let g := dyadicDifference j f
    MemLp (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ∧
    lpNorm (fun x : ℝ => jswConvolution μ g x-dyadicAverage m g x) 2 volume ≤
      smoothDyadicAmplitude * (2 : ℝ)^(-|((m-j : ℤ) : ℝ)|/2) * lpNorm g 2 volume := by
  by_cases hjm : j ≤ m
  · exact smoothDyadic_lowFrequency_decay hSupp hτ hjm hlower hf
  · have hmj : m < j := by omega
    exact ⟨(smoothDyadic_highFrequency_energy hSupp hτ hmj hf).1,
      smoothDyadic_highFrequency_decay hSupp hτ hmj hupper hf⟩

theorem smoothDyadic_source_block_decay
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (k j : ℤ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    let μ := Measure.map (fun z : ℝ => jswTau a ha k*z) (initialSquarePsiProbabilityMeasure σ)
    let g := dyadicDifference j f
    MemLp (fun x : ℝ => jswConvolution μ g x-dyadicAverage (jswM a ha k) g x) 2 volume ∧
    lpNorm (fun x : ℝ => jswConvolution μ g x-dyadicAverage (jswM a ha k) g x) 2 volume ≤
      smoothDyadicAmplitude * (2 : ℝ)^(-|((jswM a ha k-j : ℤ) : ℝ)|/2) * lpNorm g 2 volume := by
  have hτ : 0 < jswTau a ha k := zpow_pos (by linarith [jswB_gt_one ha]) _
  obtain ⟨hlo,hhi⟩ := jswTau_floor_bounds a ha k
  exact smoothDyadic_block_decay hSupp hτ hlo hhi.le j hf

#print axioms smoothDyadic_source_block_decay
#print axioms smoothDyadic_block_decay
#print axioms smoothDyadic_lowFrequency_decay
end
end FractionalPrimes.Literature.JSW
end
