module

public import FractionalPrimes.Literature.JSW.SmoothPsiAtomSupport
public import FractionalPrimes.Literature.JSW.SmoothDyadicDensityIdentity
public import FractionalPrimes.Literature.JSW.SmoothDyadicAlmostOrthogonal

/-! The literal finite-vector atom majorant off the ninefold dyadic interval. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem finiteEuclidean_norm_le_sum_norm
    {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have heq : v = ∑ i, PiLp.single 2 i (v i) := by
    ext j
    simp [PiLp.single_apply]
  calc
    _ = ‖∑ i, PiLp.single 2 i (v i)‖ := congrArg norm heq
    _ ≤ ∑ i : ι, ‖(PiLp.single 2 i (v i) : EuclideanSpace ℂ ι)‖ :=
      norm_sum_le Finset.univ (fun i : ι => (PiLp.single 2 i (v i) : EuclideanSpace ℂ ι))
    _ = _ := by simp only [PiLp.norm_single]

def smoothDyadicRawFiniteError
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (a : ℝ) (ha : 0 < a)
    (K : Finset ℤ) (u : ℝ → ℂ) (x : ℝ) : EuclideanSpace ℂ {k : ℤ // k ∈ K} :=
  WithLp.toLp 2 (fun k => smoothDyadicRawError σ a ha k.1 u x)

theorem smoothDyadicRawError_atom_eq_largeScale
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (k m j : ℤ) {u : ℝ → ℂ}
    (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0)
    {x : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) :
    smoothDyadicRawError σ a ha k u x =
      if (2 : ℝ)^m < jswTau a ha k then smoothPsiDensityConvolution σ (jswTau a ha k) u x else 0 := by
  have hτ : 0 < jswTau a ha k := zpow_pos (by linarith [jswB_gt_one ha]) _
  unfold smoothDyadicRawError
  rw [← smoothPsiDensityConvolution_eq_probability_all hτ u x,
    dyadicAverage_meanZeroAtom_zero_off_ninefold hmean m j hsupp (jswM a ha k) hx, sub_zero]
  split_ifs with hlarge
  · rfl
  · exact smoothPsiDensityConvolution_atom_smallScale_zero hSupp hτ m j (le_of_not_gt hlarge) hsupp hx

theorem smoothDyadicRawFiniteError_atom_norm_majorant
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m j : ℤ) {u : ℝ → ℂ}
    (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0)
    {x : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) :
    ‖smoothDyadicRawFiniteError σ a ha K u x‖ ≤
      ∑ k ∈ K.filter (fun k => (2 : ℝ)^m < jswTau a ha k),
        ‖smoothPsiDensityConvolution σ (jswTau a ha k) u x‖ := by
  classical
  calc
    _ ≤ ∑ k : {k : ℤ // k ∈ K}, ‖smoothDyadicRawError σ a ha k.1 u x‖ :=
      finiteEuclidean_norm_le_sum_norm _
    _ = ∑ k ∈ K, ‖smoothDyadicRawError σ a ha k u x‖ := by
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach K (fun k : ℤ => ‖smoothDyadicRawError σ a ha k u x‖)
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      rw [smoothDyadicRawError_atom_eq_largeScale hSupp ha k m j hmean hsupp hx]
      split_ifs <;> simp

#print axioms smoothDyadicRawFiniteError_atom_norm_majorant
end
end FractionalPrimes.Literature.JSW
end
