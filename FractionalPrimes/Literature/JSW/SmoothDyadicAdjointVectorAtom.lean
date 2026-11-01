module

public import FractionalPrimes.Literature.JSW.SmoothDyadicAdjointAtom

/-! The source adjoint atom bound for an actual Euclidean-valued atom. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadicRawAdjointError_vector_atom_L1
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m j : ℤ)
    {u : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}}
    (hu : Integrable u volume) (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0) :
    IntegrableOn (fun x => ‖smoothDyadicRawAdjointError σ a ha K (fun k y => u y k) x‖)
      (dyadicNinefoldInterval m j)ᶜ volume ∧
    (∫ x in (dyadicNinefoldInterval m j)ᶜ,
      ‖smoothDyadicRawAdjointError σ a ha K (fun k y => u y k) x‖ ∂volume) ≤
      smoothDyadicOffSupportConstant a ha*(∫ x, ‖u x‖ ∂volume) := by
  classical
  let L := fun k : {k : ℤ // k ∈ K} =>
    (PiLp.proj 2 (fun _ : {k : ℤ // k ∈ K} => ℂ) k :
      EuclideanSpace ℂ {k : ℤ // k ∈ K} →L[ℝ] ℂ)
  have hc (k : {k : ℤ // k ∈ K}) : Integrable (fun y => u y k) volume :=
    (L k).integrable_comp hu
  have hm (k : {k : ℤ // k ∈ K}) : ∫ y, u y k ∂volume = 0 := by
    have hi := (L k).integral_comp_comm hu
    simpa only [L, PiLp.proj_apply, hmean, map_zero] using hi
  have hs (k : {k : ℤ // k ∈ K}) (y : ℝ) (hy : y ∉ dyadicInterval m j) : u y k = 0 := by
    rw [hsupp y hy]
    rfl
  have hn (k : {k : ℤ // k ∈ K}) :
      lpNorm (fun y => u y k) 1 volume ≤ ∫ x, ‖u x‖ ∂volume := by
    rw [lpNorm_one_eq_integral_norm (hc k).aestronglyMeasurable]
    exact integral_mono (hc k).norm hu.norm (fun x => PiLp.norm_apply_le (u x) k)
  exact smoothDyadicRawAdjointError_atom_L1 hSupp ha K m j (fun k y => u y k)
    hc hm hs (integral_nonneg fun x => norm_nonneg _) hn

#print axioms smoothDyadicRawAdjointError_vector_atom_L1
end
end FractionalPrimes.Literature.JSW
end
