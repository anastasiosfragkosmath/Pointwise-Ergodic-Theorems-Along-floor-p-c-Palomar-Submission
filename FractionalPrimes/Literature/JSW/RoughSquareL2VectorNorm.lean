module

public import FractionalPrimes.Literature.JSW.LocalizedSquareDecay

/-! The finite Euclidean `L²` norm in the two source endpoint estimates. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A finite family of genuine `L²` outputs has exactly the square
integral used by the source localized Plancherel estimate. -/
theorem finiteVectorLpNorm_two_eq_sqrt_integral
    {ι : Type*} [Fintype ι]
    (g : ι → Lp ℂ 2 (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => WithLp.toLp 2
      (fun i : ι => (g i : ℝ → ℂ) x)) (ENNReal.ofReal 2) volume =
      Real.sqrt (∫ x : ℝ, ∑ i : ι, ‖(g i : ℝ → ℂ) x‖ ^ 2
        ∂(volume : Measure ℝ)) := by
  let V : ℝ → EuclideanSpace ℂ ι :=
    fun x => WithLp.toLp 2 (fun i => (g i : ℝ → ℂ) x)
  have hV : MemLp V (ENNReal.ofReal 2) volume := by
    apply MemLp.of_eval_piLp
    intro i
    simpa [V] using (Lp.memLp (g i))
  have hnorm (x : ℝ) : ‖V x‖ ^ 2 = ∑ i : ι, ‖(g i : ℝ → ℂ) x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  change lpNorm V (ENNReal.ofReal 2) volume = _
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (by positivity) (by simp) hV.aestronglyMeasurable]
  have htoReal : (ENNReal.ofReal (2 : ℝ)).toReal = 2 := by norm_num
  rw [htoReal]
  have hpow : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hpow, ← Real.sqrt_eq_rpow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Real.rpow_two] using hnorm x

/-- The source localized decay estimate in the same finite-vector norm
used by the non-Hilbert endpoint and interpolation. -/
theorem localizedSquare_finite_l2_vector_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (j : ℤ) (F : Finset ℤ) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => WithLp.toLp 2
      (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuProjectionConvolution hSupp hσ hb j k.1 G : ℝ → ℂ) x))
      (ENNReal.ofReal 2) volume ≤
      (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
        Real.sqrt (littlewoodPaleyNb b) *
          Real.rpow b (-(min 1 β * |(j : ℝ)|)) * ‖G‖ := by
  rw [finiteVectorLpNorm_two_eq_sqrt_integral]
  have hsum (x : ℝ) :
      (∑ k : {k : ℤ // k ∈ F},
        ‖(localizedSquareNuProjectionConvolution hSupp hσ hb j k.1 G : ℝ → ℂ) x‖ ^ 2) =
      ∑ k ∈ F, ‖(localizedSquareNuProjectionConvolution hSupp hσ hb j k G : ℝ → ℂ) x‖ ^ 2 := by
    rw [Finset.sum_coe_sort_eq_attach]
    exact Finset.sum_attach F (fun k : ℤ =>
      ‖(localizedSquareNuProjectionConvolution hSupp hσ hb j k G : ℝ → ℂ) x‖ ^ 2)
  simp_rw [hsum]
  exact localizedSquare_finite_l2_bound hSupp hσ hb hβ j F G

#print axioms finiteVectorLpNorm_two_eq_sqrt_integral
#print axioms localizedSquare_finite_l2_vector_bound

end

end FractionalPrimes.Literature.JSW

end
