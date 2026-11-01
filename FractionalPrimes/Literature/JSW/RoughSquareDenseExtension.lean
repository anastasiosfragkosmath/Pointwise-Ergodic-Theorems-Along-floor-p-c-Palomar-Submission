module

public import FractionalPrimes.Literature.JSW.FiniteVectorLpAssembly

/-! Dense extension of the finite rough-square bounds with unchanged
constants. -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquare_norm_bound_extend_dense
    {E : Type*} [NormedAddCommGroup E] {p C : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) → E) (hS : Continuous S)
    (hbound : ∀ (g : Variation.LayerCakeInput (volume : Measure ℝ))
      (hg : MemLp g.1 (ENNReal.ofReal p) volume),
      ‖S (hg.toLp g.1)‖ ≤ C * lpNorm g.1 (ENNReal.ofReal p) volume)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ‖S f‖ ≤ C * ‖f‖ := by
  obtain ⟨g, _, hg, _, hgnorm, _⟩ := Variation.exists_layerCakeInput_approximation
    volume (by linarith : 0 < p) (f : ℝ → ℂ) (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  let gLp : ℕ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := fun n => (hg n).toLp (g n).1
  have ht : Tendsto gLp atTop (𝓝 f) := by
    simpa only [gLp, Lp.toLp_coeFn] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (g n).1) hg
        (f : ℝ → ℂ) (Lp.memLp f)).mpr hgnorm
  apply le_of_tendsto_of_tendsto ((hS.tendsto f).comp ht).norm
    (tendsto_const_nhds.mul ht.norm)
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [gLp, Function.comp_apply, Lp.norm_toLp, toReal_eLpNorm] using hbound (g n) (hg n))

theorem roughSquareFinite_bound_extend_dense
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b p K : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p)
    (hDense : ∀ (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1
          ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤ K * lpNorm f.1 (ENNReal.ofReal p) volume)
    (F : Finset ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
      (localizedSquareNuLpConvolution hSupp p b hp k.1 f : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤ K * ‖f‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let S := roughSquareFiniteLpOperator hSupp hp b F
  have hnorm (g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
      ‖S g‖ = lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1 g : ℝ → ℂ) x))
          (ENNReal.ofReal p) volume := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae
      (roughSquareFiniteLpOperator_ae_eq hSupp hp b F g))
  rw [← hnorm]
  apply roughSquare_norm_bound_extend_dense hp S S.continuous
  intro g hg
  rw [hnorm]
  exact hDense F g

theorem roughSquareFinite_bound_lp_above_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 2 < p) (hpu : p < u)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Finset ℤ)
      (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b (by linarith : 1 < p) k.1
          f : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤ K * ‖f‖ := by
  obtain ⟨K, hK, hdense⟩ := roughSquareFinite_bound_above_two
    hSupp hσ hb hβ hq₀ hMax hp hpu hregion
  exact ⟨K, hK, fun F f => roughSquareFinite_bound_extend_dense hSupp
    (by linarith : 1 < p) hdense F f⟩

theorem roughSquareFinite_bound_lp_below_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hu : 1 < u) (hup : u < p) (hp : p < 2)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Finset ℤ)
      (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b (by linarith : 1 < p) k.1
          f : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤ K * ‖f‖ := by
  obtain ⟨K, hK, hdense⟩ := roughSquareFinite_bound_below_two
    hSupp hσ hb hβ hq₀ hMax hu hup hp hregion
  exact ⟨K, hK, fun F f => roughSquareFinite_bound_extend_dense hSupp
    (by linarith : 1 < p) hdense F f⟩

#print axioms roughSquareFinite_bound_lp_above_two
#print axioms roughSquareFinite_bound_lp_below_two
#print axioms roughSquare_norm_bound_extend_dense
#print axioms roughSquareFinite_bound_extend_dense
end
end FractionalPrimes.Literature.JSW
end
