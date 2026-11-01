module

public import FractionalPrimes.Literature.JSW.RoughSquareClosure
public import FractionalPrimes.Literature.JSW.FiniteVectorLpAssembly

/-! Finite square bounds recovered from the checked full square with the same constant. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem finiteSquare_lpNorm_le_of_full_energy
    {p : ℝ≥0∞} (v : ℤ → Lp ℂ p (volume : Measure ℝ)) {U : ℝ} (hU : 0 ≤ U)
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞)
    (hbound : eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
      ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal)) p volume ≤ ENNReal.ofReal U)
    (K : Finset ℤ) :
    lpNorm ((fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ K} => (v k.1 : ℝ → ℂ) x)) :
      ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) p volume ≤ U := by
  let V : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K} :=
    fun x => WithLp.toLp 2 (fun k => (v k.1 : ℝ → ℂ) x)
  have hV : MemLp V p volume := MemLp.of_eval_piLp (fun k => Lp.memLp (v k.1))
  have hpoint : ∀ᵐ x ∂volume, ‖V x‖ ≤ Real.sqrt ((∑' k : ℤ,
      ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal) := by
    filter_upwards [hfinite] with x hx
    rw [roughSquareSection_norm]
    apply Real.sqrt_le_sqrt
    have hs : ENNReal.ofReal (∑ k ∈ K, ‖(v k : ℝ → ℂ) x‖^2) ≤
        ∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
      exact ENNReal.sum_le_tsum K
    have ht := ENNReal.toReal_mono hx.ne hs
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at ht
    exact ht
  have hb := (eLpNorm_mono_ae_real hV.aestronglyMeasurable hpoint).trans hbound
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hU] at ht
  exact ht

theorem roughSquare_finite_bound_all
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 1 < p) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (K : Finset ℤ)
      (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      lpNorm ((fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ K} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1 F : ℝ → ℂ) x)) :
          ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) (ENNReal.ofReal p) volume ≤ S*‖F‖ := by
  obtain ⟨S,hS,hfull⟩ := roughSquare_full_bound_all hSupp hdecay hb hβ hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  refine ⟨S,hS,fun K F => ?_⟩
  exact finiteSquare_lpNorm_le_of_full_energy _ (mul_nonneg hS (norm_nonneg F))
    (hfull F).1 (hfull F).2 K

#print axioms roughSquare_finite_bound_all
end
end FractionalPrimes.Literature.JSW
end
