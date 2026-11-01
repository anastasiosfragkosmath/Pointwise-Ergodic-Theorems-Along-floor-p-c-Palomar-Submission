module

public import FractionalPrimes.Literature.JSW.RoughSquareMonotoneLimit

/-! The monotone exhaustion equals the approved square-root-of-total-energy
definition, including the common toReal convention at infinity. -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquareSection_energy_squared
    {p : ℝ≥0∞} (v : ℤ → Lp ℂ p (volume : Measure ℝ)) (x : ℝ) :
    (⨆ N : ℕ, ENNReal.ofReal
      (roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ)) x)) ^ 2 =
      ∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2) := by
  let F : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ)
  let a : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)
  let U : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (roughSquareSection v (F N) x)
  have hF : Monotone F := by
    intro N M hNM k hk
    simp only [F, Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  have hU : Monotone U := by
    intro N M hNM
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum_of_subset_of_nonneg (hF hNM) (fun k _ _ => sq_nonneg _)
  have hsq (N : ℕ) : U N ^ 2 = ∑ k ∈ F N, a k := by
    dsimp [U, roughSquareSection]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
      Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
  have hE : (∑' k, a k) = ⨆ N : ℕ, ∑ k ∈ F N, a k := by
    apply ENNReal.tsum_eq_iSup_sum' F
    intro s
    refine ⟨s.sup Int.natAbs, ?_⟩
    intro k hk
    have h := Finset.le_sup (f := Int.natAbs) hk
    simp only [F, Finset.mem_Icc]
    constructor <;> omega
  have hlim := ((ENNReal.continuous_pow 2).tendsto (⨆ N, U N)).comp
    (tendsto_atTop_iSup hU)
  have hlimE : Tendsto (fun N : ℕ => U N ^ 2) atTop (𝓝 (∑' k, a k)) := by
    simp_rw [hsq]
    rw [hE]
    apply tendsto_atTop_iSup
    intro N M hNM
    exact Finset.sum_le_sum_of_subset_of_nonneg (hF hNM) (fun k _ _ => by positivity)
  have heq : (⨆ N, U N)^2 = ∑' k, a k := tendsto_nhds_unique hlim hlimE
  exact heq

theorem roughSquareSection_energy_identity
    {p : ℝ≥0∞} (v : ℤ → Lp ℂ p (volume : Measure ℝ)) (x : ℝ) :
    (⨆ N : ℕ, ENNReal.ofReal
      (roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ)) x)).toReal =
    Real.sqrt ((∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal) := by
  rw [← roughSquareSection_energy_squared v x, ENNReal.toReal_pow,
    Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]

theorem roughSquare_full_energy_bound
    {p K : ℝ} (hp : 1 < p) (hK : 0 ≤ K)
    (v : ℤ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hbound : ∀ F : Finset ℤ,
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (v k.1 : ℝ → ℂ) x)) (ENNReal.ofReal p) volume ≤ K) :
    (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) ∧
    eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
      ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K := by
  obtain ⟨hfinite, hnorm⟩ := roughSquare_exhaustion_bound hp hK v hbound
  constructor
  · filter_upwards [hfinite] with x hx
    rw [← roughSquareSection_energy_squared v x]
    exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top hx.ne)
  · simpa only [roughSquareSection_energy_identity] using hnorm

theorem roughSquare_full_stage_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq : 1 < q)
    (hMax : ∀ s : ℝ, q < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 1 < p) (hp2 : p ≠ 2)
    (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      let v : ℤ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
        fun k => localizedSquareNuLpConvolution hSupp p b hp k f
      (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) ∧
      eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
        ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K * ‖f‖) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨K, hK, hfinite⟩ := roughSquareFinite_stage_bound hSupp hσ hb hβ hq hMax hp hp2 hr
  refine ⟨K, hK, ?_⟩
  intro f
  let v : ℤ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun k => localizedSquareNuLpConvolution hSupp p b hp k f
  have hf : ∀ F : Finset ℤ,
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (v k.1 : ℝ → ℂ) x)) (ENNReal.ofReal p) volume ≤ K * ‖f‖ :=
    fun F => hfinite F f
  exact roughSquare_full_energy_bound (K := K * ‖f‖) hp
    (mul_nonneg hK (norm_nonneg f)) v hf

#print axioms roughSquare_full_stage_bound
#print axioms roughSquare_full_energy_bound
#print axioms roughSquareSection_energy_squared
#print axioms roughSquareSection_energy_identity
end
end FractionalPrimes.Literature.JSW
end
