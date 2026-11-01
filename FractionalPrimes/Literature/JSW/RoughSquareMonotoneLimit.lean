module

public import FractionalPrimes.Literature.JSW.RoughSquareStageRegion
public import FractionalPrimes.Literature.JSW.PositiveMaximalSupFinite

/-! Monotone square sections: the exhaustion supremum is an intermediate
representation, to be identified with the source square energy. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def roughSquareSection {p : ℝ≥0∞} (v : ℤ → Lp ℂ p (volume : Measure ℝ))
    (F : Finset ℤ) (x : ℝ) : ℝ := Real.sqrt (∑ k ∈ F, ‖(v k : ℝ → ℂ) x‖^2)

theorem roughSquareSection_norm {p : ℝ≥0∞}
    (v : ℤ → Lp ℂ p (volume : Measure ℝ)) (F : Finset ℤ) (x : ℝ) :
    ‖WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} => (v k.1 : ℝ → ℂ) x)‖ =
      roughSquareSection v F x := by
  let V : EuclideanSpace ℂ {k : ℤ // k ∈ F} :=
    WithLp.toLp 2 (fun k => (v k.1 : ℝ → ℂ) x)
  change ‖V‖ = _
  calc
    _ = Real.sqrt (‖V‖^2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = Real.sqrt (∑ k : {k : ℤ // k ∈ F}, ‖(v k.1 : ℝ → ℂ) x‖^2) := by
      rw [EuclideanSpace.norm_sq_eq]
    _ = _ := by
      unfold roughSquareSection
      congr 1
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach F (fun k : ℤ => ‖(v k : ℝ → ℂ) x‖^2)

theorem roughSquare_exhaustion_bound
    {p K : ℝ} (hp : 1 < p) (hK : 0 ≤ K)
    (v : ℤ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hbound : ∀ F : Finset ℤ,
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (v k.1 : ℝ → ℂ) x)) (ENNReal.ofReal p) volume ≤ K) :
    (∀ᵐ x ∂volume, (⨆ N : ℕ, ENNReal.ofReal
      (roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ)) x)) < ∞) ∧
    eLpNorm (fun x => (⨆ N : ℕ, ENNReal.ofReal
      (roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ)) x)).toReal)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let f : ℕ → ℝ → ℝ := fun N => roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ))
  have hf : ∀ N, Measurable (f N) := by
    intro N
    dsimp [f, roughSquareSection]
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro k hk
    exact (Lp.stronglyMeasurable (v k)).measurable.norm.pow_const 2
  have hn : ∀ N, ∀ᵐ x ∂volume, 0 ≤ f N x := fun N =>
    Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _)
  have hm : ∀ N, ∀ᵐ x ∂volume, f N x ≤ f N.succ x := by
    intro N
    filter_upwards [] with x
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      constructor <;> omega
    · intro k hk hkn
      exact sq_nonneg _
  have hb : ∀ N, eLpNorm (f N) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K := by
    intro N
    let F := Finset.Icc (-(N : ℤ)) (N : ℤ)
    let V : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F} :=
      fun x => WithLp.toLp 2 (fun k => (v k.1 : ℝ → ℂ) x)
    have hV : MemLp V (ENNReal.ofReal p) volume := by
      apply MemLp.of_eval_piLp
      intro k
      exact Lp.memLp _
    have heq : (fun x => ‖V x‖) = f N := by
      funext x
      exact roughSquareSection_norm v F x
    have hmem : MemLp (f N) (ENNReal.ofReal p) volume := heq ▸ hV.norm
    rw [← ofReal_lpNorm hmem]
    apply ENNReal.ofReal_le_ofReal
    have hvnorm := eLpNorm_norm V hV.aestronglyMeasurable (p := ENNReal.ofReal p)
    have hreal := congrArg ENNReal.toReal hvnorm
    rw [heq] at hreal
    exact hreal.le.trans (hbound F)
  exact ⟨iSup_ofReal_lt_top_ae_of_uniform_eLpNorm (by linarith) f hf hn hm
      ENNReal.ofReal_ne_top hb,
    eLpNorm_toReal_iSup_ofReal_mono (by linarith) f hf hn hm hb⟩

theorem roughSquare_stage_exhaustion_bound
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
      (∀ᵐ x ∂volume, (⨆ N : ℕ, ENNReal.ofReal
        (roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ)) x)) < ∞) ∧
      eLpNorm (fun x => (⨆ N : ℕ, ENNReal.ofReal
        (roughSquareSection v (Finset.Icc (-(N : ℤ)) (N : ℤ)) x)).toReal)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K * ‖f‖) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨K, hK, hfinite⟩ := roughSquareFinite_stage_bound hSupp hσ hb hβ hq hMax hp hp2 hr
  refine ⟨K, hK, ?_⟩
  intro f
  let v : ℤ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun k => localizedSquareNuLpConvolution hSupp p b hp k f
  have hf : ∀ F : Finset ℤ,
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (v k.1 : ℝ → ℂ) x)) (ENNReal.ofReal p) volume ≤ K * ‖f‖ := by
    intro F
    exact hfinite F f
  exact roughSquare_exhaustion_bound (K := K * ‖f‖) hp
    (mul_nonneg hK (norm_nonneg f)) v hf

#print axioms roughSquare_stage_exhaustion_bound
#print axioms roughSquare_exhaustion_bound
end
end FractionalPrimes.Literature.JSW
end
