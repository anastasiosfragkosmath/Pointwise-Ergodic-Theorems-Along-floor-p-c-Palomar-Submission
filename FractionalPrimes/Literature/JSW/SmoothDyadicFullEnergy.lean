module

public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteEnergy
public import FractionalPrimes.Literature.JSW.RoughSquareEnergyIdentity
public import FractionalPrimes.Literature.JSW.PositiveVectorL2

/-! Monotone full-square exhaustion for the actual source smooth error operators. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadic_finite_vector_norm
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ)) :
    let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
      (jswTau a ha k) (jswM a ha k) F
    lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ K} =>
      (v k.1 : ℝ → ℂ) x)) (ENNReal.ofReal (2 : ℝ)) volume ≤
        smoothDyadicSquareConstant a ha * ‖F‖ := by
  let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
    (jswTau a ha k) (jswM a ha k) F
  let V : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K} :=
    fun x => WithLp.toLp 2 (fun k => (v k.1 : ℝ → ℂ) x)
  have hVP : MemLp V (ENNReal.ofReal (2 : ℝ)) volume := by
    apply MemLp.of_eval_piLp
    intro k
    exact Lp.memLp _
  have hV2 : MemLp V 2 volume := by simpa only [ENNReal.ofReal_ofNat] using hVP
  have hnorm (u : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ)) :
      lpNorm (u : ℝ → ℂ) 2 volume = ‖u‖ := by
    rw [Lp.norm_def]
    change (eLpNorm (u : ℝ → ℂ) 2 volume).toReal = _
    apply congrArg ENNReal.toReal
    exact congrArg (fun P => eLpNorm (u : ℝ → ℂ) P volume)
      (by norm_num : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ))
  have hPnorm : lpNorm V (ENNReal.ofReal (2 : ℝ)) volume = lpNorm V 2 volume := by
    change (eLpNorm V (ENNReal.ofReal (2 : ℝ)) volume).toReal = _
    exact congrArg ENNReal.toReal (congrArg (fun P => eLpNorm V P volume)
      (by norm_num : ENNReal.ofReal (2 : ℝ) = 2))
  have hs : lpNorm V 2 volume ^ 2 = ∑ k ∈ K, ‖v k‖^2 := by
    have h := lpNorm_finiteEuclidean_two_sq_eq_sum V hV2
    change lpNorm V 2 volume ^ 2 = ∑ k : {k : ℤ // k ∈ K},
      lpNorm (v k.1 : ℝ → ℂ) 2 volume ^ 2 at h
    simp_rw [hnorm] at h
    rw [h, Finset.sum_coe_sort_eq_attach]
    exact Finset.sum_attach K (fun k : ℤ => ‖v k‖^2)
  change lpNorm V (ENNReal.ofReal (2 : ℝ)) volume ≤ _
  rw [hPnorm]
  apply (sq_le_sq₀ lpNorm_nonneg
    (mul_nonneg (smoothDyadicSquareConstant_nonneg ha) (norm_nonneg F))).1
  rw [hs, mul_pow]
  exact smoothDyadic_finite_energy hSupp ha K F

theorem smoothDyadic_full_L2_energy
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {a : ℝ} (ha : 0 < a)
    (F : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ)) :
    let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
      (jswTau a ha k) (jswM a ha k) F
    (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) ∧
    eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
      ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal))
      (ENNReal.ofReal (2 : ℝ)) volume ≤ ENNReal.ofReal (smoothDyadicSquareConstant a ha * ‖F‖) := by
  exact roughSquare_full_energy_bound (p := 2) (by norm_num)
    (mul_nonneg (smoothDyadicSquareConstant_nonneg ha) (norm_nonneg F)) _
    (fun K => smoothDyadic_finite_vector_norm hSupp ha K F)

#print axioms smoothDyadic_full_L2_energy
#print axioms smoothDyadic_finite_vector_norm
end
end FractionalPrimes.Literature.JSW
end
