module
public import FractionalPrimes.Final.ArithmeticDecay
public import FractionalPrimes.Final.ForwardOperatorNorm
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Arbitrary logarithmic operator decay transfers to every forward system. -/
theorem mobiusAverage_logDecay {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : Type*} [MeasurableSpace X] (S : System X)
      (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
      ∀ N : Scale, 3 ≤ N.1 →
      eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ ≤
        ENNReal.ofReal (C * (Real.log (N.1 : ℝ)) ^ (-D)) *
          eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨C, hC, hbound⟩ := arithmeticDiscreteDecay hp c D hD
  refine ⟨C, hC, ?_⟩
  intro X _ S f hf N hN
  exact transferForwardWeightedFloorKernelOperatorNorm S hp c.value N
    (fun n => (mobiusWeight n : ℂ)) _
    (mul_nonneg hC (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N.1 by omega))) _))
    ((le_add_of_nonneg_left (norm_nonneg _)).trans (hbound N hN)) f hf

/-- Multiplication by any positive logarithmic power retains decay of every
prescribed logarithmic order. This is an Lp estimate, not yet the a.e. theorem. -/
theorem logWeightedMobiusAverage_logDecay {p : ℝ} (hp : 1 < p)
    (c : FractionalExponent) {A : ℝ} (hA : 0 < A) (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : Type*} [MeasurableSpace X] (S : System X)
      (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
      ∀ N : Scale, 3 ≤ N.1 →
      eLpNorm (logWeightedMobiusAverage S c.value A f N) (ENNReal.ofReal p) S.μ ≤
        ENNReal.ofReal (C * (Real.log (N.1 : ℝ)) ^ (-D)) *
          eLpNorm f (ENNReal.ofReal p) S.μ := by
  obtain ⟨C, hC, hb⟩ := mobiusAverage_logDecay hp c (D + A) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro X _ S f hf N hN
  have hlog : 0 < Real.log (N.1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N.1 by omega))
  have hw : 0 ≤ (Real.log (N.1 : ℝ)) ^ A := Real.rpow_nonneg hlog.le _
  rw [logWeightedMobiusAverage, eLpNorm_const_smul]
  change ‖(Real.log (N.1 : ℝ)) ^ A‖ₑ *
    eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ ≤ _
  rw [Real.enorm_of_nonneg hw]
  calc
    _ ≤ ENNReal.ofReal ((Real.log (N.1 : ℝ)) ^ A) *
        (ENNReal.ofReal (C * (Real.log (N.1 : ℝ)) ^ (-(D + A))) *
          eLpNorm f (ENNReal.ofReal p) S.μ) := mul_le_mul_of_nonneg_left (hb S f hf N hN) bot_le
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hw]
      congr 2
      rw [mul_left_comm, ← Real.rpow_add hlog]
      congr 2
      ring

/-- The logarithmically weighted Mobius averages converge in Lp to zero. -/
theorem logWeightedMobiusAverage_tendsto_eLpNorm_zero {p : ℝ} (hp : 1 < p)
    (c : FractionalExponent) {A : ℝ} (hA : 0 < A)
    {X : Type*} [MeasurableSpace X] (S : System X) (f : X → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    Tendsto (fun N : Scale =>
      eLpNorm (logWeightedMobiusAverage S c.value A f N) (ENNReal.ofReal p) S.μ)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := logWeightedMobiusAverage_logDecay hp c hA 1 (by norm_num)
  have hscale : Tendsto (fun N : Scale => N.val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (⟨b + 1, by omega⟩ : Scale)] with N hN
    exact (Nat.le_succ b).trans hN
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hscale)
  have hreal : Tendsto (fun N : Scale => C * Real.log (N.val : ℝ) ^ (-1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_neg_one, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul C
  have hmajor : Tendsto (fun N : Scale =>
      ENNReal.ofReal (C * Real.log (N.val : ℝ) ^ (-1 : ℝ)) *
        eLpNorm f (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal hreal)
      (Or.inr hf.eLpNorm_ne_top) tendsto_const_nhds (Or.inr (by simp))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (⟨3, by omega⟩ : Scale),
    hmajor.eventually (ENNReal.nhds_zero_basis_Iic.mem_of_mem hε)] with N hN hsmall
  exact (hb S f hf N hN).trans hsmall

#print axioms logWeightedMobiusAverage_tendsto_eLpNorm_zero

#print axioms mobiusAverage_logDecay
#print axioms logWeightedMobiusAverage_logDecay
end
end FractionalPrimes.Final
