module
public import FractionalPrimes.Final.MobiusLongScales
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem tendsto_logWeightedMobius_of_sparse_blocks
    {X : Type*} [MeasurableSpace X] (S : System X) (c t A : ℝ)
    (ht : 1 < t) (hA : 0 < A) (f : X → ℂ) (x : X)
    (hlong : Tendsto (fun k => logWeightedMobiusAverage S c A f (sparseScaleAsScale ht k) x)
      atTop (𝓝 0))
    (hshort : Tendsto (fun k => weightedMobiusBlock S c t A ht f k x) atTop (𝓝 0)) :
    Tendsto (fun N : Scale => logWeightedMobiusAverage S c A f N x) atTop (𝓝 0) := by
  let s := sparseScaleAsScale ht
  let idx := scaleBlockIndex (sparseScaleAsScale_monotone ht) (sparseScaleAsScale_tendsto_atTop ht)
  have hidx : Tendsto idx atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (s b)] with N hN
    by_contra h
    have hi : idx N + 1 ≤ b := by omega
    have hu := scaleBlockIndex_upper (sparseScaleAsScale_monotone ht)
      (sparseScaleAsScale_tendsto_atTop ht) N
    exact (not_lt_of_ge hN) (hu.trans_le (sparseScaleAsScale_monotone ht hi))
  have hnorm := (tendsto_zero_iff_enorm_tendsto_zero).mp hlong
  have hmain : Tendsto (fun k => ENNReal.ofReal ((6 : ℝ) ^ A) *
      ‖logWeightedMobiusAverage S c A f (s k) x‖ₑ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hnorm (Or.inr ENNReal.ofReal_ne_top)
  have hmajor : Tendsto (fun N : Scale =>
      ENNReal.ofReal ((6 : ℝ) ^ A) * ‖logWeightedMobiusAverage S c A f (s (idx N)) x‖ₑ +
        weightedMobiusBlock S c t A ht f (idx N) x) atTop (𝓝 0) := by
    simpa only [zero_add, Function.comp_def] using (hmain.add hshort).comp hidx
  apply (tendsto_zero_iff_enorm_tendsto_zero).mpr
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [hidx.eventually (eventually_ge_atTop 1),
    hmajor.eventually (ENNReal.nhds_zero_basis_Iic.mem_of_mem hε)] with N hk hsmall
  let k := idx N
  have hspec := sparseScaleBlockIndex_spec ht N
  have ha : s k ≤ N := hspec.1
  have hb : N < s (k + 1) := hspec.2
  have hdiff : ‖mobiusAverage S c f N x - mobiusAverage S c f (s k) x‖ₑ ≤
      mobiusBlockVariation S c t ht f k x := by
    by_cases heq : s k = N
    · simp [heq]
    · have hlt : s k < N := lt_of_le_of_ne ha heq
      simpa only [ofReal_norm, mobiusBlockVariation, rVariationOnFun, s] using enorm_sub_le_rVariationOn (by norm_num : (0 : ℝ) < 2)
        (fun n => mobiusAverage S c f n x) (Set.Icc (s k) (s (k + 1))) hlt
        ⟨le_rfl, ha.trans hb.le⟩ ⟨ha, hb.le⟩
  have hlogN : 0 ≤ Real.log (N.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast N.property)
  have hlogK : 0 ≤ Real.log ((s k).val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (s k).property)
  have hWN : 0 ≤ Real.log (N.val : ℝ) ^ A := Real.rpow_nonneg hlogN _
  have hWK : 0 ≤ Real.log ((s k).val : ℝ) ^ A := Real.rpow_nonneg hlogK _
  have hweight : Real.log (N.val : ℝ) ^ A ≤ sparseLogWeight t A k := by
    apply Real.rpow_le_rpow hlogN _ hA.le
    have hNb : (N.val : ℝ) ≤ ((s (k + 1)).val : ℝ) := by exact_mod_cast hb.le
    change Real.log (N.val : ℝ) ≤ Real.log (2 * ((s (k + 1)).val : ℝ))
    apply Real.log_le_log (by exact_mod_cast N.property)
    have hnonneg : (0 : ℝ) ≤ ((s (k + 1)).val : ℝ) := Nat.cast_nonneg _
    linarith
  have hratio := sparseLogWeight_le_baseLog ht hA hk
  have hnormBound : ‖mobiusAverage S c f N x‖ₑ ≤
      mobiusBlockVariation S c t ht f k x + ‖mobiusAverage S c f (s k) x‖ₑ := by
    calc
      _ = ‖(mobiusAverage S c f N x - mobiusAverage S c f (s k) x) +
          mobiusAverage S c f (s k) x‖ₑ := by rw [sub_add_cancel]
      _ ≤ _ := (enorm_add_le _ _).trans (add_le_add hdiff le_rfl)
  have hbound : ‖logWeightedMobiusAverage S c A f N x‖ₑ ≤
      ENNReal.ofReal ((6 : ℝ) ^ A) * ‖logWeightedMobiusAverage S c A f (s k) x‖ₑ +
        weightedMobiusBlock S c t A ht f k x := by
    change ‖Real.log (N.val : ℝ) ^ A • mobiusAverage S c f N x‖ₑ ≤ _
    rw [enorm_smul, Real.enorm_of_nonneg hWN]
    calc
      _ ≤ ENNReal.ofReal (sparseLogWeight t A k) *
          (mobiusBlockVariation S c t ht f k x + ‖mobiusAverage S c f (s k) x‖ₑ) :=
        mul_le_mul (ENNReal.ofReal_le_ofReal hweight) hnormBound bot_le bot_le
      _ = ENNReal.ofReal (sparseLogWeight t A k) * ‖mobiusAverage S c f (s k) x‖ₑ +
          weightedMobiusBlock S c t A ht f k x := by
        rw [weightedMobiusBlock, mul_add, add_comm]
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        change _ ≤ ENNReal.ofReal ((6 : ℝ) ^ A) *
          ‖Real.log ((s k).val : ℝ) ^ A • mobiusAverage S c f (s k) x‖ₑ
        rw [enorm_smul, Real.enorm_of_nonneg hWK, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) A)]
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hratio) bot_le
  exact hbound.trans hsmall

/-- Revised manuscript Theorem t:mobius-convergence, with its full A>1
range and no invertibility assumption. -/
theorem mobiusLogRate {p A : ℝ} (hp : 1 < p) (hA : 1 < A)
    (c : FractionalExponent) : MobiusLogRateStatement c p A := by
  intro X _ S f hf
  have hA0 : 0 < A := by linarith
  obtain ⟨t, ht, hsmall⟩ := exists_mobiusSparseParameter hp hA0
  have hsum := logWeightedMobius_sparse_norm_summable hp ht hA0 c S f hf
  have hlong := summable_norm_of_tsum_eLpNorm_ne_top (ENNReal.one_le_ofReal.mpr hp.le) hsum
  have hshort := weightedMobiusBlock_ae_tendsto_zero S c.value t A ht hp hA0 hsmall f hf
  filter_upwards [hlong, hshort] with x hxlong hxshort
  apply tendsto_logWeightedMobius_of_sparse_blocks S c.value t A ht hA0 f x _ hxshort
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr hxlong.tendsto_atTop_zero

#print axioms mobiusLogRate
end
end FractionalPrimes.Final
