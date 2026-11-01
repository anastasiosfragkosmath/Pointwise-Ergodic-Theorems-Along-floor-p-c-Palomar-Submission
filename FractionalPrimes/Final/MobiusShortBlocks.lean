module
public import FractionalPrimes.Final.MobiusBlockBounds
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

def sparseLogWeight (t A : ℝ) (k : ℕ) : ℝ :=
  Real.log (2 * (sparseScale t (k + 1) : ℝ)) ^ A

theorem sparseLogWeight_nonneg {t : ℝ} (ht : 1 < t) (A : ℝ) (k : ℕ) :
    0 ≤ sparseLogWeight t A k := by
  apply Real.rpow_nonneg
  apply Real.log_nonneg
  have hs : 1 ≤ sparseScale t (k + 1) := by
    rw [← sparseScale_zero ht]; exact sparseScale_monotone ht (Nat.zero_le _)
  exact_mod_cast (show 1 ≤ 2 * sparseScale t (k + 1) by omega)

def weightedMobiusBlock {X : Type*} [MeasurableSpace X]
    (S : System X) (c t A : ℝ) (ht : 1 < t) (f : X → ℂ) (k : ℕ) : X → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (sparseLogWeight t A k) * mobiusBlockVariation S c t ht f k x

theorem weightedMobiusBlock_ae_tendsto_zero {X : Type*} [MeasurableSpace X]
    (S : System X) (c t A : ℝ) (ht : 1 < t) {p : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hsmall : p * ((A + 2) * sparseScaleTau t - 1) < -1)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∀ᵐ x ∂S.μ, Tendsto (fun k => weightedMobiusBlock S c t A ht f k x) atTop (𝓝 0) := by
  have hV (k : ℕ) : AEStronglyMeasurable (mobiusBlockVariation S c t ht f k) S.μ := by
    apply (aemeasurable_rVariationOnFun S.μ 2 (mobiusAverage S c f) _
      (fun N => (memLp_weightedAverage S c _ f N hf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  let E := fun k => sparseLogWeight t A k * sparseScaleBlockError t k
  apply ae_tendsto_zero_of_summable_coefficient S.μ (by linarith : 0 < p)
    (weightedMobiusBlock S c t A ht f)
    (fun k => ((hV k).aemeasurable.const_mul _).aestronglyMeasurable)
    E (fun k => mul_nonneg (sparseLogWeight_nonneg ht A k) (sparseScaleBlockError_nonneg ht k))
    (summable_weightedSparseBlock hp hA ht hsmall)
    (4 * eLpNorm f (ENNReal.ofReal p) S.μ)
    (ENNReal.mul_ne_top (by norm_num) hf.eLpNorm_ne_top)
  intro k
  change eLpNorm (fun x => ENNReal.ofReal (sparseLogWeight t A k) *
    mobiusBlockVariation S c t ht f k x) (ENNReal.ofReal p) S.μ ≤ _
  rw [eLpNorm_const_mul_ennreal (hV k)]
  calc
    _ ≤ ENNReal.ofReal (sparseLogWeight t A k) *
        (ENNReal.ofReal (4 * sparseScaleBlockError t k) * eLpNorm f (ENNReal.ofReal p) S.μ) :=
      mul_le_mul_of_nonneg_left (eLpNorm_mobiusBlockVariation_le S c t ht hp f hf k) bot_le
    _ = ENNReal.ofReal (E k) * (4 * eLpNorm f (ENNReal.ofReal p) S.μ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_mul (sparseLogWeight_nonneg ht A k)]
      norm_num
      ring

#print axioms weightedMobiusBlock_ae_tendsto_zero
end
end FractionalPrimes.Final
