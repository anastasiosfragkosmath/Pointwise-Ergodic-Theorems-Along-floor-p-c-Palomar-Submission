module
public import FractionalPrimes.Final.MobiusIncrements
public import FractionalPrimes.Final.MobiusSparseScales
public import FractionalPrimes.Final.AlmostSureSummability
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

def identityModel {X : Type*} [MeasurableSpace X] (S : System X) : InvertibleSystem X where
  μ := S.μ
  sigmaFinite := S.sigmaFinite
  T := MeasurableEquiv.refl X
  preserves := MeasurePreserving.id S.μ

def mobiusBlockVariation {X : Type*} [MeasurableSpace X]
    (S : System X) (c t : ℝ) (ht : 1 < t) (f : X → ℂ) (k : ℕ) : X → ℝ≥0∞ :=
  rVariationOnFun 2 (mobiusAverage S c f)
    (Set.Icc (sparseScaleAsScale ht k) (sparseScaleAsScale ht (k + 1)))

theorem eLpNorm_mobiusBlockVariation_le {X : Type*} [MeasurableSpace X]
    (S : System X) (c t : ℝ) (ht : 1 < t) {p : ℝ} (hp : 1 < p)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) (k : ℕ) :
    eLpNorm (mobiusBlockVariation S c t ht f k) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal (4 * sparseScaleBlockError t k) * eLpNorm f (ENNReal.ofReal p) S.μ := by
  let a := sparseScaleAsScale ht k
  let b := sparseScaleAsScale ht (k + 1)
  have hab : a ≤ b := sparseScaleAsScale_monotone ht (Nat.le_succ k)
  have hF (N : Scale) : MemLp (mobiusAverage S c f N) (ENNReal.ofReal p) S.μ :=
    memLp_weightedAverage S c _ f N hf
  have hbase := eLpNorm_rVariationOnFun_scaleInterval_le_sum (identityModel S) p 2
    hp.le (by norm_num) (mobiusAverage S c f) a b hab hF
  have hterm (i : ℕ) :
      eLpNorm (fun x => mobiusAverage S c f (scaleOffset a (i + 1)) x -
        mobiusAverage S c f (scaleOffset a i) x) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal (2 * Real.log (2 * (((a.1 + i : ℕ) : ℝ) + 1)) /
        (((a.1 + i : ℕ) : ℝ) + 1)) * eLpNorm f (ENNReal.ofReal p) S.μ := by
    have h := eLpNorm_mobiusAverage_scaleSucc_sub_le S c f (scaleOffset a i) hp hf
    have heq : scaleSucc (scaleOffset a i) = scaleOffset a (i + 1) := by
      apply Subtype.ext; simp [scaleSucc, scaleOffset]; omega
    rw [heq] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ bot_le
    apply ENNReal.ofReal_le_ofReal
    have ha : 1 ≤ a.1 := a.2
    have hlog : 1 ≤ Real.log (2 * (((a.1 + i : ℕ) : ℝ) + 1)) := by
      have harg : (3 : ℝ) ≤ 2 * (((a.1 + i : ℕ) : ℝ) + 1) := by
        have hnat : (1 : ℝ) ≤ ((a.1 + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ a.1 + i by omega)
        linarith
      have h3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
      exact h3.le.trans (Real.log_le_log (by norm_num) harg)
    simp only [scaleOffset, Subtype.coe_mk, scaleSucc, Nat.cast_add, Nat.cast_one, add_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simp only [Nat.cast_add, Nat.cast_one, add_assoc] at hlog
    linarith
  calc
    _ ≤ _ := hbase
    _ ≤ ∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal (2 * Real.log (2 * (((a.1 + i : ℕ) : ℝ) + 1)) /
          (((a.1 + i : ℕ) : ℝ) + 1)) * eLpNorm f (ENNReal.ofReal p) S.μ :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i ∈ Finset.range (b.1 - a.1),
        ENNReal.ofReal (2 * Real.log (2 * (((a.1 + i : ℕ) : ℝ) + 1)) /
          (((a.1 + i : ℕ) : ℝ) + 1))) * eLpNorm f (ENNReal.ofReal p) S.μ := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (sparseScaleIncrementCoeffSum_le ht k) bot_le

#print axioms eLpNorm_mobiusBlockVariation_le
end
end FractionalPrimes.Final
