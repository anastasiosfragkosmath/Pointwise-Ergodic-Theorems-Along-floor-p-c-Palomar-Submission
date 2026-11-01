module
public import FractionalPrimes.Final.MobiusLogDecay
public import FractionalPrimes.Final.MobiusShortBlocks
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sparseLogWeight_le_baseLog {t A : ℝ} (ht : 1 < t) (hA : 0 < A)
    {k : ℕ} (hk : 1 ≤ k) :
    sparseLogWeight t A k ≤ 6 ^ A * Real.log (sparseScale t k : ℝ) ^ A := by
  have hlow := (sparseScale_log_bounds ht hk).1
  have hhigh := sparseScale_endpoint_log_bound ht hk
  have hbase : 0 ≤ Real.log (sparseScale t k : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ sparseScale t k from
      (sparseScale_zero ht ▸ sparseScale_monotone ht (Nat.zero_le k)))
  have hlog : 0 ≤ Real.log (2 * (sparseScale t (k + 1) : ℝ)) := by
    have hs : 1 ≤ sparseScale t (k + 1) := by
      rw [← sparseScale_zero ht]; exact sparseScale_monotone ht (Nat.zero_le _)
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ 2 * sparseScale t (k + 1) by omega)
  calc
    _ ≤ (6 * Real.log (sparseScale t k : ℝ)) ^ A :=
      Real.rpow_le_rpow hlog (by nlinarith) hA.le
    _ = _ := Real.mul_rpow (by norm_num) hbase

theorem logWeightedMobius_sparse_norm_summable {p t A : ℝ}
    (hp : 1 < p) (ht : 1 < t) (hA : 0 < A) (c : FractionalExponent)
    {X : Type*} [MeasurableSpace X] (S : System X) (f : X → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    (∑' k, eLpNorm (logWeightedMobiusAverage S c.value A f (sparseScaleAsScale ht k))
      (ENNReal.ofReal p) S.μ) ≠ ∞ := by
  let F := fun N => logWeightedMobiusAverage S c.value A f N
  have hmem (N : Scale) : MemLp (F N) (ENNReal.ofReal p) S.μ :=
    (memLp_weightedAverage S c.value _ f N hf).const_smul _
  let e := fun k => (eLpNorm (F (sparseScaleAsScale ht k)) (ENNReal.ofReal p) S.μ).toReal
  let B := max (eLpNorm (F ⟨1, by omega⟩) (ENNReal.ofReal p) S.μ).toReal
    (eLpNorm (F ⟨2, by omega⟩) (ENNReal.ofReal p) S.μ).toReal
  have hD : 0 < 2 / sparseScaleTau t := div_pos (by norm_num) (sparseScaleTau_pos ht)
  obtain ⟨C, hC, hb⟩ := logWeightedMobiusAverage_logDecay hp c hA _ hD
  have he : Summable e := by
    apply summable_sparseScale_error_of_log_decay ht e B
      (C * (eLpNorm f (ENNReal.ofReal p) S.μ).toReal)
      (by dsimp [B]; positivity) (by positivity) (fun _ => ENNReal.toReal_nonneg) ?_ ?_
    · intro k hk
      have hpos : 1 ≤ sparseScale t k := by
        rw [← sparseScale_zero ht]; exact sparseScale_monotone ht (Nat.zero_le _)
      have hcases : sparseScale t k = 1 ∨ sparseScale t k = 2 := by omega
      rcases hcases with h | h
      · have heq : sparseScaleAsScale ht k = ⟨1, by omega⟩ := Subtype.ext h
        simpa [e, B, heq] using le_max_left
          (eLpNorm (F ⟨1, by omega⟩) (ENNReal.ofReal p) S.μ).toReal
          (eLpNorm (F ⟨2, by omega⟩) (ENNReal.ofReal p) S.μ).toReal
      · have heq : sparseScaleAsScale ht k = ⟨2, by omega⟩ := Subtype.ext h
        simpa [e, B, heq] using le_max_right
          (eLpNorm (F ⟨1, by omega⟩) (ENNReal.ofReal p) S.μ).toReal
          (eLpNorm (F ⟨2, by omega⟩) (ENNReal.ofReal p) S.μ).toReal
    · intro k hk
      have hlog : 0 ≤ Real.log (sparseScale t k : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ sparseScale t k by omega))
      have hn : (ENNReal.ofReal (C * Real.log (sparseScale t k : ℝ) ^ (-(2 / sparseScaleTau t))) *
          eLpNorm f (ENNReal.ofReal p) S.μ) ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
      have hreal := ENNReal.toReal_mono hn (hb S f hf (sparseScaleAsScale ht k) hk)
      dsimp [e]
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC (Real.rpow_nonneg hlog _)),
        mul_right_comm] using hreal
  have hEq : (fun k => ENNReal.ofReal (e k)) =
      (fun k => eLpNorm (F (sparseScaleAsScale ht k)) (ENNReal.ofReal p) S.μ) := by
    funext k
    exact ENNReal.ofReal_toReal (hmem _).eLpNorm_ne_top
  have hsum := he.tsum_ofReal_ne_top
  rwa [hEq] at hsum

#print axioms logWeightedMobius_sparse_norm_summable
end
end FractionalPrimes.Final
