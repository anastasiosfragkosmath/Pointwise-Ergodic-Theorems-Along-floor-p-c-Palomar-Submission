module
public import FractionalPrimes.SparseScales
@[expose] public section
namespace FractionalPrimes.Final
open Filter
noncomputable section

/-- Choose the auxiliary sparse scale independently of the input Lp exponent.
This permits every logarithmic weight A, not just a bounded range of A. -/
theorem exists_mobiusSparseParameter {p A : ℝ} (hp : 1 < p) (hA : 0 < A) :
    ∃ t : ℝ, 1 < t ∧ p * ((A + 2) * sparseScaleTau t - 1) < -1 := by
  let B := p * (A + 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := (p - 1) / (B + p - 1)
  have hden : 0 < B + p - 1 := by linarith
  have hδ : 0 < δ := div_pos (by linarith) hden
  have hδ1 : δ < 1 := (div_lt_one hden).mpr (by linarith)
  have hδB : δ * B < p - 1 := by
    have hmul : δ * (B + p - 1) = p - 1 := by
      dsimp [δ]; field_simp
    nlinarith
  refine ⟨1 + δ, by linarith, ?_⟩
  have ht : 1 < 1 + δ := by linarith
  have hq : sparseScaleQ (1 + δ) = 1 + δ := by
    rw [sparseScaleQ_eq_min, min_eq_left (by linarith)]
  have hτ : sparseScaleTau (1 + δ) ≤ δ := by
    rw [sparseScaleTau_eq_on_domain ht, hq]
    have hd : 0 < 100 * (1 + δ) := by positivity
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hsmall : B * sparseScaleTau (1 + δ) < p - 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hτ hB.le) (by nlinarith [hδB])
  dsimp [B] at hsmall
  nlinarith

/-- The weighted short-block coefficients are p-summable with the chosen
sparse scale. The two extra powers cover the original logarithmic block bound. -/
theorem summable_weightedSparseBlock {p A t : ℝ} (hp : 1 < p) (hA : 0 < A)
    (ht : 1 < t) (hsmall : p * ((A + 2) * sparseScaleTau t - 1) < -1) :
    Summable (fun k : ℕ =>
      ((Real.log (2 * (sparseScale t (k + 1) : ℝ))) ^ A *
        sparseScaleBlockError t k) ^ p) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_sparseScaleBlockError_polynomial_bound ht
  let τ := sparseScaleTau t
  let C := (3 * Real.log 2) ^ A * C₀
  let β := p * ((A + 2) * τ - 1)
  have hseries : Summable (fun k : ℕ => C ^ p * (k : ℝ) ^ β) :=
    (Real.summable_nat_rpow.mpr hsmall).mul_left (C ^ p)
  apply Summable.of_norm_bounded_eventually hseries
  have hlarge : ∀ᶠ k : ℕ in cofinite, 1 ≤ k := by
    rw [Nat.cofinite_eq_atTop]; exact eventually_ge_atTop 1
  filter_upwards [hlarge] with k hk
  have hb := hbound k hk
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hs : 1 ≤ sparseScale t (k + 1) := by
    rw [← sparseScale_zero ht]
    exact sparseScale_monotone ht (Nat.zero_le _)
  have hlog : 0 ≤ Real.log (2 * (sparseScale t (k + 1) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * sparseScale t (k + 1) by omega))
  have hw := Real.rpow_le_rpow hlog (sparseScale_endpoint_log_bound ht hk) hA.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hτ : 0 < sparseScaleTau t := sparseScaleTau_pos ht
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by positivity) _) hC₀.le
  have he : 0 ≤ sparseScaleBlockError t k := sparseScaleBlockError_nonneg ht k
  have hbase : 0 ≤ Real.log (2 * (sparseScale t (k + 1) : ℝ)) ^ A *
      sparseScaleBlockError t k := mul_nonneg (Real.rpow_nonneg hlog _) he
  have hprod : Real.log (2 * (sparseScale t (k + 1) : ℝ)) ^ A *
      sparseScaleBlockError t k ≤ C * (k : ℝ) ^ ((A + 2) * τ - 1) := by
    calc
      _ ≤ (3 * Real.log 2 * (k : ℝ) ^ τ) ^ A *
          (C₀ * (k : ℝ) ^ (2 * τ - 1)) :=
        mul_le_mul hw hb he (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← mul_assoc]
        rw [mul_right_comm ((3 * Real.log 2) ^ A), mul_assoc,
          ← Real.rpow_mul hk0.le, ← Real.rpow_add hk0]
        dsimp [C]
        congr 2
        ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hbase _)]
  calc
    _ ≤ (C * (k : ℝ) ^ ((A + 2) * τ - 1)) ^ p := Real.rpow_le_rpow hbase hprod (by linarith)
    _ = _ := by
      rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul hk0.le]
      dsimp [β]
      congr 2
      ring

#print axioms exists_mobiusSparseParameter
#print axioms summable_weightedSparseBlock
end
end FractionalPrimes.Final
