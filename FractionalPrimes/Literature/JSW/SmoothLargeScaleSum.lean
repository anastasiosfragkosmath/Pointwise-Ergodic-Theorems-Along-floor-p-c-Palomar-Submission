module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The exact reciprocal geometric tail needed in both smooth off-support estimates. -/
@[expose] public section
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem finite_largeScale_reciprocal_sum
    {b ℓ : ℝ} (hb : 1 < b) (hℓ : 0 < ℓ) (K : Finset ℤ)
    (hlarge : ∀ k ∈ K, ℓ < b^k) :
    (∑ k ∈ K, ℓ/b^k) ≤ b/(b-1) := by
  classical
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
  have hq1 : b⁻¹ < 1 := (inv_lt_one₀ hb0).2 hb
  by_cases hK : K.Nonempty
  · let k₀ := K.min' hK
    have hk₀ : k₀ ∈ K := Finset.min'_mem K hK
    have hfirst : ℓ/b^k₀ ≤ 1 := (div_le_one (zpow_pos hb0 _)).2 (hlarge k₀ hk₀).le
    let e : ℤ → ℕ := fun k => (k-k₀).toNat
    have he (k : ℤ) (hk : k ∈ K) : (e k : ℤ) = k-k₀ :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (Finset.min'_le K k hk))
    have hterm (k : ℤ) (hk : k ∈ K) : ℓ/b^k ≤ (b⁻¹)^(e k) := by
      have hpow : b^k = b^k₀*b^(e k : ℤ) := by
        rw [← zpow_add₀ hb0.ne', he k hk]
        congr 1
        omega
      have hrec : (b^(e k : ℤ))⁻¹ = (b⁻¹)^(e k) := by simp
      calc
        ℓ/b^k = (ℓ/b^k₀)*(b^(e k : ℤ))⁻¹ := by rw [hpow]; ring
        _ ≤ 1*(b^(e k : ℤ))⁻¹ := mul_le_mul_of_nonneg_right hfirst (by positivity)
        _ = _ := by rw [one_mul, hrec]
    have hsum : (∑ k ∈ K, (b⁻¹)^(e k)) = ∑ n ∈ K.image e, (b⁻¹)^n := by
      rw [Finset.sum_image]
      intro k hk l hl heq
      have hcast := congrArg (fun n : ℕ => (n : ℤ)) heq
      rw [he k hk, he l hl] at hcast
      omega
    calc
      _ ≤ ∑ k ∈ K, (b⁻¹)^(e k) := Finset.sum_le_sum hterm
      _ = ∑ n ∈ K.image e, (b⁻¹)^n := hsum
      _ ≤ ∑' n : ℕ, (b⁻¹)^n := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
        (fun n _ => pow_nonneg hq0 _)
      _ = (1-b⁻¹)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
      _ = _ := by field_simp
  · have hz : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    simp only [hz, Finset.sum_empty]
    exact div_nonneg hb0.le (by linarith)

theorem jswTau_finite_largeScale_reciprocal_sum
    {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (K : Finset ℤ) :
    (∑ k ∈ K.filter (fun k => ℓ < jswTau a ha k), ℓ/jswTau a ha k) ≤
      jswB a ha/(jswB a ha-1) := by
  apply finite_largeScale_reciprocal_sum (jswB_gt_one ha) hℓ
  intro k hk
  exact (Finset.mem_filter.mp hk).2

#print axioms finite_largeScale_reciprocal_sum
#print axioms jswTau_finite_largeScale_reciprocal_sum
end
end FractionalPrimes.Literature.JSW
end
