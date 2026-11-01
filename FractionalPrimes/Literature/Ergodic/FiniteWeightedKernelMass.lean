module

public import FractionalPrimes.Operators

/-! Kernel mass bounds that retain collisions of the floor-time map. -/
@[expose] public section
namespace FractionalPrimes
noncomputable section

theorem finiteWeightedIntegerKernel_norm_tsum_le
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) :
    (∑' m : ℤ, ‖(finiteWeightedIntegerKernel c N w).coeff m‖) ≤
      (N.val : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val, ‖w n‖ := by
  classical
  let I := Finset.Icc 1 N.val
  let S := I.image (floorPower c)
  rw [tsum_eq_sum (s := S) (fun m hm => by
    rw [finiteWeightedIntegerKernel_coeff_eq_zero_of_not_mem c N w hm, norm_zero])]
  have hInv : ‖(N.val : ℂ)⁻¹‖ = (N.val : ℝ)⁻¹ := by simp
  calc
    _ ≤ ∑ m ∈ S, (N.val : ℝ)⁻¹ *
        ∑ n ∈ I, if floorPower c n = m then ‖w n‖ else 0 := by
      apply Finset.sum_le_sum
      intro m _
      change ‖(N.val : ℂ)⁻¹ * ∑ n ∈ I,
        if floorPower c n = m then w n else 0‖ ≤ _
      rw [norm_mul, hInv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [apply_ite, norm_zero] using
        norm_sum_le I (fun n => if floorPower c n = m then w n else 0)
    _ = (N.val : ℝ)⁻¹ * ∑ n ∈ I, ‖w n‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      simp_rw [eq_comm (a := floorPower c n)]
      rw [Finset.sum_ite_eq']
      exact if_pos (Finset.mem_image.mpr ⟨n, hn, rfl⟩)

theorem finiteWeightedIntegerKernel_norm_tsum_le_of_weight_bound
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) (B : ℝ)
    (hw : ∀ n ∈ Finset.Icc 1 N.val, ‖w n‖ ≤ B) :
    (∑' m : ℤ, ‖(finiteWeightedIntegerKernel c N w).coeff m‖) ≤ B := by
  have hN : (N.val : ℝ) ≠ 0 := by exact_mod_cast N.property.ne'
  calc
    _ ≤ (N.val : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val, ‖w n‖ :=
      finiteWeightedIntegerKernel_norm_tsum_le c N w
    _ ≤ (N.val : ℝ)⁻¹ * ∑ _n ∈ Finset.Icc 1 N.val, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (by positivity)
    _ = B := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

#print axioms finiteWeightedIntegerKernel_norm_tsum_le
end
end FractionalPrimes
