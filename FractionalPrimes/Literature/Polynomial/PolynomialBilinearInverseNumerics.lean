module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseBudgets

/-!
# Numerical setup for the bilinear inverse theorem

This file isolates the first standalone step in blueprint item
`lbi:inverse-theorem`: the scale and auxiliary-density consequences of the
single explicit length hypothesis.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The length hypothesis forces both bilinear aspect ratios above the exact
budget `Z`, while `H≤X=LM` supplies the reverse geometric inequalities. -/
theorem bilinearInverse_scale_bounds
    (d : ℕ) (hd : 1 ≤ d) (X H L M ρ : ℝ)
    (hX : 3 ≤ X) (hH : 2 ≤ H) (hHX : H ≤ X)
    (hM : 2 ≤ M) (hL : L = X / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hlength :
      (bilinearInverseConstant d : ℝ) *
          (ρ⁻¹) ^ bilinearInverseExponent d * max L M ≤ H) :
    8 ≤ bilinearInverseZ d ρ⁻¹ ∧
    bilinearInverseZ d ρ⁻¹ ≤ H / L ∧
    bilinearInverseZ d ρ⁻¹ ≤ H / M ∧
    H / L ≤ M ∧ H / M ≤ L := by
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := by
    rw [hL]
    positivity
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hvalues := bilinearInverseBudget_values d hd ρ⁻¹ hρinv
  have hZ8 : 8 ≤ bilinearInverseZ d ρ⁻¹ := hvalues.2.2.2.2.2.2.2.2
  have hρinvOne : 1 ≤ ρ⁻¹ := by linarith
  have hZpower := bilinearInverseZ_le_budget d ρ⁻¹ hρinvOne
  have hmax0 : 0 ≤ max L M := by
    exact le_trans (by linarith : 0 ≤ M) (le_max_right L M)
  have hZmax : bilinearInverseZ d ρ⁻¹ * max L M ≤ H := by
    calc
      bilinearInverseZ d ρ⁻¹ * max L M ≤
          ((bilinearInverseConstant d : ℝ) *
            (ρ⁻¹) ^ bilinearInverseExponent d) * max L M :=
        mul_le_mul_of_nonneg_right hZpower hmax0
      _ ≤ H := hlength
  have hZ0 : 0 ≤ bilinearInverseZ d ρ⁻¹ := by linarith
  have hZLmul : bilinearInverseZ d ρ⁻¹ * L ≤ H := by
    calc
      bilinearInverseZ d ρ⁻¹ * L ≤
          bilinearInverseZ d ρ⁻¹ * max L M :=
        mul_le_mul_of_nonneg_left (le_max_left L M) hZ0
      _ ≤ H := hZmax
  have hZMmul : bilinearInverseZ d ρ⁻¹ * M ≤ H := by
    calc
      bilinearInverseZ d ρ⁻¹ * M ≤
          bilinearInverseZ d ρ⁻¹ * max L M :=
        mul_le_mul_of_nonneg_left (le_max_right L M) hZ0
      _ ≤ H := hZmax
  have hZr : bilinearInverseZ d ρ⁻¹ ≤ H / L :=
    (le_div_iff₀ hLpos).2 hZLmul
  have hZs : bilinearInverseZ d ρ⁻¹ ≤ H / M :=
    (le_div_iff₀ hMpos).2 hZMmul
  have hXL : X = L * M := by
    rw [hL]
    field_simp [hMpos.ne']
  have hrM : H / L ≤ M := by
    calc
      H / L ≤ X / L := div_le_div_of_nonneg_right hHX hLpos.le
      _ = M := by rw [hXL]; field_simp [hLpos.ne']
  have hsL : H / M ≤ L := by
    calc
      H / M ≤ X / M := div_le_div_of_nonneg_right hHX hMpos.le
      _ = L := hL.symm
  exact ⟨hZ8, hZr, hZs, hrM, hsL⟩

/-- The two inverse intermediate scales define genuine densities in
`(0,1/2)`. -/
theorem bilinearInverse_auxiliary_densities
    (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    0 < (bilinearInverseZOne d ρ⁻¹)⁻¹ ∧
    (bilinearInverseZOne d ρ⁻¹)⁻¹ < 1 / 2 ∧
    0 < (bilinearInverseZTwo d ρ⁻¹)⁻¹ ∧
    (bilinearInverseZTwo d ρ⁻¹)⁻¹ < 1 / 2 := by
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  rcases bilinearInverseBudget_values d hd ρ⁻¹ hρinv with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  have hZOnePos : 0 < bilinearInverseZOne d ρ⁻¹ := by linarith
  have hZTwoPos : 0 < bilinearInverseZTwo d ρ⁻¹ := by linarith
  constructor
  · exact inv_pos.mpr hZOnePos
  constructor
  · simpa only [one_div] using
      ((inv_lt_inv₀ hZOnePos (by norm_num : (0 : ℝ) < 2)).2 hZOne)
  constructor
  · exact inv_pos.mpr hZTwoPos
  · simpa only [one_div] using
      ((inv_lt_inv₀ hZTwoPos (by norm_num : (0 : ℝ) < 2)).2 hZTwo)

#print axioms bilinearInverse_scale_bounds
#print axioms bilinearInverse_auxiliary_densities

end

end FractionalPrimes.Literature.Polynomial
