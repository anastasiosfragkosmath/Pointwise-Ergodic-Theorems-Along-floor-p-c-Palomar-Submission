module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylLowCoefficient
public import FractionalPrimes.Literature.Polynomial.ScalarWeylTopDenominator
public import FractionalPrimes.Literature.Polynomial.ScalarWeylRecursiveBudget

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- Long-branch coefficient control after the degree-`d-1` induction
hypothesis. The bounds `hβ` and `hN'lower` are its outputs after the
source's residue-fiber reindexing and density transfer. The explicit
`hLowCoeff` relation identifies the lower-degree polynomial's coefficients
with those of the original polynomial below degree `d`. -/
theorem scalarWeyl_longInductionCoefficientControl
    {d N N' r s : ℕ} {δ R D : ℝ}
    (hd : 2 ≤ d) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hN : 1 ≤ N) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrR : (r : ℝ) ≤ R) (hrN : (r : ℝ) ≤ (N : ℝ))
    (hsD : (s : ℝ) ≤ D)
    (hRdef : R =
      (weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹)
    (hDdef : D =
      (weylBoundPolynomialD d).eval₂ (Nat.castRingHom ℝ) δ⁻¹)
    (hN'lower : (N : ℝ) / (r : ℝ) ≤ (N' : ℝ))
    (c : ℤ) (hc : |(c : ℝ)| ≤ (r : ℝ))
    (P Plo : Polynomial ℝ) (hPlo : Plo.natDegree ≤ d - 1)
    (hLowCoeff : ∀ j, 1 ≤ j → j < d → P.coeff j = Plo.coeff j)
    (hnear : realDistanceToIntegers ((r : ℝ) * P.coeff d) ≤
      R / ((N : ℝ) ^ d))
    (hβ : ∀ i, 1 ≤ i → i < d →
      realDistanceToIntegers
        ((s : ℝ) *
          (Plo.comp (Polynomial.C (r : ℝ) * Polynomial.X +
            Polynomial.C (c : ℝ))).coeff i) ≤
        D / ((N' : ℝ) ^ i)) :
    1 ≤ s * r ^ (d - 1) ∧
      ((s * r ^ (d - 1) : ℕ) : ℝ) ≤
        (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ ∧
      (∀ j, 1 ≤ j → j < d →
        (N : ℝ) ^ j * realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) ≤
            (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) ∧
      (N : ℝ) ^ d * realDistanceToIntegers
        (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff d) ≤
          (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
  have hRD := weylBoundPolynomialRD_eval_inv_ge_one d hd hδ hδhalf
  have hRone : 1 ≤ R := by simpa [hRdef] using hRD.1
  have hbudget := weylBoundPolynomial_inductionBudgets_le d hd hδ hδhalf
  have hbudgetLow :
      (2 : ℝ) ^ d * D * R ^ (d - 1) ≤
        (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
    simpa [hDdef, hRdef] using hbudget.1
  have hbudgetTop :
      D * R ^ (d - 1) ≤
        (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
    simpa [hDdef, hRdef] using hbudget.2
  have htop := scalarWeyl_topCoefficientAndDenominator
    hd hN hr hs hrR hsD hRone hnear
  have hdenomCap : ((s * r ^ (d - 1) : ℕ) : ℝ) ≤
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ :=
    htop.2.1.trans hbudgetTop
  have hNposNat : 0 < N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hNdpos : 0 < (N : ℝ) ^ d := pow_pos hNpos _
  have htopScaled :
      (N : ℝ) ^ d * realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff d) ≤
        (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
    calc
      (N : ℝ) ^ d * realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff d) ≤
          (N : ℝ) ^ d * (D * R ^ (d - 1) / ((N : ℝ) ^ d)) :=
        mul_le_mul_of_nonneg_left htop.2.2 (pow_nonneg (Nat.cast_nonneg _) _)
      _ = D * R ^ (d - 1) := by
        field_simp [ne_of_gt hNdpos]
      _ ≤ (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ :=
        hbudgetTop
  have hlowScaled : ∀ j, 1 ≤ j → j < d →
      (N : ℝ) ^ j * realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) ≤
        (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
    intro j hj hjd
    have hlow := scalarWeyl_lowCoefficientBound
      hd hj hjd hN hr hs hrR hrN hsD hN'lower c hc Plo hPlo hβ
    have hNjpos : 0 < (N : ℝ) ^ j := pow_pos hNpos _
    calc
      (N : ℝ) ^ j * realDistanceToIntegers
          (((s * r ^ (d - 1) : ℕ) : ℝ) * P.coeff j) =
          (N : ℝ) ^ j * realDistanceToIntegers
            (((s * r ^ (d - 1) : ℕ) : ℝ) * Plo.coeff j) := by
              rw [hLowCoeff j hj hjd]
      _ ≤ (N : ℝ) ^ j *
          ((2 : ℝ) ^ d * D * R ^ (d - 1) / ((N : ℝ) ^ j)) :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt hNjpos)
      _ = (2 : ℝ) ^ d * D * R ^ (d - 1) := by
        field_simp [ne_of_gt hNjpos]
      _ ≤ (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ :=
        hbudgetLow
  exact ⟨htop.1, hdenomCap, hlowScaled, htopScaled⟩

end FractionalPrimes.Literature.Polynomial
