module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalTypeIInverseCase
public import FractionalPrimes.Literature.Uniformity.ScalarInverseClauses

/-!
# Applying the exact Type-I and Type-I₂ inverse clauses

This adapter takes the selected component supplied by the decomposition,
applies the checked common-constant inverse clauses, rules out their short
length alternatives using the source threshold, and feeds the resulting
binomial witness into the original-weight PMA contradiction.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators

private theorem typeI2ScaleProduct_le
    (X C A : ℝ) (hX : 0 < X) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hAupper : A ≤ C * X ^ (7 / 16 : ℝ)) :
    X ^ (1 / 3 : ℝ) * A ^ (2 / 3 : ℝ) ≤ C * X ^ (5 / 8 : ℝ) := by
  have hAupperRpow : A ^ (2 / 3 : ℝ) ≤
      (C * X ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hAupper (by norm_num)
  have hsplit : (C * X ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ) =
      C ^ (2 / 3 : ℝ) * X ^ (7 / 24 : ℝ) := by
    calc
      (C * X ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ) =
          C ^ (2 / 3 : ℝ) * (X ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.mul_rpow (by linarith) (Real.rpow_nonneg hX.le _)
      _ = C ^ (2 / 3 : ℝ) * X ^ (7 / 24 : ℝ) := by
        rw [← Real.rpow_mul hX.le]
        congr 1
        norm_num
  have hCpower : C ^ (2 / 3 : ℝ) ≤ C :=
    calc
      C ^ (2 / 3 : ℝ) ≤ C ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hC (by norm_num)
      _ = C := by rw [Real.rpow_one]
  have hAquarter : A ^ (2 / 3 : ℝ) ≤
      C ^ (2 / 3 : ℝ) * X ^ (7 / 24 : ℝ) := by
    calc
      A ^ (2 / 3 : ℝ) ≤
          (C * X ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ) := hAupperRpow
      _ = C ^ (2 / 3 : ℝ) * X ^ (7 / 24 : ℝ) := hsplit
  have hXnonneg : 0 ≤ X ^ (7 / 24 : ℝ) := Real.rpow_nonneg hX.le _
  calc
    X ^ (1 / 3 : ℝ) * A ^ (2 / 3 : ℝ) ≤
        X ^ (1 / 3 : ℝ) * (C ^ (2 / 3 : ℝ) * X ^ (7 / 24 : ℝ)) :=
      mul_le_mul_of_nonneg_left hAquarter
        (Real.rpow_nonneg hX.le _)
    _ ≤ X ^ (1 / 3 : ℝ) * (C * X ^ (7 / 24 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hCpower hXnonneg)
        (Real.rpow_nonneg hX.le _)
    _ = C * X ^ (5 / 8 : ℝ) := by
      calc
        X ^ (1 / 3 : ℝ) * (C * X ^ (7 / 24 : ℝ)) =
            C * (X ^ (1 / 3 : ℝ) * X ^ (7 / 24 : ℝ)) := by ring
        _ = C * X ^ (5 / 8 : ℝ) := by
          calc
            C * (X ^ (1 / 3 : ℝ) * X ^ (7 / 24 : ℝ)) =
                C * X ^ ((1 / 3 : ℝ) + 7 / 24) := by
              rw [← Real.rpow_add hX]
            _ = C * X ^ (5 / 8 : ℝ) := by
              congr 1
              norm_num

/-- From the exact Type-I or Type-I₂ inverse clause, a selected large
component forces the binomial witness used by
`typeIOrTypeI2BinomialPMAContradiction`. The first alternative is excluded
by the source scale bounds and
`2 K C (log X)^(cD) < X^η`, the corresponding clause of the large-`X`
threshold. -/
theorem selectedTypeIOrTypeI2_refutes_largeCorrelation
    (d X H K c D E a b : ℕ) (A a₀ η δ : ℝ)
    (P : Polynomial ℝ) (f : ComplexPositiveIntegerFunction)
    (w : ℤ → ℂ) (Cpm Ctype : ℝ)
    (hInv : arithmeticInverseTasksWithConstants d K c)
    (hd : 1 ≤ d) (hX : 3 ≤ X)
    (hA : 0 < A) (hη : 0 < η) (_hηmax : η < 3 / 16)
    (hDsource : A + (b : ℝ) + 5 < (D : ℝ))
    (hE : E = 2 * c * D + 3) (hEa : E < a)
    (ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hδpos : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹))
    (hδinv : δ⁻¹ = (Real.log (X : ℝ)) ^ D)
    (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η))
    (hCtype : 1 ≤ Ctype)
    (hScaleBudget :
      2 * (K : ℝ) * Ctype * (Real.log (X : ℝ)) ^ (c * D) <
        (X : ℝ) ^ η)
    (hP : P.natDegree ≤ d)
    (hSelectedType :
      typeIFunction δ
          (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) f ∨
        typeI2Function δ
          (Ctype * (X : ℝ) ^ (7 / 16 : ℝ)) f)
    (hComponentLarge :
      δ * (H : ℝ) ≤
        typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ))
    (hL3modulus : (d.factorial : ℝ) * (K : ℝ) ≤
      (Real.log (X : ℝ)) ^ 3)
    (hL3variation : (d.factorial : ℝ) *
      (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ) ≤
        (Real.log (X : ℝ)) ^ 3)
    (hCpmPos : 0 < Cpm)
    (hCpmSmall : 2 * Cpm < (Real.log (X : ℝ)) ^ 2)
    (hMuPrefix :
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        Cpm * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀))
    (hCramerPrefix :
      residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        Cpm * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀))
    (hw : w = (fun n => (paperMu n : ℂ)) ∨
      w = (fun n => (paperLambda n : ℂ) -
        (paperShortBlockCramerWeight (X : ℝ) n : ℂ)))
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    False := by
  rcases hInv with ⟨hK, hc, hTypeIClause, hTypeI2Clause, _hTypeIIClause⟩
  let L : ℝ := Real.log (X : ℝ)
  let W : ℝ := (K : ℝ) * L ^ (c * D)
  have hLpos : 0 < L := by linarith
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hDlargeReal : (1 : ℝ) ≤ (D : ℝ) := by
    have hbnonneg : 0 ≤ (b : ℝ) := by positivity
    linarith
  have hDpos : 1 ≤ D := by exact_mod_cast hDlargeReal
  have hXrealOne : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hXrealGtOne : (1 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 1 < X by omega)
  have hLengthExponentPos : 0 < (5 / 8 : ℝ) + η := by positivity
  have hHgtOne : (1 : ℝ) < (H : ℝ) :=
    (Real.one_lt_rpow hXrealGtOne hLengthExponentPos).trans_le hHlower
  have hHtwo : 2 ≤ H := by
    have hHnatGtOne : 1 < H := by exact_mod_cast hHgtOne
    omega
  have hEtaExponent : 1 - η ≤ 1 := by linarith
  have hUpperPower : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
    calc
      (X : ℝ) ^ (1 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXrealOne hEtaExponent
      _ = (X : ℝ) := Real.rpow_one _
  have hHleX : H ≤ X := by
    exact_mod_cast (le_trans hHupper hUpperPower)
  have hXint : (3 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX
  have hHint : (2 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hHtwo
  have hHXint : (H : ℤ) ≤ (X : ℤ) := by exact_mod_cast hHleX
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hWnonneg : 0 ≤ W := by positivity
  have hBudgetPower : (δ⁻¹) ^ c = L ^ (c * D) := by
    calc
      (δ⁻¹) ^ c = (L ^ D) ^ c := by rw [hδinv]
      _ = L ^ (D * c) := by rw [pow_mul]
      _ = L ^ (c * D) := by rw [Nat.mul_comm D c]
  have hBudgetEq : arithmeticInverseBudget K c δ = W := by
    simp [arithmeticInverseBudget, W, hBudgetPower]
  have hScaleSmall : W * Ctype < (X : ℝ) ^ η := by
    have hTwice : 2 * (W * Ctype) < (X : ℝ) ^ η := by
      calc
        2 * (W * Ctype) =
            2 * (K : ℝ) * Ctype * (Real.log (X : ℝ)) ^ (c * D) := by
          simp [W, L]
          ring
        _ < (X : ℝ) ^ η := hScaleBudget
    nlinarith
  have hXpos : 0 < (X : ℝ) := by positivity
  have hXfiveEighthPos : 0 < (X : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_pos_of_pos hXpos _
  have hScaleTimesX :
      W * Ctype * (X : ℝ) ^ (5 / 8 : ℝ) <
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) := by
    calc
      W * Ctype * (X : ℝ) ^ (5 / 8 : ℝ) <
          (X : ℝ) ^ η * (X : ℝ) ^ (5 / 8 : ℝ) :=
        mul_lt_mul_of_pos_right hScaleSmall hXfiveEighthPos
      _ = (X : ℝ) ^ (η + (5 / 8 : ℝ)) :=
        (Real.rpow_add hXpos η (5 / 8 : ℝ)).symm
      _ = (X : ℝ) ^ ((5 / 8 : ℝ) + η) := by
        congr 1
        ring
  have hTypeIShortLt :
      W * (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) < (H : ℝ) := by
    calc
      W * (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) =
          W * Ctype * (X : ℝ) ^ (5 / 8 : ℝ) := by ring
      _ < (X : ℝ) ^ ((5 / 8 : ℝ) + η) := hScaleTimesX
      _ ≤ (H : ℝ) := hHlower
  rcases hSelectedType with hSelectedI | hSelectedI2
  · rcases hTypeIClause (X : ℤ) (H : ℤ) P δ
        (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) f
        hXint hHint hHXint hP hδpos hδsmall hSelectedI hComponentLarge with
      hShort | ⟨r, hr, hrbudget, hnorm⟩
    · have hShort' :
          (H : ℝ) ≤ W * (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) := by
        simpa [hBudgetEq] using hShort
      exact (not_le_of_gt hTypeIShortLt) hShort'
    · have hrbudget' : (r : ℝ) ≤ (K : ℝ) * (δ⁻¹) ^ c := by
        simpa [arithmeticInverseBudget] using hrbudget
      have hnorm' :
          binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
            (X : ℤ) (H : ℝ) ≤ (K : ℝ) * (δ⁻¹) ^ c := by
        simpa [arithmeticInverseBudget] using hnorm
      exact typeIOrTypeI2BinomialPMAContradiction
        d X H K c D E a A a₀ η δ P r w Cpm
        hd hX hη _hηmax hHlower hHupper hL hA hE hEa ha₀ hK hc hDpos
        hP hr hδinv hrbudget' hnorm' hL3modulus hL3variation
        hCpmPos hCpmSmall hMuPrefix hCramerPrefix hw hLarge
  · rcases hTypeI2Clause (X : ℤ) (H : ℤ) P δ
        (Ctype * (X : ℝ) ^ (7 / 16 : ℝ)) f
        hXint hHint hHXint hP hδpos hδsmall hSelectedI2 hComponentLarge with
      hShort | ⟨r, hr, hrbudget, hnorm⟩
    · have hTypeI2Scale := typeI2ScaleProduct_le (X : ℝ) Ctype
        (Ctype * (X : ℝ) ^ (7 / 16 : ℝ)) hXpos hCtype
        (hSelectedI2.2.2.1) le_rfl
      have hShort' :
          (H : ℝ) ≤ W * (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) := by
        calc
          (H : ℝ) ≤ arithmeticInverseBudget K c δ *
              (X : ℝ) ^ (1 / 3 : ℝ) *
              (Ctype * (X : ℝ) ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ) := hShort
          _ = arithmeticInverseBudget K c δ *
              ((X : ℝ) ^ (1 / 3 : ℝ) *
                (Ctype * (X : ℝ) ^ (7 / 16 : ℝ)) ^ (2 / 3 : ℝ)) := by ring
          _ ≤ arithmeticInverseBudget K c δ *
              (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) := by
            rw [hBudgetEq]
            exact mul_le_mul_of_nonneg_left hTypeI2Scale hWnonneg
          _ = W * (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) := by rw [hBudgetEq]
      exact (not_le_of_gt hTypeIShortLt) hShort'
    · have hrbudget' : (r : ℝ) ≤ (K : ℝ) * (δ⁻¹) ^ c := by
        simpa [arithmeticInverseBudget] using hrbudget
      have hnorm' :
          binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
            (X : ℤ) (H : ℝ) ≤ (K : ℝ) * (δ⁻¹) ^ c := by
        simpa [arithmeticInverseBudget] using hnorm
      exact typeIOrTypeI2BinomialPMAContradiction
        d X H K c D E a A a₀ η δ P r w Cpm
        hd hX hη _hηmax hHlower hHupper hL hA hE hEa ha₀ hK hc hDpos
        hP hr hδinv hrbudget' hnorm' hL3modulus hL3variation
        hCpmPos hCpmSmall hMuPrefix hCramerPrefix hw hLarge

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.selectedTypeIOrTypeI2_refutes_largeCorrelation
