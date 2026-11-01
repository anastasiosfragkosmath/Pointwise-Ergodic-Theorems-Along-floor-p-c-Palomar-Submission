module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLowFrequencyCaseSplit
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalVariationAdapter
public import FractionalPrimes.Literature.Uniformity.ScalarInverseClauses
public import FractionalPrimes.Literature.Uniformity.TypeIIRecurrenceOutput

/-!
# Applying the exact Type-II inverse clause in the short-interval split

This file connects the checked coefficient-recurrence inverse clause to the
selected-component high/low frequency split in `lupo:conditional-integer`.
The selected high-frequency twist estimate is an explicit task premise, as in
the approved conditional theorem; the low-frequency case uses the already
checked original-weight PMA contradiction.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators ENNReal

private theorem archimedeanTwist_mul_neg (T x : ℝ) :
    archimedeanTwist T x * archimedeanTwist (-T) x = 1 := by
  unfold archimedeanTwist
  rw [← Complex.exp_add]
  have harg : Complex.I * (T : ℂ) * (Real.log x : ℂ) +
      Complex.I * ((-T : ℝ) : ℂ) * (Real.log x : ℂ) = 0 := by
    push_cast
    ring_nf
  rw [harg, Complex.exp_zero]

private theorem typeIScalarPhaseSum_eq_twisted_interval
    (X H : ℕ) (hX : 3 ≤ X) (P : Polynomial ℝ)
    (f : ComplexPositiveIntegerFunction) (T : ℝ) :
    typeIScalarPhaseSum f P (X : ℝ) (H : ℝ) =
      ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        (complexPositiveIntegerZeroExtension f n *
          archimedeanTwist T (n : ℝ)) *
          (unitFrequencyPhase (P.eval (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ)) := by
  classical
  unfold typeIScalarPhaseSum
  apply Finset.sum_bij
    (s := typeIIntervalSet (X : ℝ) (H : ℝ))
    (t := realIntegerInterval (X : ℝ) (H : ℝ))
    (f := fun n : ℕ => complexPositivePhaseTerm f P n)
    (g := fun n : ℤ =>
      (complexPositiveIntegerZeroExtension f n *
        archimedeanTwist T (n : ℝ)) *
        (unitFrequencyPhase (P.eval (n : ℝ)) *
          archimedeanTwist (-T) (n : ℝ)))
    (fun n _ => (n : ℤ))
  · intro n hn
    have hmem := (mem_typeIIntervalSet (X : ℝ) (H : ℝ) n).mp hn
    apply (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) (n : ℤ)).2
    constructor
    · exact_mod_cast hmem.2.1
    · exact_mod_cast hmem.2.2
  · intro n hn m hm hnm
    exact_mod_cast hnm
  · intro z hz
    have hbounds := (mem_realIntegerInterval_iff (X : ℝ) (H : ℝ) z).mp hz
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hzpos : 0 < z := by exact_mod_cast (lt_trans hXpos hbounds.1)
    have hznonneg : 0 ≤ z := le_of_lt hzpos
    have hcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hznonneg
    refine ⟨z.toNat, ?_, hcast⟩
    · apply (mem_typeIIntervalSet (X : ℝ) (H : ℝ) z.toNat).2
      constructor
      · omega
      constructor
      · have : (X : ℝ) < (z.toNat : ℝ) := by
          rw [show (z.toNat : ℝ) = (z : ℝ) by exact_mod_cast hcast]
          exact hbounds.1
        exact this
      · have : (z.toNat : ℝ) ≤ (X : ℝ) + (H : ℝ) := by
          rw [show (z.toNat : ℝ) = (z : ℝ) by exact_mod_cast hcast]
          exact hbounds.2
        exact this
  · intro n hn
    have hnpos : 0 < n := by
      have hmem := (mem_typeIIntervalSet (X : ℝ) (H : ℝ) n).mp hn
      omega
    rw [complexPositivePhaseTerm_eq_natExtension]
    simp only [complexPositiveIntegerNatExtension, dite_eq_left hnpos]
    have hext : complexPositiveIntegerZeroExtension f (n : ℤ) =
        f ⟨n, hnpos⟩ := by
      simp [complexPositiveIntegerZeroExtension, hnpos]
    rw [hext]
    calc
      f ⟨n, hnpos⟩ * unitFrequencyPhase (P.eval (n : ℝ)) =
          f ⟨n, hnpos⟩ *
            (unitFrequencyPhase (P.eval (n : ℝ)) *
              (archimedeanTwist T (n : ℝ) *
                archimedeanTwist (-T) (n : ℝ))) := by
        rw [archimedeanTwist_mul_neg]
        simp
      _ = (f ⟨n, hnpos⟩ * archimedeanTwist T (n : ℝ)) *
          (unitFrequencyPhase (P.eval (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ)) := by ring

private theorem residuePrefixFiniteInterval_subset_logPhase
    (X H : ℕ) :
    ∀ n ∈ (residuePrefixFiniteInterval X H).points,
      n ∈ logPhaseIntegerInterval (X : ℝ) (H : ℝ) := by
  intro n hn
  simp only [residuePrefixFiniteInterval, FiniteIntegerInterval.points,
    arithmeticProgressionPoints, Finset.mem_image, Finset.mem_range] at hn
  rcases hn with ⟨j, hj, rfl⟩
  simp only [logPhaseIntegerInterval, Set.mem_ofPred_eq]
  have hj1 : j + 1 ≤ H := Nat.succ_le_iff.mpr hj
  constructor
  · norm_num
    exact_mod_cast (show X < X + 1 + j by omega)
  · norm_num
    exact_mod_cast (show X + 1 + j ≤ X + H by omega)

private theorem scalarInverseOutput_log_power_bounds
    (d K c D E : ℕ) (L : ℝ)
    (hK : 1 ≤ K)
    (hL : 2 ≤ L) (hE : E = 2 * c * D + 3)
    (hL3q : (d.factorial : ℝ) * (K : ℝ) ≤ L ^ 3)
    (hL3T : 2 * Real.pi * (d : ℝ) * (K : ℝ) ≤ L ^ 3)
    (hL3tv : (d.factorial : ℝ) *
      (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2 ≤ L ^ 3) :
    (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) ≤ L ^ E ∧
    (2 * Real.pi * (d : ℝ) * ((K : ℝ) * L ^ (c * D))) ≤ L ^ E ∧
    (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) *
      (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ) *
        ((K : ℝ) * L ^ (c * D))) ≤ L ^ E := by
  have hLone : 1 ≤ L := by linarith
  have hLpow : 1 ≤ L ^ (c * D) := one_le_pow₀ hLone
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hWone : 1 ≤ (K : ℝ) * L ^ (c * D) := by
    nlinarith [hKreal, hLpow]
  have hcD : 0 ≤ c * D := Nat.zero_le _
  have hExp : E = 2 * (c * D) + 3 := by
    rw [hE]
    ring
  have hExpSmall : c * D + 3 ≤ E := by
    rw [hExp]
    omega
  have hq : (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) ≤ L ^ E := by
    calc
      (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) =
          ((d.factorial : ℝ) * (K : ℝ)) * L ^ (c * D) := by ring
      _ ≤ L ^ 3 * L ^ (c * D) :=
        mul_le_mul_of_nonneg_right hL3q (by positivity)
      _ = L ^ (c * D + 3) := by rw [← pow_add]; congr 1; omega
      _ ≤ L ^ E := pow_le_pow_right₀ hLone hExpSmall
  have hT : 2 * Real.pi * (d : ℝ) * ((K : ℝ) * L ^ (c * D)) ≤ L ^ E := by
    calc
      2 * Real.pi * (d : ℝ) * ((K : ℝ) * L ^ (c * D)) =
          (2 * Real.pi * (d : ℝ) * (K : ℝ)) * L ^ (c * D) := by ring
      _ ≤ L ^ 3 * L ^ (c * D) :=
        mul_le_mul_of_nonneg_right hL3T (by positivity)
      _ = L ^ (c * D + 3) := by rw [← pow_add]; congr 1; omega
      _ ≤ L ^ E := pow_le_pow_right₀ hLone hExpSmall
  have hconst : (1 : ℝ) + 2 * Real.pi * ((d + 1 : ℕ) : ℝ) ≥ 0 := by positivity
  have hinner :
      1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ) * ((K : ℝ) * L ^ (c * D)) ≤
        (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) *
          ((K : ℝ) * L ^ (c * D)) := by
    nlinarith [hWone, hconst]
  have htvCore :
      (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) *
        (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ) *
          ((K : ℝ) * L ^ (c * D))) ≤
        ((d.factorial : ℝ) *
          (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) *
          (K : ℝ) ^ 2) * L ^ (2 * (c * D)) := by
    have hWnonneg : 0 ≤ (K : ℝ) * L ^ (c * D) := by positivity
    have hfactorNonneg :
        0 ≤ (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) := by positivity
    have hcore := mul_le_mul_of_nonneg_left hinner
      hfactorNonneg
    have hWsq : ((K : ℝ) * L ^ (c * D)) ^ 2 =
        (K : ℝ) ^ 2 * L ^ (2 * (c * D)) := by
      calc
        ((K : ℝ) * L ^ (c * D)) ^ 2 =
            (K : ℝ) ^ 2 * (L ^ (c * D)) ^ 2 := by rw [mul_pow]
        _ = (K : ℝ) ^ 2 * L ^ ((c * D) * 2) := by rw [← pow_mul]
        _ = (K : ℝ) ^ 2 * L ^ (2 * (c * D)) := by
          congr 1
          ring
    calc
      _ ≤ ((d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D))) *
          ((1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) *
            ((K : ℝ) * L ^ (c * D))) := hcore
      _ = (d.factorial : ℝ) *
          (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) *
          ((K : ℝ) * L ^ (c * D)) ^ 2 := by ring
      _ = ((d.factorial : ℝ) *
          (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) *
          (K : ℝ) ^ 2) * L ^ (2 * (c * D)) := by rw [hWsq]; ring
  have htv :
      (d.factorial : ℝ) * ((K : ℝ) * L ^ (c * D)) *
        (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ) *
          ((K : ℝ) * L ^ (c * D))) ≤ L ^ E := by
    calc
      _ ≤ ((d.factorial : ℝ) *
          (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) *
          (K : ℝ) ^ 2) * L ^ (2 * (c * D)) := htvCore
      _ ≤ L ^ 3 * L ^ (2 * (c * D)) :=
        mul_le_mul_of_nonneg_right hL3tv (by positivity)
      _ = L ^ E := by
        rw [← pow_add, hExp]
        congr 1
        omega
  exact ⟨hq, hT, htv⟩

theorem selectedTypeII_refutes_largeCorrelation
    (d X H K c D E a b : ℕ)
    (A a₀ η δ Aminus Aplus Cpm Ctype Ctw : ℝ)
    (P : Polynomial ℝ) (f : ComplexPositiveIntegerFunction)
    (w : ℤ → ℂ)
    (hInv : arithmeticInverseTasksWithConstants d K c)
    (hd : 1 ≤ d) (hX : 3 ≤ X)
    (hA : 0 < A) (hη : 0 < η) (hηmax : η < 3 / 16)
    (hDsource : A + (b : ℝ) + 5 < (D : ℝ))
    (hE : E = 2 * c * D + 3) (hEa : E < a)
    (hAgtDE : (D : ℝ) + (E : ℝ) + 3 < (a : ℝ))
    (hAgtD : d + 3 < a)
    (ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3)
    (hL : 2 ≤ Real.log (X : ℝ))
    (hδpos : 0 < δ)
    (hδsmall : δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹))
    (hδinv : δ⁻¹ = (Real.log (X : ℝ)) ^ D)
    (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η))
    (hTypeIIScale : max Aplus ((X : ℝ) / Aminus) ≤
      Ctype * (X : ℝ) ^ (5 / 8 : ℝ))
    (hCtype : 1 ≤ Ctype)
    (hScaleBudget :
      2 * (K : ℝ) * Ctype * (Real.log (X : ℝ)) ^ (c * D) <
        (X : ℝ) ^ η)
    (hL3q : (d.factorial : ℝ) * (K : ℝ) ≤
      (Real.log (X : ℝ)) ^ 3)
    (hL3T : 2 * Real.pi * (d : ℝ) * (K : ℝ) ≤
      (Real.log (X : ℝ)) ^ 3)
    (hL3tv : (d.factorial : ℝ) *
      (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2 ≤
        (Real.log (X : ℝ)) ^ 3)
    (hLE : (Real.log (X : ℝ)) ^ E ≤ X)
    (hP : P.natDegree ≤ d)
    (hf : typeIIFunction δ Aminus Aplus f)
    (hComponentLarge : δ * (H : ℝ) ≤
      typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ))
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
    (hTwistPrefix : ∀ T : ℝ,
      (X : ℝ) / (H : ℝ) * (Real.log (X : ℝ)) ^ (50 * a) ≤ |T| →
      |T| ≤ (X : ℝ) ^ (a : ℕ) →
      residuePrefixEnvelope X H
        (fun n => complexPositiveIntegerZeroExtension f n *
          archimedeanTwist T (n : ℝ)) ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        Ctw * (H : ℝ) * (Real.log (X : ℝ)) ^ (-(a : ℝ)))
    (hCtwPos : 0 < Ctw)
    (hCtwSmall : Ctw < (Real.log (X : ℝ)) ^ 2)
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    False := by
  rcases hInv with ⟨hK, hc, _hTypeIClause, _hTypeI2Clause, hTypeIIClause⟩
  let L : ℝ := Real.log (X : ℝ)
  let W : ℝ := (K : ℝ) * L ^ (c * D)
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hDreal : (1 : ℝ) ≤ (D : ℝ) := by
    have hbnonneg : 0 ≤ (b : ℝ) := by positivity
    linarith
  have hD : 1 ≤ D := by exact_mod_cast hDreal
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hXgtOne : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hHexp : 0 ≤ (5 / 8 : ℝ) + η := by positivity
  have hHexpPos : 0 < (5 / 8 : ℝ) + η := by positivity
  have hHrealOne : (1 : ℝ) ≤ (H : ℝ) := by
    calc
      1 ≤ (X : ℝ) ^ ((5 / 8 : ℝ) + η) := Real.one_le_rpow hXone hHexp
      _ ≤ (H : ℝ) := hHlower
  have hHgtOne : (1 : ℝ) < (H : ℝ) := by
    exact (Real.one_lt_rpow hXgtOne hHexpPos).trans_le hHlower
  have hHtwo : 2 ≤ H := by
    have hHnat : 1 < H := by exact_mod_cast hHgtOne
    omega
  have hHone : 1 ≤ H := by omega
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hEtaExponent : 1 - η ≤ 1 := by linarith
  have hUpperPower : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
    calc
      (X : ℝ) ^ (1 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hEtaExponent
      _ = (X : ℝ) := Real.rpow_one _
  have hHleX : H ≤ X := by exact_mod_cast (le_trans hHupper hUpperPower)
  have hXint : 3 ≤ (X : ℤ) := by exact_mod_cast hX
  have hHint : 2 ≤ (H : ℤ) := by exact_mod_cast hHtwo
  have hHXint : (H : ℤ) ≤ (X : ℤ) := by exact_mod_cast hHleX
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hWnonneg : 0 ≤ W := by positivity
  have hδbudget : (δ⁻¹) ^ c = L ^ (c * D) := by
    calc
      (δ⁻¹) ^ c = (L ^ D) ^ c := by rw [hδinv]
      _ = L ^ (D * c) := by rw [pow_mul]
      _ = L ^ (c * D) := by rw [Nat.mul_comm D c]
  have hBudgetEq : arithmeticInverseBudget K c δ = W := by
    simp [arithmeticInverseBudget, W, hδbudget]
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
  have hScaleTimesX : W * Ctype * (X : ℝ) ^ (5 / 8 : ℝ) <
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
  have hTypeIIShortLt :
      W * max Aplus ((X : ℝ) / Aminus) < (H : ℝ) := by
    calc
      W * max Aplus ((X : ℝ) / Aminus) ≤
          W * (Ctype * (X : ℝ) ^ (5 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hTypeIIScale hWnonneg
      _ = W * Ctype * (X : ℝ) ^ (5 / 8 : ℝ) := by ring
      _ < (X : ℝ) ^ ((5 / 8 : ℝ) + η) := hScaleTimesX
      _ ≤ (H : ℝ) := hHlower
  have hδeq : δ = L ^ (-(D : ℝ)) := by
    calc
      δ = (δ⁻¹)⁻¹ := by simp
      _ = (L ^ D)⁻¹ := by rw [hδinv]
      _ = L ^ (-(D : ℝ)) := by
        rw [← Real.rpow_natCast L D, ← Real.rpow_neg hLpos.le]
  have hTypeII :
      typeIIFunction δ Aminus Aplus f := hf
  rcases hTypeIIClause (X : ℤ) (H : ℤ) P δ Aminus Aplus f
      hXint hHint hHXint hP hδpos hδsmall hTypeII hComponentLarge with
    hShort | ⟨Q, hQone, hQbudget, hQrecurrence⟩
  · have hShort' : (H : ℝ) ≤ W * max Aplus ((X : ℝ) / Aminus) := by
      simpa [hBudgetEq] using hShort
    exact (not_le_of_gt hTypeIIShortLt) hShort'
  · have hQbudget' : (Q : ℝ) ≤ W := by
      simpa [arithmeticInverseBudget, W, hδbudget] using hQbudget
    have hrecurrence : ∀ j, 1 ≤ j → j ≤ d →
        realDistanceToIntegers
          ((Q : ℝ) * bilinearDerivativeCoefficient (X : ℝ)
            (fun i => (phaseCenteredAt P (X : ℤ)).coeff i) j) ≤
          W * (X : ℝ) / (H : ℝ) ^ (j + 1) := by
      simpa [arithmeticInverseBudget, W, hδbudget] using hQrecurrence
    obtain ⟨T, q, hq, hqBound, hTBound, hTVBound⟩ :=
      typeIIRecurrenceOutput d (X : ℤ) (H : ℤ) P W Q hd
        hXint hHint hHXint hP hQone hQbudget' hrecurrence
    have hSourceBudgets := scalarInverseOutput_log_power_bounds
      d K c D E L (by omega) hL hE hL3q hL3T hL3tv
    rcases hSourceBudgets with ⟨hqCoeff, hTCoeff, hTVCoeff⟩
    have hqLog : (q : ℝ) ≤ L ^ E := hqBound.trans hqCoeff
    have hTVLog : residueClassTotalVariation
        (logPhaseIntegerInterval (X : ℝ) (H : ℝ))
        (fun n : ℤ => unitFrequencyPhase (P.eval (n : ℝ)) *
          archimedeanTwist (-T) (n : ℝ)) q hq ≤ ENNReal.ofReal (L ^ E) :=
      hTVBound.trans (ENNReal.ofReal_le_ofReal hTVCoeff)
    have hTLog : |T| ≤ L ^ E * ((X : ℝ) / (H : ℝ)) ^ (d + 1) := by
      calc
        |T| ≤ 2 * Real.pi * (d : ℝ) * W *
            ((X : ℝ) / (H : ℝ)) ^ (d + 1) := hTBound
        _ ≤ L ^ E * ((X : ℝ) / (H : ℝ)) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right hTCoeff (by positivity)
    have hRatio : (X : ℝ) / (H : ℝ) ≤ (X : ℝ) := by
      exact div_le_self (by positivity) hHrealOne
    have hRatioPow : ((X : ℝ) / (H : ℝ)) ^ (d + 1) ≤
        (X : ℝ) ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) hRatio (d + 1)
    have hTtoX : |T| ≤ (X : ℝ) ^ (d + 2) := by
      calc
        |T| ≤ L ^ E * ((X : ℝ) / (H : ℝ)) ^ (d + 1) := hTLog
        _ ≤ (X : ℝ) * ((X : ℝ) ^ (d + 1)) :=
          mul_le_mul hLE hRatioPow (by positivity) (by positivity)
        _ = (X : ℝ) ^ (d + 2) := by
          rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
          ring
    have hTupper : |T| ≤ (X : ℝ) ^ (a : ℕ) := by
      exact hTtoX.trans (pow_le_pow_right₀ hXone (by omega))
    have hqLoga : (q : ℝ) ≤ L ^ (a : ℝ) := by
      calc
        (q : ℝ) ≤ L ^ (E : ℝ) := by simpa only [← Real.rpow_natCast] using hqLog
        _ ≤ L ^ (a : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLone (by exact_mod_cast hEa.le)
    let g : ℤ → ℂ := fun n => unitFrequencyPhase (P.eval (n : ℝ))
    by_cases hHigh : (X : ℝ) / (H : ℝ) * L ^ (50 * a) ≤ |T|
    · have hPTW := hTwistPrefix T hHigh hTupper
      have hTest := testByResiduePrefixes q X H (L ^ (a : ℝ))
        (fun n => complexPositiveIntegerZeroExtension f n *
          archimedeanTwist T (n : ℝ))
        (fun n => unitFrequencyPhase (P.eval (n : ℝ)) *
          archimedeanTwist (-T) (n : ℝ))
        hq (by omega) hHone hqLoga
      have hfiniteENN :=
        (finiteResidueClassVariation_le_of_subset
          (residuePrefixFiniteInterval X H)
          (logPhaseIntegerInterval (X : ℝ) (H : ℝ))
          (fun n => unitFrequencyPhase (P.eval (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ)) q hq
          (residuePrefixFiniteInterval_subset_logPhase X H)).trans hTVLog
      have hfinite : finiteResidueClassVariation
          (residuePrefixFiniteInterval X H)
          (fun n => unitFrequencyPhase (P.eval (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ)) q ≤ L ^ E :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfiniteENN
      have hEnvNonneg : 0 ≤ residuePrefixEnvelope X H
          (fun n => complexPositiveIntegerZeroExtension f n *
            archimedeanTwist T (n : ℝ)) (L ^ (a : ℝ)) := by
        unfold residuePrefixEnvelope
        exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
      have hCorrelationUpper :
          typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) ≤
            Ctw * (H : ℝ) * L ^ (- (a : ℝ)) * L ^ E := by
        rw [typeIScalarPhaseCorrelation, typeIScalarPhaseSum_eq_twisted_interval
          X H hX P f T]
        calc
          ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
              (complexPositiveIntegerZeroExtension f n *
                archimedeanTwist T (n : ℝ)) *
              (unitFrequencyPhase (P.eval (n : ℝ)) *
                archimedeanTwist (-T) (n : ℝ))‖ ≤
              residuePrefixEnvelope X H
                (fun n => complexPositiveIntegerZeroExtension f n *
                  archimedeanTwist T (n : ℝ)) (L ^ (a : ℝ)) *
              finiteResidueClassVariation (residuePrefixFiniteInterval X H)
                (fun n => unitFrequencyPhase (P.eval (n : ℝ)) *
                  archimedeanTwist (-T) (n : ℝ)) q := by
            simpa only [g] using hTest
          _ ≤ residuePrefixEnvelope X H
                (fun n => complexPositiveIntegerZeroExtension f n *
                  archimedeanTwist T (n : ℝ)) (L ^ (a : ℝ)) * L ^ E :=
            mul_le_mul_of_nonneg_left hfinite hEnvNonneg
          _ ≤ Ctw * (H : ℝ) * L ^ (- (a : ℝ)) * L ^ E :=
            mul_le_mul_of_nonneg_right hPTW (by positivity)
      have hExpGap : (E : ℝ) - (a : ℝ) < -(D : ℝ) - 3 := by
        linarith
      have hLgtOne : 1 < L := by linarith
      have hDecay : Ctw * L ^ ((E : ℝ) - (a : ℝ)) < L ^ (-(D : ℝ)) := by
        calc
          Ctw * L ^ ((E : ℝ) - (a : ℝ)) ≤
              Ctw * L ^ (-(D : ℝ) - 3) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hLone hExpGap.le)
              hCtwPos.le
          _ < L ^ 2 * L ^ (-(D : ℝ) - 3) :=
            mul_lt_mul_of_pos_right hCtwSmall
              (Real.rpow_pos_of_pos hLpos _)
          _ = L ^ (-(D : ℝ) - 1) := by
            rw [← Real.rpow_natCast L 2, ← Real.rpow_add hLpos]
            congr 1
            ring
          _ < L ^ (-(D : ℝ)) :=
            Real.rpow_lt_rpow_of_exponent_lt hLgtOne (by linarith)
      have hDecay' :
          Ctw * (H : ℝ) * L ^ (- (a : ℝ)) * L ^ E <
            (H : ℝ) * L ^ (-(D : ℝ)) := by
        calc
          Ctw * (H : ℝ) * L ^ (- (a : ℝ)) * L ^ E =
              (H : ℝ) * (Ctw * L ^ ((E : ℝ) - (a : ℝ))) := by
            rw [← Real.rpow_natCast L E]
            calc
              Ctw * (H : ℝ) * L ^ (- (a : ℝ)) * L ^ (E : ℝ) =
                  (H : ℝ) * (Ctw *
                    (L ^ (- (a : ℝ)) * L ^ (E : ℝ))) := by ring
              _ = (H : ℝ) * (Ctw * L ^ ((E : ℝ) - (a : ℝ))) := by
                rw [← Real.rpow_add hLpos]
                congr 3
                ring
          _ < (H : ℝ) * L ^ (-(D : ℝ)) :=
            mul_lt_mul_of_pos_left hDecay hHpos
      have hcomponentLower : (H : ℝ) * L ^ (-(D : ℝ)) ≤
          typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) := by
        calc
          (H : ℝ) * L ^ (-(D : ℝ)) = δ * (H : ℝ) := by rw [hδeq]; ring
          _ ≤ typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) := hComponentLarge
      have hcorrLt := hCorrelationUpper.trans_lt hDecay'
      exact (not_le_of_gt hcorrLt) hcomponentLower
    · have hTlow : |T| < (X : ℝ) / (H : ℝ) * L ^ (50 * a) :=
        lt_of_not_ge hHigh
      exact lowFrequencyTypeII_refutes_largeCorrelation
        X H A a₀ η E a T q g w Cpm hX hη hηmax hHlower hHupper hL hA
        ha₀ (by exact_mod_cast (show 1 ≤ a by omega)) hEa hCpmPos hCpmSmall
        hMuPrefix hCramerPrefix hw hq hqLog hTlow
        (by simpa [g] using hTVLog) hLarge

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.selectedTypeII_refutes_largeCorrelation

