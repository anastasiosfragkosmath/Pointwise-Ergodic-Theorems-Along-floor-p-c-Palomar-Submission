module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLogParameters
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceCorrelationBound

/-!
# Constructing the source-bound data from PMA, PTW, and P1

This module records the exact restricted PTW premise from the blueprint and
uses the global PMA/PTW constants, the checked logarithmic parameter choice,
and the uniform P1 cutoff to construct the context-free data consumed by the
positive-degree source correlation estimate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- Source PTW contract: after fixing eta, the threshold Astar; after fixing
a, one common constant Ctw; and for every X and each arithmetic weight, one
selected decomposition whose designated Type-II components satisfy the full
uniform-in-H,T twisted prefix estimate. -/
def restrictedPolynomialTwistedTask : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 16 →
    ∃ Astar : ℝ, 1 ≤ Astar ∧
      ∀ a : ℝ, Astar ≤ a →
        ∃ Ctw : ℝ, 0 < Ctw ∧
          ∀ X : ℕ, 3 ≤ X →
            Nonempty (RestrictedPTWSelection X Astar a η Ctw
                mobiusComplexPositiveFunction) ∧
              Nonempty (RestrictedPTWSelection X Astar a η Ctw
                vonMangoldtComplexPositiveFunction)

/-- The source log choices and global PMA/PTW constants yield one cutoff
Xstar, chosen before H, P, or the coefficients, such that the exact
positive-degree inverse-context data are available for every admissible
integer interval and either arithmetic weight. -/
theorem exists_conditionalIntegerSourceBoundData_uniform
    (d K c : ℕ) (A η : ℝ)
    (hd : 1 ≤ d) (hA : 0 < A) (hη : 0 < η) (hηmax : η < 3 / 16)
    (hInv : arithmeticInverseTasksWithConstants d K c)
    (hPMA : polynomialMajorArcTask)
    (hPTW : restrictedPolynomialTwistedTask) :
    ∃ D E a : ℕ, ∃ a₀ Astar Cpm Ctw : ℝ, ∃ Xstar : ℕ,
      A + (decompositionB : ℝ) + 5 < (D : ℝ) ∧
      E = 2 * c * D + 3 ∧
      max Astar
        (max ((D : ℝ) + (E : ℝ) + 3) ((d : ℝ) + 3)) < (a : ℝ) ∧
      a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3 ∧
      1 ≤ Astar ∧ Astar ≤ (a : ℝ) ∧
      0 < Cpm ∧ 0 < Ctw ∧ 3 ≤ Xstar ∧
      ∀ X H : ℕ, ∀ P : Polynomial ℝ, ∀ w : ℤ → ℂ,
        Xstar ≤ X →
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
        P.natDegree ≤ d →
        (w = (fun n => (paperMu n : ℂ)) ∨
          w = (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))) →
        Nonempty (ConditionalIntegerSourceBoundData d X H K c D E a
          decompositionB A a₀ η ((Real.log (X : ℝ)) ^ (-(D : ℝ)))
          Cpm Ctw Astar P w) := by
  classical
  rcases hPTW η hη hηmax with ⟨Astar, hAstar, hPTWAtEta⟩
  rcases exists_conditionalIntegerLogParameters d c decompositionB A Astar with
    ⟨D, E, a, a₀, hDsource, hE, hAmax, ha₀⟩
  have hAstarLt : Astar < (a : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hAmax
  have hAstarLeA : Astar ≤ (a : ℝ) := hAstarLt.le
  have hInnerMaxLt :
      max ((D : ℝ) + (E : ℝ) + 3) ((d : ℝ) + 3) < (a : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hAmax
  have hDElt : (D : ℝ) + (E : ℝ) + 3 < (a : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hInnerMaxLt
  have hdPlusLt : (d : ℝ) + 3 < (a : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hInnerMaxLt
  have hEaReal : (E : ℝ) < (a : ℝ) := by
    have hEbelow : (E : ℝ) ≤ (D : ℝ) + (E : ℝ) + 3 := by
      have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast (Nat.zero_le D)
      nlinarith [hDnonneg]
    exact lt_of_le_of_lt hEbelow hDElt
  have hEa : E < a := by exact_mod_cast hEaReal
  have hAgtD : d + 3 < a := by exact_mod_cast hdPlusLt
  have hAstarPos : 0 < Astar := by linarith [hAstar]
  have haPos : 0 < (a : ℝ) := lt_trans hAstarPos hAstarLt
  have ha₀Pos : 0 < a₀ := by
    rw [ha₀]
    positivity
  rcases hPMA a₀ (a : ℝ) η ha₀Pos haPos hη hηmax with
    ⟨Cpm, hCpm, hPMAUniform⟩
  rcases hPTWAtEta (a : ℝ) hAstarLeA with ⟨Ctw, hCtw, hPTWUniform⟩
  obtain ⟨Xstar, hXstarThree, hP1⟩ :=
    exists_conditionalIntegerP1Threshold d c K D E A η Cpm Ctw
      hA hη hDsource hCpm hCtw
  refine ⟨D, E, a, a₀, Astar, Cpm, Ctw, Xstar,
    hDsource, hE, hAmax, ha₀, hAstar, hAstarLeA, hCpm, hCtw,
    hXstarThree, ?_⟩
  intro X H P w hXstar hHlower hHupper hP hw
  have hXthree : 3 ≤ X := le_trans hXstarThree hXstar
  rcases hP1 X hXstar with
    ⟨hL, hLevelFirst, hThreshold, hLevel, hApp, hCpmSmall,
      hCtwSmall, hScaleBudget, hLE, hL3Max⟩
  let L : ℝ := Real.log (X : ℝ)
  let δ : ℝ := (Real.log (X : ℝ)) ^ (-(D : ℝ))
  have hLpos : 0 < L := by
    dsimp [L]
    linarith
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith
  have hDgtFive : 5 < D := by
    have hDgtFiveReal : (5 : ℝ) < (D : ℝ) := by
      have hb : 0 ≤ (decompositionB : ℝ) := Nat.cast_nonneg _
      linarith [hDsource, hA]
    exact_mod_cast hDgtFiveReal
  have hDgeTwo : 2 ≤ D := by omega
  have hDgeTwoReal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDgeTwo
  have hLpowTwo : L ^ (2 : ℝ) ≤ L ^ (D : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone hDgeTwoReal
  have hLpow2Eq : L ^ (2 : ℝ) = L * L := by
    calc
      L ^ (2 : ℝ) = L ^ 2 := Real.rpow_two L
      _ = L * L := by ring
  have hLsq : 4 ≤ L ^ (2 : ℝ) := by
    rw [hLpow2Eq]
    nlinarith [sq_nonneg (L - 2)]
  have hLpowFour : 4 ≤ L ^ (D : ℝ) := le_trans hLsq hLpowTwo
  have hLtwo : 2 ≤ L := by
    dsimp [L]
    exact hL
  have hTwoL : 2 * L ≤ L ^ (2 : ℝ) := by
    calc
      2 * L = L * 2 := by ring
      _ ≤ L * L := mul_le_mul_of_nonneg_left hLtwo hLpos.le
      _ = L ^ (2 : ℝ) := hLpow2Eq.symm
  have hLltSquare : L < L ^ (2 : ℝ) := by
    linarith [hLpos, hTwoL]
  have hLltPowD : L < L ^ (D : ℝ) := lt_of_lt_of_le hLltSquare hLpowTwo
  have hDelta : δ = (Real.log (X : ℝ)) ^ (-(D : ℝ)) := rfl
  have hDeltaInv : δ⁻¹ = (Real.log (X : ℝ)) ^ (D : ℝ) :=
    conditionalDelta_inv X D δ (by simpa [L] using hLpos) hDelta
  have hδpos : 0 < δ := Real.rpow_pos_of_pos (by simpa [L] using hLpos) _
  have hδltHalf : δ < 1 / 2 := by
    dsimp [δ]
    rw [Real.rpow_neg (by simpa [L] using hLpos.le)]
    have hrecip : (L ^ (D : ℝ))⁻¹ ≤ (1 : ℝ) / 4 := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hLpowFour)
    have hrecip' : ((Real.log (X : ℝ)) ^ (D : ℝ))⁻¹ ≤ (1 : ℝ) / 4 := by
      simpa [L] using hrecip
    linarith
  have hδltInvL : δ < L⁻¹ := by
    dsimp [δ]
    rw [Real.rpow_neg (by simpa [L] using hLpos.le)]
    simpa only [one_div] using one_div_lt_one_div_of_lt hLpos hLltPowD
  have hδsmall : δ < min (1 / 2) (L⁻¹) := lt_min hδltHalf hδltInvL
  have hCtimesLogB :
      decompositionC * L ^ ((decompositionB : ℕ) : ℝ) ≤ L ^ (D : ℝ) := by
    calc
      decompositionC * L ^ ((decompositionB : ℕ) : ℝ) ≤
          (L ^ ((D : ℝ) - (decompositionB : ℝ))) *
            L ^ ((decompositionB : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hLevelFirst
          (Real.rpow_nonneg (by simpa [L] using hLpos.le) _)
      _ = L ^ (D : ℝ) := by
        rw [← Real.rpow_add hLpos]
        congr 1
        push_cast
        ring
  have hDtypeBound : decompositionDType (X : ℝ) ≤ L ^ (D : ℝ) := by
    simpa [decompositionDType, L, Real.rpow_natCast] using hCtimesLogB
  have hCtype : 1 ≤ decompositionC := by
    unfold decompositionC
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by norm_num)
  have hCpos : 0 < decompositionC := lt_of_lt_of_le zero_lt_one hCtype
  have hDtypepos : 0 < decompositionDType (X : ℝ) := by
    dsimp [decompositionDType, L]
    exact mul_pos hCpos (by positivity)
  have hδasInv : δ = (L ^ (D : ℝ))⁻¹ := by
    dsimp [δ]
    rw [Real.rpow_neg (by simpa [L] using hLpos.le)]
  have hDeltaType : δ ≤ decompositionDelta (X : ℝ) := by
    rw [hδasInv, decompositionDelta]
    simpa only [one_div] using
      (one_div_le_one_div_of_le hDtypepos hDtypeBound)
  have hPMAat := hPMAUniform X H hXthree hHlower hHupper
  have hMuEnvelopeNonneg :
      0 ≤ residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) := by
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  have hCramerEnvelopeNonneg :
      0 ≤ residuePrefixEnvelope X H
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) := by
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  have hMuPrefix :=
    (le_add_of_nonneg_right hCramerEnvelopeNonneg).trans hPMAat
  have hCramerPrefix :=
    (le_add_of_nonneg_left hMuEnvelopeNonneg).trans hPMAat
  rcases hPTWUniform X hXthree with
    ⟨hMuSelectionNonempty, hLambdaSelectionNonempty⟩
  let hMuSelection := Classical.choice hMuSelectionNonempty
  let hLambdaSelection := Classical.choice hLambdaSelectionNonempty
  let M0 : ℝ := (d.factorial : ℝ) * (K : ℝ)
  let M1 : ℝ := (d.factorial : ℝ) *
    (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ)
  let M2 : ℝ := 2 * Real.pi * (d : ℝ) * (K : ℝ)
  let M3 : ℝ := (d.factorial : ℝ) *
    (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2
  have hL3 : max M0 (max M1 (max M2 M3)) ≤
      (Real.log (X : ℝ)) ^ (3 : ℕ) := by
    simpa [M0, M1, M2, M3] using hL3Max
  have hL3Middle : max M1 (max M2 M3) ≤
      (Real.log (X : ℝ)) ^ (3 : ℕ) :=
    (le_max_right M0 _).trans hL3
  have hL3Inner : max M2 M3 ≤
      (Real.log (X : ℝ)) ^ (3 : ℕ) :=
    (le_max_right M1 _).trans hL3Middle
  refine ⟨{
    hInv := hInv
    hd := hd
    hX := hXthree
    hA := hA
    hη := hη
    hηmax := hηmax
    hDsource := hDsource
    hE := hE
    hEa := hEa
    hAgtDE := hDElt
    hAgtD := hAgtD
    ha₀ := ha₀
    hL := by simpa [L] using hL
    hδpos := hδpos
    hδsmall := by simpa only [L] using hδsmall
    hδinv := hDeltaInv
    hDelta := hDelta
    hDeltaType := hDeltaType
    hThreshold := hThreshold
    hHlower := hHlower
    hHupper := hHupper
    hApp := hApp
    hLevel := hLevel
    hCtype := hCtype
    hScaleBudget := by simpa only [Real.rpow_natCast] using hScaleBudget
    hP := hP
    hL3modulus := (le_max_left M0 _).trans hL3
    hL3variation := (le_max_left M1 _).trans hL3Middle
    hL3q := (le_max_left M0 _).trans hL3
    hL3T := (le_max_left M2 M3).trans hL3Inner
    hL3tv := (le_max_right M2 M3).trans hL3Inner
    hLE := hLE
    hCpmPos := hCpm
    hCpmSmall := hCpmSmall
    hMuPrefix := hMuPrefix
    hCramerPrefix := hCramerPrefix
    hw := hw
    muPTWSelection := hMuSelection
    lambdaPTWSelection := hLambdaSelection
    hCtwPos := hCtw
    hCtwSmall := hCtwSmall
  }⟩

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.exists_conditionalIntegerSourceBoundData_uniform
