module

public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerToRealCentreTransfer

/-!
# Large-centre transfer of polynomial-phase estimates

This module proves the large-`X` branch of blueprint `lc:integer-to-real`.
The integer cancellation hypothesis keeps its source quantifier order; the
small-centre bounded-range branch is separate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Centres

open _root_.Polynomial

noncomputable section

/-- The Möbius polynomial-phase sum on the exact integer-centred interval. -/
def integerToRealMobiusPhaseSum
    (P : Polynomial ℝ) (M L : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
    (FractionalPrimes.paperMu n : ℂ) *
      FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))

/-- The integer-centred von Mangoldt-minus-Cramér polynomial-phase sum. -/
def integerToRealLambdaModelPhaseSum
    (P : Polynomial ℝ) (M L : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
    ((FractionalPrimes.paperLambda n -
        FractionalPrimes.paperCramerWeight
          (FractionalPrimes.paperShortBlockCutoff (M : ℝ)) n : ℝ) : ℂ) *
      FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))

/-- The real-centred von Mangoldt-minus-Cramér sum on `(X,X+H]`. -/
def realCenterLambdaModelPhaseSum
    (P : Polynomial ℝ) (X H : ℝ) : ℂ :=
  ∑ n ∈ FractionalPrimes.realIntegerInterval X H,
    ((FractionalPrimes.paperLambda n -
        FractionalPrimes.paperCramerWeight
          (FractionalPrimes.paperShortBlockCutoff X) n : ℝ) : ℂ) *
      FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))

private theorem norm_real_phase_sum_le_sum_abs
    (S : Finset ℤ) (a : ℤ → ℝ) (P : Polynomial ℝ) :
    ‖∑ n ∈ S, (a n : ℂ) *
        FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
      ∑ n ∈ S, |a n| := by
  calc
    ‖∑ n ∈ S, (a n : ℂ) *
          FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        ∑ n ∈ S, ‖(a n : ℂ) *
          FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ := norm_sum_le _ _
    _ = ∑ n ∈ S, |a n| := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        FractionalPrimes.norm_unitFrequencyPhase]
      ring

/-- Large-`X` part of blueprint `lc:integer-to-real`. The integer estimate
has the order `∀ η, ∃ C_int, ∀ P, ∀ M,L`; after selecting `η = ε/2`, the
real-centred estimate has the exact large-centre constant
`2^(A+1) C_int + K_A`. -/
theorem integerToRealLargeXTransfer
    (k : ℕ) (A : ℝ) (hA : 0 < A)
    (hInteger : ∀ η : ℝ, 0 < η → η < 3 / 16 →
      ∃ C_int : ℝ, 0 < C_int ∧
        ∀ P : Polynomial ℝ, P.natDegree ≤ k →
          ∀ M L : ℕ, 3 ≤ M →
            (M : ℝ) ^ (5 / 8 + η) ≤ (L : ℝ) →
            (L : ℝ) ≤ (M : ℝ) ^ (1 - η) →
              ‖integerToRealMobiusPhaseSum P M L‖ +
                ‖integerToRealLambdaModelPhaseSum P M L‖ ≤
                C_int * (L : ℝ) * (Real.log (M : ℝ)) ^ (-A : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hεtop : ε < 3 / 16) :
    ∃ C_int : ℝ, 0 < C_int ∧
      ∀ X H : ℝ,
        integerToRealThreshold ε ≤ X →
        X ^ (5 / 8 + ε) ≤ H →
        H ≤ X ^ (1 - ε) →
        ∀ P : Polynomial ℝ, P.natDegree ≤ k →
          ‖∑ n ∈ FractionalPrimes.realIntegerInterval X H,
              (FractionalPrimes.paperMu n : ℂ) *
                FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖realCenterLambdaModelPhaseSum P X H‖ ≤
            (2 ^ (A + 1) * C_int +
              Real.exp 13 * 2 ^ A *
                (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                    (10 * (A + 2 / 5)) +
                  4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                    (A + 2 / 5))) *
              H * (Real.log X) ^ (-A : ℝ) := by
  obtain ⟨C_int, hC_int, hIntegerEta⟩ :=
    hInteger (ε / 2) (by positivity) (by linarith)
  refine ⟨C_int, hC_int, ?_⟩
  intro X H hX₀ hHlower hHupper P hP
  let M : ℕ := Nat.floor X
  let L : ℕ := Nat.floor (X + H) - M
  have hparameters := integerToRealFloorParameterTransfer
    hε hεtop hX₀ hHlower hHupper
  dsimp [M, L] at hparameters
  rcases hparameters with
    ⟨hMthree, hEtaPos, hEtaTop, hMXlower, hMXupper, hHL, hLU,
      hScaleLower, hScaleUpper, hLogCompare, hInterval⟩
  have hIntegerBound := hIntegerEta P hP M L hMthree hScaleLower hScaleUpper
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hXpos : 0 < X := by linarith [hMXupper, hMpos]
  have hMcenter : (M : ℝ) = (Int.floor X : ℝ) := by
    dsimp [M]
    exact_mod_cast (Int.natCast_floor_eq_floor (le_of_lt hXpos))
  have hModelChange := integerToRealCramerModelError
    hA hε hεtop hX₀ hHlower
  have hHpos : 0 < H := by
    have hpowpos := Real.rpow_pos_of_pos hXpos (5 / 8 + ε)
    linarith [hHlower]
  have hIoc :
      Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ) =
        FractionalPrimes.realIntegerInterval X H := by
    rw [hInterval]
    congr 1
  have hModelChangeIoc :
      (∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
        |FractionalPrimes.paperCramerWeight
              (FractionalPrimes.paperShortBlockCutoff (M : ℝ)) n -
            FractionalPrimes.paperCramerWeight
              (FractionalPrimes.paperShortBlockCutoff X) n|) ≤
        Real.exp 13 * 2 ^ A *
          (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
              (10 * (A + 2 / 5)) +
            4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
              (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ) := by
    calc
      _ = ∑ n ∈ FractionalPrimes.realIntegerInterval X H,
            |FractionalPrimes.paperCramerWeight
                  (FractionalPrimes.paperShortBlockCutoff (Int.floor X)) n -
                FractionalPrimes.paperCramerWeight
                  (FractionalPrimes.paperShortBlockCutoff X) n| := by
          rw [hIoc]
          apply Finset.sum_congr rfl
          intro n hn
          rw [hMcenter]
      _ = ∑ n ∈ FractionalPrimes.realIntegerInterval X H,
            |FractionalPrimes.paperCramerWeight
                  (FractionalPrimes.paperShortBlockCutoff X) n -
                FractionalPrimes.paperCramerWeight
                  (FractionalPrimes.paperShortBlockCutoff (Int.floor X)) n| := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [abs_sub_comm]
      _ ≤ Real.exp 13 * 2 ^ A *
            (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                (10 * (A + 2 / 5)) +
              4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ) := hModelChange
  have hMgt1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
  have hXgt1 : (1 : ℝ) < X := by linarith [hMXupper, hMgt1]
  have hMlogpos : 0 < Real.log (M : ℝ) := Real.log_pos hMgt1
  have hXlogpos : 0 < Real.log X := Real.log_pos hXgt1
  have hlogHalf : Real.log X / 2 ≤ Real.log (M : ℝ) := by
    linarith [hLogCompare]
  have hlogPower :
      (Real.log (M : ℝ)) ^ (-A : ℝ) ≤
        2 ^ A * (Real.log X) ^ (-A : ℝ) := by
    have hdecrease := Real.rpow_le_rpow_of_nonpos
      (x := Real.log X / 2) (y := Real.log (M : ℝ)) (z := -A)
      (by positivity) hlogHalf (by linarith [hA])
    have hdivide :
        (Real.log X / 2) ^ (-A : ℝ) =
          2 ^ A * (Real.log X) ^ (-A : ℝ) := by
      calc
        (Real.log X / 2) ^ (-A : ℝ) =
            (Real.log X) ^ (-A : ℝ) / (2 : ℝ) ^ (-A : ℝ) := by
          rw [Real.div_rpow hXlogpos.le (by norm_num) (-A)]
        _ = 2 ^ A * (Real.log X) ^ (-A : ℝ) := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) A]
          rw [div_eq_mul_inv, inv_inv]
          ring
    exact hdecrease.trans_eq hdivide
  have hIntScaled :
      C_int * (L : ℝ) * (Real.log (M : ℝ)) ^ (-A : ℝ) ≤
        2 ^ (A + 1) * C_int * H * (Real.log X) ^ (-A : ℝ) := by
    have hpowMnonneg : 0 ≤ (Real.log (M : ℝ)) ^ (-A : ℝ) :=
      Real.rpow_nonneg hMlogpos.le _
    calc
      C_int * (L : ℝ) * (Real.log (M : ℝ)) ^ (-A : ℝ) ≤
          C_int * (2 * H) * (Real.log (M : ℝ)) ^ (-A : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLU hC_int.le) hpowMnonneg
      _ ≤ C_int * (2 * H) *
            (2 ^ A * (Real.log X) ^ (-A : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogPower (by positivity)
      _ = 2 ^ (A + 1) * C_int * H * (Real.log X) ^ (-A : ℝ) := by
        calc
          C_int * (2 * H) * (2 ^ A * (Real.log X) ^ (-A : ℝ)) =
              (2 ^ (1 : ℝ) * 2 ^ A) * C_int * H *
                (Real.log X) ^ (-A : ℝ) := by rw [Real.rpow_one]; ring
          _ = 2 ^ (1 + A) * C_int * H * (Real.log X) ^ (-A : ℝ) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 A]
          _ = 2 ^ (A + 1) * C_int * H * (Real.log X) ^ (-A : ℝ) := by
              rw [show (1 : ℝ) + A = A + 1 by ring]
  have hLambdaSplit :
      realCenterLambdaModelPhaseSum P X H =
        integerToRealLambdaModelPhaseSum P M L +
          ∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
            ((FractionalPrimes.paperCramerWeight
                  (FractionalPrimes.paperShortBlockCutoff (M : ℝ)) n -
                FractionalPrimes.paperCramerWeight
                  (FractionalPrimes.paperShortBlockCutoff X) n : ℝ) : ℂ) *
              FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ)) := by
    unfold realCenterLambdaModelPhaseSum integerToRealLambdaModelPhaseSum
    rw [← hIoc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  have hLambdaNorm :
      ‖realCenterLambdaModelPhaseSum P X H‖ ≤
        ‖integerToRealLambdaModelPhaseSum P M L‖ +
          Real.exp 13 * 2 ^ A *
            (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                (10 * (A + 2 / 5)) +
              4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ) := by
    rw [hLambdaSplit]
    calc
      _ ≤ ‖integerToRealLambdaModelPhaseSum P M L‖ +
            ‖∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
                ((FractionalPrimes.paperCramerWeight
                      (FractionalPrimes.paperShortBlockCutoff (M : ℝ)) n -
                    FractionalPrimes.paperCramerWeight
                      (FractionalPrimes.paperShortBlockCutoff X) n : ℝ) : ℂ) *
                  FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ :=
          norm_add_le _ _
      _ ≤ ‖integerToRealLambdaModelPhaseSum P M L‖ +
            ∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
              |FractionalPrimes.paperCramerWeight
                    (FractionalPrimes.paperShortBlockCutoff (M : ℝ)) n -
                  FractionalPrimes.paperCramerWeight
                    (FractionalPrimes.paperShortBlockCutoff X) n| :=
          add_le_add le_rfl (norm_real_phase_sum_le_sum_abs _ _ P)
      _ ≤ _ := add_le_add le_rfl hModelChangeIoc
  have hMuEq :
      (∑ n ∈ FractionalPrimes.realIntegerInterval X H,
        (FractionalPrimes.paperMu n : ℂ) *
          FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))) =
        integerToRealMobiusPhaseSum P M L := by
    unfold integerToRealMobiusPhaseSum
    rw [← hIoc]
  calc
    _ = ‖integerToRealMobiusPhaseSum P M L‖ +
          ‖realCenterLambdaModelPhaseSum P X H‖ := by rw [hMuEq]
    _ ≤ ‖integerToRealMobiusPhaseSum P M L‖ +
          ‖integerToRealLambdaModelPhaseSum P M L‖ +
          Real.exp 13 * 2 ^ A *
            (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                (10 * (A + 2 / 5)) +
              4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ) := by
          calc
            _ ≤ ‖integerToRealMobiusPhaseSum P M L‖ +
                  (‖integerToRealLambdaModelPhaseSum P M L‖ +
                    Real.exp 13 * 2 ^ A *
                      (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                          (10 * (A + 2 / 5)) +
                        4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                          (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ)) :=
                add_le_add le_rfl hLambdaNorm
            _ = _ := by ring
    _ ≤ C_int * (L : ℝ) * (Real.log (M : ℝ)) ^ (-A : ℝ) +
          Real.exp 13 * 2 ^ A *
            (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                (10 * (A + 2 / 5)) +
              4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ) :=
            add_le_add hIntegerBound le_rfl
    _ ≤ 2 ^ (A + 1) * C_int * H * (Real.log X) ^ (-A : ℝ) +
          Real.exp 13 * 2 ^ A *
            (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                (10 * (A + 2 / 5)) +
              4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                (A + 2 / 5)) * H * (Real.log X) ^ (-A : ℝ) :=
            add_le_add hIntScaled le_rfl
    _ = (2 ^ (A + 1) * C_int +
          Real.exp 13 * 2 ^ A *
            (8 * (10 * (A + 2 / 5) / Real.exp 1) ^
                (10 * (A + 2 / 5)) +
              4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^
                (A + 2 / 5))) * H * (Real.log X) ^ (-A : ℝ) := by ring

#print axioms integerToRealLargeXTransfer

end

end FractionalPrimes.Literature.Centres

end
