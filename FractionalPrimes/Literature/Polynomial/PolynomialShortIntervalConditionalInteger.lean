module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalSourceBoundDataAssembly
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalDegreeZeroPMA
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor

/-!
# Conditional integer-centred polynomial short-interval bound

This module assembles the checked positive-degree source correlation bound,
the degree-zero PMA branch, and the elementary bounded-X estimate into the
conditional theorem stated in `lupo:conditional-integer`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators
open FractionalPrimes.Literature.Uniformity

/-- The elementary pointwise bound used on the finite range below the P1
cutoff. The model term is bounded by the exact density estimate at the
location-dependent Cramér cutoff. -/
theorem conditionalIntegerFiniteXNaturalTwoWeightBound
    (X H : ℕ) (η : ℝ) (hX : 3 ≤ X) (hη : 0 < η)
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η))
    (P : Polynomial ℝ) :
    ‖∑ n ∈ Finset.Ioc X (X + H),
        (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
      ‖∑ n ∈ Finset.Ioc X (X + H),
        ((paperLambda (n : ℤ) : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
      (H : ℝ) *
        (1 + Real.log (2 * (X : ℝ)) +
          Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := by
  classical
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by linarith
  have hExp : 1 - η ≤ (1 : ℝ) := by linarith
  have hHleXreal : (H : ℝ) ≤ (X : ℝ) := by
    calc
      (H : ℝ) ≤ (X : ℝ) ^ (1 - η) := hHupper
      _ ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hExp
      _ = (X : ℝ) := Real.rpow_one _
  have hHleX : H ≤ X := by exact_mod_cast hHleXreal
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlog2Xpos : 0 < Real.log (2 * (X : ℝ)) := by
    apply Real.log_pos
    nlinarith
  have hmodelBound :
      paperCramerDensity (paperShortBlockCutoff (X : ℝ)) ≤
        Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
    simpa [paperShortBlockCutoff] using
      FractionalPrimes.paperCramerDensity_at_cutoff_scale hXreal
  have hMuPoint : ∀ n ∈ Finset.Ioc X (X + H),
      ‖(paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤ 1 := by
    intro n hn
    have hnlarge : X < n := (Finset.mem_Ioc.mp hn).1
    have hnpositive : 1 ≤ (n : ℤ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    rw [norm_mul, norm_unitFrequencyPhase, mul_one]
    exact_mod_cast paperMu_abs_le_one hnpositive
  have hLambdaPoint : ∀ n ∈ Finset.Ioc X (X + H),
      ‖((paperLambda (n : ℤ) : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        Real.log (2 * (X : ℝ)) +
          Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
    intro n hn
    have hnlarge : X < n := (Finset.mem_Ioc.mp hn).1
    have hnupperNat : n ≤ X + H := (Finset.mem_Ioc.mp hn).2
    have hnupper : (n : ℝ) ≤ 2 * (X : ℝ) := by
      have hnupperNat' : n ≤ 2 * X := by omega
      exact_mod_cast hnupperNat'
    have hnpositive : 1 ≤ (n : ℤ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hLambdaBounds := paperLambda_bounds hnpositive
    have hLambdaUpper : paperLambda (n : ℤ) ≤ Real.log (2 * (X : ℝ)) := by
      exact le_trans hLambdaBounds.2
        (Real.log_le_log (by positivity) hnupper)
    have hLambdaAbsUpper : |paperLambda (n : ℤ)| ≤ Real.log (2 * (X : ℝ)) := by
      rw [abs_of_nonneg hLambdaBounds.1]
      exact hLambdaUpper
    have hModelAbs :
        |paperShortBlockCramerWeight (X : ℝ) (n : ℤ)| ≤
          Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
      exact (cramerWeight_abs_le_density (X : ℝ) (n : ℤ)).trans hmodelBound
    rw [norm_mul, norm_unitFrequencyPhase, mul_one]
    calc
      _ ≤ ‖(paperLambda (n : ℤ) : ℂ)‖ +
          ‖(paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)‖ :=
        norm_sub_le _ _
      _ = |paperLambda (n : ℤ)| +
          |paperShortBlockCramerWeight (X : ℝ) (n : ℤ)| := by simp
      _ ≤ Real.log (2 * (X : ℝ)) +
          Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) :=
        add_le_add hLambdaAbsUpper hModelAbs
  have hMuSum :
      ‖∑ n ∈ Finset.Ioc X (X + H),
          (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        (H : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc X (X + H),
          ‖(paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc X (X + H), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hMuPoint n hn
      _ = (H : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul, cramerShortInterval_card]
  have hLambdaSum :
      ‖∑ n ∈ Finset.Ioc X (X + H),
          ((paperLambda (n : ℤ) : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        (H : ℝ) *
          (Real.log (2 * (X : ℝ)) +
            Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc X (X + H),
          ‖((paperLambda (n : ℤ) : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc X (X + H),
          (Real.log (2 * (X : ℝ)) +
            Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hLambdaPoint n hn
      _ = (H : ℝ) *
          (Real.log (2 * (X : ℝ)) +
            Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul, cramerShortInterval_card]
        ring
  calc
    _ ≤ (H : ℝ) + (H : ℝ) *
          (Real.log (2 * (X : ℝ)) +
            Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) :=
      add_le_add hMuSum hLambdaSum
    _ = (H : ℝ) *
          (1 + Real.log (2 * (X : ℝ)) +
            Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := by ring

/-- The conditional integer polynomial estimate from the three scalar source
tasks. Its large-X range is controlled by P1 and the checked source case
split; the smaller X range uses the exact elementary bound stated in the
blueprint. -/
theorem conditionalIntegerUniformityOfScalarTasks
    (d : ℕ) (A η : ℝ) (hA : 0 < A) (hη : 0 < η)
    (hηmax : η < 3 / 16)
    (hPMA : polynomialMajorArcTask)
    (hInv : arithmeticInverseTasks)
    (hPTW : restrictedPolynomialTwistedTask) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X H : ℕ, 3 ≤ X →
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
        ∀ P : Polynomial ℝ, P.natDegree ≤ d →
          ‖∑ n ∈ Finset.Ioc X (X + H),
              (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖∑ n ∈ Finset.Ioc X (X + H),
              ((paperLambda (n : ℤ) : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
                unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
            C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  classical
  by_cases hd0 : d = 0
  · obtain ⟨C, hC, hBound⟩ :=
      degreeZeroIntegerUniformityOfPMA hPMA A η hA hη hηmax
    refine ⟨C, hC, ?_⟩
    intro X H hX hHlower hHupper P hP
    have hPzero : P.natDegree ≤ 0 := by omega
    have hRealBound := hBound X H hX hHlower hHupper P hPzero
    have hMuSum :
        (∑ n ∈ Finset.Ioc X (X + H),
          (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))) =
        ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ)) :=
      (realIntegerInterval_sum_eq_nat_Ioc X H (fun n : ℤ =>
        (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ)))).symm
    have hLambdaSum :
        (∑ n ∈ Finset.Ioc X (X + H),
          ((paperLambda (n : ℤ) : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ))) =
        ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ)) :=
      (realIntegerInterval_sum_eq_nat_Ioc X H (fun n : ℤ =>
        ((paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ)))).symm
    simpa only [hMuSum, hLambdaSum] using hRealBound
  · have hdpos : 1 ≤ d := by omega
    obtain ⟨K, c, hInvAtD⟩ := hInv d hdpos
    obtain ⟨D, E, a, a₀, Astar, Cpm, Ctw, Xstar,
      hDsource, hE, hAmax, ha₀, hAstar, hAstarLeA, hCpm, hCtw,
      hXstarThree, hData⟩ :=
      exists_conditionalIntegerSourceBoundData_uniform d K c A η hdpos
        hA hη hηmax hInvAtD hPMA hPTW
    let Bstar : ℝ :=
      1 + Real.log (2 * (Xstar : ℝ)) +
        Real.exp 13 * (Real.log (Xstar : ℝ)) ^ (2 / 5 : ℝ)
    let Cfinal : ℝ := max 2 ((Real.log (Xstar : ℝ)) ^ A * Bstar)
    have hXstarReal : (3 : ℝ) ≤ (Xstar : ℝ) := by exact_mod_cast hXstarThree
    have hlogXstarpos : 0 < Real.log (Xstar : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Xstar by omega))
    have hBstarpos : 0 < Bstar := by
      dsimp [Bstar]
      have hlog2Xstar : 0 < Real.log (2 * (Xstar : ℝ)) := by
        exact Real.log_pos (by nlinarith [hXstarReal])
      positivity
    have hCfinalpos : 0 < Cfinal := by
      dsimp [Cfinal]
      exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hCfinalgeTwo : 2 ≤ Cfinal := by
      exact le_max_left _ _
    refine ⟨Cfinal, hCfinalpos, ?_⟩
    intro X H hX hHlower hHupper P hP
    by_cases hlarge : Xstar ≤ X
    · have hMuNonempty := hData X H P (fun n => (paperMu n : ℂ)) hlarge
        hHlower hHupper hP (Or.inl rfl)
      have hLambdaNonempty := hData X H P
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) hlarge
        hHlower hHupper hP (Or.inr rfl)
      let muData := Classical.choice hMuNonempty
      let lambdaData := Classical.choice hLambdaNonempty
      have hLarge := conditionalIntegerSourceNaturalTwoWeightCorrelation_le
        muData lambdaData
      have hcoef : 2 * (H : ℝ) ≤ Cfinal * (H : ℝ) :=
        mul_le_mul_of_nonneg_right hCfinalgeTwo (Nat.cast_nonneg H)
      calc
        _ ≤ 2 * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := hLarge
        _ ≤ Cfinal * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcoef
            (Real.rpow_nonneg
              (Real.log_nonneg (by
                have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
                linarith)) _)
    · have hXlt : X < Xstar := Nat.lt_of_not_ge hlarge
      have hXstarReal : (3 : ℝ) ≤ (Xstar : ℝ) := by exact_mod_cast hXstarThree
      have hXltReal : (X : ℝ) ≤ (Xstar : ℝ) := by exact_mod_cast hXlt.le
      have hlogXpos : 0 < Real.log (X : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < X by omega))
      have hlogXle : Real.log (X : ℝ) ≤ Real.log (Xstar : ℝ) :=
        Real.log_le_log (by positivity) hXltReal
      have hlogTwoXle : Real.log (2 * (X : ℝ)) ≤
          Real.log (2 * (Xstar : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · nlinarith
      have hlogPowerle :
          (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) ≤
            (Real.log (Xstar : ℝ)) ^ (2 / 5 : ℝ) :=
        Real.rpow_le_rpow hlogXpos.le hlogXle (by norm_num)
      have hbracket :
          1 + Real.log (2 * (X : ℝ)) +
              Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) ≤ Bstar := by
        dsimp [Bstar]
        exact add_le_add
          (add_le_add (le_refl 1) hlogTwoXle)
          (mul_le_mul_of_nonneg_left hlogPowerle (Real.exp_pos 13).le)
      have hlogPowerAle :
          (Real.log (X : ℝ)) ^ A ≤ (Real.log (Xstar : ℝ)) ^ A :=
        Real.rpow_le_rpow hlogXpos.le hlogXle hA.le
      have hlogPowerPos : 0 < (Real.log (X : ℝ)) ^ A :=
        Real.rpow_pos_of_pos hlogXpos A
      have hscaled :
          (1 + Real.log (2 * (X : ℝ)) +
              Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) *
            (Real.log (X : ℝ)) ^ A ≤ Cfinal := by
        calc
          _ ≤ Bstar * (Real.log (X : ℝ)) ^ A :=
            mul_le_mul_of_nonneg_right hbracket (Real.rpow_nonneg hlogXpos.le A)
          _ ≤ Bstar * (Real.log (Xstar : ℝ)) ^ A :=
            mul_le_mul_of_nonneg_left hlogPowerAle hBstarpos.le
          _ = (Real.log (Xstar : ℝ)) ^ A * Bstar := by ring
          _ ≤ Cfinal := by
            dsimp [Cfinal]
            exact le_max_right _ _
      have hHnonneg : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
      have htargetMul :
          (H : ℝ) *
              (1 + Real.log (2 * (X : ℝ)) +
                Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) ≤
            Cfinal * (H : ℝ) / ((Real.log (X : ℝ)) ^ A) := by
        apply (le_div_iff₀ hlogPowerPos).2
        calc
          (H : ℝ) *
              (1 + Real.log (2 * (X : ℝ)) +
                Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) *
              (Real.log (X : ℝ)) ^ A =
            (H : ℝ) *
              ((1 + Real.log (2 * (X : ℝ)) +
                Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) *
                (Real.log (X : ℝ)) ^ A) := by ring
          _ ≤ (H : ℝ) * Cfinal :=
            mul_le_mul_of_nonneg_left hscaled hHnonneg
          _ = Cfinal * (H : ℝ) := by ring
      have hfinite := conditionalIntegerFiniteXNaturalTwoWeightBound
        X H η hX hη hHupper P
      calc
        _ ≤ (H : ℝ) *
            (1 + Real.log (2 * (X : ℝ)) +
              Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)) := hfinite
        _ ≤ Cfinal * (H : ℝ) / ((Real.log (X : ℝ)) ^ A) := htargetMul
        _ = Cfinal * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          rw [Real.rpow_neg hlogXpos.le]
          ring

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerFiniteXNaturalTwoWeightBound
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerUniformityOfScalarTasks
