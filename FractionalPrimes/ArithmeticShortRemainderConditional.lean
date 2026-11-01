module
public import FractionalPrimes.Literature.Polynomial.PolynomialFullResidueSourceAssembly
public import FractionalPrimes.PolynomialFloorReduction
public import FractionalPrimes.ShortRemainderBlockSummation
public import FractionalPrimes.CramerBlockCorrelation
@[expose] public section

/-! The first arithmetic consequence of the conditional polynomial
uniformity package: on an integer-centred full block, uniform polynomial
phase cancellation bounds the normalized polynomial-correlation seminorm
for both source weights. The full fractional floor-phase assembly follows
in this module. -/

namespace FractionalPrimes

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Centres
open FractionalPrimes.Literature.Uniformity
open Polynomial
open scoped BigOperators

theorem polynomialCorrelationMobius_le_of_uniformity
    (k : ℕ) (A ε C : ℝ)
    (hUniformity : ∀ P : Polynomial ℝ, P.natDegree ≤ k →
      ∀ X H : ℝ, 3 ≤ X → X ^ (5 / 8 + ε) ≤ H →
        H ≤ X ^ (1 - ε) →
          ‖∑ n ∈ realIntegerInterval X H,
              (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖realCenterLambdaModelPhaseSum P X H‖ ≤
            C * H * (Real.log X) ^ (-A : ℝ))
    {X H : ℕ} (hX : 3 ≤ X)
    (hLower : (X : ℝ) ^ (5 / 8 + ε) ≤ (H : ℝ))
    (hUpper : (H : ℝ) ≤ (X : ℝ) ^ (1 - ε)) :
    polynomialCorrelation (k + 1) (realIntegerInterval (X : ℝ) (H : ℝ))
        (fun n => (paperMu n : ℂ)) ≤ C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  classical
  let I : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  have hHpos : 0 < H := by
    by_contra h
    have hHzero : H = 0 := by omega
    subst H
    have hXpos : 0 < (X : ℝ) := by positivity
    have hpow : 0 < (X : ℝ) ^ (5 / 8 + ε) := Real.rpow_pos_of_pos hXpos _
    norm_num at hLower
    linarith
  have hI : I.Nonempty := by
    have hcard : I.card = H := by
      simpa [I] using realIntegerInterval_nat_card X H
    have hHnat : 0 < H := hHpos
    have : 0 < I.card := by omega
    exact Finset.card_pos.mp this
  have hcard : (I.card : ℝ) = (H : ℝ) := by
    exact_mod_cast (realIntegerInterval_nat_card X H)
  have hHposR : 0 < (H : ℝ) := by exact_mod_cast hHpos
  unfold polynomialCorrelation
  apply csSup_le
  · refine ⟨‖(∑ n ∈ I, (paperMu n : ℂ) *
        unitFrequencyPhase (-(0 : Polynomial ℝ).eval (n : ℝ))) /
          (I.card : ℂ)‖, ?_⟩
    exact ⟨⟨0, by simp⟩, rfl⟩
  · intro z hz
    rcases hz with ⟨P, rfl⟩
    let Q : Polynomial ℝ := -P.1
    have hQ : Q.natDegree ≤ k := by
      dsimp [Q]
      simpa using P.2
    have hbound := hUniformity Q hQ (X : ℝ) (H : ℝ)
      (by exact_mod_cast hX) hLower hUpper
    have hterm :
        ‖∑ n ∈ I, (paperMu n : ℂ) *
            unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ ≤
          C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      have hmu := le_trans (le_add_of_nonneg_right (norm_nonneg
        (realCenterLambdaModelPhaseSum Q (X : ℝ) (H : ℝ)))) hbound
      have hphase :
          (∑ n ∈ I, (paperMu n : ℂ) *
            unitFrequencyPhase (-(P.1.eval (n : ℝ)))) =
          ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
            (paperMu n : ℂ) * unitFrequencyPhase (Q.eval (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [Q, Polynomial.eval_neg]
      rw [hphase]
      exact hmu
    have hden : 0 < (I.card : ℝ) := by
      rw [hcard]
      exact hHposR
    have hquot :
        ‖(∑ n ∈ I, (paperMu n : ℂ) *
            unitFrequencyPhase (-(P.1.eval (n : ℝ)))) /
            (I.card : ℂ)‖ ≤ C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      calc
        _ = ‖∑ n ∈ I, (paperMu n : ℂ) *
              unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ /
                (I.card : ℝ) := by
          rw [norm_div]
          simp
        _ ≤
            (C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ)) /
              (I.card : ℝ) := div_le_div_of_nonneg_right hterm hden.le
        _ = C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          rw [hcard]
          field_simp
    simpa [I] using hquot

/-- The corresponding seminorm bound for the location-dependent
von-Mangoldt-minus-Cramér weight. -/
theorem polynomialCorrelationLambdaModel_le_of_uniformity
    (k : ℕ) (A ε C : ℝ)
    (hUniformity : ∀ P : Polynomial ℝ, P.natDegree ≤ k →
      ∀ X H : ℝ, 3 ≤ X → X ^ (5 / 8 + ε) ≤ H →
        H ≤ X ^ (1 - ε) →
          ‖∑ n ∈ realIntegerInterval X H,
              (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖realCenterLambdaModelPhaseSum P X H‖ ≤
            C * H * (Real.log X) ^ (-A : ℝ))
    {X H : ℕ} (hX : 3 ≤ X)
    (hLower : (X : ℝ) ^ (5 / 8 + ε) ≤ (H : ℝ))
    (hUpper : (H : ℝ) ≤ (X : ℝ) ^ (1 - ε)) :
    polynomialCorrelation (k + 1) (realIntegerInterval (X : ℝ) (H : ℝ))
        (fun n => ((paperLambda n -
          paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)) ≤
      C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  classical
  let I : Finset ℤ := realIntegerInterval (X : ℝ) (H : ℝ)
  have hHpos : 0 < H := by
    by_contra h
    have hHzero : H = 0 := by omega
    subst H
    have hXpos : 0 < (X : ℝ) := by positivity
    have hpow : 0 < (X : ℝ) ^ (5 / 8 + ε) := Real.rpow_pos_of_pos hXpos _
    norm_num at hLower
    linarith
  have hI : I.Nonempty := by
    have hcard : I.card = H := by
      simpa [I] using realIntegerInterval_nat_card X H
    have : 0 < I.card := by omega
    exact Finset.card_pos.mp this
  have hcard : (I.card : ℝ) = (H : ℝ) := by
    exact_mod_cast (realIntegerInterval_nat_card X H)
  have hHposR : 0 < (H : ℝ) := by exact_mod_cast hHpos
  unfold polynomialCorrelation
  apply csSup_le
  · refine ⟨‖(∑ n ∈ I,
        ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
          unitFrequencyPhase (-(0 : Polynomial ℝ).eval (n : ℝ))) /
          (I.card : ℂ)‖, ?_⟩
    exact ⟨⟨0, by simp⟩, rfl⟩
  · intro z hz
    rcases hz with ⟨P, rfl⟩
    let Q : Polynomial ℝ := -P.1
    have hQ : Q.natDegree ≤ k := by
      dsimp [Q]
      simpa using P.2
    have hbound := hUniformity Q hQ (X : ℝ) (H : ℝ)
      (by exact_mod_cast hX) hLower hUpper
    have hphase :
        (∑ n ∈ I,
          ((paperLambda n -
            paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
            unitFrequencyPhase (-(P.1.eval (n : ℝ)))) =
        realCenterLambdaModelPhaseSum Q (X : ℝ) (H : ℝ) := by
      simp [I, realCenterLambdaModelPhaseSum, Q,
        paperShortBlockCramerWeight, Polynomial.eval_neg]
    have hterm :
        ‖∑ n ∈ I,
          ((paperLambda n -
            paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
            unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ ≤
          C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      rw [hphase]
      have hmuNonneg : 0 ≤
          ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
            (paperMu n : ℂ) * unitFrequencyPhase (Q.eval (n : ℝ))‖ := by positivity
      linarith
    have hden : 0 < (I.card : ℝ) := by
      rw [hcard]
      exact hHposR
    have hquot :
        ‖(∑ n ∈ I,
          ((paperLambda n -
            paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
            unitFrequencyPhase (-(P.1.eval (n : ℝ)))) /
            (I.card : ℂ)‖ ≤ C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
      calc
        _ = ‖∑ n ∈ I,
              ((paperLambda n -
                paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
                unitFrequencyPhase (-(P.1.eval (n : ℝ)))‖ /
                  (I.card : ℝ) := by
          rw [norm_div]
          simp
        _ ≤
            (C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ)) /
              (I.card : ℝ) := div_le_div_of_nonneg_right hterm hden.le
        _ = C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          rw [hcard]
          field_simp
    simpa [I] using hquot

/-- Conditional source-package version of the preceding block estimates.
The only arithmetic premises are precisely MUF, the scalar Dirichlet task,
and the selected/restricted PTW task. -/
theorem shortBlockPolynomialCorrelationsOf_MUF_DP_PTW
    {c : ℝ} (hc : 1 < c)
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    (hDP : FractionalPrimes.Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : FractionalPrimes.Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X H : ℕ, 3 ≤ X →
        (X : ℝ) ^ (5 / 8 + (arithmeticParameters c).ε) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - (arithmeticParameters c).ε) →
          polynomialCorrelation ((arithmeticParameters c).k + 1)
            (realIntegerInterval (X : ℝ) (H : ℝ))
            (fun n => (paperMu n : ℂ)) ≤
              C * (Real.log (X : ℝ)) ^ (-A : ℝ) ∧
          polynomialCorrelation ((arithmeticParameters c).k + 1)
            (realIntegerInterval (X : ℝ) (H : ℝ))
            (fun n => ((paperLambda n -
              paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)) ≤
              C * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  let p := arithmeticParameters c
  have hη := arithmeticParameters_eta_pos_lt_one hc
  have hθeq : p.θ = 1 - p.η / 16 := by
    dsimp [p, arithmeticParameters]
    ring
  have hεeq : p.ε = p.η / 64 := by
    change (1 - p.θ) / 4 = p.η / 64
    rw [hθeq]
    ring
  have hε : 0 < p.ε := by rw [hεeq]; linarith [hη.1]
  have hεtop : p.ε < 3 / 16 := by
    rw [hεeq]
    nlinarith [hη.2]
  obtain ⟨Cint, hCint, hUniformity⟩ :=
    FractionalPrimes.Literature.Polynomial.conditionalRealUniformityOf_MUF_DP_PTW
      hMUF hDP hPTW p.k A p.ε hA hε hεtop
  let C : ℝ := integerToRealUniformityConstant A p.ε Cint
  have hC : 0 < C := by
    have hX₀gt1 : 1 < integerToRealThreshold p.ε := by
      unfold integerToRealThreshold
      exact Real.one_lt_rpow (by norm_num) (by positivity)
    have hlogX₀pos : 0 < Real.log (integerToRealThreshold p.ε) :=
      Real.log_pos hX₀gt1
    have hlog2X₀pos : 0 < Real.log (2 * integerToRealThreshold p.ε) :=
      Real.log_pos (by nlinarith [hX₀gt1])
    have hKnonneg : 0 ≤ integerToRealModelChangeConstant A := by
      unfold integerToRealModelChangeConstant
      positivity
    have hC₀nonneg : 0 ≤ integerToRealSmallXConstant A p.ε := by
      unfold integerToRealSmallXConstant
      have hlogpower :
          0 ≤ (Real.log (integerToRealThreshold p.ε)) ^ (2 / 5 : ℝ) :=
        Real.rpow_nonneg hlogX₀pos.le _
      have hbracket :
          0 ≤ 1 + Real.log (2 * integerToRealThreshold p.ε) +
            Real.exp 13 * (Real.log (integerToRealThreshold p.ε)) ^
              (2 / 5 : ℝ) := by positivity
      exact mul_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogX₀pos.le _)) hbracket
    dsimp [C, integerToRealUniformityConstant]
    positivity
  refine ⟨C, hC, ?_⟩
  intro X H hX hLower hUpper
  have hMu := polynomialCorrelationMobius_le_of_uniformity
    p.k A p.ε C hUniformity hX hLower hUpper
  have hLambda := polynomialCorrelationLambdaModel_le_of_uniformity
    p.k A p.ε C hUniformity hX hLower hUpper
  exact ⟨hMu, hLambda⟩

end FractionalPrimes

#print axioms FractionalPrimes.polynomialCorrelationMobius_le_of_uniformity
#print axioms FractionalPrimes.polynomialCorrelationLambdaModel_le_of_uniformity
#print axioms FractionalPrimes.shortBlockPolynomialCorrelationsOf_MUF_DP_PTW

