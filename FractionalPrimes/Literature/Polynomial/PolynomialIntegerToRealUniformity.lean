module

public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerToRealLargeTransfer
public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerToRealSmallTransfer

/-!
# Conditional integer-to-real centre transfer

This assembles both centre ranges in approved blueprint `lc:integer-to-real`
and Astra `literature-expansion/sections/centres.tex`. The integer-centred
estimate remains an explicit premise; its quantifier order and exact Cramér
model are preserved.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Centres

noncomputable section

/-- The exact model-change constant `K_A` from blueprint
`lc:model-difference`. -/
def integerToRealModelChangeConstant (A : ℝ) : ℝ :=
  Real.exp 13 * 2 ^ A *
    (8 * (10 * (A + 2 / 5) / Real.exp 1) ^ (10 * (A + 2 / 5)) +
      4 * (8 * (A + 2 / 5) / (5 * Real.exp 1)) ^ (A + 2 / 5))

/-- The source's full real-centred constant, including the bounded-centre
term `C₀`. -/
def integerToRealUniformityConstant (A ε C_int : ℝ) : ℝ :=
  2 ^ (A + 1) * C_int + integerToRealModelChangeConstant A +
    integerToRealSmallXConstant A ε

/-- Blueprint `lc:integer-to-real`: a conditional estimate at every
integer-centred scale transfers to all real centres with the stated
large-centre, Cramér-model-change, and bounded-centre constants. -/
theorem uniformityRealOfInteger
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
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
        ∀ X H : ℝ,
          3 ≤ X →
          X ^ (5 / 8 + ε) ≤ H →
          H ≤ X ^ (1 - ε) →
            ‖∑ n ∈ FractionalPrimes.realIntegerInterval X H,
                (FractionalPrimes.paperMu n : ℂ) *
                  FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ +
              ‖realCenterLambdaModelPhaseSum P X H‖ ≤
              integerToRealUniformityConstant A ε C_int * H *
                (Real.log X) ^ (-A : ℝ) := by
  obtain ⟨C_int, hC_int, hLargeX⟩ :=
    integerToRealLargeXTransfer k A hA hInteger ε hε hεtop
  have hX₀gt1 : 1 < integerToRealThreshold ε := by
    unfold integerToRealThreshold
    exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hlogX₀pos :
      0 < Real.log (integerToRealThreshold ε) := Real.log_pos hX₀gt1
  have hlog2X₀pos :
      0 < Real.log (2 * integerToRealThreshold ε) :=
    Real.log_pos (by nlinarith [hX₀gt1])
  have hK_nonneg : 0 ≤ integerToRealModelChangeConstant A := by
    unfold integerToRealModelChangeConstant
    positivity
  have hC₀_nonneg : 0 ≤ integerToRealSmallXConstant A ε := by
    unfold integerToRealSmallXConstant
    have hlogpower :
        0 ≤ (Real.log (integerToRealThreshold ε)) ^ (2 / 5 : ℝ) :=
      Real.rpow_nonneg hlogX₀pos.le _
    have hbracket :
        0 ≤ 1 + Real.log (2 * integerToRealThreshold ε) +
          Real.exp 13 * (Real.log (integerToRealThreshold ε)) ^ (2 / 5 : ℝ) :=
      by positivity
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogX₀pos.le _)) hbracket
  refine ⟨C_int, hC_int, ?_⟩
  intro P hP X H hX hHlower hHupper
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by
    have h := Real.rpow_pos_of_pos hXpos (5 / 8 + ε)
    linarith [hHlower]
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hscale_nonneg :
      0 ≤ H * (Real.log X) ^ (-A : ℝ) :=
    mul_nonneg hHpos.le (Real.rpow_nonneg hlogXpos.le _)
  have hbase_nonneg :
      0 ≤ 2 ^ (A + 1) * C_int + integerToRealModelChangeConstant A := by
    apply add_nonneg
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        hC_int.le
    · exact hK_nonneg
  by_cases hLarge : integerToRealThreshold ε ≤ X
  · have hLargeBound := hLargeX X H hLarge hHlower hHupper P hP
    have hLargeBound' :
        ‖∑ n ∈ FractionalPrimes.realIntegerInterval X H,
            (FractionalPrimes.paperMu n : ℂ) *
              FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ +
          ‖realCenterLambdaModelPhaseSum P X H‖ ≤
          (2 ^ (A + 1) * C_int +
            integerToRealModelChangeConstant A) * H *
              (Real.log X) ^ (-A : ℝ) := by
      simpa [integerToRealModelChangeConstant] using hLargeBound
    have hcoeff :
        2 ^ (A + 1) * C_int + integerToRealModelChangeConstant A ≤
          integerToRealUniformityConstant A ε C_int := by
      unfold integerToRealUniformityConstant
      linarith [hC₀_nonneg]
    calc
      _ ≤ (2 ^ (A + 1) * C_int +
            integerToRealModelChangeConstant A) * H *
              (Real.log X) ^ (-A : ℝ) := hLargeBound'
      _ = (2 ^ (A + 1) * C_int +
            integerToRealModelChangeConstant A) *
              (H * (Real.log X) ^ (-A : ℝ)) := by ring
      _ ≤ integerToRealUniformityConstant A ε C_int *
            (H * (Real.log X) ^ (-A : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
      _ = integerToRealUniformityConstant A ε C_int * H *
            (Real.log X) ^ (-A : ℝ) := by ring
  · have hSmall : X < integerToRealThreshold ε := lt_of_not_ge hLarge
    have hSmallBound := integerToRealSmallXTransfer
      k A ε hA hε hεtop X H hX hSmall hHlower hHupper P hP
    have hcoeff :
        integerToRealSmallXConstant A ε ≤
          integerToRealUniformityConstant A ε C_int := by
      unfold integerToRealUniformityConstant
      linarith [hbase_nonneg]
    calc
      _ ≤ integerToRealSmallXConstant A ε * H *
            (Real.log X) ^ (-A : ℝ) := hSmallBound
      _ = integerToRealSmallXConstant A ε *
            (H * (Real.log X) ^ (-A : ℝ)) := by ring
      _ ≤ integerToRealUniformityConstant A ε C_int *
            (H * (Real.log X) ^ (-A : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
      _ = integerToRealUniformityConstant A ε C_int * H *
            (Real.log X) ^ (-A : ℝ) := by ring

#print axioms uniformityRealOfInteger

end

end FractionalPrimes.Literature.Centres

end
