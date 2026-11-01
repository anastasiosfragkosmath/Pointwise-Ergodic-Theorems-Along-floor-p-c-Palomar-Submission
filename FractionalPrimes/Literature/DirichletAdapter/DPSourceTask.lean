module
public import FractionalPrimes.Literature.DirichletAdapter.DPRetainedAggregateEnvelope
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceWindowThreshold
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalDirichletTaskContract
@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
noncomputable section

/-- The exact scalar Dirichlet task from the source's smooth
Heath--Brown decomposition and its checked Type-I/IImaj bounds. -/
theorem shortIntervalDirichletTask_of_sourceComponents :
    shortIntervalDirichletTask := by
  intro A B η hA hB hη hη₃
  let D₀ : ℝ := 128 * dpSourceBudgetS A B
  have hpNat : 100 ≤ dpSourceBudgetP := by
    unfold dpSourceBudgetP
    omega
  have hpReal : (100 : ℝ) ≤ (dpSourceBudgetP : ℝ) := by
    exact_mod_cast hpNat
  have hSone : 1 ≤ dpSourceBudgetS A B := by
    unfold dpSourceBudgetS
    nlinarith [hA, hB, hpReal]
  have hD₀one : 1 ≤ D₀ := by
    dsimp [D₀]
    nlinarith [hSone]
  refine ⟨D₀, hD₀one, ?_⟩
  intro D hD
  have hDsource : 128 * dpSourceBudgetS A B ≤ D := by
    simpa only [D₀] using hD
  obtain ⟨j, _, hj, hκpos, hκD, hκabs, hDabs, hDtail, hjη⟩ :=
    dpSourceParameterBudget hA hB hη hη₃ hDsource
  let κ : ℝ := dpSourceBudgetKappa A B
  obtain ⟨Xagg, hXagg, hAgg⟩ :=
    smoothHeathBrownDPSourceRetained_aggregateEnvelope
      hB hκpos hκD hη hη₃ hA hκabs hDabs
  let X_D : ℝ := max Xagg (dpSourceWindowThreshold A η D)
  let C₀ : ℝ := 10 * (8 : ℝ) ^ 20 *
      (2 * dpSourceTypeIConstant j +
        (2 : ℝ) ^ 12 * dpSourceIImajConstant)
  let C_D : ℝ := C₀ + 1
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    have hI := dpSourceTypeIConstant_nonneg j
    have hII := dpSourceIImajConstant_nonneg
    positivity
  have hC_D : 0 < C_D := by dsimp [C_D]; linarith
  have hX_D : 3 ≤ X_D := hXagg.trans (le_max_left _ _)
  refine ⟨C_D, X_D, hC_D, hX_D, ?_⟩
  intro hXD X H hDX hHlower hHupper
  let W : ℝ := (Real.log (X : ℝ)) ^ D
  let T₀ : ℝ := (X : ℝ) / (H : ℝ)
  have hwindowX : dpSourceWindowThreshold A η D ≤ (X : ℝ) :=
    (le_max_right _ _).trans hDX
  have haggX : Xagg ≤ (X : ℝ) := (le_max_left _ _).trans hDX
  rcases dpSourceWindowThreshold_source_conditions
      hA hB hη hη₃ hDsource hwindowX hHlower hHupper with
    ⟨hX3, hlog, hAbs, hWtwo, hW100, _, hWT₀⟩
  have hX35 : (2 : ℝ) ^ 35 ≤ (X : ℝ) := by
    have hbase : dpSourceLogThreshold A ≤ (X : ℝ) :=
      (le_max_left _ _).trans hwindowX
    exact ((dpSourceLogThreshold_spec A).2 (X : ℝ) hbase).1
  have hXpos : 0 < (X : ℝ) := by linarith
  have hHpos : 0 < (H : ℝ) := by
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hHlower
  have hHX : (H : ℝ) ≤ (X : ℝ) := by
    have hXone : 1 ≤ (X : ℝ) := by linarith
    have hpow : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith : 1 - η ≤ 1)
    exact hHupper.trans hpow
  have hqpos (q : ℕ) (hq : 1 ≤ q) : 0 < q := by omega
  have hfactor : 0 ≤ Real.sqrt (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-A) := by positivity
  have hCcomp : C₀ ≤ C_D := by dsimp [C_D]; linarith
  have hCscale : C₀ * Real.sqrt (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-A) ≤
      C_D * Real.sqrt (X : ℝ) *
      (Real.log (X : ℝ)) ^ (-A) := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hCcomp hfactor
  refine ⟨?_, ?_⟩
  · exact ⟨hWtwo, hW100, hWT₀⟩
  · intro q hq hqQ a f hf
    have hAggBounds := hAgg haggX hX35 hlog hAbs hHpos hHX hHlower
      rfl hWtwo hWT₀ q hq hqQ a j hj hDtail hjη
      polynomialKernelRho hX3 (hqpos q hq)
    rcases hf with rfl | rfl
    · exact hAggBounds.2.trans hCscale
    · exact hAggBounds.1.trans hCscale

#print axioms shortIntervalDirichletTask_of_sourceComponents
end
end FractionalPrimes.Literature.DirichletAdapter
