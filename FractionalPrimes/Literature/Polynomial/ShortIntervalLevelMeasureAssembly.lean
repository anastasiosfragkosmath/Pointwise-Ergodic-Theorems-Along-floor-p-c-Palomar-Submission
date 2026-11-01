module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalLevelMeasure

/-! Assembly of the two exact conclusions in `lgv:level-measure` from its
separated-family input. The separated finite bound is an explicit argument so
this file remains independent of the worker proving `lgv:separated`.

Blueprint: `expanded-blueprint.tex:5598-5621`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex`.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.LargeValues

noncomputable section

/-- The exact `lgv:level-measure` pair of bounds, conditional only on the
finite separated-family estimate proved at `lgv:separated`. -/
theorem levelSetMeasureBound_fromFiniteSeparatedBound
    (N T V : ℝ) (a : ℕ → ℂ) (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (hseparatedBound : ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ j, t j ∈ dirichletLevelSet N T V a) →
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (R : ℝ) ≤ 2 ^ 24 * Real.log (4 * N * T) *
        (N * dirichletEnergy N a / V ^ 2 +
          T * N * (dirichletEnergy N a) ^ 3 / V ^ 6)) :
    MeasurableSet (dirichletLevelSet N T V a) ∧
      volume.real (dirichletLevelSet N T V a) ≤
        2 ^ 25 * Real.log (4 * N * T) *
          (N * dirichletEnergy N a / V ^ 2 +
            T * N * (dirichletEnergy N a) ^ 3 / V ^ 6) ∧
      volume.real (dirichletLevelSet N T V a) ≤
        (2 * T + 8 * N * (1 + Real.log (2 * N))) *
          dirichletEnergy N a / V ^ 2 := by
  let B := 2 ^ 24 * Real.log (4 * N * T) *
    (N * dirichletEnergy N a / V ^ 2 +
      T * N * (dirichletEnergy N a) ^ 3 / V ^ 6)
  have hmeas := dirichletLevelSet_measurable N T V a
  have hseparatedCover :=
    dirichletLevelSetMeasureBound_of_separated N T V B a hseparatedBound
  have hmeanSquare := dirichletLevelSetMeasureBound_meanSquare N T V a hN hT hV
  refine ⟨hmeas, ?_, hmeanSquare⟩
  calc
    volume.real (dirichletLevelSet N T V a) ≤ 2 * B := hseparatedCover
    _ = 2 ^ 25 * Real.log (4 * N * T) *
          (N * dirichletEnergy N a / V ^ 2 +
            T * N * (dirichletEnergy N a) ^ 3 / V ^ 6) := by
      dsimp [B]
      ring

end

end FractionalPrimes.Literature.LargeValues

end

#print axioms FractionalPrimes.Literature.LargeValues.levelSetMeasureBound_fromFiniteSeparatedBound
