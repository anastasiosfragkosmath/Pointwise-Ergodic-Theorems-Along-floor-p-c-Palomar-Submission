module

public import FractionalPrimes.Literature.MSZ.LocalizedGridVectorL2Bridge
public import FractionalPrimes.Literature.MSZ.LocalizedInterpolation

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The direct localized grid endpoint at `q=2`, obtained from the actual
finite vector `lp²` output witness. The input is an arbitrary sequence `lp²`
representative, so finite-support inputs are included by their canonical
`lp²` representatives. -/
theorem localInterpolation_localizedIncrement_qTwoEndpoint
    (A : AdmissibleData) (K : ℕ) (j : ℤ) (l : ℕ)
    (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) :
    eLpNorm
        (fun x : ℤ => ‖integerKernelVectorConvolution
          (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
            mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
              A.projections (i.1.1 + j) (f : ℤ → ℂ) y)) x‖)
        (2 : ℝ≥0∞) Measure.count ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l) *
        eLpNorm (fun x : ℤ => (f : ℤ → ℂ) x)
          (2 : ℝ≥0∞) Measure.count := by
  classical
  let C : ℝ := (2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l
  let V : ℤ → PiLp 2
      (fun _ : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) => ℂ) :=
    fun x => integerKernelVectorConvolution
      (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
        mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
      (fun y => WithLp.toLp 2
        (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
          A.projections (i.1.1 + j) (f : ℤ → ℂ) y)) x
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (A.a_nonneg j l)
  obtain ⟨U, hU, hUnorm⟩ :=
    localInterpolation_localizedIncrement_l2VectorWitness A K j l f
  have hUfun : (fun x : ℤ => ‖U x‖) = fun x => ‖V x‖ := by
    funext x
    dsimp [V]
    rw [hU x]
  have hCore := localInterpolation_qTwo_directEndpoint C hC U f (by
    simpa [C] using hUnorm)
  simpa only [hUfun, C] using hCore

end

end FractionalPrimes.Literature.MSZ

end
