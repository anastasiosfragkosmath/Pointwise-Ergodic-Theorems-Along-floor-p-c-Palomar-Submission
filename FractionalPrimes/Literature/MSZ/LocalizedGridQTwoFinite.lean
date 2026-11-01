module

public import FractionalPrimes.Literature.MSZ.LocalizedGridQTwoEndpoint

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The finite-support specialization of the direct localized grid endpoint
at `q=2`. The coefficient and vector output are exactly those of the direct
endpoint theorem; only the input representative is specialized to a raw
finite-support sequence. -/
theorem localInterpolation_localizedIncrement_qTwoFiniteEndpoint
    (A : AdmissibleData) (K : ℕ) (j : ℤ) (l : ℕ)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm
        (fun x : ℤ => ‖integerKernelVectorConvolution
          (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
            mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
              A.projections (i.1.1 + j) f y)) x‖)
        (2 : ℝ≥0∞) Measure.count ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l) *
        eLpNorm f (2 : ℝ≥0∞) Measure.count := by
  classical
  have hp20 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp2top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hp2one : 1 ≤ (2 : ℝ≥0∞) := by norm_num
  let F₂ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
    finiteSupportSequenceLpGeneral (p := (2 : ℝ≥0∞))
      hp20 hp2top hp2one hf.toFinset f
  have hF₂point : ∀ x, F₂ x = f x := by
    intro x
    rw [finiteSupportSequenceLpGeneral_apply
      (p := (2 : ℝ≥0∞)) hp20 hp2top hp2one hf.toFinset f x]
    by_cases hx : x ∈ hf.toFinset
    · simp [hx]
    · have hfx : f x = 0 := by
        by_contra hfx
        exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hfx))
      simp [hx, hfx]
  have hF₂seq : (F₂ : ℤ → ℂ) = f := funext hF₂point
  simpa only [hF₂seq] using
    (localInterpolation_localizedIncrement_qTwoEndpoint A K j l F₂)

end

end FractionalPrimes.Literature.MSZ

end
