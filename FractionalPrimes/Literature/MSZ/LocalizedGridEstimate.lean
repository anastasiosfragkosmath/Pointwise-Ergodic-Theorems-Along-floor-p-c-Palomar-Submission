module

public import FractionalPrimes.Literature.MSZ.LocalizedGridStrictEndpoint
public import FractionalPrimes.Literature.MSZ.LocalizedGridQTwoFinite
public import FractionalPrimes.Literature.MSZ.LocalizedGridSquareIdentity

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The localized interpolation factor `K_q` from `lm:localizedGrid`.
At the endpoint `q=2` it has the source value `1`. -/
noncomputable def mszLocalizedGridKq (A : AdmissibleData) : ℝ :=
  if A.q < 2 then
    localInterpolationC A.q *
      (max 1 (max (A.P (localInterpolationR A.q))
        (A.P (localInterpolationRPrime A.q))) : ℝ) ^ (2 - A.q) *
      (2 * max 1 A.D) ^ ((2 - A.q) / 2)
  else 1

/-- The approved localized grid estimate `lm:localizedGrid`, with
the output written as the literal finite square sum over `-K ≤ k ≤ K` and
`m : Fin (2^l)`. The two exponents are `q` and `q/(q-1)`, and the coefficient
uses the source convention `K₂ = 1`. -/
theorem localizedGridEstimate
    (A : AdmissibleData) (K L l : ℕ) (hl : l ≤ L) (j : ℤ)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm
        (fun x : ℤ => Real.sqrt
          (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            ∑ m : Fin (2 ^ l),
              ‖mszGridIncrement A.kernel k l m.val
                (A.projections (j + k) f) x‖ ^ 2))
        (ENNReal.ofReal A.q) Measure.count ≤
      ENNReal.ofReal
          (mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
            (A.a j l) ^ (A.q - 1)) *
        eLpNorm f (ENNReal.ofReal A.q) Measure.count ∧
    eLpNorm
        (fun x : ℤ => Real.sqrt
          (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            ∑ m : Fin (2 ^ l),
              ‖mszGridIncrement A.kernel k l m.val
                (A.projections (j + k) f) x‖ ^ 2))
        (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count ≤
      ENNReal.ofReal
          (mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
            (A.a j l) ^ (A.q - 1)) *
        eLpNorm f (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count := by
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
  let gridSquare : ℤ → ℝ := fun x => Real.sqrt
    (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∑ m : Fin (2 ^ l),
        ‖mszGridIncrement A.kernel k l m.val
          (A.projections (j + k) f) x‖ ^ 2)
  have hSquareFun : gridSquare = fun x : ℤ =>
      ‖integerKernelVectorConvolution
        (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
          mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
        (fun y => WithLp.toLp 2
          (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
            A.projections (i.1.1 + j) f y)) x‖ := by
    funext x
    dsimp [gridSquare]
    simpa only [hF₂seq] using
      (mszLocalizedGridVector_norm_eq_finiteSquare A K j l F₂ x).symm
  change eLpNorm gridSquare (ENNReal.ofReal A.q) Measure.count ≤ _ ∧
    eLpNorm gridSquare (ENNReal.ofReal (A.q / (A.q - 1)))
      Measure.count ≤ _
  rcases lt_or_eq_of_le A.q_le_two with hq2 | hqEq
  · have hStrict :=
      mszLocalizedGridEstimate_strict A hq2 K L l hl j f hf
    constructor
    · calc
        eLpNorm gridSquare (ENNReal.ofReal A.q) Measure.count =
            eLpNorm
              (fun x : ℤ => ‖integerKernelVectorConvolution
                (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                    Fin (2 ^ l) =>
                  mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
                (fun y => WithLp.toLp 2
                  (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                      Fin (2 ^ l) =>
                    A.projections (i.1.1 + j) f y)) x‖)
              (ENNReal.ofReal A.q) Measure.count :=
          congrArg
            (fun g : ℤ → ℝ => eLpNorm g (ENNReal.ofReal A.q) Measure.count)
            hSquareFun
        _ ≤ _ := by
          simpa [mszLocalizedGridKq, hq2] using hStrict.1
    · calc
        eLpNorm gridSquare
            (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count =
            eLpNorm
              (fun x : ℤ => ‖integerKernelVectorConvolution
                (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                    Fin (2 ^ l) =>
                  mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
                (fun y => WithLp.toLp 2
                  (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                      Fin (2 ^ l) =>
                    A.projections (i.1.1 + j) f y)) x‖)
              (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count :=
          congrArg
            (fun g : ℤ → ℝ =>
              eLpNorm g (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count)
            hSquareFun
        _ ≤ _ := by
          simpa [localInterpolationQPrime, mszLocalizedGridKq, hq2] using
            hStrict.2
  · have hP₂ : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
    have hqExponent : ENNReal.ofReal A.q = (2 : ℝ≥0∞) := by
      rw [hqEq, hP₂]
    have hqPrime : A.q / (A.q - 1) = 2 := by
      rw [hqEq]
      norm_num
    have hqPrimeExponent :
        ENNReal.ofReal (A.q / (A.q - 1)) = (2 : ℝ≥0∞) := by
      rw [hqPrime, hP₂]
    have hTwo :=
      localInterpolation_localizedIncrement_qTwoFiniteEndpoint A K j l f hf
    have hCoefficient :
        mszLocalizedGridKq A *
          (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
          (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
          (A.a j l) ^ (A.q - 1) =
        (2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l := by
      norm_num [mszLocalizedGridKq, hqEq]
    constructor
    · calc
        eLpNorm gridSquare (ENNReal.ofReal A.q) Measure.count =
            eLpNorm
              (fun x : ℤ => ‖integerKernelVectorConvolution
                (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                    Fin (2 ^ l) =>
                  mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
                (fun y => WithLp.toLp 2
                  (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                      Fin (2 ^ l) =>
                    A.projections (i.1.1 + j) f y)) x‖)
              (ENNReal.ofReal A.q) Measure.count :=
          congrArg
            (fun g : ℤ → ℝ => eLpNorm g (ENNReal.ofReal A.q) Measure.count)
            hSquareFun
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l) *
            eLpNorm f (ENNReal.ofReal A.q) Measure.count := by
          simpa only [hqExponent] using hTwo
        _ = _ := by rw [← hCoefficient]
    · calc
        eLpNorm gridSquare
            (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count =
            eLpNorm
              (fun x : ℤ => ‖integerKernelVectorConvolution
                (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                    Fin (2 ^ l) =>
                  mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
                (fun y => WithLp.toLp 2
                  (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
                      Fin (2 ^ l) =>
                    A.projections (i.1.1 + j) f y)) x‖)
              (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count :=
          congrArg
            (fun g : ℤ → ℝ =>
              eLpNorm g (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count)
            hSquareFun
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l) *
            eLpNorm f (ENNReal.ofReal (A.q / (A.q - 1))) Measure.count := by
          simpa only [hqPrimeExponent] using hTwo
        _ = _ := by rw [← hCoefficient]

end

end FractionalPrimes.Literature.MSZ

end
