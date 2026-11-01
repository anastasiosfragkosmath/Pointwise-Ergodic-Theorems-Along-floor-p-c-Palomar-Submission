module

public import FractionalPrimes.Literature.MSZ.LocalizedGridSquareBridge
public import FractionalPrimes.Literature.MSZ.LocalizedGridVectorL2Bridge
public import FractionalPrimes.Literature.MSZ.LocalizedGridPositiveMaxBridge
public import FractionalPrimes.Literature.MSZ.LocalizedGridCoefficient
public import FractionalPrimes.Literature.MSZ.FiniteGridBounds

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The strict `1 < q < 2` localized grid estimate, in the scalar norm form
of the finite vector of level-`l` increments. Its coefficient is the exact
specialization of `lm:localInterpolation` to the approved MSZ grid data. -/
theorem mszLocalizedGridEstimate_strict
    (A : AdmissibleData) (hq2 : A.q < 2)
    (K L l : ℕ) (hl : l ≤ L) (j : ℤ)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm
        (fun x : ℤ => ‖integerKernelVectorConvolution
          (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
            mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
              A.projections (i.1.1 + j) f y)) x‖)
        (ENNReal.ofReal A.q) Measure.count ≤
      ENNReal.ofReal
        ((localInterpolationC A.q *
            (max 1 (max (A.P (localInterpolationR A.q))
              (A.P (localInterpolationRPrime A.q))) : ℝ) ^ (2 - A.q) *
            (2 * max 1 A.D) ^ ((2 - A.q) / 2)) *
          (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
          (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
          (A.a j l) ^ (A.q - 1)) *
        eLpNorm f (ENNReal.ofReal A.q) Measure.count ∧
    eLpNorm
        (fun x : ℤ => ‖integerKernelVectorConvolution
          (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
            mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
              A.projections (i.1.1 + j) f y)) x‖)
        (ENNReal.ofReal (localInterpolationQPrime A.q)) Measure.count ≤
      ENNReal.ofReal
        ((localInterpolationC A.q *
            (max 1 (max (A.P (localInterpolationR A.q))
              (A.P (localInterpolationRPrime A.q))) : ℝ) ^ (2 - A.q) *
            (2 * max 1 A.D) ^ ((2 - A.q) / 2)) *
          (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
          (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
          (A.a j l) ^ (A.q - 1)) *
        eLpNorm f (ENNReal.ofReal (localInterpolationQPrime A.q)) Measure.count := by
  classical
  let Kset : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let N : ℕ := 2 ^ l
  let E₀ : ℝ := max 1 A.D * (2 : ℝ) ^ (-(l : ℤ))
  let B : ℝ := 2 * mszFiniteGridMaximalConstant A K L
  let P_r : ℝ := A.P (localInterpolationR A.q)
  let P_r' : ℝ := A.P (localInterpolationRPrime A.q)
  let A_l : ℝ := (2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l
  let Pstar : ℝ := max 1 (max P_r P_r')
  let α : ℝ := (2 - A.q) / 2
  let kernels : {k : ℤ // k ∈ Kset} × Fin N → IntegerL1Kernel := fun i =>
    mszGridIncrementKernel A.kernel i.1.1 l i.2.val
  let interpolationCoefficient : ℝ :=
    localInterpolationC A.q * Pstar ^ (2 - A.q) *
      ((N : ℝ) * E₀ * B) ^ α * A_l ^ (A.q - 1)
  let gridCoefficient : ℝ :=
    (localInterpolationC A.q * Pstar ^ (2 - A.q) *
        (2 * max 1 A.D) ^ α) *
      (mszFiniteGridMaximalConstant A K L) ^ α *
      (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
      (A.a j l) ^ (A.q - 1)
  have hqminus : 0 < A.q - 1 := sub_pos.mpr A.q_gt_one
  have hqplus : 0 < A.q + 1 := by linarith
  have hrOne : 1 < localInterpolationR A.q := by
    dsimp [localInterpolationR]
    rw [lt_div_iff₀ hqplus]
    nlinarith
  have hr'One : 1 < localInterpolationRPrime A.q := by
    dsimp [localInterpolationRPrime]
    rw [lt_div_iff₀ hqminus]
    nlinarith
  have hN : 1 ≤ N := by
    exact pow_pos (by norm_num : 0 < (2 : ℕ)) l
  have hE₀ : 0 ≤ E₀ := by
    dsimp [E₀]
    exact mul_nonneg
      (le_trans (by norm_num) (le_max_left 1 A.D))
      (zpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
  have hB : 0 ≤ B := by
    dsimp [B, mszFiniteGridMaximalConstant]
    positivity
  have hBounds := mszFiniteGridBounds A K L
  have hAtL := hBounds.2.2 l hl
  have hmass : ∀ i, integerKernelL1Mass (kernels i) ≤ E₀ := by
    intro i
    have hi : (i.1.1, i.2) ∈ mszFiniteGridIncrementIndices K l := by
      simpa [mszFiniteGridIncrementIndices] using
        (Finset.mk_mem_product i.1.2 (Finset.mem_univ i.2))
    simpa [E₀, kernels] using hAtL.1 (i.1.1, i.2) hi
  have hmax : ∀ (H : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal A.q)),
      (hh : ∀ x, 0 ≤ H x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal A.q),
        (∀ x, M x = integerKernelPositiveConvolutionMax kernels H hh x) ∧
          ‖M‖ ≤ B * ‖H‖ := by
    intro H hh
    rcases hAtL.2 H hh with ⟨_hPointwise, G, hG, hGnorm⟩
    refine ⟨G, ?_, ?_⟩
    · intro x
      calc
        G x = mszFiniteGridIncrementPositiveMajorant A K L l H x := hG x
        _ = integerKernelPositiveConvolutionMax kernels H hh x := by
          exact congrArg (fun g : ℤ → ℝ => g x)
            (by
              simpa [kernels, mszQExponent] using
                mszFiniteGridIncrementPositiveMajorant_eq_positiveConvolutionMax
                  A K L l H hh)
    · change ‖G‖ ≤ 2 * mszFiniteGridMaximalConstant A K L * ‖H‖
      exact hGnorm
  have hSqR : ∀ F : lp (fun _ : ℤ => ℂ)
      (ENNReal.ofReal (localInterpolationR A.q)),
      ∃ G : lp (fun _ : ℤ => ℝ)
          (ENNReal.ofReal (localInterpolationR A.q)),
        (∀ x, 0 ≤ G x) ∧
        (∀ x, ENNReal.ofReal (G x) =
          localInterpolationExtendedSquareFunction
            (fun x h => A.projections h (F : ℤ → ℂ) x) x) ∧
        ‖G‖ ≤ P_r * ‖F‖ := by
    simpa [P_r] using
      (localInterpolation_realSquareWitness_to_extended
        (p := localInterpolationR A.q) (P := A.P (localInterpolationR A.q))
        A.projections
        (fun F x => A.square_function_summable
          (localInterpolationR A.q) hrOne F x)
        (fun F => A.square_function_bound
          (localInterpolationR A.q) hrOne F))
  have hSqR' : ∀ F : lp (fun _ : ℤ => ℂ)
      (ENNReal.ofReal (localInterpolationRPrime A.q)),
      ∃ G : lp (fun _ : ℤ => ℝ)
          (ENNReal.ofReal (localInterpolationRPrime A.q)),
        (∀ x, 0 ≤ G x) ∧
        (∀ x, ENNReal.ofReal (G x) =
          localInterpolationExtendedSquareFunction
            (fun x h => A.projections h (F : ℤ → ℂ) x) x) ∧
        ‖G‖ ≤ P_r' * ‖F‖ := by
    simpa [P_r'] using
      (localInterpolation_realSquareWitness_to_extended
        (p := localInterpolationRPrime A.q)
        (P := A.P (localInterpolationRPrime A.q))
        A.projections
        (fun F x => A.square_function_summable
          (localInterpolationRPrime A.q) hr'One F x)
        (fun F => A.square_function_bound
          (localInterpolationRPrime A.q) hr'One F))
  have hDirect : ∀ F : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞),
      ∃ U : lp
          (fun _ : ℤ => PiLp 2 (fun _ : {k : ℤ // k ∈ Kset} × Fin N => ℂ))
          (2 : ℝ≥0∞),
        (∀ x, U x = integerKernelVectorConvolution kernels
          (fun y => WithLp.toLp 2
            (fun i : {k : ℤ // k ∈ Kset} × Fin N =>
              A.projections (i.1.1 + j) (F : ℤ → ℂ) y)) x) ∧
        ‖U‖ ≤ A_l * ‖F‖ := by
    intro F
    obtain ⟨U, hU, hUnorm⟩ :=
      localInterpolation_localizedIncrement_l2VectorWitness A K j l F
    refine ⟨U, ?_, ?_⟩
    · intro x
      simpa [kernels, Kset, N] using hU x
    · simpa [A_l] using hUnorm
  have hInterpolation :=
    localizedInterpolation (q := A.q) (E₀ := E₀) (B := B)
      (P_r := P_r) (P_r' := P_r') (A := A_l)
      A.q_gt_one hq2 N hN Kset j kernels A.projections
      hE₀ hB hmass hmax hSqR hSqR' hDirect f hf
  have hCoefficient : interpolationCoefficient = gridCoefficient := by
    dsimp [interpolationCoefficient, gridCoefficient]
    simpa [N, E₀, B, A_l, P_r, P_r', Pstar, α] using
      mszLocalizedGridCoefficient_eq A K L l j
  have hqInterpolation :
      eLpNorm
          (fun x : ℤ => ‖integerKernelVectorConvolution kernels
            (fun y => WithLp.toLp 2
              (fun i : {k : ℤ // k ∈ Kset} × Fin N =>
                A.projections (i.1.1 + j) f y)) x‖)
          (ENNReal.ofReal A.q) Measure.count ≤
        ENNReal.ofReal interpolationCoefficient *
          eLpNorm f (ENNReal.ofReal A.q) Measure.count := by
    simpa [interpolationCoefficient, Pstar, P_r, P_r', α] using
      hInterpolation.1
  have hq'Interpolation :
      eLpNorm
          (fun x : ℤ => ‖integerKernelVectorConvolution kernels
            (fun y => WithLp.toLp 2
              (fun i : {k : ℤ // k ∈ Kset} × Fin N =>
                A.projections (i.1.1 + j) f y)) x‖)
          (ENNReal.ofReal (localInterpolationQPrime A.q)) Measure.count ≤
        ENNReal.ofReal interpolationCoefficient *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime A.q)) Measure.count := by
    simpa [interpolationCoefficient, Pstar, P_r, P_r', α] using
      hInterpolation.2
  constructor
  · calc
      _ ≤ ENNReal.ofReal interpolationCoefficient *
          eLpNorm f (ENNReal.ofReal A.q) Measure.count := by
        simpa [kernels, Kset, N] using hqInterpolation
      _ = ENNReal.ofReal gridCoefficient *
          eLpNorm f (ENNReal.ofReal A.q) Measure.count := by
        rw [hCoefficient]
  · calc
      _ ≤ ENNReal.ofReal interpolationCoefficient *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime A.q)) Measure.count := by
        simpa [kernels, Kset, N] using hq'Interpolation
      _ = ENNReal.ofReal gridCoefficient *
          eLpNorm f (ENNReal.ofReal (localInterpolationQPrime A.q)) Measure.count := by
        rw [hCoefficient]

end

end FractionalPrimes.Literature.MSZ

end
