module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteCoordinateFatou

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

/-! Finite-vector Minkowski for the square function used in
`lm:finiteVariationEstimate`. It converts the individual shifted-grid bounds
into the uniform finite-J bound consumed by the finite-coordinate Fatou
adapter. -/

/-- The `eLpNorm` of the finite Euclidean norm of a sum is bounded by the sum
of the individual finite Euclidean `eLpNorm`s, for `p ≥ 1`. -/
theorem msz_counting_eLpNorm_finiteSquare_sum_le
    {ι σ : Type*} [Fintype ι] [DecidableEq σ] {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (s : Finset σ)
    (terms : σ → ℤ → ι → ℂ) (C : σ → ℝ≥0∞)
    (hbound : ∀ j ∈ s,
      eLpNorm
        (fun x : ℤ => Real.sqrt (∑ i : ι, ‖terms j x i‖ ^ 2))
        p (Measure.count : Measure ℤ) ≤ C j) :
    eLpNorm
      (fun x : ℤ => Real.sqrt
        (∑ i : ι, ‖∑ j ∈ s, terms j x i‖ ^ 2))
      p (Measure.count : Measure ℤ) ≤ ∑ j ∈ s, C j := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let V : σ → ℤ → PiLp 2 (fun _ : ι => ℂ) := fun j x =>
    WithLp.toLp 2 (terms j x)
  have htermNorm (j : σ) (x : ℤ) :
      ‖V j x‖ = Real.sqrt (∑ i : ι, ‖terms j x i‖ ^ 2) := by
    simp [V, PiLp.norm_eq_of_L2]
  have hsumVector (x : ℤ) :
      (∑ j ∈ s, V j x) =
        WithLp.toLp 2 (fun i : ι => ∑ j ∈ s, terms j x i) := by
    ext i
    simp [V, Finset.sum_apply]
  have hsumNorm (x : ℤ) :
      ‖∑ j ∈ s, V j x‖ =
        Real.sqrt (∑ i : ι, ‖∑ j ∈ s, terms j x i‖ ^ 2) := by
    rw [hsumVector x, PiLp.norm_eq_of_L2]
  have htermBound (j : σ) (hj : j ∈ s) :
      eLpNorm (fun x : ℤ => V j x) p (Measure.count : Measure ℤ) ≤ C j := by
    have hsm : AEStronglyMeasurable (fun x : ℤ => V j x)
        (Measure.count : Measure ℤ) :=
      (show Continuous (fun x : ℤ => V j x) from continuous_of_discreteTopology).stronglyMeasurable.aestronglyMeasurable
    calc
      eLpNorm (fun x : ℤ => V j x) p (Measure.count : Measure ℤ) =
          eLpNorm (fun x : ℤ => ‖V j x‖) p (Measure.count : Measure ℤ) :=
        (eLpNorm_norm (fun x : ℤ => V j x) hsm).symm
      _ = eLpNorm
          (fun x : ℤ => Real.sqrt (∑ i : ι, ‖terms j x i‖ ^ 2))
          p (Measure.count : Measure ℤ) := by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall (htermNorm j)
      _ ≤ C j := hbound j hj
  have htriangle :
      eLpNorm (fun x : ℤ => ∑ j ∈ s, V j x) p
          (Measure.count : Measure ℤ) ≤
        ∑ j ∈ s, eLpNorm (fun x : ℤ => V j x) p
          (Measure.count : Measure ℤ) := by
    have hsumFn : (fun x : ℤ => ∑ j ∈ s, V j x) =
        ∑ j ∈ s, fun x : ℤ => V j x := by
      funext x
      simp
    rw [hsumFn]
    exact eLpNorm_sum_le (p := p) (f := fun j x => V j x) (s := s) hp1
  have hsumBound :
      (∑ j ∈ s, eLpNorm (fun x : ℤ => V j x) p
        (Measure.count : Measure ℤ)) ≤ ∑ j ∈ s, C j :=
    Finset.sum_le_sum fun j hj => htermBound j hj
  have hsmSum : AEStronglyMeasurable
      (fun x : ℤ => ∑ j ∈ s, V j x) (Measure.count : Measure ℤ) :=
    (show Continuous (fun x : ℤ => ∑ j ∈ s, V j x) from continuous_of_discreteTopology).stronglyMeasurable.aestronglyMeasurable
  calc
    eLpNorm
        (fun x : ℤ => Real.sqrt
          (∑ i : ι, ‖∑ j ∈ s, terms j x i‖ ^ 2))
        p (Measure.count : Measure ℤ) =
      eLpNorm (fun x : ℤ => ‖∑ j ∈ s, V j x‖)
        p (Measure.count : Measure ℤ) := by
          apply eLpNorm_congr_ae
          exact Filter.Eventually.of_forall fun x => (hsumNorm x).symm
    _ = eLpNorm (fun x : ℤ => ∑ j ∈ s, V j x)
        p (Measure.count : Measure ℤ) := eLpNorm_norm _ hsmSum
    _ ≤ ∑ j ∈ s, eLpNorm (fun x : ℤ => V j x) p
        (Measure.count : Measure ℤ) := htriangle
    _ ≤ ∑ j ∈ s, C j := hsumBound

end FractionalPrimes.Literature.MSZ

end
