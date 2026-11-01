module

public import FractionalPrimes.Literature.MSZ.LocalizedGridVectorL2Bridge

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem localizedGrid_sum_subtypeProduct_eq
    (K : Finset ℤ) (N : ℕ) (a : ℤ × Fin N → ℝ) :
    (∑ i : {k : ℤ // k ∈ K} × Fin N, a (i.1.1, i.2)) =
      ∑ i ∈ K.product Finset.univ, a i := by
  classical
  calc
    _ = ∑ k : {k : ℤ // k ∈ K}, ∑ m : Fin N, a (k.1, m) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ k ∈ K, ∑ m : Fin N, a (k, m) :=
      Finset.sum_coe_sort K (fun k : ℤ => ∑ m : Fin N, a (k, m))
    _ = ∑ i ∈ K.product Finset.univ, a i := by
      exact (Finset.sum_product K (Finset.univ : Finset (Fin N)) a).symm

/-- The norm of the finite `PiLp 2` grid-convolution vector is exactly the
literal square root of the finite double sum of localized increments in
`lm:localizedGrid`. -/
theorem mszLocalizedGridVector_norm_eq_finiteSquare
    (A : AdmissibleData) (K : ℕ) (j : ℤ) (l : ℕ)
    (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) (x : ℤ) :
    ‖integerKernelVectorConvolution
      (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
        mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
      (fun y => WithLp.toLp 2
        (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
          A.projections (i.1.1 + j) (f : ℤ → ℂ) y)) x‖ =
      Real.sqrt (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ m : Fin (2 ^ l),
          ‖mszGridIncrement A.kernel k l m.val
            (A.projections (j + k) (f : ℤ → ℂ)) x‖ ^ 2) := by
  classical
  let Kset : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let N : ℕ := 2 ^ l
  let ι : Type := {k : ℤ // k ∈ Kset} × Fin N
  let kernels : ι → IntegerL1Kernel := fun i =>
    mszGridIncrementKernel A.kernel i.1.1 l i.2.val
  let input : ℤ → PiLp 2 (fun _ : ι => ℂ) := fun y =>
    WithLp.toLp 2 (fun i : ι =>
      A.projections (i.1.1 + j) (f : ℤ → ℂ) y)
  let V : ℤ → PiLp 2 (fun _ : ι => ℂ) := fun y =>
    integerKernelVectorConvolution kernels input y
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpTop : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hincrementKernel (k : ℤ) (m : Fin N) (y : ℤ) :
      mszGridIncrement A.kernel k l m.val
        (A.projections (j + k) (f : ℤ → ℂ)) y =
      integerKernelConvolution (mszGridIncrementKernel A.kernel k l m.val)
        (A.projections (j + k) (f : ℤ → ℂ)) y := by
    let g : lp (fun _ : ℤ => ℂ) 2 := A.projectionsL2 (j + k) f
    let gCount : Lp ℂ (2 : ℝ≥0∞) (Measure.count : Measure ℤ) :=
      generalLpToCountLp (p := (2 : ℝ≥0∞)) hp0 hpTop g
    have hgc : (gCount : ℤ → ℂ) =
        A.projections (j + k) (f : ℤ → ℂ) := by
      funext z
      calc
        (gCount : ℤ → ℂ) z = g z :=
          generalLpToCountLp_apply hp0 hpTop g z
        _ = A.projections (j + k) (f : ℤ → ℂ) z :=
          A.projectionsL2_agree (j + k) f z
    simpa only [hgc] using
      (mszGridIncrement_eq_kernelConvolution
        (p := (2 : ℝ≥0∞)) (by norm_num) A.kernel k l m.val gCount y)
  have hcoord (i : ι) :
      V x i = mszGridIncrement A.kernel i.1.1 l i.2.val
        (A.projections (j + i.1.1) (f : ℤ → ℂ)) x := by
    change integerKernelConvolution
        (mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
        (fun y => A.projections (i.1.1 + j) (f : ℤ → ℂ) y) x = _
    have hinput :
        (fun y : ℤ => A.projections (i.1.1 + j) (f : ℤ → ℂ) y) =
          fun y => A.projections (j + i.1.1) (f : ℤ → ℂ) y := by
      funext y
      rw [add_comm]
    calc
      _ = integerKernelConvolution
          (mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
          (fun y => A.projections (j + i.1.1) (f : ℤ → ℂ) y) x := by
        rw [hinput]
      _ = mszGridIncrement A.kernel i.1.1 l i.2.val
          (A.projections (j + i.1.1) (f : ℤ → ℂ)) x :=
        (hincrementKernel i.1.1 i.2 x).symm
  let term : ℤ × Fin N → ℝ := fun i =>
    ‖mszGridIncrement A.kernel i.1 l i.2.val
      (A.projections (j + i.1) (f : ℤ → ℂ)) x‖ ^ 2
  have hcoordSum :
      (∑ i : ι, ‖V x i‖ ^ 2) =
        ∑ k ∈ Kset, ∑ m : Fin N, term (k, m) := by
    calc
      _ = ∑ i : ι, term (i.1.1, i.2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoord i]
      _ = ∑ i ∈ Kset.product Finset.univ, term i :=
        localizedGrid_sum_subtypeProduct_eq Kset N term
      _ = ∑ k ∈ Kset, ∑ m : Fin N, term (k, m) := by
        exact Finset.sum_product Kset (Finset.univ : Finset (Fin N)) term
  have hnormSq :
      ‖V x‖ ^ 2 = ∑ k ∈ Kset, ∑ m : Fin N, term (k, m) := by
    calc
      ‖V x‖ ^ 2 = ∑ i : ι, ‖V x i‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
      _ = _ := hcoordSum
  change ‖V x‖ = Real.sqrt
    (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∑ m : Fin (2 ^ l),
        ‖mszGridIncrement A.kernel k l m.val
          (A.projections (j + k) (f : ℤ → ℂ)) x‖ ^ 2)
  calc
    ‖V x‖ = Real.sqrt (‖V x‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (V x))]
    _ = Real.sqrt (∑ k ∈ Kset, ∑ m : Fin N, term (k, m)) :=
      congrArg Real.sqrt hnormSq
    _ = _ := by
      simp only [Kset, N, term]

end

end FractionalPrimes.Literature.MSZ

end
