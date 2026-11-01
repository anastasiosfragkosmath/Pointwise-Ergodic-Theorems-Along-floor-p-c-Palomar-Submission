module

public import FractionalPrimes.GeneralDiscreteLpBridge
public import FractionalPrimes.Literature.MSZ.AdmissibleData
public import FractionalPrimes.Literature.MSZ.LocalizedInterpolation

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped BigOperators ENNReal

/-! The localized scalar `L²` square-function witness controls the actual
finite vector of grid-increment convolutions pointwise. Finite-moment
exhaustion then supplies the sequence-`lp²` representative needed by the
direct endpoint in localized interpolation. -/

private theorem localInterpolation_sum_subtypeProduct_eq
    (K : Finset ℤ) (N : ℕ) (a : ℤ × Fin N → ℝ) :
    (∑ i : {k : ℤ // k ∈ K} × Fin N, a (i.1.1, i.2)) =
      ∑ i ∈ K.product Finset.univ, a i := by
  classical
  calc
    _ = ∑ k : {k : ℤ // k ∈ K}, ∑ m : Fin N, a (k.1, m) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ k ∈ K, ∑ m : Fin N, a (k, m) :=
      Finset.sum_coe_sort K (fun k : ℤ => ∑ m : Fin N, a (k, m))
    _ = ∑ i ∈ K.product Finset.univ, a i :=
      (Finset.sum_product K (Finset.univ : Finset (Fin N)) a).symm

/-- Lift the source localized scalar `L²` bound to the actual finite-family
vector output, with the exact convolution representatives and unchanged
constant. The finite spatial index set is `−K ≤ k ≤ K`; each `k` is repeated
for the `2^l` increment coordinates. -/
theorem localInterpolation_localizedIncrement_l2VectorWitness
    (A : AdmissibleData) (K : ℕ) (j : ℤ) (l : ℕ)
    (f : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) :
    ∃ U : lp
        (fun _ : ℤ => PiLp 2
          (fun _ : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} ×
            Fin (2 ^ l) => ℂ))
        (2 : ℝ≥0∞),
      (∀ x, U x = integerKernelVectorConvolution
        (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
          mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
        (fun y => WithLp.toLp 2
          (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
            A.projections (i.1.1 + j) (f : ℤ → ℂ) y)) x) ∧
      ‖U‖ ≤ (2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l * ‖f‖ := by
  classical
  let Kset : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let N : ℕ := 2 ^ l
  let ι : Type := {k : ℤ // k ∈ Kset} × Fin N
  let kernels : ι → IntegerL1Kernel := fun i =>
    mszGridIncrementKernel A.kernel i.1.1 l i.2.val
  let input : ℤ → PiLp 2 (fun _ : ι => ℂ) := fun y =>
    WithLp.toLp 2 (fun i : ι => A.projections (i.1.1 + j) (f : ℤ → ℂ) y)
  let V : ℤ → PiLp 2 (fun _ : ι => ℂ) := fun x =>
    integerKernelVectorConvolution kernels input x
  let R : ℝ := (2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l * ‖f‖
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (A.a_nonneg j l))
      (norm_nonneg f)
  obtain ⟨G, hG, hGnorm⟩ := A.localized_increment_bound j l f
  have hGbound : ‖G‖ ≤ R := by
    simpa [R] using hGnorm
  have hGpoint (x : ℤ) :
      G x = Real.sqrt (∑' i : ℤ × Fin N,
        ‖mszGridIncrement A.kernel i.1 l i.2.val
          (A.projections (j + i.1) (f : ℤ → ℂ)) x‖ ^ 2) := by
    simpa [localizedIncrementSquareFunction, N] using hG x
  have hGnonneg (x : ℤ) : 0 ≤ G x := by
    rw [hGpoint x]
    exact Real.sqrt_nonneg _
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpTop : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hpToReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hincrementKernel (k : ℤ) (m : Fin N) (x : ℤ) :
      mszGridIncrement A.kernel k l m.val
        (A.projections (j + k) (f : ℤ → ℂ)) x =
      integerKernelConvolution (mszGridIncrementKernel A.kernel k l m.val)
        (A.projections (j + k) (f : ℤ → ℂ)) x := by
    let g : lp (fun _ : ℤ => ℂ) 2 := A.projectionsL2 (j + k) f
    let gCount : Lp ℂ (2 : ℝ≥0∞) (Measure.count : Measure ℤ) :=
      generalLpToCountLp (p := (2 : ℝ≥0∞)) hp0 hpTop g
    have hgc : (gCount : ℤ → ℂ) =
        A.projections (j + k) (f : ℤ → ℂ) := by
      funext y
      calc
        (gCount : ℤ → ℂ) y = g y :=
          generalLpToCountLp_apply hp0 hpTop g y
        _ = A.projections (j + k) (f : ℤ → ℂ) y :=
          A.projectionsL2_agree (j + k) f y
    simpa only [hgc] using
      (mszGridIncrement_eq_kernelConvolution
        (p := (2 : ℝ≥0∞)) (by norm_num) A.kernel k l m.val gCount x)
  have hcoord (x : ℤ) (i : ι) :
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
  let term : ℤ → (ℤ × Fin N) → ℝ := fun x i =>
    ‖mszGridIncrement A.kernel i.1 l i.2.val
      (A.projections (j + i.1) (f : ℤ → ℂ)) x‖ ^ 2
  have htermSummable (x : ℤ) : Summable (term x) := by
    simpa [term, N] using A.localized_increment_summable j l f x
  have hfiniteOutput (x : ℤ) :
      ∑ i : ι, ‖V x i‖ ^ 2 ≤ ∑' i : ℤ × Fin N, term x i := by
    calc
      ∑ i : ι, ‖V x i‖ ^ 2 =
          ∑ i : ι, term x (i.1.1, i.2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoord x i]
      _ = ∑ i ∈ Kset.product Finset.univ, term x i :=
        localInterpolation_sum_subtypeProduct_eq Kset N (term x)
      _ ≤ ∑' i : ℤ × Fin N, term x i :=
        (htermSummable x).sum_le_tsum (Kset.product Finset.univ)
          (fun i _ => sq_nonneg
            (‖mszGridIncrement A.kernel i.1 l i.2.val
              (A.projections (j + i.1) (f : ℤ → ℂ)) x‖))
  have hpointwise (x : ℤ) : ‖V x‖ ≤ G x := by
    have htermNonneg : 0 ≤ ∑' i : ℤ × Fin N, term x i :=
      tsum_nonneg fun i => by
        dsimp [term]
        positivity
    have hGsq : G x ^ 2 = ∑' i : ℤ × Fin N, term x i := by
      rw [hGpoint x]
      change (Real.sqrt (∑' i : ℤ × Fin N, term x i)) ^ 2 = _
      exact Real.sq_sqrt htermNonneg
    have hnormSq : ‖V x‖ ^ 2 ≤ G x ^ 2 := by
      calc
        ‖V x‖ ^ 2 = ∑ i : ι, ‖V x i‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
        _ ≤ ∑' i : ℤ × Fin N, term x i := hfiniteOutput x
        _ = G x ^ 2 := hGsq.symm
    nlinarith [hnormSq, norm_nonneg (V x), hGnonneg x]
  have hsumGReal : Summable (fun x : ℤ => ‖G x‖ ^ (2 : ℝ)) := by
    simpa only [hpToReal] using
      (lp.memℓp G).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hsumGAbs : Summable (fun x : ℤ => ‖G x‖ ^ 2) := by
    have hpowFun : (fun x : ℤ => ‖G x‖ ^ (2 : ℝ)) =
        (fun x : ℤ => ‖G x‖ ^ 2) := by
      funext x
      exact Real.rpow_natCast _ 2
    rw [← hpowFun]
    exact hsumGReal
  have hsumG : Summable (fun x : ℤ => G x ^ 2) := by
    refine hsumGAbs.congr ?_
    intro x
    rw [Real.norm_of_nonneg (hGnonneg x)]
  have hnormG :
      (∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ) = ‖G‖ := by
    have hnormGReal :
        (∑' x : ℤ, ‖G x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ‖G‖ := by
      simpa only [hpToReal] using
      (lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) G).symm
    convert hnormGReal using 1
    congr 1
    exact tsum_congr (fun x : ℤ => (Real.rpow_natCast (‖G x‖) 2).symm)
  have hsumGNonneg : 0 ≤ ∑' x : ℤ, ‖G x‖ ^ 2 :=
    tsum_nonneg fun x => sq_nonneg (‖G x‖)
  have hnormGSq : ‖G‖ ^ 2 = ∑' x : ℤ, G x ^ 2 := by
    calc
      ‖G‖ ^ 2 = ((∑' x : ℤ, ‖G x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← hnormG]
      _ = ∑' x : ℤ, ‖G x‖ ^ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsumGNonneg]
      _ = ∑' x : ℤ, G x ^ 2 := by
        apply tsum_congr
        intro x
        rw [Real.norm_of_nonneg (hGnonneg x)]
  have hGfiniteMoment (s : Finset ℤ) :
      ∑ x ∈ s, G x ^ 2 ≤ ‖G‖ ^ 2 := by
    calc
      ∑ x ∈ s, G x ^ 2 ≤ ∑' x : ℤ, G x ^ 2 :=
        hsumG.sum_le_tsum s (fun x _ => sq_nonneg (G x))
      _ = ‖G‖ ^ 2 := hnormGSq.symm
  have hfiniteMoment (s : Finset ℤ) :
      ∑ x ∈ s, ‖V x‖ ^ 2 ≤ R ^ 2 := by
    calc
      ∑ x ∈ s, ‖V x‖ ^ 2 ≤ ∑ x ∈ s, G x ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        nlinarith [hpointwise x, norm_nonneg (V x), hGnonneg x]
      _ ≤ ‖G‖ ^ 2 := hGfiniteMoment s
      _ ≤ R ^ 2 := by
        nlinarith [hGbound, norm_nonneg G, hR]
  have hfiniteMomentReal (s : Finset ℤ) :
      ∑ x ∈ s, ‖V x‖ ^ (2 : ℝ) ≤ R ^ 2 := by
    calc
      ∑ x ∈ s, ‖V x‖ ^ (2 : ℝ) = ∑ x ∈ s, ‖V x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Real.rpow_natCast _ 2
      _ ≤ R ^ 2 := hfiniteMoment s
  let U : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (2 : ℝ≥0∞) :=
    lpOfUniformFiniteMomentBound hp0 hpTop V (sq_nonneg R) (by
      intro s
      simpa only [hpToReal] using hfiniteMomentReal s)
  have hUnorm : ‖U‖ ≤ R := by
    apply lp.norm_le_of_forall_sum_le
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) hR
    intro s
    calc
      ∑ i ∈ s, ‖U i‖ ^ (2 : ℝ) ≤ R ^ 2 := by
        simpa only [U, lpOfUniformFiniteMomentBound_apply, hpToReal] using
          hfiniteMomentReal s
      _ = R ^ (2 : ℝ) := (Real.rpow_natCast R 2).symm
  refine ⟨U, ?_, ?_⟩
  · intro x
    rfl
  · simpa [R] using hUnorm

end FractionalPrimes.Literature.MSZ

end
