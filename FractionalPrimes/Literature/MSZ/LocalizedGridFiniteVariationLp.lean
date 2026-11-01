module

public import FractionalPrimes.Literature.MSZ.LocalizedGridEstimate
public import FractionalPrimes.Literature.MSZ.LocalizedGridSigma
public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteCoordinateMinkowski
public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteCoordinateFatou
public import FractionalPrimes.Literature.MSZ.LocalizedGridShiftedIncrementLimit
public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteVariationChaining

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

private theorem mszLocalizedGridKq_nonneg (A : AdmissibleData) :
    0 ≤ mszLocalizedGridKq A := by
  unfold mszLocalizedGridKq
  split_ifs with hq2
  · have hq1 : 1 < A.q := A.q_gt_one
    have hr_lt : localInterpolationR A.q < A.q := by
      unfold localInterpolationR
      rw [div_lt_iff₀ (by linarith : 0 < A.q + 1)]
      nlinarith
    have hqPrimePos : 0 < localInterpolationQPrime A.q := by
      unfold localInterpolationQPrime
      exact div_pos (lt_trans zero_lt_one A.q_gt_one)
        (sub_pos.mpr A.q_gt_one)
    have hqPrimeGtTwo : 2 < localInterpolationQPrime A.q := by
      unfold localInterpolationQPrime
      rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
      nlinarith
    have hrPrimeEq : localInterpolationRPrime A.q =
        2 * localInterpolationQPrime A.q := by
      unfold localInterpolationRPrime localInterpolationQPrime
      field_simp [ne_of_gt (sub_pos.mpr A.q_gt_one)]
    have hden1 : 0 < A.q - localInterpolationR A.q := by linarith
    have hden2 : 0 < 2 - A.q := sub_pos.mpr hq2
    have hden3 : 0 < localInterpolationQPrime A.q - 2 := by linarith
    have hden4 : 0 < localInterpolationRPrime A.q -
        localInterpolationQPrime A.q := by
      rw [hrPrimeEq]
      linarith
    have hC : 0 ≤ localInterpolationC A.q := by
      unfold localInterpolationC
      positivity
    have hP : 0 ≤ (max 1 (max (A.P (localInterpolationR A.q))
        (A.P (localInterpolationRPrime A.q))) : ℝ) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hD : 0 ≤ 2 * max 1 A.D := by positivity
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hP _))
      (Real.rpow_nonneg hD _)
  · norm_num

/-- For a fixed dyadic level, the source square function is bounded in both
localized interpolation exponents. The proof first applies finite-vector
Minkowski to the symmetric shifted sums, then uses shifted resolution and
finite-coordinate Fatou to pass to the actual grid increments. -/
theorem mszFiniteVariationLevelSquare_eLpNorm_le
    (A : AdmissibleData) (K L l : ℕ) (hl : l ≤ L)
    (p : ℝ) (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm (fun x : ℤ => mszFiniteVariationLevelSquareFunction A K l f x)
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
          (mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            mszSigmaQLevel A l) *
        eLpNorm f (ENNReal.ofReal p) Measure.count := by
  classical
  let Kset : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let ι := {k : ℤ // k ∈ Kset} × Fin (2 ^ l)
  let shifts : ℕ → Finset ℤ := fun J => Finset.Icc (-(J : ℤ)) (J : ℤ)
  let terms : ℤ → ℤ → ι → ℂ := fun j x i =>
    mszGridIncrement A.kernel i.1.1 l i.2.val
      (A.projections (j + i.1.1) f) x
  let coefficient : ℤ → ℝ := fun j =>
    mszLocalizedGridKq A *
      (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
      (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
      (A.a j l) ^ (A.q - 1)
  let inputNorm : ℝ≥0∞ := eLpNorm f (ENNReal.ofReal p) Measure.count
  let C₀ : ℝ := mszLocalizedGridKq A *
      (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2)
  let C : ℤ → ℝ≥0∞ := fun j => ENNReal.ofReal (coefficient j) * inputNorm
  have hB : 0 ≤ mszFiniteGridMaximalConstant A K L := by
    dsimp [mszFiniteGridMaximalConstant]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact mul_nonneg (mszLocalizedGridKq_nonneg A)
      (Real.rpow_nonneg hB _)
  have hterm_nonneg (j : ℤ) : 0 ≤ mszSigmaQTerm A (l, j) :=
    mszSigmaQTerm_nonneg A (l, j)
  have hcoeff (j : ℤ) : coefficient j =
      C₀ * mszSigmaQTerm A (l, j) := by
    dsimp [coefficient, C₀, mszSigmaQTerm]
    rw [show -(((A.q - 1) / 2) * (l : ℝ)) =
        -((A.q - 1) * (l : ℝ)) / 2 by ring]
    ring
  have hqPrime_gt_one : 1 < A.q / (A.q - 1) := by
    rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
    linarith
  have hpENNNeg : 1 ≤ ENNReal.ofReal p := by
    rcases hp with hpq | hpq'
    · rw [hpq]
      simpa using ENNReal.ofReal_le_ofReal A.q_gt_one.le
    · rw [hpq']
      simpa using ENNReal.ofReal_le_ofReal hqPrime_gt_one.le
  have hcoeffSum : ∀ J : ℕ,
      (∑ j ∈ shifts J, ENNReal.ofReal (coefficient j)) =
        ENNReal.ofReal
          (C₀ * ∑ j ∈ shifts J, mszSigmaQTerm A (l, j)) := by
    intro J
    calc
      (∑ j ∈ shifts J, ENNReal.ofReal (coefficient j)) =
          ∑ j ∈ shifts J, ENNReal.ofReal
            (C₀ * mszSigmaQTerm A (l, j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hcoeff j]
      _ = ENNReal.ofReal
          (∑ j ∈ shifts J, C₀ * mszSigmaQTerm A (l, j)) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg
              (fun j hj => mul_nonneg hC₀ (hterm_nonneg j))
      _ = ENNReal.ofReal
          (C₀ * ∑ j ∈ shifts J, mszSigmaQTerm A (l, j)) := by
            rw [Finset.mul_sum]
  have hsumBound (J : ℕ) :
      (∑ j ∈ shifts J, C j) ≤
        ENNReal.ofReal (C₀ * mszSigmaQLevel A l) * inputNorm := by
    have hsumC : (∑ j ∈ shifts J, C j) =
        ENNReal.ofReal
          (C₀ * ∑ j ∈ shifts J, mszSigmaQTerm A (l, j)) * inputNorm := by
      dsimp [C]
      rw [← Finset.sum_mul, hcoeffSum J]
    have hsumTerm := mszSigmaQLevel_sum_le A l (shifts J)
    have hsumReal : C₀ * (∑ j ∈ shifts J,
        mszSigmaQTerm A (l, j)) ≤ C₀ * mszSigmaQLevel A l :=
      mul_le_mul_of_nonneg_left hsumTerm hC₀
    have hsumENN : ENNReal.ofReal
        (C₀ * ∑ j ∈ shifts J, mszSigmaQTerm A (l, j)) ≤
        ENNReal.ofReal (C₀ * mszSigmaQLevel A l) :=
      ENNReal.ofReal_le_ofReal hsumReal
    rw [hsumC]
    exact (mul_le_mul_left hsumENN inputNorm).trans_eq (by rw [mul_comm])
  have hfiniteJ (J : ℕ) :
      eLpNorm
        (fun x : ℤ => Real.sqrt
          (∑ i : ι, ‖∑ j ∈ shifts J, terms j x i‖ ^ 2))
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (C₀ * mszSigmaQLevel A l) * inputNorm := by
    have hbound : ∀ j ∈ shifts J,
        eLpNorm
          (fun x : ℤ => Real.sqrt (∑ i : ι, ‖terms j x i‖ ^ 2))
          (ENNReal.ofReal p) Measure.count ≤ C j := by
      intro j hj
      have hgrid := localizedGridEstimate A K L l hl j f hf
      have hsum (x : ℤ) :
          (∑ i : ι, ‖terms j x i‖ ^ 2) =
            ∑ k ∈ Kset, ∑ m : Fin (2 ^ l),
              ‖mszGridIncrement A.kernel k l m.val
                (A.projections (j + k) f) x‖ ^ 2 := by
        dsimp [terms, ι, Kset]
        calc
          _ = ∑ k : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)},
              ∑ m : Fin (2 ^ l),
                ‖mszGridIncrement A.kernel k.1 l m.val
                  (A.projections (j + k.1) f) x‖ ^ 2 := by
                rw [← Finset.univ_product_univ, Finset.sum_product]
          _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              ∑ m : Fin (2 ^ l),
                ‖mszGridIncrement A.kernel k l m.val
                  (A.projections (j + k) f) x‖ ^ 2 :=
                Finset.sum_coe_sort (Finset.Icc (-(K : ℤ)) (K : ℤ))
                  (fun k : ℤ => ∑ m : Fin (2 ^ l),
                    ‖mszGridIncrement A.kernel k l m.val
                      (A.projections (j + k) f) x‖ ^ 2)
      have hnormEq :
          eLpNorm
            (fun x : ℤ => Real.sqrt (∑ i : ι, ‖terms j x i‖ ^ 2))
            (ENNReal.ofReal p) Measure.count =
          eLpNorm
            (fun x : ℤ => Real.sqrt
              (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
                ∑ m : Fin (2 ^ l),
                  ‖mszGridIncrement A.kernel k l m.val
                    (A.projections (j + k) f) x‖ ^ 2))
            (ENNReal.ofReal p) Measure.count := by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun x => congrArg Real.sqrt (hsum x)
      rw [hnormEq]
      rcases hp with hpq | hpq'
      · subst p
        simpa only [coefficient, C] using hgrid.1
      · subst p
        simpa only [coefficient, C] using hgrid.2
    have hfinite := msz_counting_eLpNorm_finiteSquare_sum_le
      hpENNNeg (shifts J) terms C hbound
    exact hfinite.trans (hsumBound J)
  let F₂ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
    finiteSupportSequenceLpGeneral (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) (by norm_num) hf.toFinset f
  have hF₂point (x : ℤ) : (F₂ : ℤ → ℂ) x = f x := by
    rw [finiteSupportSequenceLpGeneral_apply
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (by norm_num)
      hf.toFinset f x]
    by_cases hx : x ∈ hf.toFinset
    · simp [hx]
    · have hfx : f x = 0 := by
        by_contra hfx
        exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hfx))
      simp [hx, hfx]
  have hF₂seq : (F₂ : ℤ → ℂ) = f := funext hF₂point
  have hcoordinate (i : ι) (x : ℤ) :
      Tendsto (fun J : ℕ => ∑ j ∈ shifts J, terms j x i) atTop
        (𝓝 (mszGridIncrement A.kernel i.1.1 l i.2.val f x)) := by
    letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    let k := i.1.1
    let m := i.2.val
    have hRes := mszLocalizedGridIncrementShiftedResolution A F₂ k l m
    have hEval :=
      (lp.lipschitzWith_one_eval (p := (2 : ℝ≥0∞)) x).continuous.tendsto
        (mszGridIncrementLpCLM A k l m F₂)
    have hpoint := hEval.comp hRes
    have hproj (j : ℤ) (y : ℤ) :
        A.projectionsL2 (k + j) F₂ y = A.projections (j + k) f y := by
      calc
        A.projectionsL2 (k + j) F₂ y =
            A.projections (k + j) (F₂ : ℤ → ℂ) y :=
          A.projectionsL2_agree (k + j) F₂ y
        _ = A.projections (j + k) f y := by
          rw [hF₂seq, add_comm]
    have hApprox (J : ℕ) :
        (∑ j ∈ shifts J,
          mszGridIncrement A.kernel k l m
            (A.projectionsL2 (k + j) F₂ : ℤ → ℂ) x) =
          ∑ j ∈ shifts J, terms j x i := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [terms, k, m]
      congr 1
      funext y
      exact hproj j y
    have hlimit :
        mszGridIncrement A.kernel k l m (F₂ : ℤ → ℂ) x =
          mszGridIncrement A.kernel k l m f x := by
      rw [hF₂seq]
    have hpoint' : Tendsto
        (fun J : ℕ => ∑ j ∈ shifts J, terms j x i) atTop
        (𝓝 (mszGridIncrement A.kernel k l m f x)) := by
      have hpointLp : Tendsto
          (fun J : ℕ =>
            ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              mszGridIncrementLpCLM A k l m
                (A.projectionsL2 (k + j) F₂) :
                lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) : ℤ → ℂ) x)
          atTop
          (𝓝 ((mszGridIncrementLpCLM A k l m F₂ : ℤ → ℂ) x)) := by
        change Tendsto
          ((fun g : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) => (g : ℤ → ℂ) x) ∘
            fun J : ℕ => ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              mszGridIncrementLpCLM A k l m
                (A.projectionsL2 (k + j) F₂))
          atTop (𝓝 ((mszGridIncrementLpCLM A k l m F₂ : ℤ → ℂ) x))
        exact hpoint
      have hsumEval (J : ℕ) :
          ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            mszGridIncrementLpCLM A k l m
              (A.projectionsL2 (k + j) F₂) :
              lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) : ℤ → ℂ) x =
            ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              mszGridIncrement A.kernel k l m
                (A.projectionsL2 (k + j) F₂ : ℤ → ℂ) x := by
        rw [lp.coeFn_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        exact mszGridIncrementLpCLM_apply A k l m
          (A.projectionsL2 (k + j) F₂) x
      have hpointLpRaw : Tendsto
          (fun J : ℕ =>
            ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
              mszGridIncrementLpCLM A k l m
                (A.projectionsL2 (k + j) F₂) :
                lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞)) : ℤ → ℂ) x)
          atTop (𝓝 (mszGridIncrement A.kernel k l m (F₂ : ℤ → ℂ) x)) := by
        simpa only [mszGridIncrementLpCLM_apply] using hpointLp
      have hpoint'' : Tendsto
          (fun J : ℕ => ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
            mszGridIncrement A.kernel k l m
              (A.projectionsL2 (k + j) F₂ : ℤ → ℂ) x) atTop
          (𝓝 (mszGridIncrement A.kernel k l m (F₂ : ℤ → ℂ) x)) :=
        hpointLpRaw.congr' (Filter.Eventually.of_forall hsumEval)
      have hpoint''' : Tendsto
          (fun J : ℕ => ∑ j ∈ shifts J,
            mszGridIncrement A.kernel k l m
              (A.projectionsL2 (k + j) F₂ : ℤ → ℂ) x) atTop
          (𝓝 (mszGridIncrement A.kernel k l m (F₂ : ℤ → ℂ) x)) := by
        simpa only [shifts] using hpoint''
      simpa only [hApprox, hlimit] using hpoint'''
    simpa [k, m] using hpoint'
  let limit : ℤ → ι → ℂ := fun x i =>
    mszGridIncrement A.kernel i.1.1 l i.2.val f x
  have hfatou := msz_counting_eLpNorm_finiteSquare_le_of_coordinatewise_limit
    (fun J x i => ∑ j ∈ shifts J, terms j x i) limit
    (ENNReal.ofReal (C₀ * mszSigmaQLevel A l) * inputNorm)
    (by intro J; simpa [inputNorm] using hfiniteJ J)
    (by intro i x; exact hcoordinate i x)
  have hlimitSquare :
      (fun x : ℤ => Real.sqrt (∑ i : ι, ‖limit x i‖ ^ 2)) =
        fun x => mszFiniteVariationLevelSquareFunction A K l f x := by
    funext x
    dsimp [limit, mszFiniteVariationLevelSquareFunction, ι, Kset]
    congr 1
    calc
      (∑ i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l),
          ‖mszGridIncrement A.kernel i.1.1 l i.2.val f x‖ ^ 2) =
        ∑ k : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)},
          ∑ m : Fin (2 ^ l),
            ‖mszGridIncrement A.kernel k.1 l m.val f x‖ ^ 2 := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ m : Fin (2 ^ l),
            ‖mszGridIncrement A.kernel k l m.val f x‖ ^ 2 :=
              Finset.sum_coe_sort (Finset.Icc (-(K : ℤ)) (K : ℤ))
                (fun k : ℤ => ∑ m : Fin (2 ^ l),
                  ‖mszGridIncrement A.kernel k l m.val f x‖ ^ 2)
      _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ m ∈ Finset.range (2 ^ l),
            ‖mszGridIncrement A.kernel k l m f x‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [← Fin.sum_univ_eq_sum_range]
  have hfinal := hfatou
  rw [hlimitSquare] at hfinal
  simpa [C₀, inputNorm] using hfinal

end

end FractionalPrimes.Literature.MSZ

end
