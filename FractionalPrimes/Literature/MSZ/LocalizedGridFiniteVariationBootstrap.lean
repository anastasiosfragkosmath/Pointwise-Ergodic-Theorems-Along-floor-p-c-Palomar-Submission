module

public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteVariationGeneral
public import FractionalPrimes.Literature.MSZ.ScalarBootstrap

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! The finite-grid maximal bootstrap step in `lm:main`. -/

private theorem msz_dyadicGridVariationTwoIndex_ge_pair
    (L m : ℕ) (g : ℚ → ℂ) (hm : 0 < m) (hM : m ≤ 2 ^ L) :
    ENNReal.ofReal ‖g (dyadicGridPoint L m) - g (dyadicGridPoint L 0)‖ ≤
      dyadicGridVariationTwoIndex L g := by
  unfold dyadicGridVariationTwoIndex
  let u : Fin (1 + 1) → ℕ := fun i => i.val * m
  have huStrict : StrictMono u := by
    intro i j hij
    have hij' : i.val < j.val := Fin.lt_def.mp hij
    exact Nat.mul_lt_mul_of_pos_right hij' hm
  have huBound : ∀ i, u i ≤ 2 ^ L := by
    intro i
    have hi : i.val ≤ 1 := Nat.lt_succ_iff.mp i.isLt
    have hu : i.val * m ≤ 1 * m := Nat.mul_le_mul_right m hi
    have hM' : 1 * m ≤ 2 ^ L := by simpa using hM
    simpa [u] using hu.trans hM'
  have hcond : 0 < 1 ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L :=
    ⟨by norm_num, huStrict, huBound⟩
  apply le_iSup_of_le 1
  apply le_iSup_of_le u
  rw [dif_pos hcond]
  have hzero : u (0 : Fin 2) = 0 := by simp [u]
  have hone : u (1 : Fin 2) = m := by simp [u]
  have hsum : (∑ i : Fin 1,
      ‖g (dyadicGridPoint L (u i.succ)) -
        g (dyadicGridPoint L (u i.castSucc))‖ ^ 2) =
      ‖g (dyadicGridPoint L m) - g (dyadicGridPoint L 0)‖ ^ 2 := by
    simp [hzero, hone]
  rw [hsum]
  have hnonneg : 0 ≤ ‖g (dyadicGridPoint L m) -
      g (dyadicGridPoint L 0)‖ := norm_nonneg _
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

private theorem msz_dyadicGridVariationSubtype_ge_pair
    (L m : ℕ) (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    (hm : 0 < m) (hM : m ≤ 2 ^ L) :
    ENNReal.ofReal ‖g ⟨dyadicGridPoint L m, ⟨m, hM, rfl⟩⟩ -
      g ⟨dyadicGridPoint L 0, ⟨0, Nat.zero_le _, rfl⟩⟩‖ ≤
      dyadicGridVariationTwoSubtype L g := by
  change ENNReal.ofReal ‖g ⟨dyadicGridPoint L m, ⟨m, hM, rfl⟩⟩ -
      g ⟨dyadicGridPoint L 0, ⟨0, Nat.zero_le _, rfl⟩⟩‖ ≤
    dyadicGridVariationTwo L (dyadicGridExtend L g)
  rw [dyadicGridVariationTwo_eq_index]
  have hp := msz_dyadicGridVariationTwoIndex_ge_pair L m
    (dyadicGridExtend L g) hm hM
  have hmem : dyadicGridPoint L m ∈ dyadicGridTimes L := ⟨m, hM, rfl⟩
  have hmem0 : dyadicGridPoint L 0 ∈ dyadicGridTimes L :=
    ⟨0, Nat.zero_le _, rfl⟩
  rw [dyadicGridExtend_of_mem L g hmem,
    dyadicGridExtend_of_mem L g hmem0] at hp
  exact hp

/-- A two-point increment from the dyadic block base is controlled by its
finite-grid variation, with the source's exact rational grid points. -/
theorem mszFiniteShortBlockVariation_pair_le
    (A : AdmissibleData) (k : ℤ) (L m : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hm : m ≤ 2 ^ L) :
    ‖mszKernelAverage (A.kernel (mszGridTime k L m)) f x -
      mszKernelAverage (A.kernel (mszGridTime k 0 0)) f x‖ ≤
        (mszFiniteShortBlockVariation A k L f x).toReal := by
  classical
  by_cases hzero : m = 0
  · subst m
    have htime : mszGridTime k L 0 = mszGridTime k 0 0 := by
      simpa using mszGridTime_refine_start k 0 0 L
    rw [htime]
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hzero
    have hvar := msz_dyadicGridVariationSubtype_ge_pair L m
      (mszFiniteShortBlockValues A k L f x) hmpos hm
    have hbase : mszFiniteShortBlockValues A k L f x
        ⟨dyadicGridPoint L 0, ⟨0, Nat.zero_le _, rfl⟩⟩ =
          mszKernelAverage (A.kernel (mszGridTime k 0 0)) f x := by
      rw [mszFiniteShortBlockValues_gridPoint]
      · have htime : mszGridTime k L 0 = mszGridTime k 0 0 := by
          simpa using mszGridTime_refine_start k 0 0 L
        rw [htime]
      · simp
    have hpoint : mszFiniteShortBlockValues A k L f x
        ⟨dyadicGridPoint L m, ⟨m, hm, rfl⟩⟩ =
          mszKernelAverage (A.kernel (mszGridTime k L m)) f x :=
      mszFiniteShortBlockValues_gridPoint A k L m f x hm
    have hvar' : ENNReal.ofReal
        ‖mszKernelAverage (A.kernel (mszGridTime k L m)) f x -
          mszKernelAverage (A.kernel (mszGridTime k 0 0)) f x‖ ≤
          mszFiniteShortBlockVariation A k L f x := by
      simpa [mszFiniteShortBlockVariation, hpoint, hbase] using hvar
    have hfinite := mszFiniteShortBlockVariation_ne_top A k L f x
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hvar'

private theorem mszFiniteShortVariation_block_toReal_le
    (A : AdmissibleData) (K L : ℕ) (k : ℤ) (f : ℤ → ℂ) (x : ℤ)
    (hk : k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)) :
    (mszFiniteShortBlockVariation A k L f x).toReal ≤
      mszFiniteShortVariation A K L f x := by
  classical
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum
    (f := fun j => (mszFiniteShortBlockVariation A j L f x).toReal ^ 2)
    (fun j hj => sq_nonneg _) hk

private theorem msz_eLpNorm_lp_raw_eq_norm
    {p : ℝ} (hp : 1 < p)
    (f : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p)) :
    eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count =
      ENNReal.ofReal ‖f‖ := by
  calc
    eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count =
        eLpNorm (fun x : ℤ => ‖f x‖) (ENNReal.ofReal p) Measure.count :=
          (eLpNorm_norm (fun x : ℤ => f x)
            (measurable_of_countable _).aestronglyMeasurable).symm
    _ = ENNReal.ofReal ‖f‖ := localInterpolation_eLpNorm_lp_norm hp f

private theorem msz_eLpNorm_complexLp_raw_eq_norm
    {p : ℝ} (hp : 1 < p)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count =
      ENNReal.ofReal ‖f‖ := by
  calc
    eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count =
        eLpNorm (fun x : ℤ => ‖f x‖) (ENNReal.ofReal p) Measure.count :=
          (eLpNorm_norm (fun x : ℤ => f x)
            (measurable_of_countable _).aestronglyMeasurable).symm
    _ = ENNReal.ofReal ‖f‖ := localInterpolation_eLpNorm_lp_norm hp f

/-- The finite-grid maximal norm obeys the exact nonlinear inequality used
in the source bootstrap, before the scalar numerical step. -/
theorem mszFiniteGridMaximalNorm_bootstrap_ineq
    (A : AdmissibleData) (K L : ℕ) :
    mszFiniteGridMaximalNorm A K L ≤
      ENNReal.ofReal (A.Mq +
        (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A) *
          (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2)) := by
  classical
  let pENN : ℝ≥0∞ := ENNReal.ofReal A.q
  let B : ℝ := mszFiniteGridMaximalConstant A K L
  let H : ℝ := Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A
  let C : ℝ := A.Mq + H * B ^ ((2 - A.q) / 2)
  have hp : 1 < A.q := A.q_gt_one
  have hp0 : pENN ≠ 0 := by
    dsimp [pENN]
    exact ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp)
  have hpTop : pENN ≠ ∞ := by
    dsimp [pENN]
    exact ENNReal.ofReal_ne_top
  have hpOne : 1 ≤ pENN := by
    dsimp [pENN]
    exact (ENNReal.one_le_ofReal).2 hp.le
  have hKnonneg : 0 ≤ mszLocalizedGridKq A := by
    unfold mszLocalizedGridKq
    split_ifs with hq2
    · have hq2pos : 0 < 2 - A.q := sub_pos.mpr hq2
      have hr_lt : localInterpolationR A.q < A.q := by
        unfold localInterpolationR
        rw [div_lt_iff₀ (by linarith [A.q_gt_one] : 0 < A.q + 1)]
        nlinarith [A.q_gt_one]
      have hqPrimePos : 0 < localInterpolationQPrime A.q := by
        unfold localInterpolationQPrime
        exact div_pos (lt_trans zero_lt_one A.q_gt_one)
          (sub_pos.mpr A.q_gt_one)
      have hqPrimeGtTwo : 2 < localInterpolationQPrime A.q := by
        unfold localInterpolationQPrime
        rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
        nlinarith [A.q_gt_one, hq2]
      have hrPrimeEq : localInterpolationRPrime A.q =
          2 * localInterpolationQPrime A.q := by
        unfold localInterpolationRPrime localInterpolationQPrime
        field_simp [ne_of_gt (sub_pos.mpr A.q_gt_one)]
      have hden1 : 0 < A.q - localInterpolationR A.q := by linarith
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
  have hsigmaNonneg : 0 ≤ mszSigmaQ A :=
    tsum_nonneg (fun z => mszSigmaQTerm_nonneg A z)
  have hBnonneg : 0 ≤ B := by
    dsimp [B, mszFiniteGridMaximalConstant]
    positivity
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
      hKnonneg) hsigmaNonneg
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg A.Mq_nonneg
      (mul_nonneg hHnonneg (Real.rpow_nonneg hBnonneg _))
  have hVnonneg (f : ℤ → ℂ) (x : ℤ) :
      0 ≤ mszFiniteShortVariation A K L f x := Real.sqrt_nonneg _
  have hunit (f : lp (fun _ : ℤ => ℂ) pENN) (hf : ‖f‖ ≤ 1) :
      ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖ ≤
        ENNReal.ofReal C := by
    letI : Fact (1 ≤ pENN) := ⟨hpOne⟩
    let g : lp (fun _ : ℤ => ℝ) pENN := mszFiniteGridMaximalSequence A K L f
    let V : ℤ → ℝ := mszFiniteShortVariation A K L (f : ℤ → ℂ)
    obtain ⟨G, hGnonneg, hGmax, hGnorm⟩ := A.dyadic_maximal_bound f
    have hVbound : eLpNorm V pENN Measure.count ≤
        ENNReal.ofReal (H * B ^ ((2 - A.q) / 2)) *
          eLpNorm (fun x : ℤ => f x) pENN Measure.count := by
      have h := finiteVariationEstimate A K L A.q (Or.inl rfl) f
      calc
        _ ≤ ENNReal.ofReal
            (Real.sqrt 2 * mszLocalizedGridKq A * B ^ ((2 - A.q) / 2) *
              mszSigmaQ A) * eLpNorm (fun x : ℤ => f x) pENN Measure.count := by
                simpa [V, pENN, B, mszFiniteGridMaximalConstant] using h
        _ = _ := by
          congr 1
          dsimp [H]
          ring_nf
    have hpoint (x : ℤ) : g x ≤ G x + V x := by
      change mszFiniteGridMaximalSequence A K L f x ≤ G x + V x
      have hsup : mszFiniteGridMaximalSequence A K L f x =
          (mszFiniteTimeGrid K L).sup'
            (mszFiniteTimeGrid_nonempty K L)
            (fun t => ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖) := by
        simpa [pENN, mszQExponent] using
          mszFiniteGridMaximalSequence_apply A K L f x
      rw [hsup]
      apply Finset.sup'_le
      intro t ht
      have hmem : t ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).biUnion
          (fun k => (Finset.range (2 ^ L + 1)).image (mszGridTime k L)) := by
        simpa [mszFiniteTimeGrid] using ht
      rcases Finset.mem_biUnion.mp hmem with ⟨k, hk, hrest⟩
      rcases Finset.mem_image.mp hrest with ⟨m, hm, htime⟩
      have hm' : m ≤ 2 ^ L := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have htime' : t = mszGridTime k L m := htime.symm
      subst t
      have hbase : ‖mszKernelAverage (A.kernel (mszGridTime k 0 0))
          (f : ℤ → ℂ) x‖ ≤ G x := by
        simpa [mszDyadicTime] using hGmax k x
      have hinc := mszFiniteShortBlockVariation_pair_le A k L m
        (f : ℤ → ℂ) x hm'
      have hblock : (mszFiniteShortBlockVariation A k L
          (f : ℤ → ℂ) x).toReal ≤ V x := by
        exact mszFiniteShortVariation_block_toReal_le A K L k
          (f : ℤ → ℂ) x hk
      have hvalue := calc
          ‖mszKernelAverage (A.kernel (mszGridTime k L m))
              (f : ℤ → ℂ) x‖ =
            ‖(mszKernelAverage (A.kernel (mszGridTime k L m))
                (f : ℤ → ℂ) x -
              mszKernelAverage (A.kernel (mszGridTime k 0 0))
                (f : ℤ → ℂ) x) +
              mszKernelAverage (A.kernel (mszGridTime k 0 0))
                (f : ℤ → ℂ) x‖ := by congr 1 <;> ring
          _ ≤ ‖mszKernelAverage (A.kernel (mszGridTime k L m))
                (f : ℤ → ℂ) x -
              mszKernelAverage (A.kernel (mszGridTime k 0 0))
                (f : ℤ → ℂ) x‖ +
              ‖mszKernelAverage (A.kernel (mszGridTime k 0 0))
                (f : ℤ → ℂ) x‖ := norm_add_le _ _
          _ ≤ (mszFiniteShortBlockVariation A k L
                (f : ℤ → ℂ) x).toReal + G x := add_le_add hinc hbase
          _ ≤ V x + G x := add_le_add hblock le_rfl
          _ = G x + V x := by ring
      simpa [g] using hvalue
    have hGmeas : AEStronglyMeasurable (fun x : ℤ => G x) Measure.count :=
      (measurable_of_countable _).aestronglyMeasurable
    have hgmeas : AEStronglyMeasurable (fun x : ℤ => g x) Measure.count :=
      (measurable_of_countable _).aestronglyMeasurable
    have hVmeas : AEStronglyMeasurable V Measure.count :=
      (measurable_of_countable V).aestronglyMeasurable
    have hgnonneg (x : ℤ) : 0 ≤ g x := by
      have hsup : mszFiniteGridMaximalSequence A K L f x =
          (mszFiniteTimeGrid K L).sup'
            (mszFiniteTimeGrid_nonempty K L)
            (fun t => ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖) := by
        simpa [pENN, mszQExponent] using
          mszFiniteGridMaximalSequence_apply A K L f x
      rw [hsup]
      obtain ⟨t, ht, heq⟩ := Finset.exists_mem_eq_sup'
        (mszFiniteTimeGrid_nonempty K L)
        (fun t => ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖)
      rw [heq]
      exact norm_nonneg _
    have hMle : eLpNorm (fun x : ℤ => g x) pENN Measure.count ≤
        eLpNorm (fun x : ℤ => G x + V x) pENN Measure.count := by
      apply eLpNorm_mono_real hgmeas
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (hgnonneg x)]
      exact hpoint x
    have hTriangle :
        eLpNorm (fun x : ℤ => G x + V x) pENN Measure.count ≤
          eLpNorm (fun x : ℤ => G x) pENN Measure.count +
            eLpNorm V pENN Measure.count := by
      exact eLpNorm_add_le hpOne
    have hGbound : eLpNorm (fun x : ℤ => G x) pENN Measure.count ≤
        ENNReal.ofReal (A.Mq * ‖f‖) := by
      rw [msz_eLpNorm_lp_raw_eq_norm hp G]
      exact ENNReal.ofReal_le_ofReal hGnorm
    have hVnorm : eLpNorm V pENN Measure.count ≤
        ENNReal.ofReal (H * B ^ ((2 - A.q) / 2) * ‖f‖) := by
      rw [msz_eLpNorm_complexLp_raw_eq_norm hp f] at hVbound
      have hcoeff : 0 ≤ H * B ^ ((2 - A.q) / 2) :=
        mul_nonneg hHnonneg (Real.rpow_nonneg hBnonneg _)
      rw [ENNReal.ofReal_mul hcoeff]
      exact hVbound
    have hsum : eLpNorm (fun x : ℤ => G x + V x) pENN Measure.count ≤
        ENNReal.ofReal (C * ‖f‖) := by
      calc
        _ ≤ eLpNorm (fun x : ℤ => G x) pENN Measure.count +
            eLpNorm V pENN Measure.count := hTriangle
        _ ≤ ENNReal.ofReal (A.Mq * ‖f‖) +
            ENNReal.ofReal (H * B ^ ((2 - A.q) / 2) * ‖f‖) :=
              add_le_add hGbound hVnorm
        _ = ENNReal.ofReal (C * ‖f‖) := by
          rw [← ENNReal.ofReal_add]
          · congr 1
            dsimp [C]
            ring
          · exact mul_nonneg A.Mq_nonneg (norm_nonneg f)
          · exact mul_nonneg
              (mul_nonneg hHnonneg (Real.rpow_nonneg hBnonneg _))
              (norm_nonneg f)
    have hMbound : eLpNorm (fun x : ℤ => g x) pENN Measure.count ≤
        ENNReal.ofReal (C * ‖f‖) := hMle.trans hsum
    rw [msz_eLpNorm_lp_raw_eq_norm hp g] at hMbound
    have hscaled : C * ‖f‖ ≤ C := mul_le_of_le_one_right hCnonneg hf
    exact hMbound.trans (ENNReal.ofReal_le_ofReal hscaled)
  let S : Set ℝ≥0∞ := {r | ∃ f : lp (fun _ : ℤ => ℂ) pENN,
    ‖f‖ ≤ 1 ∧ r = ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖}
  have hnonempty : S.Nonempty := by
    refine ⟨ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L (0 :
      lp (fun _ : ℤ => ℂ) pENN)‖, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hbounded : ∀ r ∈ S, r ≤ ENNReal.ofReal C := by
    intro r hr
    rcases hr with ⟨f, hf, rfl⟩
    exact hunit f hf
  have hN : mszFiniteGridMaximalNorm A K L ≤ ENNReal.ofReal C := by
    change sSup S ≤ ENNReal.ofReal C
    exact csSup_le hnonempty hbounded
  simpa [C, H, B, pENN, mszQExponent] using hN

/-- The finite-grid maximal constants are uniformly bounded by the exact
scalar bootstrap constant from `lm:bootstrap`. -/
theorem mszFiniteGridMaximalConstant_le_bootstrap
    (A : AdmissibleData) (K L : ℕ) :
    mszFiniteGridMaximalConstant A K L ≤
      max (2 * (1 + A.Mq))
        ((2 * (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A)) ^
          (2 / A.q)) := by
  let B : ℝ := mszFiniteGridMaximalConstant A K L
  let H : ℝ := Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A
  let α : ℝ := (2 - A.q) / 2
  let b : ℝ := 1 + A.Mq
  have hKnonneg : 0 ≤ mszLocalizedGridKq A := by
    unfold mszLocalizedGridKq
    split_ifs with hq2
    · have hq2pos : 0 < 2 - A.q := sub_pos.mpr hq2
      have hr_lt : localInterpolationR A.q < A.q := by
        unfold localInterpolationR
        have hqPos : 0 < A.q := lt_trans zero_lt_one A.q_gt_one
        have hden : 0 < A.q + 1 := add_pos_of_pos_of_nonneg hqPos (by norm_num)
        rw [div_lt_iff₀ hden]
        nlinarith [mul_pos hqPos (sub_pos.mpr A.q_gt_one)]
      have hqPrimePos : 0 < localInterpolationQPrime A.q := by
        unfold localInterpolationQPrime
        exact div_pos (lt_trans zero_lt_one A.q_gt_one)
          (sub_pos.mpr A.q_gt_one)
      have hqPrimeGtTwo : 2 < localInterpolationQPrime A.q := by
        unfold localInterpolationQPrime
        rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
        nlinarith [A.q_gt_one, hq2]
      have hrPrimeEq : localInterpolationRPrime A.q =
          2 * localInterpolationQPrime A.q := by
        unfold localInterpolationRPrime localInterpolationQPrime
        field_simp [ne_of_gt (sub_pos.mpr A.q_gt_one)]
      have hden1 : 0 < A.q - localInterpolationR A.q := by linarith
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
  have hsigmaNonneg : 0 ≤ mszSigmaQ A :=
    tsum_nonneg (fun z => mszSigmaQTerm_nonneg A z)
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hKnonneg)
      hsigmaNonneg
  have hB_one : 1 ≤ B := by
    dsimp [B, mszFiniteGridMaximalConstant]
    exact le_max_left _ _
  have hBnonneg : 0 ≤ B := le_trans (by norm_num) hB_one
  have hαnonneg : 0 ≤ α := by
    dsimp [α]
    linarith [A.q_le_two]
  have hαlt : α < 1 := by
    dsimp [α]
    linarith [A.q_gt_one]
  have hbpos : 0 < b := by
    dsimp [b]
    linarith [A.Mq_nonneg]
  have hpowNonneg : 0 ≤ B ^ α := Real.rpow_nonneg hBnonneg _
  have hcoefNonneg : 0 ≤ H * B ^ α := mul_nonneg hHnonneg hpowNonneg
  have hCnonneg : 0 ≤ A.Mq + H * B ^ α :=
    add_nonneg A.Mq_nonneg hcoefNonneg
  have hreal : (mszFiniteGridMaximalNorm A K L).toReal ≤
      A.Mq + H * B ^ α := by
    have h := ENNReal.toReal_mono
      ENNReal.ofReal_ne_top
      (mszFiniteGridMaximalNorm_bootstrap_ineq A K L)
    rw [ENNReal.toReal_ofReal hCnonneg] at h
    simpa [H, B, α, mul_assoc, mul_left_comm, mul_comm] using h
  have hBineq : B ≤ b + H * B ^ α := by
    have hfirst : 1 ≤ b + H * B ^ α := by
      have hb : 1 ≤ b := by dsimp [b]; linarith [A.Mq_nonneg]
      exact hb.trans (le_add_of_nonneg_right hcoefNonneg)
    have hsecond : (mszFiniteGridMaximalNorm A K L).toReal ≤
        b + H * B ^ α := by
      calc
        _ ≤ A.Mq + H * B ^ α := hreal
        _ ≤ b + H * B ^ α := by dsimp [b]; linarith
    dsimp [B, mszFiniteGridMaximalConstant]
    exact max_le hfirst hsecond
  have hpower : scalarBootstrapPower B α = B ^ α := by
    unfold scalarBootstrapPower
    split_ifs with hzero
    · rw [hzero]
      simp
    · rfl
  have hscalar := scalarBootstrap hBnonneg hbpos hHnonneg
    hαnonneg hαlt (by simpa [hpower] using hBineq)
  have hexponent : 1 / (1 - α) = 2 / A.q := by
    dsimp [α]
    have hqpos : A.q ≠ 0 := ne_of_gt (lt_trans zero_lt_one A.q_gt_one)
    field_simp [hqpos]
    <;> ring
  simpa [B, H, b, α, hexponent] using hscalar

private theorem mszFiniteGridBootstrap_Kq_nonneg (A : AdmissibleData) :
    0 ≤ mszLocalizedGridKq A := by
  unfold mszLocalizedGridKq
  split_ifs with hq2
  · have hq2pos : 0 < 2 - A.q := sub_pos.mpr hq2
    have hr_lt : localInterpolationR A.q < A.q := by
      unfold localInterpolationR
      have hqPos : 0 < A.q := lt_trans zero_lt_one A.q_gt_one
      have hden : 0 < A.q + 1 := add_pos_of_pos_of_nonneg hqPos (by norm_num)
      rw [div_lt_iff₀ hden]
      nlinarith [mul_pos hqPos (sub_pos.mpr A.q_gt_one)]
    have hqPrimePos : 0 < localInterpolationQPrime A.q := by
      unfold localInterpolationQPrime
      exact div_pos (lt_trans zero_lt_one A.q_gt_one)
        (sub_pos.mpr A.q_gt_one)
    have hqPrimeGtTwo : 2 < localInterpolationQPrime A.q := by
      unfold localInterpolationQPrime
      rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
      nlinarith [A.q_gt_one, hq2]
    have hrPrimeEq : localInterpolationRPrime A.q =
        2 * localInterpolationQPrime A.q := by
      unfold localInterpolationRPrime localInterpolationQPrime
      field_simp [ne_of_gt (sub_pos.mpr A.q_gt_one)]
    have hden1 : 0 < A.q - localInterpolationR A.q := by linarith
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

/-- Uniform finite-grid short-variation estimate at either exact exponent
from `lm:finiteVariation`, after the maximal bootstrap but before the global
monotone-limit step in `lm:main`. -/
theorem mszFiniteShortVariation_uniform
    (A : AdmissibleData) (K L : ℕ) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    eLpNorm (fun x : ℤ => mszFiniteShortVariation A K L (f : ℤ → ℂ) x)
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
          ((Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A) *
            (max (2 * (1 + A.Mq))
              ((2 * (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A)) ^
                (2 / A.q))) ^ ((2 - A.q) / 2)) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
  let H : ℝ := Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A
  let α : ℝ := (2 - A.q) / 2
  let B : ℝ := mszFiniteGridMaximalConstant A K L
  let B₀ : ℝ := max (2 * (1 + A.Mq)) ((2 * H) ^ (2 / A.q))
  have hKnonneg := mszFiniteGridBootstrap_Kq_nonneg A
  have hsigmaNonneg : 0 ≤ mszSigmaQ A :=
    tsum_nonneg (fun z => mszSigmaQTerm_nonneg A z)
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hKnonneg)
      hsigmaNonneg
  have hBnonneg : 0 ≤ B := by
    dsimp [B, mszFiniteGridMaximalConstant]
    positivity
  have hαnonneg : 0 ≤ α := by
    dsimp [α]
    linarith [A.q_le_two]
  have hB₀nonneg : 0 ≤ B₀ := by
    dsimp [B₀]
    have hleft : 0 ≤ 2 * (1 + A.Mq) :=
      mul_nonneg (by norm_num) (add_nonneg (by norm_num) A.Mq_nonneg)
    exact le_trans hleft (le_max_left _ _)
  have hB₀upper : B ≤ B₀ := by
    simpa [B, H, B₀] using mszFiniteGridMaximalConstant_le_bootstrap A K L
  have hpow : B ^ α ≤ B₀ ^ α := Real.rpow_le_rpow hBnonneg hB₀upper hαnonneg
  have hcoeff :
      Real.sqrt 2 * mszLocalizedGridKq A * B ^ α * mszSigmaQ A ≤
        H * B₀ ^ α := by
    calc
      _ = H * B ^ α := by dsimp [H]; ring
      _ ≤ H * B₀ ^ α := mul_le_mul_of_nonneg_left hpow hHnonneg
  have hcoeffENN : ENNReal.ofReal
      (Real.sqrt 2 * mszLocalizedGridKq A * B ^ α * mszSigmaQ A) ≤
        ENNReal.ofReal (H * B₀ ^ α) := ENNReal.ofReal_le_ofReal hcoeff
  have hfinite := finiteVariationEstimate A K L p hp f
  calc
    _ ≤ ENNReal.ofReal
          (Real.sqrt 2 * mszLocalizedGridKq A * B ^ α * mszSigmaQ A) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
          simpa [B, α, mszFiniteGridMaximalConstant] using hfinite
    _ ≤ ENNReal.ofReal (H * B₀ ^ α) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count :=
      mul_le_mul_of_nonneg_right hcoeffENN bot_le
    _ = _ := by
      simpa [H, B₀, α]

end

end FractionalPrimes.Literature.MSZ

end
