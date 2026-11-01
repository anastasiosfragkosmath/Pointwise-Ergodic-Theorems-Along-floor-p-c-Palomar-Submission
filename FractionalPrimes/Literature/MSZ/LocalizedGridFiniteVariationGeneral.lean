module

public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteVariationEstimate
public import FractionalPrimes.Literature.Multiplier.FiniteSupportDensity
public import Mathlib.Topology.Order.Lattice
public import FractionalPrimes.Literature.MSZ.FiniteGridMaximalData
public import FractionalPrimes.Literature.MSZ.LocalizedGridCountableFatouCore

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

private abbrev mszFiniteDyadicChain (L : ℕ) :=
  Σ n : Fin (2 ^ L + 1), Fin (n.val + 1) → Fin (2 ^ L + 1)

private def mszFiniteDyadicChainScore (L : ℕ)
    (g : Fin (2 ^ L + 1) → ℂ) (c : mszFiniteDyadicChain L) : ℝ≥0∞ :=
  if 0 < c.1.val ∧ StrictMono (fun i => (c.2 i).val) then
    ENNReal.ofReal (Real.sqrt (∑ i : Fin c.1.val,
      ‖g (c.2 i.succ) - g (c.2 i.castSucc)‖ ^ 2))
  else 0

private def mszGridPointSubtype (L m : ℕ) (hm : m ≤ 2 ^ L) :
    {t : ℚ // t ∈ dyadicGridTimes L} :=
  ⟨dyadicGridPoint L m, ⟨m, hm, rfl⟩⟩

private def mszGridSubtypeValues (L : ℕ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ) :
    Fin (2 ^ L + 1) → ℂ :=
  fun m => dyadicGridExtend L g (dyadicGridPoint L m.val)

private theorem msz_dyadicGridVariationTwoSubtype_eq_finiteSup
    (L : ℕ) (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ) :
    dyadicGridVariationTwoSubtype L g =
      Finset.univ.sup (mszFiniteDyadicChainScore L (mszGridSubtypeValues L g)) := by
  classical
  rw [dyadicGridVariationTwoSubtype, dyadicGridVariationTwo_eq_index]
  let M : ℕ := 2 ^ L
  change (⨆ N : ℕ, ⨆ u : Fin (N + 1) → ℕ,
      if h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ M then
        ENNReal.ofReal (Real.sqrt (∑ i : Fin N,
          ‖dyadicGridExtend L g (dyadicGridPoint L (u i.succ)) -
            dyadicGridExtend L g (dyadicGridPoint L (u i.castSucc))‖ ^ 2))
      else 0) = _
  apply le_antisymm
  · apply iSup_le
    intro N
    apply iSup_le
    intro u
    by_cases h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ M
    · have huInjective : Function.Injective u := h.2.1.injective
      let v : Fin (N + 1) → Fin (M + 1) := fun i =>
        ⟨u i, by have := h.2.2 i; omega⟩
      have hvInjective : Function.Injective v := by
        intro i j hij
        apply huInjective
        exact congrArg Fin.val hij
      have hcard : N + 1 ≤ M + 1 := by
        have hcard' := Fintype.card_le_of_injective v hvInjective
        simpa using hcard'
      have hNM : N ≤ M := by omega
      let n : Fin (M + 1) := ⟨N, by omega⟩
      let c : mszFiniteDyadicChain L := ⟨n, v⟩
      have hc : 0 < c.1.val ∧ StrictMono (fun i => (c.2 i).val) := by
        refine ⟨h.1, ?_⟩
        intro i j hij
        exact h.2.1 hij
      have hscore : mszFiniteDyadicChainScore L
          (mszGridSubtypeValues L g) c =
          ENNReal.ofReal (Real.sqrt (∑ i : Fin N,
            ‖dyadicGridExtend L g (dyadicGridPoint L (u i.succ)) -
              dyadicGridExtend L g (dyadicGridPoint L (u i.castSucc))‖ ^ 2)) := by
        rw [mszFiniteDyadicChainScore, if_pos hc]
        rfl
      have hle : mszFiniteDyadicChainScore L
          (mszGridSubtypeValues L g) c ≤
          Finset.univ.sup (mszFiniteDyadicChainScore L
            (mszGridSubtypeValues L g)) :=
        Finset.le_sup (Finset.mem_univ c)
      rw [dif_pos h]
      calc
        _ = mszFiniteDyadicChainScore L
            (mszGridSubtypeValues L g) c := hscore.symm
        _ ≤ Finset.univ.sup (mszFiniteDyadicChainScore L
            (mszGridSubtypeValues L g)) := hle
    · simp [h]
  · apply Finset.sup_le
    intro c hc
    by_cases h : 0 < c.1.val ∧ StrictMono (fun i => (c.2 i).val)
    · let N : ℕ := c.1.val
      let u : Fin (N + 1) → ℕ := fun i => (c.2 i).val
      have hu : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ M := by
        refine ⟨h.1, h.2, ?_⟩
        intro i
        exact Nat.lt_succ_iff.mp (by simpa [u, M] using (c.2 i).isLt)
      have hscore : mszFiniteDyadicChainScore L
          (mszGridSubtypeValues L g) c =
          ENNReal.ofReal (Real.sqrt (∑ i : Fin N,
            ‖dyadicGridExtend L g (dyadicGridPoint L (u i.succ)) -
              dyadicGridExtend L g (dyadicGridPoint L (u i.castSucc))‖ ^ 2)) := by
        rw [mszFiniteDyadicChainScore, if_pos h]
        rfl
      rw [hscore]
      apply le_iSup_of_le N
      apply le_iSup_of_le u
      rw [dif_pos hu]
    · unfold mszFiniteDyadicChainScore
      rw [if_neg h]
      exact bot_le

private theorem mszFiniteDyadicChainScore_continuous
    (L : ℕ) (c : mszFiniteDyadicChain L) :
    Continuous (fun g : Fin (2 ^ L + 1) → ℂ =>
      mszFiniteDyadicChainScore L g c) := by
  by_cases h : 0 < c.1.val ∧ StrictMono (fun i => (c.2 i).val)
  · simp only [mszFiniteDyadicChainScore, if_pos h]
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_sqrt.comp
    fun_prop
  · have hconst : (fun g : Fin (2 ^ L + 1) → ℂ =>
        mszFiniteDyadicChainScore L g c) = fun _ => (0 : ℝ≥0∞) := by
      funext g
      unfold mszFiniteDyadicChainScore
      exact if_neg h
    rw [hconst]
    exact continuous_const

private theorem msz_dyadicGridVariationTwoSubtype_tendsto
    (L : ℕ) (gseq : ℕ → {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ)
    (hgrid : ∀ t, Tendsto (fun n => gseq n t) atTop (𝓝 (g t))) :
    Tendsto (fun n => dyadicGridVariationTwoSubtype L (gseq n)) atTop
      (𝓝 (dyadicGridVariationTwoSubtype L g)) := by
  classical
  have hvec : Tendsto (fun n => mszGridSubtypeValues L (gseq n)) atTop
      (𝓝 (mszGridSubtypeValues L g)) := by
    apply tendsto_pi_nhds.2
    intro m
    have hm : m.val ≤ 2 ^ L := Nat.lt_succ_iff.mp m.isLt
    let t := mszGridPointSubtype L m.val hm
    have ht := hgrid t
    have hmap : (fun n => mszGridSubtypeValues L (gseq n) m) =
        fun n => gseq n t := by
      funext n
      dsimp [mszGridSubtypeValues, mszGridPointSubtype]
      rw [dyadicGridExtend_of_mem L (gseq n) ⟨m.val, hm, rfl⟩]
      exact congrArg (gseq n) (Subtype.ext rfl)
    have hlim : mszGridSubtypeValues L g m = g t := by
      dsimp [mszGridSubtypeValues, mszGridPointSubtype]
      rw [dyadicGridExtend_of_mem L g ⟨m.val, hm, rfl⟩]
      exact congrArg g (Subtype.ext rfl)
    rw [hmap, hlim]
    exact ht
  have hcont : Continuous (fun v : Fin (2 ^ L + 1) → ℂ =>
      Finset.univ.sup (mszFiniteDyadicChainScore L v)) := by
    exact Continuous.finset_sup_apply
      (s := (Finset.univ : Finset (mszFiniteDyadicChain L)))
      (f := fun c v => mszFiniteDyadicChainScore L v c)
      (fun c hc => mszFiniteDyadicChainScore_continuous L c)
  have hmax : Tendsto
      (fun n => Finset.univ.sup
        (mszFiniteDyadicChainScore L (mszGridSubtypeValues L (gseq n)))) atTop
      (𝓝 (Finset.univ.sup
        (mszFiniteDyadicChainScore L (mszGridSubtypeValues L g)))) := by
    convert (hcont.tendsto (mszGridSubtypeValues L g)).comp hvec using 1 <;> rfl
  simpa only [msz_dyadicGridVariationTwoSubtype_eq_finiteSup] using hmax

private noncomputable def mszKernelSequenceOperatorAt
    {P : ℝ≥0∞} (hp0 : P ≠ 0) (hpTop : P ≠ ∞)
    [Fact (1 ≤ P)] (K : MSZKernel) :
    lp (fun _ : ℤ => ℂ) P →ₗ[ℂ] lp (fun _ : ℤ => ℂ) P := by
  exact (countLpToGeneralLp hp0 hpTop).comp
    ((integerKernelLpConvolutionCLM (p := P) K.toIntegerL1Kernel).toLinearMap.comp
      (generalLpToCountLp hp0 hpTop))

private theorem mszKernelSequenceOperatorAt_norm_le
    {P : ℝ≥0∞} (hp0 : P ≠ 0) (hpTop : P ≠ ∞)
    [Fact (1 ≤ P)] (K : MSZKernel)
    (f : lp (fun _ : ℤ => ℂ) P) :
    ‖mszKernelSequenceOperatorAt hp0 hpTop K f‖ ≤ ‖f‖ := by
  rw [mszKernelSequenceOperatorAt]
  let hin : Lp ℂ P (Measure.count : Measure ℤ) :=
    generalLpToCountLp hp0 hpTop f
  have hinNorm : ‖hin‖ = ‖f‖ := generalLpToCountLp_norm hp0 hpTop f
  change ‖countLpToGeneralLp hp0 hpTop
      (integerKernelLpConvolutionCLM (p := P) K.toIntegerL1Kernel hin)‖ ≤ ‖f‖
  rw [countLpToGeneralLp_norm]
  calc
    ‖integerKernelLpConvolutionCLM (p := P) K.toIntegerL1Kernel hin‖ ≤
        (∑' n : ℤ, ‖K.toIntegerL1Kernel.coeff n‖) * ‖hin‖ :=
          integerKernelLpConvolutionCLM_norm_le _ _
    _ ≤ 1 * ‖f‖ := by
      exact mul_le_mul (mszKernel_complexMass_le_one K) hinNorm.le
        (norm_nonneg _) (by positivity)
    _ = ‖f‖ := by ring

private theorem mszKernelSequenceOperatorAt_apply
    {P : ℝ≥0∞} (hp0 : P ≠ 0) (hpTop : P ≠ ∞)
    [Fact (1 ≤ P)] (K : MSZKernel)
    (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    mszKernelSequenceOperatorAt hp0 hpTop K f x =
      mszKernelAverage K (f : ℤ → ℂ) x := by
  change (countLpToGeneralLp hp0 hpTop
      (integerKernelLpConvolutionCLM (p := P) K.toIntegerL1Kernel
        (generalLpToCountLp hp0 hpTop f))) x = _
  rw [countLpToGeneralLp_apply, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  have hf : (generalLpToCountLp hp0 hpTop f : ℤ → ℂ) = f := by
    funext n
    exact generalLpToCountLp_apply hp0 hpTop f n
  rw [hf]
  rfl

private theorem mszKernelAverage_spatialTruncation_tendsto
    {P : ℝ≥0∞} (hp0 : P ≠ 0) (hpTop : P ≠ ∞)
    [Fact (1 ≤ P)] (K : MSZKernel)
    (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    Tendsto (fun N : ℕ => mszKernelAverage K
      (Multiplier.finiteSupportLpTruncation (P := P)
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) f : ℤ → ℂ) x)
      atTop (𝓝 (mszKernelAverage K (f : ℤ → ℂ) x)) := by
  let trunc : ℕ → lp (fun _ : ℤ => ℂ) P := fun N =>
    Multiplier.finiteSupportLpTruncation (P := P)
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  have htrunc : Tendsto trunc atTop (𝓝 f) :=
    Multiplier.finiteSupportLpTruncation_Icc_tendsto hpTop f
  have hop : ∀ N,
      ‖mszKernelSequenceOperatorAt hp0 hpTop K (trunc N) -
          mszKernelSequenceOperatorAt hp0 hpTop K f‖ ≤
        ‖trunc N - f‖ := by
    intro N
    have hdiff : mszKernelSequenceOperatorAt hp0 hpTop K (trunc N) -
        mszKernelSequenceOperatorAt hp0 hpTop K f =
        mszKernelSequenceOperatorAt hp0 hpTop K (trunc N - f) := by
      simp only [map_sub]
    rw [hdiff]
    exact mszKernelSequenceOperatorAt_norm_le hp0 hpTop K _
  have hoperator : Tendsto
      (fun N => mszKernelSequenceOperatorAt hp0 hpTop K (trunc N))
      atTop (𝓝 (mszKernelSequenceOperatorAt hp0 hpTop K f)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp htrunc) ε hε] with N hN
    have hdist : dist
        (mszKernelSequenceOperatorAt hp0 hpTop K (trunc N))
        (mszKernelSequenceOperatorAt hp0 hpTop K f) ≤ dist (trunc N) f := by
      rw [dist_eq_norm, dist_eq_norm]
      exact hop N
    exact lt_of_le_of_lt hdist hN
  have heval := (lp.lipschitzWith_one_eval (p := P) x).continuous.tendsto
    (mszKernelSequenceOperatorAt hp0 hpTop K f)
  have hpoint : Tendsto
      (fun N => mszKernelSequenceOperatorAt hp0 hpTop K (trunc N) x)
      atTop (𝓝 (mszKernelSequenceOperatorAt hp0 hpTop K f x)) := by
    have hcomp := heval.comp hoperator
    change Tendsto
      (fun N => mszKernelSequenceOperatorAt hp0 hpTop K (trunc N) x)
      atTop (𝓝 (mszKernelSequenceOperatorAt hp0 hpTop K f x)) at hcomp
    exact hcomp
  simpa only [trunc, mszKernelSequenceOperatorAt_apply] using hpoint

private theorem msz_eLpNorm_lp_raw_eq_norm
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

private theorem mszFiniteShortVariation_spatialTruncation_tendsto
    (A : AdmissibleData) (K L : ℕ) {p : ℝ} (hp : 1 < p)
    (hp0 : ENNReal.ofReal p ≠ 0) (hpTop : ENNReal.ofReal p ≠ ∞)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    Tendsto (fun N : ℕ => mszFiniteShortVariation A K L
      (Multiplier.finiteSupportLpTruncation (P := ENNReal.ofReal p)
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) f : ℤ → ℂ) x)
      atTop (𝓝 (mszFiniteShortVariation A K L (f : ℤ → ℂ) x)) := by
  let trunc : ℕ → lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) := fun N =>
    Multiplier.finiteSupportLpTruncation (P := ENNReal.ofReal p)
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  have hblock (k : ℤ) : Tendsto
      (fun N => mszFiniteShortBlockVariation A k L (trunc N : ℤ → ℂ) x)
      atTop (𝓝 (mszFiniteShortBlockVariation A k L (f : ℤ → ℂ) x)) := by
    have hgrid : ∀ t : {t : ℚ // t ∈ dyadicGridTimes L},
        Tendsto (fun N => mszFiniteShortBlockValues A k L
          (trunc N : ℤ → ℂ) x t) atTop
          (𝓝 (mszFiniteShortBlockValues A k L (f : ℤ → ℂ) x t)) := by
      intro t
      simpa [mszFiniteShortBlockValues, trunc] using
        mszKernelAverage_spatialTruncation_tendsto hp0 hpTop
          (A.kernel (mszGridTimeAffine k L t)) f x
    simpa only [mszFiniteShortBlockVariation] using
      msz_dyadicGridVariationTwoSubtype_tendsto L
        (fun N t => mszFiniteShortBlockValues A k L
          (trunc N : ℤ → ℂ) x t)
        (fun t => mszFiniteShortBlockValues A k L (f : ℤ → ℂ) x t) hgrid
  have hblockReal (k : ℤ) : Tendsto
      (fun N => (mszFiniteShortBlockVariation A k L (trunc N : ℤ → ℂ) x).toReal)
      atTop
      (𝓝 ((mszFiniteShortBlockVariation A k L (f : ℤ → ℂ) x).toReal)) := by
    exact (ENNReal.continuousAt_toReal
      (mszFiniteShortBlockVariation_ne_top A k L (f : ℤ → ℂ) x)).tendsto.comp
        (hblock k)
  let Kset := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let ι := {k : ℤ // k ∈ Kset}
  let blockVector : ℕ → ι → ℝ := fun N k =>
    (mszFiniteShortBlockVariation A k.1 L (trunc N : ℤ → ℂ) x).toReal
  let blockLimit : ι → ℝ := fun k =>
    (mszFiniteShortBlockVariation A k.1 L (f : ℤ → ℂ) x).toReal
  have hvec : Tendsto blockVector atTop (𝓝 blockLimit) := by
    apply tendsto_pi_nhds.2
    intro k
    exact hblockReal k.1
  have hcont : Continuous (fun v : ι → ℝ =>
      Real.sqrt (∑ k : ι, v k ^ 2)) := by
    fun_prop
  have hshortVector : Tendsto
      (fun N => Real.sqrt (∑ k : ι, blockVector N k ^ 2)) atTop
      (𝓝 (Real.sqrt (∑ k : ι, blockLimit k ^ 2))) := by
    have hcomp := (hcont.tendsto blockLimit).comp hvec
    change Tendsto
      (fun N => Real.sqrt (∑ k : ι, blockVector N k ^ 2)) atTop
      (𝓝 (Real.sqrt (∑ k : ι, blockLimit k ^ 2))) at hcomp
    exact hcomp
  have hsum (g : ℤ → ℂ) :
      (∑ k ∈ Kset, (mszFiniteShortBlockVariation A k L g x).toReal ^ 2) =
        ∑ k : ι, (mszFiniteShortBlockVariation A k.1 L g x).toReal ^ 2 := by
    symm
    exact Finset.sum_coe_sort Kset
      (fun k : ℤ => (mszFiniteShortBlockVariation A k L g x).toReal ^ 2)
  have hfun : (fun N => mszFiniteShortVariation A K L
      (trunc N : ℤ → ℂ) x) =
      (fun N => Real.sqrt (∑ k : ι, blockVector N k ^ 2)) := by
    funext N
    simp only [mszFiniteShortVariation]
    exact congrArg Real.sqrt (hsum (trunc N : ℤ → ℂ))
  have hlim : mszFiniteShortVariation A K L (f : ℤ → ℂ) x =
      Real.sqrt (∑ k : ι, blockLimit k ^ 2) := by
    simp only [mszFiniteShortVariation]
    exact congrArg Real.sqrt (hsum (f : ℤ → ℂ))
  change Tendsto (fun N => mszFiniteShortVariation A K L
      (trunc N : ℤ → ℂ) x) atTop
    (𝓝 (mszFiniteShortVariation A K L (f : ℤ → ℂ) x))
  rw [hfun, hlim]
  exact hshortVector

/-- The source finite-variation estimate for every sequence in either
localized interpolation exponent.  The proof removes the finite-support
restriction by symmetric spatial truncation, contractivity of each positive
kernel average on the full exponent, finite-grid continuity of variation,
and counting-measure Fatou. -/
theorem finiteVariationEstimate
    (A : AdmissibleData) (K L : ℕ) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    eLpNorm (fun x : ℤ => mszFiniteShortVariation A K L (f : ℤ → ℂ) x)
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
          (Real.sqrt 2 * mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            mszSigmaQ A) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
  classical
  have hqPrime : 1 < A.q / (A.q - 1) := by
    rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
    linarith
  have hpOne : 1 < p := by
    rcases hp with hpq | hpq'
    · rw [hpq]
      exact A.q_gt_one
    · rw [hpq']
      exact hqPrime
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hpOne)
  have hPTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  letI : Fact (1 ≤ P) := ⟨by
    dsimp [P]
    exact (ENNReal.one_le_ofReal).2 hpOne.le⟩
  let trunc : ℕ → lp (fun _ : ℤ => ℂ) P := fun N =>
    Multiplier.finiteSupportLpTruncation (P := P)
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) f
  let truncFn : ℕ → ℤ → ℂ := fun N => trunc N
  have htruncSupport (N : ℕ) : (truncFn N).HasFiniteSupport := by
    change (Function.support (truncFn N)).Finite
    dsimp [truncFn, trunc]
    exact (Finset.Icc (-(N : ℤ)) (N : ℤ)).finite_toSet.subset
      (Multiplier.finiteSupportLpTruncation_support_subset (P := P)
        (Finset.Icc (-(N : ℤ)) (N : ℤ)) f)
  have htruncNorm (N : ℕ) : ‖trunc N‖ ≤ ‖f‖ := by
    apply lp.norm_mono hP0
    intro x
    rw [Multiplier.finiteSupportLpTruncation_apply]
    by_cases hx : x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) <;> simp [hx]
  have hinputBound (N : ℕ) :
      eLpNorm (truncFn N) P Measure.count ≤
        eLpNorm (fun x : ℤ => f x) P Measure.count := by
    rw [msz_eLpNorm_lp_raw_eq_norm (p := p) hpOne (trunc N),
      msz_eLpNorm_lp_raw_eq_norm (p := p) hpOne f]
    exact ENNReal.ofReal_le_ofReal (htruncNorm N)
  let C : ℝ := Real.sqrt 2 * mszLocalizedGridKq A *
      (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
      mszSigmaQ A
  let CENN : ℝ≥0∞ := ENNReal.ofReal C
  have hbound (N : ℕ) :
      eLpNorm (fun x : ℤ => mszFiniteShortVariation A K L (truncFn N) x)
          P Measure.count ≤
        CENN * eLpNorm (fun x : ℤ => f x) P Measure.count := by
    have hfinite := mszFiniteVariationEstimate_finiteSupport A K L p hp
      (truncFn N) (htruncSupport N)
    have hscaled : CENN * eLpNorm (truncFn N) P Measure.count ≤
        CENN * eLpNorm (fun x : ℤ => f x) P Measure.count := by
      have hmul := mul_le_mul_left (hinputBound N) CENN
      simpa [mul_comm] using hmul
    calc
      _ ≤ ENNReal.ofReal
          (Real.sqrt 2 * mszLocalizedGridKq A *
            (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
            mszSigmaQ A) * eLpNorm (truncFn N) P Measure.count := by
              simpa [P, truncFn] using hfinite
      _ ≤ CENN * eLpNorm (fun x : ℤ => f x) P Measure.count := by
              simpa [CENN, C] using hscaled
  have hpoint (x : ℤ) : Tendsto
      (fun N => mszFiniteShortVariation A K L (truncFn N) x) atTop
      (𝓝 (mszFiniteShortVariation A K L (f : ℤ → ℂ) x)) := by
    simpa [truncFn, trunc, P] using
      mszFiniteShortVariation_spatialTruncation_tendsto A K L hpOne
        hP0 hPTop f x
  have hfatou := msz_counting_eLpNorm_le_of_pointwise_limit_core
    (approximant := fun N x => mszFiniteShortVariation A K L (truncFn N) x)
    (limit := fun x => mszFiniteShortVariation A K L (f : ℤ → ℂ) x)
    (CENN * eLpNorm (fun x : ℤ => f x) P Measure.count)
    hbound hpoint
  simpa [P, CENN, C] using hfatou

end

end FractionalPrimes.Literature.MSZ

end
