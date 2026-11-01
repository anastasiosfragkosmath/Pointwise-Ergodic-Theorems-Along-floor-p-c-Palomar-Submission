module

public import FractionalPrimes.Literature.MSZ.AdmissibleData
public import FractionalPrimes.Literature.MSZ.FiniteGridEndpoint
public import FractionalPrimes.GeneralDiscreteLpBridge

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The finite real exponent used by the approved MSZ data, as an `ENNReal`
exponent for the project's `Lp` and sequence spaces. -/
def mszQExponent (A : AdmissibleData) : ℝ≥0∞ := ENNReal.ofReal A.q

theorem mszQExponent_pos (A : AdmissibleData) : 0 < A.q :=
  lt_trans zero_lt_one A.q_gt_one

theorem mszQExponent_ne_zero (A : AdmissibleData) :
    mszQExponent A ≠ 0 := by
  rw [mszQExponent, ENNReal.ofReal_ne_zero_iff]
  exact mszQExponent_pos A

theorem mszQExponent_ne_top (A : AdmissibleData) :
    mszQExponent A ≠ ∞ := by
  simp [mszQExponent]

theorem mszQExponent_ge_one (A : AdmissibleData) :
    1 ≤ mszQExponent A := by
  rw [mszQExponent]
  calc
    1 = ENNReal.ofReal 1 := by norm_num
    _ ≤ ENNReal.ofReal A.q := ENNReal.ofReal_le_ofReal A.q_gt_one.le

/-- The convolution action of one admissible MSZ kernel on the sequence
`ℓ^q` space, transported through the exact counting-measure bridge. -/
noncomputable def mszKernelSequenceOperator (A : AdmissibleData)
    (t : MSZTime) : lp (fun _ : ℤ => ℂ) (mszQExponent A) →ₗ[ℂ]
      lp (fun _ : ℤ => ℂ) (mszQExponent A) := by
  let p := mszQExponent A
  letI : Fact (1 ≤ p) := ⟨mszQExponent_ge_one A⟩
  exact (countLpToGeneralLp (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A)).comp
    ((integerKernelLpConvolutionCLM (p := p)
      (A.kernel t).toIntegerL1Kernel).toLinearMap.comp
      (generalLpToCountLp (mszQExponent_ne_zero A)
        (mszQExponent_ne_top A)))

theorem mszKernel_complexMass_le_one (K : MSZKernel) :
    (∑' n : ℤ, ‖(K.toIntegerL1Kernel).coeff n‖) ≤ 1 := by
  have hsum : (∑' n : ℤ, ‖(K.toIntegerL1Kernel).coeff n‖) =
      ∑' n : ℤ, K.coeff n := by
    apply tsum_congr
    intro n
    rw [MSZKernel.toIntegerL1Kernel, Complex.norm_real,
      Real.norm_of_nonneg (K.nonneg n)]
  rw [hsum]
  exact K.mass_le_one

/-- Every admissible kernel acts contractively on the precise `ℓ^q`
sequence space. -/
theorem mszKernelSequenceOperator_norm_le (A : AdmissibleData)
    (t : MSZTime) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) :
    ‖mszKernelSequenceOperator A t f‖ ≤ ‖f‖ := by
  let p := mszQExponent A
  letI : Fact (1 ≤ p) := ⟨mszQExponent_ge_one A⟩
  rw [mszKernelSequenceOperator]
  let hin : Lp ℂ p (Measure.count : Measure ℤ) :=
    generalLpToCountLp (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A) f
  have hin_norm : ‖hin‖ = ‖f‖ :=
    generalLpToCountLp_norm (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A) f
  change ‖countLpToGeneralLp (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A)
      ((integerKernelLpConvolutionCLM (p := p)
        (A.kernel t).toIntegerL1Kernel) hin)‖ ≤ ‖f‖
  rw [countLpToGeneralLp_norm]
  calc
    ‖integerKernelLpConvolutionCLM (p := p)
        (A.kernel t).toIntegerL1Kernel
        hin‖ ≤
      (∑' n : ℤ, ‖((A.kernel t).toIntegerL1Kernel).coeff n‖) *
        ‖hin‖ :=
            integerKernelLpConvolutionCLM_norm_le _ _
    _ ≤ 1 * ‖f‖ := by
      exact mul_le_mul
        (mszKernel_complexMass_le_one (A.kernel t))
        (le_of_eq hin_norm)
        (norm_nonneg _) (by positivity)
    _ = ‖f‖ := by ring

/-- The approved finite time set `I_{K,L}` is nonempty, since it contains
the dyadic time `1`. -/
theorem mszFiniteTimeGrid_nonempty (K L : ℕ) :
    (mszFiniteTimeGrid K L).Nonempty := by
  refine ⟨mszGridTime 0 L 0, ?_⟩
  apply mszGridTime_mem_finiteTimeGrid K L 0 0 <;> simp

/-- The finite maximal function over precisely `I_{K,L}`, represented in
the real sequence `ℓ^q` space. -/
noncomputable def mszFiniteGridMaximalSequence (A : AdmissibleData)
    (K L : ℕ) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) :
    lp (fun _ : ℤ => ℝ) (mszQExponent A) := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  exact finiteGridMaximalSequence (mszQExponent_ne_zero A)
    (mszQExponent_ne_top A) (mszFiniteTimeGrid K L)
    (mszFiniteTimeGrid_nonempty K L)
    (fun t f => mszKernelSequenceOperator A t f)
    (fun t _ g => mszKernelSequenceOperator_norm_le A t g) f

theorem mszQExponent_toReal (A : AdmissibleData) :
    (mszQExponent A).toReal = A.q := by
  rw [mszQExponent, ENNReal.toReal_ofReal (le_of_lt (mszQExponent_pos A))]

/-- The finite-grid maximal function has the cardinality bound from
`lm:finiteBounds`. -/
theorem mszFiniteGridMaximalSequence_norm_le (A : AdmissibleData)
    (K L : ℕ) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) :
    ‖mszFiniteGridMaximalSequence A K L f‖ ≤
      ((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q) * ‖f‖ := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  have h := finiteGridMaximalSequence_norm_le
    (mszQExponent_ne_zero A) (mszQExponent_ne_top A)
    (mszFiniteTimeGrid K L) (mszFiniteTimeGrid_nonempty K L)
    (fun t f => mszKernelSequenceOperator A t f)
    (fun t _ g => mszKernelSequenceOperator_norm_le A t g) f
  simpa only [mszFiniteGridMaximalSequence, mszQExponent_toReal] using h

/-- The exact extended-real unit-ball supremum `N_{K,L}` from the approved
finite-grid definition. -/
noncomputable def mszFiniteGridMaximalNorm (A : AdmissibleData)
    (K L : ℕ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ f : lp (fun _ : ℤ => ℂ) (mszQExponent A),
    ‖f‖ ≤ 1 ∧ r = ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖}

theorem mszFiniteGridMaximalNorm_le (A : AdmissibleData) (K L : ℕ) :
    mszFiniteGridMaximalNorm A K L ≤
      ENNReal.ofReal (((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q)) := by
  let S : Set ℝ≥0∞ := {r | ∃ f : lp (fun _ : ℤ => ℂ) (mszQExponent A),
    ‖f‖ ≤ 1 ∧ r = ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖}
  have hnonempty : S.Nonempty := by
    refine ⟨ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L (0 :
      lp (fun _ : ℤ => ℂ) (mszQExponent A))‖, ?_⟩
    exact ⟨0, by simp, rfl⟩
  change sSup S ≤ _
  apply csSup_le hnonempty
  rintro r ⟨f, hf, rfl⟩
  have hmax := mszFiniteGridMaximalSequence_norm_le A K L f
  have hnorm : ‖mszFiniteGridMaximalSequence A K L f‖ ≤
      ((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q) := by
    calc
      ‖mszFiniteGridMaximalSequence A K L f‖ ≤
          ((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q) * ‖f‖ := hmax
      _ ≤ ((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q) := by
        exact mul_le_of_le_one_right (by positivity) hf
  exact ENNReal.ofReal_le_ofReal hnorm

theorem mszFiniteGridMaximalNorm_unit_ball_bound (A : AdmissibleData)
    (K L : ℕ) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A))
    (hf : ‖f‖ ≤ 1) :
    ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖ ≤
      mszFiniteGridMaximalNorm A K L := by
  let S : Set ℝ≥0∞ := {r | ∃ g : lp (fun _ : ℤ => ℂ) (mszQExponent A),
    ‖g‖ ≤ 1 ∧ r = ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L g‖}
  let C : ℝ := ((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q)
  have hbound (r : ℝ≥0∞) (hr : r ∈ S) : r ≤ ENNReal.ofReal C := by
    rcases hr with ⟨g, hg, rfl⟩
    have hmax := mszFiniteGridMaximalSequence_norm_le A K L g
    have hnorm : ‖mszFiniteGridMaximalSequence A K L g‖ ≤ C := by
      calc
        ‖mszFiniteGridMaximalSequence A K L g‖ ≤ C * ‖g‖ := hmax
        _ ≤ C := mul_le_of_le_one_right (by positivity) hg
    exact ENNReal.ofReal_le_ofReal hnorm
  have hbdd : BddAbove S := ⟨ENNReal.ofReal C, hbound⟩
  have hmem : ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖ ∈ S :=
    ⟨f, hf, rfl⟩
  change ENNReal.ofReal ‖mszFiniteGridMaximalSequence A K L f‖ ≤ sSup S
  exact le_csSup hbdd hmem

/-- The exact `B_{K,L}=max(1,N_{K,L})` constant in `lm:finiteGrids`, as a
finite real number. -/
noncomputable def mszFiniteGridMaximalConstant (A : AdmissibleData)
    (K L : ℕ) : ℝ := max 1 (mszFiniteGridMaximalNorm A K L).toReal

theorem mszFiniteGridMaximalNorm_ne_top (A : AdmissibleData) (K L : ℕ) :
    mszFiniteGridMaximalNorm A K L ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (mszFiniteGridMaximalNorm_le A K L)

/-- The pointwise real inclusion into the complex sequence space. -/
noncomputable def mszRealLpToComplexLp {p : ℝ≥0∞}
    (f : lp (fun _ : ℤ => ℝ) p) : lp (fun _ : ℤ => ℂ) p :=
  ⟨fun n => (f n : ℂ), (lp.memℓp f).mono'
    (fun n => by rw [Complex.norm_real])⟩

@[simp] theorem mszRealLpToComplexLp_apply {p : ℝ≥0∞}
    (f : lp (fun _ : ℤ => ℝ) p) (n : ℤ) :
    mszRealLpToComplexLp f n = (f n : ℂ) := rfl

theorem mszRealLpToComplexLp_norm {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (f : lp (fun _ : ℤ => ℝ) p) :
    ‖mszRealLpToComplexLp f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow hp (mszRealLpToComplexLp f),
    lp.norm_eq_tsum_rpow hp f]
  congr 1
  apply tsum_congr
  intro n
  simp [Complex.norm_real]

theorem mszKernelSequenceOperator_apply (A : AdmissibleData)
    (t : MSZTime) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) (x : ℤ) :
    mszKernelSequenceOperator A t f x =
      mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  change (countLpToGeneralLp (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A)
      (integerKernelLpConvolutionCLM (p := mszQExponent A)
        (A.kernel t).toIntegerL1Kernel
        (generalLpToCountLp (mszQExponent_ne_zero A)
          (mszQExponent_ne_top A) f))) x = _
  rw [countLpToGeneralLp_apply, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  have hf : (generalLpToCountLp (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A) f : ℤ → ℂ) = f := by
    funext n
    exact generalLpToCountLp_apply (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A) f n
  rw [hf]
  exact rfl

theorem mszFiniteGridMaximalSequence_apply (A : AdmissibleData)
    (K L : ℕ) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) (x : ℤ) :
    mszFiniteGridMaximalSequence A K L f x =
      (mszFiniteTimeGrid K L).sup' (mszFiniteTimeGrid_nonempty K L)
        (fun t => ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖) := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  simp [mszFiniteGridMaximalSequence, finiteGridMaximalSequence,
    mszKernelSequenceOperator_apply]

private theorem finiteSup_mul_of_nonneg {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    s.sup' hs (fun i => c * f i) = c * s.sup' hs f := by
  apply le_antisymm
  · apply Finset.sup'_le hs
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (f := f) hi) hc
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hsup]
    exact Finset.le_sup' (f := fun j => c * f j) hi

/-- The finite-grid maximal function is homogeneous for nonnegative real
scalars, with the scalar acting through the canonical inclusion into `ℂ`. -/
theorem mszFiniteGridMaximalSequence_nonneg_smul (A : AdmissibleData)
    (K L : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) :
    mszFiniteGridMaximalSequence A K L ((c : ℂ) • f) =
      c • mszFiniteGridMaximalSequence A K L f := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  let fc : lp (fun _ : ℤ => ℂ) (mszQExponent A) := (c : ℂ) • f
  apply lp.ext
  funext x
  change mszFiniteGridMaximalSequence A K L fc x =
    c * mszFiniteGridMaximalSequence A K L f x
  have hscale (t : MSZTime) :
      ‖mszKernelAverage (A.kernel t) (fc : ℤ → ℂ) x‖ =
        c * ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖ := by
    have hval := congrArg (fun g : lp (fun _ : ℤ => ℂ) (mszQExponent A) => g x)
      ((mszKernelSequenceOperator A t).map_smul (c : ℂ) f)
    have hval' : mszKernelSequenceOperator A t fc x =
        (c : ℂ) * mszKernelSequenceOperator A t f x := by
      simpa [fc, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using hval
    calc
      ‖mszKernelAverage (A.kernel t) (fc : ℤ → ℂ) x‖ =
          ‖mszKernelSequenceOperator A t fc x‖ := by
            rw [mszKernelSequenceOperator_apply]
      _ = ‖(c : ℂ) * mszKernelSequenceOperator A t f x‖ := by rw [hval']
      _ = c * ‖mszKernelSequenceOperator A t f x‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
      _ = c * ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖ := by
          rw [mszKernelSequenceOperator_apply]
  rw [mszFiniteGridMaximalSequence_apply,
    mszFiniteGridMaximalSequence_apply]
  have hfun :
      (fun t : MSZTime => ‖mszKernelAverage (A.kernel t) (fc : ℤ → ℂ) x‖) =
      fun t => c * ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖ := by
    funext t
    exact hscale t
  rw [hfun]
  exact finiteSup_mul_of_nonneg (mszFiniteTimeGrid K L)
    (mszFiniteTimeGrid_nonempty K L)
    (fun t => ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖) c hc

/-- The finite-grid maximal estimate extends from the unit ball in the
definition of `N_{K,L}` by exact positive homogeneity. -/
theorem mszFiniteGridMaximalSequence_real_norm_le (A : AdmissibleData)
    (K L : ℕ) (h : lp (fun _ : ℤ => ℝ) (mszQExponent A)) :
    ‖mszFiniteGridMaximalSequence A K L (mszRealLpToComplexLp h)‖ ≤
      mszFiniteGridMaximalConstant A K L * ‖h‖ := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  by_cases hc0 : ‖h‖ = 0
  · have hh0 : h = 0 := lp.norm_eq_zero_iff.mp hc0
    subst h
    have hlift : mszRealLpToComplexLp
        (0 : lp (fun _ : ℤ => ℝ) (mszQExponent A)) = 0 := by
      apply lp.ext
      funext n
      rfl
    have hmaxzero : mszFiniteGridMaximalSequence A K L
        (0 : lp (fun _ : ℤ => ℂ) (mszQExponent A)) = 0 := by
      have h := mszFiniteGridMaximalSequence_nonneg_smul A K L 0
        (le_rfl : 0 ≤ (0 : ℝ))
        (0 : lp (fun _ : ℤ => ℂ) (mszQExponent A))
      simpa using h
    rw [hlift, hmaxzero]
    simp [mszFiniteGridMaximalConstant]
  · have hc : 0 < ‖h‖ :=
      lt_of_le_of_ne (norm_nonneg h) (Ne.symm hc0)
    let c : ℝ := ‖h‖
    let f : lp (fun _ : ℤ => ℂ) (mszQExponent A) :=
      mszRealLpToComplexLp h
    let g : lp (fun _ : ℤ => ℂ) (mszQExponent A) :=
      mszRealLpToComplexLp ((c⁻¹ : ℝ) • h)
    have hqpos : 0 < (mszQExponent A).toReal := by
      rw [mszQExponent_toReal]
      exact mszQExponent_pos A
    have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
    have hg_norm : ‖g‖ = 1 := by
      dsimp [g]
      rw [mszRealLpToComplexLp_norm hqpos, norm_smul,
        Real.norm_of_nonneg hcInv]
      dsimp [c]
      exact inv_mul_cancel₀ hc.ne'
    have hg_unit : ‖g‖ ≤ 1 := by rw [hg_norm]
    have hN := mszFiniteGridMaximalNorm_unit_ball_bound A K L g hg_unit
    have hNreal : ‖mszFiniteGridMaximalSequence A K L g‖ ≤
        (mszFiniteGridMaximalNorm A K L).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal
        (mszFiniteGridMaximalNorm_ne_top A K L)).mp hN
    have hNB : ‖mszFiniteGridMaximalSequence A K L g‖ ≤
        mszFiniteGridMaximalConstant A K L := by
      exact hNreal.trans (le_max_right 1 _)
    have hcf : (c : ℂ) • g = f := by
      apply lp.ext
      funext n
      change (c : ℂ) * (((c⁻¹ : ℝ) * h n : ℝ) : ℂ) = (h n : ℂ)
      have hreal : c * (c⁻¹ * h n) = h n := by
        calc
          c * (c⁻¹ * h n) = (c * c⁻¹) * h n := by ring
          _ = h n := by rw [mul_inv_cancel₀ hc.ne', one_mul]
      calc
        (c : ℂ) * (((c⁻¹ : ℝ) * h n : ℝ) : ℂ) =
            ((c * (c⁻¹ * h n) : ℝ) : ℂ) :=
              (Complex.ofReal_mul c (c⁻¹ * h n)).symm
        _ = (h n : ℂ) := congrArg (fun r : ℝ => (r : ℂ)) hreal
    have hmaxscale : mszFiniteGridMaximalSequence A K L f =
        c • mszFiniteGridMaximalSequence A K L g := by
      rw [← hcf]
      exact mszFiniteGridMaximalSequence_nonneg_smul A K L c hc.le g
    calc
      ‖mszFiniteGridMaximalSequence A K L
          (mszRealLpToComplexLp h)‖ =
          ‖mszFiniteGridMaximalSequence A K L f‖ := by rfl
      _ = c * ‖mszFiniteGridMaximalSequence A K L g‖ := by
          rw [hmaxscale, norm_smul, Real.norm_of_nonneg hc.le]
      _ ≤ c * mszFiniteGridMaximalConstant A K L :=
        mul_le_mul_of_nonneg_left hNB hc.le
      _ = mszFiniteGridMaximalConstant A K L * ‖h‖ := by
        dsimp [c]
        ring

/-- For a nonnegative real input, the positive convolution majorant of an
admissible kernel equals the absolute value of its complexified average. -/
theorem mszKernelPositiveConvolution_eq_average_norm (A : AdmissibleData)
    (t : MSZTime) (h : lp (fun _ : ℤ => ℝ) (mszQExponent A))
    (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    integerKernelPositiveConvolution
        (A.kernel t).toIntegerL1Kernel h x =
      ‖mszKernelAverage (A.kernel t) (mszRealLpToComplexLp h) x‖ := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  let K := (A.kernel t).toIntegerL1Kernel
  have hreal (n : ℤ) : (K.coeff n).im = 0 := by
    simp [K, MSZKernel.toIntegerL1Kernel]
  have hnonneg (n : ℤ) : 0 ≤ (K.coeff n).re := by
    simpa [K, MSZKernel.toIntegerL1Kernel] using (A.kernel t).nonneg n
  have hposSeries : integerKernelPositiveConvolution K h x =
      ∑' n : ℤ, (A.kernel t).coeff n * h (x - n) := by
    unfold integerKernelPositiveConvolution
    change (∑' n : ℤ, ‖((A.kernel t).coeff n : ℂ)‖ * h (x - n)) = _
    apply tsum_congr
    intro n
    rw [Complex.norm_real,
      Real.norm_of_nonneg ((A.kernel t).nonneg n)]
  let hLp := generalLpToCountLp (mszQExponent_ne_zero A)
    (mszQExponent_ne_top A) (mszRealLpToComplexLp h)
  have hLpcoe : (hLp : ℤ → ℂ) = mszRealLpToComplexLp h := by
    funext n
    exact generalLpToCountLp_apply (mszQExponent_ne_zero A)
      (mszQExponent_ne_top A) (mszRealLpToComplexLp h) n
  have hinput : IntegerKernelConvolutionExistsAt K
      (mszRealLpToComplexLp h : ℤ → ℂ) x := by
    have hinput' := integerKernelConvolutionExistsAt_of_Lp
      (mszQExponent_ge_one A) K
      hLp x
    rw [hLpcoe] at hinput'
    exact hinput'
  have haverage : mszKernelAverage (A.kernel t)
      (mszRealLpToComplexLp h) x =
      (integerKernelPositiveConvolution K h x : ℂ) := by
    rw [mszKernelAverage, integerKernelConvolution_eq_tsum K
      (mszRealLpToComplexLp h : ℤ → ℂ) x hinput]
    calc
      (∑' n : ℤ, K.coeff n * mszRealLpToComplexLp h (x - n)) =
          ∑' n : ℤ, (((A.kernel t).coeff n * h (x - n) : ℝ) : ℂ) := by
            apply tsum_congr
            intro n
            simp [K, MSZKernel.toIntegerL1Kernel,
              mszRealLpToComplexLp]
      _ = ((∑' n : ℤ, (A.kernel t).coeff n * h (x - n) : ℝ) : ℂ) := by
            rw [← Complex.ofReal_tsum]
      _ = (integerKernelPositiveConvolution K h x : ℂ) := by
            rw [hposSeries]
  rw [haverage, Complex.norm_real,
    Real.norm_of_nonneg
      (integerKernelPositiveConvolution_nonneg hh x)]

/-- Endpoint positive convolutions on `I_{K,L}` are pointwise dominated by
the finite-grid maximal function used in the definition of `N_{K,L}`. -/
theorem mszKernelPositiveConvolution_le_finiteGridMaximalSequence
    (A : AdmissibleData) (K L : ℕ) (t : MSZTime)
    (ht : t ∈ mszFiniteTimeGrid K L)
    (h : lp (fun _ : ℤ => ℝ) (mszQExponent A))
    (hh : ∀ x, 0 ≤ h x) (x : ℤ) :
    integerKernelPositiveConvolution (A.kernel t).toIntegerL1Kernel h x ≤
      mszFiniteGridMaximalSequence A K L (mszRealLpToComplexLp h) x := by
  rw [mszKernelPositiveConvolution_eq_average_norm A t h hh x,
    mszFiniteGridMaximalSequence_apply]
  exact Finset.le_sup' (s := mszFiniteTimeGrid K L)
    (f := fun t => ‖mszKernelAverage (A.kernel t)
      (mszRealLpToComplexLp h : ℤ → ℂ) x‖) ht

/-- The finite-grid maximal majorant is pointwise nonnegative. -/
theorem mszFiniteGridMaximalSequence_nonneg (A : AdmissibleData)
    (K L : ℕ) (f : lp (fun _ : ℤ => ℂ) (mszQExponent A)) (x : ℤ) :
    0 ≤ mszFiniteGridMaximalSequence A K L f x := by
  letI : Fact (1 ≤ mszQExponent A) := ⟨mszQExponent_ge_one A⟩
  rw [mszFiniteGridMaximalSequence_apply]
  obtain ⟨t, ht, hsup⟩ := Finset.exists_mem_eq_sup'
    (mszFiniteTimeGrid_nonempty K L)
    (fun t => ‖mszKernelAverage (A.kernel t) (f : ℤ → ℂ) x‖)
  rw [hsup]
  exact norm_nonneg _

/-- The left endpoint of a level-`l` increment, with the exact finite-grid
index type used by the approved `I_{K,L}` construction. -/
def mszFiniteGridIncrementLeftTime (l : ℕ)
    (i : ℤ × Fin (2 ^ l)) : MSZTime :=
  mszGridTime i.1 l i.2.val

/-- The right endpoint of a level-`l` increment, with no change to its
approved `m+1` endpoint convention. -/
def mszFiniteGridIncrementRightTime (l : ℕ)
    (i : ℤ × Fin (2 ^ l)) : MSZTime :=
  mszGridTime i.1 l (i.2.val + 1)

/-- The family of admissible kernels, viewed in the project's complex
`IntegerL1Kernel` representation. -/
noncomputable def mszAdmissibleIntegerKernel (A : AdmissibleData) :
    MSZTime → IntegerL1Kernel :=
  fun t => (A.kernel t).toIntegerL1Kernel

theorem mszFiniteGridIncrementIndices_nonempty (K l : ℕ) :
    (mszFiniteGridIncrementIndices K l).Nonempty := by
  have hleft : (0 : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp
  have hright : (⟨0, Nat.two_pow_pos l⟩ : Fin (2 ^ l)) ∈ Finset.univ :=
    Finset.mem_univ _
  refine ⟨(0, ⟨0, Nat.two_pow_pos l⟩), ?_⟩
  simpa [mszFiniteGridIncrementIndices, Finset.product_eq_sprod] using
    Finset.mk_mem_product hleft hright

/-- Every left endpoint of an increment in the level-`l` finite family lies
in the approved level-`L` time set whenever `l ≤ L`. -/
theorem mszFiniteGridIncrementLeftTime_mem (K L l : ℕ) (hl : l ≤ L)
    (i : ℤ × Fin (2 ^ l))
    (hi : i ∈ mszFiniteGridIncrementIndices K l) :
    mszFiniteGridIncrementLeftTime l i ∈ mszFiniteTimeGrid K L := by
  have hi' : i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).product Finset.univ := by
    simpa [mszFiniteGridIncrementIndices] using hi
  rcases Finset.mem_product.mp hi' with ⟨hk, _⟩
  rcases Finset.mem_Icc.mp hk with ⟨hk₀, hk₁⟩
  have hm : i.2.val ≤ 2 ^ l := i.2.isLt.le
  have hnadd : l + (L - l) = L := Nat.add_sub_of_le hl
  have hidx : i.2.val * 2 ^ (L - l) ≤ 2 ^ L := by
    calc
      i.2.val * 2 ^ (L - l) ≤ 2 ^ l * 2 ^ (L - l) :=
        Nat.mul_le_mul_right _ hm
      _ = 2 ^ L := by rw [← Nat.pow_add, hnadd]
  have htime : mszFiniteGridIncrementLeftTime l i =
      mszGridTime i.1 L (i.2.val * 2 ^ (L - l)) := by
    dsimp [mszFiniteGridIncrementLeftTime]
    have htime' := mszGridTime_refine_start i.1 l i.2.val (L - l)
    rw [hnadd] at htime'
    exact htime'.symm
  rw [htime]
  exact mszGridTime_mem_finiteTimeGrid K L i.1 _ hk₀ hk₁ hidx

/-- Every right endpoint of an increment in the level-`l` finite family
lies in the approved level-`L` time set whenever `l ≤ L`. -/
theorem mszFiniteGridIncrementRightTime_mem (K L l : ℕ) (hl : l ≤ L)
    (i : ℤ × Fin (2 ^ l))
    (hi : i ∈ mszFiniteGridIncrementIndices K l) :
    mszFiniteGridIncrementRightTime l i ∈ mszFiniteTimeGrid K L := by
  have hi' : i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).product Finset.univ := by
    simpa [mszFiniteGridIncrementIndices] using hi
  rcases Finset.mem_product.mp hi' with ⟨hk, _⟩
  rcases Finset.mem_Icc.mp hk with ⟨hk₀, hk₁⟩
  have hm : i.2.val + 1 ≤ 2 ^ l := by omega
  have hnadd : l + (L - l) = L := Nat.add_sub_of_le hl
  have hidx : (i.2.val + 1) * 2 ^ (L - l) ≤ 2 ^ L := by
    calc
      (i.2.val + 1) * 2 ^ (L - l) ≤ 2 ^ l * 2 ^ (L - l) :=
        Nat.mul_le_mul_right _ hm
      _ = 2 ^ L := by rw [← Nat.pow_add, hnadd]
  have htime : mszFiniteGridIncrementRightTime l i =
      mszGridTime i.1 L ((i.2.val + 1) * 2 ^ (L - l)) := by
    dsimp [mszFiniteGridIncrementRightTime]
    have htime' := mszGridTime_refine_start i.1 l (i.2.val + 1) (L - l)
    rw [hnadd] at htime'
    exact htime'.symm
  rw [htime]
  exact mszGridTime_mem_finiteTimeGrid K L i.1 _ hk₀ hk₁ hidx

/-- The exact finite family of positive convolution increments specified by
the blueprint, indexed by `-K ≤ k ≤ K` and `0 ≤ m < 2^l`. -/
noncomputable def mszFiniteGridIncrementPositiveMajorant (A : AdmissibleData)
    (K L l : ℕ) (h : lp (fun _ : ℤ => ℝ) (mszQExponent A)) : ℤ → ℝ :=
  finiteIncrementKernelPositiveMajorant
    (mszFiniteGridIncrementIndices K l)
    (mszFiniteGridIncrementIndices_nonempty K l)
    (mszAdmissibleIntegerKernel A)
    (mszFiniteGridIncrementLeftTime l)
    (mszFiniteGridIncrementRightTime l) h

/-- The exact `E₀=\overline D 2^{-l}` kernel-mass clause of
`lm:finiteBounds` for every member of the finite increment family. -/
theorem mszFiniteGridIncrementPositiveMajorant_mass_le
    (A : AdmissibleData) (K L l : ℕ) (i : ℤ × Fin (2 ^ l))
    (hi : i ∈ mszFiniteGridIncrementIndices K l) :
    integerKernelL1Mass
        (integerKernelDifference
          (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementRightTime l i))
          (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementLeftTime l i))) ≤
      max 1 A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
  simpa [mszAdmissibleIntegerKernel, mszFiniteGridIncrementLeftTime,
    mszFiniteGridIncrementRightTime, mszGridIncrementKernel] using
      mszGridIncrementKernel_mass_le A i.1 l i.2.val

/-- The precise positive-majorant conclusion of `lm:finiteBounds`, for the
approved time grid and the full family of level-`l` increments. -/
theorem mszFiniteGridIncrementPositiveMajorant_exists
    (A : AdmissibleData) (K L l : ℕ) (hl : l ≤ L)
    (h : lp (fun _ : ℤ => ℝ) (mszQExponent A))
    (hh : ∀ x, 0 ≤ h x) :
    ∃ G : lp (fun _ : ℤ => ℝ) (mszQExponent A),
      (∀ x, G x = mszFiniteGridIncrementPositiveMajorant A K L l h x) ∧
      ‖G‖ ≤ 2 * mszFiniteGridMaximalConstant A K L * ‖h‖ := by
  let p := mszQExponent A
  let E := mszFiniteGridIncrementIndices K l
  let s := mszFiniteTimeGrid K L
  let κ := mszAdmissibleIntegerKernel A
  let left := mszFiniteGridIncrementLeftTime l
  let right := mszFiniteGridIncrementRightTime l
  let M := mszFiniteGridMaximalSequence A K L (mszRealLpToComplexLp h)
  let B := mszFiniteGridMaximalConstant A K L
  letI : Fact (1 ≤ p) := ⟨mszQExponent_ge_one A⟩
  have hs : s.Nonempty := mszFiniteTimeGrid_nonempty K L
  have hE : E.Nonempty := mszFiniteGridIncrementIndices_nonempty K l
  have hleft : ∀ i ∈ E, left i ∈ s := by
    intro i hi
    exact mszFiniteGridIncrementLeftTime_mem K L l hl i hi
  have hright : ∀ i ∈ E, right i ∈ s := by
    intro i hi
    exact mszFiniteGridIncrementRightTime_mem K L l hl i hi
  have hM : ∀ x, 0 ≤ M x := by
    intro x
    exact mszFiniteGridMaximalSequence_nonneg A K L
      (mszRealLpToComplexLp h) x
  have hEndpoint : ∀ t ∈ s, ∀ x,
      integerKernelPositiveConvolution (κ t) h x ≤ M x := by
    intro t ht x
    exact mszKernelPositiveConvolution_le_finiteGridMaximalSequence
      A K L t ht h hh x
  have hMaximalNorm : ‖M‖ ≤ B * ‖h‖ := by
    exact mszFiniteGridMaximalSequence_real_norm_le A K L h
  have hB : 0 ≤ B := by
    dsimp [B, mszFiniteGridMaximalConstant]
    positivity
  obtain ⟨G, hG, hGnorm⟩ :=
    finiteIncrementKernelPositiveMajorant_norm_le
      (mszQExponent_ne_zero A) (mszQExponent_ne_top A)
      s hs E hE κ left right hleft hright h hh M hM B hB
      hEndpoint hMaximalNorm
  refine ⟨G, ?_, ?_⟩
  · intro x
    simpa [mszFiniteGridIncrementPositiveMajorant, E, κ, left, right] using hG x
  · simpa [B] using hGnorm

end

end FractionalPrimes.Literature.MSZ

end
