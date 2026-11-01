module

public import FractionalPrimes.Literature.MSZ.FiniteGridPositiveMajorant

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory Filter
open scoped ENNReal

/-- The positive dyadic rational set `𝒰` from blueprint `lm:spaces`, in its
approved form `m 2^{-v}` with `m ≥ 1` and `v ∈ ℕ`. -/
def positiveDyadicRationals : Set ℚ :=
  {t | ∃ n : ℕ, 0 < n ∧ ∃ v : ℕ, t = (n : ℚ) * (2 : ℚ) ^ (-(v : ℤ))}

/-- A convenient equivalent presentation of the positive dyadics, allowing
an arbitrary integer exponent. -/
def positiveDyadicPowerRationals : Set ℚ :=
  {t | ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ, t = (n : ℚ) * (2 : ℚ) ^ k}

theorem positiveDyadicRationals_iff_powerRationals (t : ℚ) :
    t ∈ positiveDyadicRationals ↔ t ∈ positiveDyadicPowerRationals := by
  constructor
  · rintro ⟨n, hn, v, rfl⟩
    exact ⟨n, hn, -(v : ℤ), rfl⟩
  · rintro ⟨n, hn, k, rfl⟩
    cases k with
    | ofNat v =>
        refine ⟨n * 2 ^ v, by positivity, 0, ?_⟩
        norm_cast
        simp [zpow_natCast]
    | negSucc v =>
        refine ⟨n, hn, v + 1, ?_⟩
        simp [Int.negSucc_eq, zpow_negSucc]

/-- The time parameter type for the positive dyadic rational set `𝒰`. -/
abbrev MSZTime := {t : ℚ // t ∈ positiveDyadicRationals}

theorem mszTime_pos (t : MSZTime) : 0 < t.val := by
  rcases (positiveDyadicRationals_iff_powerRationals _).1 t.property with
    ⟨n, hn, k, ht⟩
  rw [ht]
  exact mul_pos (Nat.cast_pos.mpr hn) (zpow_pos (by norm_num : (0 : ℚ) < 2) k)

/-- A real, nonnegative, absolutely summable integer kernel of mass at most
one, as in the first clause of the approved MSZ data. -/
structure MSZKernel where
  coeff : ℤ → ℝ
  nonneg : ∀ n, 0 ≤ coeff n
  summable_norm : Summable fun n => ‖coeff n‖
  mass_le_one : (∑' n : ℤ, coeff n) ≤ 1

/-- The project convolution API uses complex coefficients. This conversion
retains the exact real-valued kernel through the real inclusion into `ℂ`. -/
noncomputable def MSZKernel.toIntegerL1Kernel (K : MSZKernel) : IntegerL1Kernel where
  coeff := fun n => (K.coeff n : ℂ)
  summable_norm := by
    apply K.summable_norm.congr
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (K.nonneg n)]

/-- The counting-measure `ℓ¹` convolution operator attached to an MSZ kernel. -/
noncomputable def mszKernelL1Operator (K : MSZKernel) :
    Lp ℂ 1 (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ 1 (Measure.count : Measure ℤ) :=
  convolutionL1Operator K.toIntegerL1Kernel

/-- The exact time `2^k(1 + m 2^{-l})`, expressed with a positive integer
numerator and an integer power of two so membership in `𝒰` is explicit. -/
noncomputable def mszGridTime (k : ℤ) (l m : ℕ) : MSZTime :=
  ⟨((2 ^ l + m : ℕ) : ℚ) * (2 : ℚ) ^ (k - (l : ℤ)),
    (positiveDyadicRationals_iff_powerRationals _).2
      ⟨2 ^ l + m, by positivity, k - (l : ℤ), rfl⟩⟩

@[simp] theorem mszGridTime_val (k : ℤ) (l m : ℕ) :
    (mszGridTime k l m).val =
      ((2 ^ l + m : ℕ) : ℚ) * (2 : ℚ) ^ (k - (l : ℤ)) := rfl

/-- Refining a grid interval by `2^n` pieces gives the level-`l+n` grid
times, with the exact affine placement from the blueprint. -/
theorem mszGridTime_refinement (k : ℤ) (l m n i : ℕ) :
    (mszGridTime k (l + n) (m * 2 ^ n + i)).val =
      (mszGridTime k l m).val + (i : ℚ) *
        (2 : ℚ) ^ (k - (l : ℤ) - (n : ℤ)) := by
  have hnum : 2 ^ (l + n) + (m * 2 ^ n + i) =
      (2 ^ l + m) * 2 ^ n + i := by
    rw [Nat.pow_add]
    ring
  have hexp : k - ((l + n : ℕ) : ℤ) =
      k - (l : ℤ) - (n : ℤ) := by
    norm_cast
    omega
  have hpow : (2 : ℚ) ^ (k - (l : ℤ)) =
      ((2 ^ n : ℕ) : ℚ) *
        (2 : ℚ) ^ (k - (l : ℤ) - (n : ℤ)) := by
    calc
      (2 : ℚ) ^ (k - (l : ℤ)) =
          (2 : ℚ) ^ ((n : ℤ) + (k - (l : ℤ) - (n : ℤ))) := by
            congr 1 <;> omega
      _ = (2 : ℚ) ^ (n : ℤ) *
          (2 : ℚ) ^ (k - (l : ℤ) - (n : ℤ)) :=
            zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0) _ _
      _ = ((2 ^ n : ℕ) : ℚ) *
          (2 : ℚ) ^ (k - (l : ℤ) - (n : ℤ)) := by norm_cast
  change ((2 ^ (l + n) + (m * 2 ^ n + i) : ℕ) : ℚ) *
      (2 : ℚ) ^ (k - ((l + n : ℕ) : ℤ)) = _
  rw [hnum, hexp, mszGridTime_val, hpow]
  push_cast
  ring

theorem mszGridTime_succ_eq_add_mesh (k : ℤ) (l m : ℕ) :
    (mszGridTime k l (m + 1)).val =
      (mszGridTime k l m).val + (2 : ℚ) ^ (k - (l : ℤ)) := by
  simpa using mszGridTime_refinement k l m 0 1

theorem mszGridTime_refine_start (k : ℤ) (l m n : ℕ) :
    mszGridTime k (l + n) (m * 2 ^ n) = mszGridTime k l m := by
  apply Subtype.ext
  simpa using mszGridTime_refinement k l m n 0

theorem mszGridTime_refine_end (k : ℤ) (l m n : ℕ) :
    mszGridTime k (l + n) (m * 2 ^ n + 2 ^ n) =
      mszGridTime k l (m + 1) := by
  have hindex : m * 2 ^ n + 2 ^ n = (m + 1) * 2 ^ n := by ring
  rw [hindex]
  apply Subtype.ext
  simpa using mszGridTime_refinement k l (m + 1) n 0

private theorem exists_small_dyadic_mesh (r : ℤ) :
    ∃ n : ℕ, (2 : ℚ) ^ (r - (n : ℤ)) ≤ 1 := by
  let n := r.toNat
  by_cases hr : 0 ≤ r
  · refine ⟨n, ?_⟩
    simp [n, Int.toNat_of_nonneg hr]
  · have hr' : r < 0 := lt_of_not_ge hr
    have hn : (n : ℤ) = 0 := by
      simp [n, Int.toNat_of_nonpos hr'.le]
    refine ⟨n, ?_⟩
    have hexp : r - (n : ℤ) ≤ 0 := by simpa [hn] using hr'.le
    exact zpow_le_one_of_nonpos₀ (by norm_num : 1 ≤ (2 : ℚ)) hexp

private theorem rational_two_zpow_split (r : ℤ) (n : ℕ) :
    (2 : ℚ) ^ r = ((2 ^ n : ℕ) : ℚ) *
      (2 : ℚ) ^ (r - (n : ℤ)) := by
  calc
    (2 : ℚ) ^ r = (2 : ℚ) ^ ((n : ℤ) + (r - (n : ℤ))) := by
      congr 1 <;> omega
    _ = (2 : ℚ) ^ (n : ℤ) * (2 : ℚ) ^ (r - (n : ℤ)) :=
      zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0) _ _
    _ = ((2 ^ n : ℕ) : ℚ) * (2 : ℚ) ^ (r - (n : ℤ)) := by norm_cast

theorem mszGridTime_eq_blueprint (k : ℤ) (l m : ℕ) :
    (mszGridTime k l m).val =
      (2 : ℚ) ^ k * (1 + (m : ℚ) * (2 : ℚ) ^ (-(l : ℤ))) := by
  have hcast : ((2 ^ l + m : ℕ) : ℚ) = (2 : ℚ) ^ l + (m : ℚ) := by
    norm_cast
  have hpow1 : (2 : ℚ) ^ l * (2 : ℚ) ^ (k - (l : ℤ)) = (2 : ℚ) ^ k := by
    calc
      (2 : ℚ) ^ l * (2 : ℚ) ^ (k - (l : ℤ)) =
          (2 : ℚ) ^ (l : ℤ) * (2 : ℚ) ^ (k - (l : ℤ)) := by
            rw [zpow_natCast]
      _ = (2 : ℚ) ^ ((l : ℤ) + (k - (l : ℤ))) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      _ = (2 : ℚ) ^ k := by congr 2 <;> omega
  have hpow2 : (2 : ℚ) ^ (k - (l : ℤ)) =
      (2 : ℚ) ^ k * (2 : ℚ) ^ (-(l : ℤ)) := by
    calc
      (2 : ℚ) ^ (k - (l : ℤ)) =
          (2 : ℚ) ^ (k + (-(l : ℤ))) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ k * (2 : ℚ) ^ (-(l : ℤ)) := by
          rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  change ((2 ^ l + m : ℕ) : ℚ) * (2 : ℚ) ^ (k - (l : ℤ)) = _
  rw [hcast]
  calc
    ((2 : ℚ) ^ l + (m : ℚ)) * (2 : ℚ) ^ (k - (l : ℤ)) =
        (2 : ℚ) ^ l * (2 : ℚ) ^ (k - (l : ℤ)) +
          (m : ℚ) * (2 : ℚ) ^ (k - (l : ℤ)) := by ring
    _ = (2 : ℚ) ^ k +
          (m : ℚ) * ((2 : ℚ) ^ k * (2 : ℚ) ^ (-(l : ℤ))) := by
            rw [hpow1, hpow2]
    _ = (2 : ℚ) ^ k * (1 + (m : ℚ) * (2 : ℚ) ^ (-(l : ℤ))) := by ring

theorem mszGridTime_meshRatio_le (k : ℤ) (l m : ℕ) :
    (2 : ℝ) ^ (k - (l : ℤ)) /
      ((mszGridTime k l m).val : ℝ) ≤ (2 : ℝ) ^ (-(l : ℤ)) := by
  have htime : ((mszGridTime k l m).val : ℝ) =
      (2 : ℝ) ^ k * (1 + (m : ℝ) * (2 : ℝ) ^ (-(l : ℤ))) := by
    calc
      ((mszGridTime k l m).val : ℝ) =
          (((2 : ℚ) ^ k *
            (1 + (m : ℚ) * (2 : ℚ) ^ (-(l : ℤ))) : ℚ) : ℝ) :=
            congrArg (fun x : ℚ => (x : ℝ)) (mszGridTime_eq_blueprint k l m)
      _ = (2 : ℝ) ^ k * (1 + (m : ℝ) * (2 : ℝ) ^ (-(l : ℤ))) := by
        simp [Rat.cast_zpow]
  have hpow : (2 : ℝ) ^ (k - (l : ℤ)) =
      (2 : ℝ) ^ k * (2 : ℝ) ^ (-(l : ℤ)) := by
    calc
      (2 : ℝ) ^ (k - (l : ℤ)) =
          (2 : ℝ) ^ (k + (-(l : ℤ))) := by congr 1 <;> omega
      _ = (2 : ℝ) ^ k * (2 : ℝ) ^ (-(l : ℤ)) :=
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _
  have h2pos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hden : 1 ≤ 1 + (m : ℝ) * (2 : ℝ) ^ (-(l : ℤ)) := by
    have hm : 0 ≤ (m : ℝ) := by positivity
    have hz : 0 ≤ (2 : ℝ) ^ (-(l : ℤ)) := zpow_nonneg (by norm_num) _
    nlinarith [mul_nonneg hm hz]
  rw [htime, hpow]
  calc
    (2 : ℝ) ^ k * (2 : ℝ) ^ (-(l : ℤ)) /
        ((2 : ℝ) ^ k * (1 + (m : ℝ) * (2 : ℝ) ^ (-(l : ℤ)))) =
      (2 : ℝ) ^ (-(l : ℤ)) /
        (1 + (m : ℝ) * (2 : ℝ) ^ (-(l : ℤ))) :=
          mul_div_mul_left _ _ h2pos.ne'
    _ ≤ (2 : ℝ) ^ (-(l : ℤ)) :=
      div_le_self (by positivity) hden

/-- The `2^k` dyadic time used in the MSZ dyadic maximal hypothesis. -/
noncomputable def mszDyadicTime (k : ℤ) : MSZTime := mszGridTime k 0 0

@[simp] theorem mszDyadicTime_value (k : ℤ) :
    (mszDyadicTime k).val = (2 : ℚ) ^ k := by
  rw [mszDyadicTime, mszGridTime_eq_blueprint]
  norm_num

/-- The pointwise averaging operator on sequences, using the established
counting-measure convolution definition. -/
noncomputable def mszKernelAverage (K : MSZKernel) (f : ℤ → ℂ) : ℤ → ℂ :=
  integerKernelConvolution K.toIntegerL1Kernel f

/-- The pointwise level-`l` increment operator `A_{t_{k,l,m+1}}-A_{t_{k,l,m}}`.
Its finite index convention is `0 ≤ m < 2^l`, exactly as in `lm:data`. -/
noncomputable def mszGridIncrement (K : MSZTime → MSZKernel)
    (k : ℤ) (l m : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  mszKernelAverage (K (mszGridTime k l (m + 1))) f -
    mszKernelAverage (K (mszGridTime k l m)) f

/-- The exact finite time set `I_{K,L}` in the approved finite-grid
definition. -/
noncomputable def mszFiniteTimeGrid (K L : ℕ) : Finset MSZTime := by
  classical
  exact (Finset.Icc (-(K : ℤ)) (K : ℤ)).biUnion fun k =>
    (Finset.range (2 ^ L + 1)).image fun m => mszGridTime k L m

theorem mszGridTime_mem_finiteTimeGrid (K L : ℕ) (k : ℤ) (m : ℕ)
    (hk : -(K : ℤ) ≤ k) (hk' : k ≤ K) (hm : m ≤ 2 ^ L) :
    mszGridTime k L m ∈ mszFiniteTimeGrid K L := by
  classical
  rw [mszFiniteTimeGrid, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk, hk'⟩, ?_⟩
  rw [Finset.mem_image]
  exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), rfl⟩

/-- The exact finite index set for level-`L` increments on scales
`-K ≤ k ≤ K`. -/
noncomputable def mszFiniteGridIncrementIndices (K L : ℕ) :
    Finset (ℤ × Fin (2 ^ L)) := by
  classical
  exact (Finset.Icc (-(K : ℤ)) (K : ℤ)).product Finset.univ

/-- The kernel of a finite-grid increment, as the difference of the two
approved time kernels. -/
noncomputable def mszGridIncrementKernel (K : MSZTime → MSZKernel)
    (k : ℤ) (l m : ℕ) : IntegerL1Kernel :=
  integerKernelDifference
    (K (mszGridTime k l (m + 1))).toIntegerL1Kernel
    (K (mszGridTime k l m)).toIntegerL1Kernel

private theorem mszKernelSeriesSummable
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (x : ℤ) :
    Summable (fun n : ℤ => K.coeff n * f (x - n)) := by
  have hi := integerKernelConvolutionExistsAt_of_Lp hp K f x
  change Integrable (fun n : ℤ => K.coeff n * f (x - n)) Measure.count at hi
  exact Summable.of_norm (MeasureTheory.integrable_count_iff.mp hi)

/-- Convolution is linear in the kernel on every counting-measure Lp input
with exponent at least one. -/
theorem integerKernelDifference_convolution_eq_sub
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K₂ K₁ : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (x : ℤ) :
    integerKernelConvolution (integerKernelDifference K₂ K₁)
        (f : ℤ → ℂ) x =
      integerKernelConvolution K₂ (f : ℤ → ℂ) x -
        integerKernelConvolution K₁ (f : ℤ → ℂ) x := by
  let ΔK := integerKernelDifference K₂ K₁
  have h₂ := mszKernelSeriesSummable hp K₂ f x
  have h₁ := mszKernelSeriesSummable hp K₁ f x
  rw [integerKernelConvolution_eq_tsum ΔK _ _
      (integerKernelConvolutionExistsAt_of_Lp hp ΔK f x),
    integerKernelConvolution_eq_tsum K₂ _ _
      (integerKernelConvolutionExistsAt_of_Lp hp K₂ f x),
    integerKernelConvolution_eq_tsum K₁ _ _
      (integerKernelConvolutionExistsAt_of_Lp hp K₁ f x)]
  rw [← h₂.tsum_sub h₁]
  apply tsum_congr
  intro n
  simp [ΔK, integerKernelDifference, sub_mul]

/-- The exact difference-kernel identity for the `ℓ¹` convolution CLM. -/
theorem convolutionL1Operator_difference
    (K₂ K₁ : IntegerL1Kernel) :
    convolutionL1Operator (integerKernelDifference K₂ K₁) =
      convolutionL1Operator K₂ - convolutionL1Operator K₁ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  apply ae_count_int_iff_forall.mpr
  intro x
  calc
    ((convolutionL1Operator (integerKernelDifference K₂ K₁) f :
        Lp ℂ 1 (Measure.count : Measure ℤ)) : ℤ → ℂ) x =
        integerKernelConvolution (integerKernelDifference K₂ K₁)
          (f : ℤ → ℂ) x := by
            simp [convolutionL1Operator, integerKernelLpConvolutionCLM_apply,
              integerKernelLpConvolution_apply_eq_integerKernelConvolution]
    _ = integerKernelConvolution K₂ (f : ℤ → ℂ) x -
        integerKernelConvolution K₁ (f : ℤ → ℂ) x :=
          integerKernelDifference_convolution_eq_sub
            (by norm_num : 1 ≤ (1 : ℝ≥0∞)) K₂ K₁ f x
    _ = ((convolutionL1Operator K₂ f - convolutionL1Operator K₁ f :
        Lp ℂ 1 (Measure.count : Measure ℤ)) : ℤ → ℂ) x := by
          have hsub := (ae_count_int_iff_forall.mp
            (Lp.coeFn_sub (convolutionL1Operator K₂ f)
              (convolutionL1Operator K₁ f))) x
          simpa [convolutionL1Operator, integerKernelLpConvolutionCLM_apply,
            integerKernelLpConvolution_apply_eq_integerKernelConvolution] using
            hsub.symm

/-- The pointwise finite-grid increment is convolution with the exact
difference kernel. This is the kernel contract used by `lm:finiteBounds`. -/
theorem mszGridIncrement_eq_kernelConvolution
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : MSZTime → MSZKernel)
    (k : ℤ) (l m : ℕ) (f : Lp ℂ p (Measure.count : Measure ℤ)) (x : ℤ) :
    mszGridIncrement K k l m (f : ℤ → ℂ) x =
      integerKernelConvolution (mszGridIncrementKernel K k l m)
        (f : ℤ → ℂ) x := by
  let K₂ := (K (mszGridTime k l (m + 1))).toIntegerL1Kernel
  let K₁ := (K (mszGridTime k l m)).toIntegerL1Kernel
  change integerKernelConvolution K₂ (f : ℤ → ℂ) x -
      integerKernelConvolution K₁ (f : ℤ → ℂ) x =
    integerKernelConvolution (integerKernelDifference K₂ K₁)
      (f : ℤ → ℂ) x
  exact (integerKernelDifference_convolution_eq_sub hp K₂ K₁ f x).symm

/-- The raw-function meaning of `ℓ¹+ℓ∞` used for the domain of the projection
operators in the MSZ contract. -/
def MemL1PlusLInfty (f : ℤ → ℂ) : Prop :=
  ∃ f₁ finfty : ℤ → ℂ,
    Memℓp f₁ (1 : ℝ≥0∞) ∧ Memℓp finfty (⊤ : ℝ≥0∞) ∧ f = f₁ + finfty

/-- The pointwise square function of the specified projection family. -/
noncomputable def projectionSquareFunction
    (S : ℤ → ((ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ)))
    {p : ℝ≥0∞} (f : lp (fun _ : ℤ => ℂ) p) (x : ℤ) : ℝ :=
  Real.sqrt (∑' h : ℤ, ‖S h (f : ℤ → ℂ) x‖ ^ 2)

/-- The pointwise square function of the localized level-`l` increment family
in the exact index order used in `lm:data`. -/
noncomputable def localizedIncrementSquareFunction
    (K : MSZTime → MSZKernel)
    (S : ℤ → ((ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ)))
    (j : ℤ) (l : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) : ℝ :=
  Real.sqrt (∑' i : ℤ × Fin (2 ^ l),
    ‖mszGridIncrement K i.1 l i.2.val
      (S (j + i.1) (f : ℤ → ℂ)) x‖ ^ 2)

/-- Full approved data for the positive-convolution MSZ input (`lm:data`).
The square-function and infinite-maximal estimates are recorded by exact
sequence witnesses, avoiding any change to their stated constants or
quantifiers. -/
structure AdmissibleData where
  q : ℝ
  q_gt_one : 1 < q
  q_le_two : q ≤ 2
  D : ℝ
  D_nonneg : 0 ≤ D
  Mq : ℝ
  Mq_nonneg : 0 ≤ Mq
  kernel : MSZTime → MSZKernel
  projections : ℤ → ((ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ))
  projections_preserve_l1_add_linf :
    ∀ h f, MemL1PlusLInfty f → MemL1PlusLInfty (projections h f)
  projectionsL2 :
    ℤ → lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2
  projectionsL2_agree :
    ∀ h (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ),
      projectionsL2 h f x = projections h (f : ℤ → ℂ) x
  symmetric_resolution :
    ∀ f : lp (fun _ : ℤ => ℂ) 2,
      Tendsto (fun J : ℕ =>
        ‖(∑ h ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), projectionsL2 h f) - f‖)
        atTop (nhds 0)
  P : ℝ → ℝ
  P_nonneg : ∀ s, 1 < s → 0 ≤ P s
  square_function_summable :
    ∀ (s : ℝ), 1 < s →
      ∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal s), ∀ x : ℤ,
        Summable (fun h : ℤ => ‖projections h (f : ℤ → ℂ) x‖ ^ 2)
  square_function_bound :
    ∀ (s : ℝ), 1 < s →
      ∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal s),
        ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal s),
          (∀ x, g x = projectionSquareFunction projections f x) ∧
          ‖g‖ ≤ P s * ‖f‖
  a : ℤ → ℕ → ℝ
  a_nonneg : ∀ j l, 0 ≤ a j l
  localized_increment_summable :
    ∀ j l (f : lp (fun _ : ℤ => ℂ) 2) x,
      Summable (fun i : ℤ × Fin (2 ^ l) =>
        ‖mszGridIncrement kernel i.1 l i.2.val
          (projections (j + i.1) (f : ℤ → ℂ)) x‖ ^ 2)
  localized_increment_bound :
    ∀ j l (f : lp (fun _ : ℤ => ℂ) 2),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,
        (∀ x, g x = localizedIncrementSquareFunction kernel projections j l f x) ∧
        ‖g‖ ≤ (2 : ℝ) ^ (-(l : ℝ) / 2) * a j l * ‖f‖
  a_summability :
    ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      Summable (fun z : ℕ × ℤ =>
        (2 : ℝ) ^ (-(ε * (z.1 : ℝ))) * (a z.2 z.1) ^ ρ)
  local_time_estimate :
    ∀ (t : MSZTime) (h : ℚ), 0 < h → h ≤ 1 →
      ∀ ht : t.val + h ∈ positiveDyadicRationals,
        ‖mszKernelL1Operator (kernel ⟨t.val + h, ht⟩) -
          mszKernelL1Operator (kernel t)‖ ≤
          D * (h : ℝ) / (t.val : ℝ)
  dyadic_maximal_bound :
    ∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal q),
      ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, 0 ≤ g x) ∧
        (∀ k x,
          ‖mszKernelAverage (kernel (mszDyadicTime k)) (f : ℤ → ℂ) x‖ ≤ g x) ∧
        ‖g‖ ≤ Mq * ‖f‖

/-- The finite family of time-increment kernels on `I_{K,L}`. -/
noncomputable def mszFiniteGridIncrementKernel (A : AdmissibleData)
    (L : ℕ) (i : ℤ × Fin (2 ^ L)) : IntegerL1Kernel :=
  mszGridIncrementKernel A.kernel i.1 L i.2.val

/-- Extending the local MSZ time estimate across a dyadic grid interval.
This is the exact `D·h/t` estimate before using the grid ratio `h/t≤2^{-L}`. -/
theorem mszGridIncrementOperatorNorm_le_timeRatio (A : AdmissibleData)
    (k : ℤ) (l m : ℕ) :
    ‖mszKernelL1Operator (A.kernel (mszGridTime k l (m + 1))) -
      mszKernelL1Operator (A.kernel (mszGridTime k l m))‖ ≤
        A.D * (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
          ((mszGridTime k l m).val : ℝ) := by
  let r : ℤ := k - (l : ℤ)
  obtain ⟨n, hn⟩ := exists_small_dyadic_mesh r
  let δ : ℚ := (2 : ℚ) ^ (r - (n : ℤ))
  let N : ℕ := 2 ^ n
  let t₀ : MSZTime := mszGridTime k l m
  let F : ℕ → (Lp ℂ 1 (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ 1 (Measure.count : Measure ℤ)) := fun i =>
    mszKernelL1Operator
      (A.kernel (mszGridTime k (l + n) (m * 2 ^ n + i)))
  have hδpos : 0 < δ := by
    exact zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hδle : δ ≤ 1 := by simpa [δ, r] using hn
  have hexp : k - ((l + n : ℕ) : ℤ) = r - (n : ℤ) := by
    dsimp [r]
    norm_cast
    omega
  have htime (i : ℕ) :
      (mszGridTime k (l + n) (m * 2 ^ n + i)).val =
        t₀.val + (i : ℚ) * δ := by
    simpa [t₀, δ, r] using mszGridTime_refinement k l m n i
  have hstep (i : ℕ) :
      (mszGridTime k (l + n) (m * 2 ^ n + (i + 1))).val =
        (mszGridTime k (l + n) (m * 2 ^ n + i)).val + δ := by
    have hs := mszGridTime_succ_eq_add_mesh k (l + n) (m * 2 ^ n + i)
    have hi : m * 2 ^ n + (i + 1) = (m * 2 ^ n + i) + 1 := by omega
    rw [hi]
    calc
      (mszGridTime k (l + n) ((m * 2 ^ n + i) + 1)).val =
          (mszGridTime k (l + n) (m * 2 ^ n + i)).val +
            (2 : ℚ) ^ (k - ((l + n : ℕ) : ℤ)) := hs
      _ = (mszGridTime k (l + n) (m * 2 ^ n + i)).val + δ := by
        rw [hexp]
  have hlocal (i : ℕ) :
      ‖F (i + 1) - F i‖ ≤
        A.D * (δ : ℝ) / ((t₀.val : ℝ)) := by
    let ti := mszGridTime k (l + n) (m * 2 ^ n + i)
    let ti' := mszGridTime k (l + n) (m * 2 ^ n + (i + 1))
    have hstepi : ti'.val = ti.val + δ := by simpa [ti, ti'] using hstep i
    have hUi : ti.val + δ ∈ positiveDyadicRationals := by
      rw [← hstepi]
      exact ti'.property
    have htimeEq : (⟨ti.val + δ, hUi⟩ : MSZTime) = ti' :=
      Subtype.ext hstepi.symm
    have hlocal' := A.local_time_estimate ti δ hδpos hδle hUi
    rw [htimeEq] at hlocal'
    have htiFormula : ti.val = t₀.val + (i : ℚ) * δ := by
      simpa [ti, t₀, δ, r] using mszGridTime_refinement k l m n i
    have hti_le : t₀.val ≤ ti.val := by
      rw [htiFormula]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) hδpos.le)
    have ht₀pos : 0 < (t₀.val : ℝ) := by
      exact_mod_cast mszTime_pos t₀
    have hti_le_real : (t₀.val : ℝ) ≤ (ti.val : ℝ) := by
      exact_mod_cast hti_le
    have hnum_nonneg : 0 ≤ A.D * (δ : ℝ) :=
      mul_nonneg A.D_nonneg (by exact_mod_cast hδpos.le)
    have hratio := div_le_div_of_nonneg_left hnum_nonneg ht₀pos hti_le_real
    simpa [F, ti, ti'] using hlocal'.trans hratio
  have htel : F N - F 0 =
      ∑ i ∈ Finset.range N, (F (i + 1) - F i) := by
    symm
    exact Finset.sum_range_sub F N
  have hFbound :
      ‖F N - F 0‖ ≤ (N : ℝ) *
        (A.D * (δ : ℝ) / ((t₀.val : ℝ))) := by
    calc
      ‖F N - F 0‖ =
          ‖∑ i ∈ Finset.range N, (F (i + 1) - F i)‖ := by rw [htel]
      _ ≤ ∑ i ∈ Finset.range N, ‖F (i + 1) - F i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N,
          A.D * (δ : ℝ) / ((t₀.val : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hlocal i
      _ = (N : ℝ) * (A.D * (δ : ℝ) / ((t₀.val : ℝ))) := by simp
  have hstart : mszGridTime k (l + n) (m * 2 ^ n) = t₀ := by
    simpa [t₀] using mszGridTime_refine_start k l m n
  have hend : mszGridTime k (l + n) (m * 2 ^ n + N) =
      mszGridTime k l (m + 1) := by
    simpa [N] using mszGridTime_refine_end k l m n
  have hNδ : (N : ℝ) * (δ : ℝ) =
      (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) := by
    have hs := rational_two_zpow_split (k - (l : ℤ)) n
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hs
    simpa [N, δ, r] using hcast.symm
  calc
    ‖mszKernelL1Operator (A.kernel (mszGridTime k l (m + 1))) -
        mszKernelL1Operator (A.kernel (mszGridTime k l m))‖ =
      ‖F N - F 0‖ := by simp [F, N, t₀, hstart, hend]
    _ ≤ (N : ℝ) * (A.D * (δ : ℝ) / ((t₀.val : ℝ))) := hFbound
    _ = A.D * ((N : ℝ) * (δ : ℝ)) /
        ((t₀.val : ℝ)) := by ring
    _ = A.D * (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
        ((mszGridTime k l m).val : ℝ) := by rw [hNδ]

/-- The exact increment-kernel mass bound needed by `lm:finiteBounds`,
derived from the local time hypothesis and the exact grid spacing. -/
theorem mszGridIncrementKernel_mass_le (A : AdmissibleData)
    (k : ℤ) (l m : ℕ) :
    integerKernelL1Mass (mszGridIncrementKernel A.kernel k l m) ≤
      max 1 A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
  let K₂ := (A.kernel (mszGridTime k l (m + 1))).toIntegerL1Kernel
  let K₁ := (A.kernel (mszGridTime k l m)).toIntegerL1Kernel
  have hmass : integerKernelL1Mass (mszGridIncrementKernel A.kernel k l m) =
      ‖convolutionL1Operator (mszGridIncrementKernel A.kernel k l m)‖ := by
    unfold integerKernelL1Mass
    exact (convolutionL1Operator_norm_eq _).symm
  have hclm : convolutionL1Operator (mszGridIncrementKernel A.kernel k l m) =
      mszKernelL1Operator (A.kernel (mszGridTime k l (m + 1))) -
        mszKernelL1Operator (A.kernel (mszGridTime k l m)) := by
    simpa [mszGridIncrementKernel, K₂, K₁, mszKernelL1Operator] using
      convolutionL1Operator_difference K₂ K₁
  have hratio := mszGridIncrementOperatorNorm_le_timeRatio A k l m
  have hscaled : A.D *
      (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
        ((mszGridTime k l m).val : ℝ) ≤
      A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
    have h := mul_le_mul_of_nonneg_left
      (mszGridTime_meshRatio_le k l m) A.D_nonneg
    calc
      A.D * (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
          ((mszGridTime k l m).val : ℝ) =
        A.D * ((((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
          ((mszGridTime k l m).val : ℝ)) := by ring
      _ ≤ A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
        simpa [Rat.cast_zpow] using h
  calc
    integerKernelL1Mass (mszGridIncrementKernel A.kernel k l m) =
        ‖convolutionL1Operator (mszGridIncrementKernel A.kernel k l m)‖ := hmass
    _ = ‖mszKernelL1Operator (A.kernel (mszGridTime k l (m + 1))) -
        mszKernelL1Operator (A.kernel (mszGridTime k l m))‖ := by rw [hclm]
    _ ≤ A.D * (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
        ((mszGridTime k l m).val : ℝ) := hratio
    _ ≤ A.D * (2 : ℝ) ^ (-(l : ℤ)) := hscaled
    _ ≤ max 1 A.D * (2 : ℝ) ^ (-(l : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 A.D) (by positivity)

end FractionalPrimes.Literature.MSZ

end
