module

public import FractionalPrimes.Literature.MSZ.VectorNormDuality
public import FractionalPrimes.GeneralAdjointPairing

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open Filter
open scoped Topology

noncomputable section

/-- The reflected-conjugate adjoint kernel has exactly the same `ℓ¹` mass. -/
theorem integerKernelAdjointL1Mass_eq (K : IntegerL1Kernel) :
    integerKernelL1Mass (integerKernelAdjoint K) = integerKernelL1Mass K := by
  rw [integerKernelL1Mass, integerKernelL1Mass, integerKernelAdjoint_norm_tsum]

/-- The family mass hypothesis transfers unchanged to the adjoint family. -/
theorem integerKernelAdjointFamilyL1Mass_le
    {ι : Type*} [Fintype ι] (K : ι → IntegerL1Kernel) (E₀ : ℝ)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀) :
    ∀ i, integerKernelL1Mass (integerKernelAdjoint (K i)) ≤ E₀ := by
  intro i
  rw [integerKernelAdjointL1Mass_eq]
  exact hmass i

/-- The exact finite-support adjoint pairing for a general absolutely
summable integer kernel. The finite spatial supports make the pairings
finite sums, while the convolution itself remains the full `ℓ¹`-kernel
convolution. -/
theorem integerKernelFiniteSupportPairing_adjoint
    (K : IntegerL1Kernel) (t u : Finset ℤ) (b c : ℤ → ℂ) :
    (∑ x ∈ u,
      integerKernelConvolution K (finiteIntegerSequenceL2 t b) x *
        starRingEnd ℂ (c x)) =
      ∑ y ∈ t,
        b y * starRingEnd ℂ
          (integerKernelConvolution (integerKernelAdjoint K)
            (finiteIntegerSequenceL2 u c) y) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hpair := integerKernelFiniteConvolutionLimitL2_pairing_adjoint
    (hT := ⟨by norm_num⟩) K t u b c
  rw [inner_left_finiteIntegerSequenceL2,
    inner_right_finiteIntegerSequenceL2] at hpair
  simpa only [integerKernelFiniteConvolutionLimitL2_apply,
    finiteIntegerSequenceL2_apply, if_pos] using hpair

/-- The finite-index mixed-vector adjoint pairing. This is obtained by
expanding the finite-dimensional `PiLp 2` inner products, interchanging the
finite spatial and fiber sums, and applying the scalar general-kernel pairing
to each coordinate. -/
theorem integerKernelVectorFiniteSupportPairing_adjoint
    {ι : Type*} [Fintype ι] (K : ι → IntegerL1Kernel)
    (t u : Finset ℤ) (f g : ℤ → PiLp 2 (fun _ : ι => ℂ))
    (hf : ∀ x ∉ t, f x = 0) (hg : ∀ x ∉ u, g x = 0) :
    (∑ x ∈ u,
      inner ℂ (g x) (integerKernelVectorConvolution K f x)) =
      ∑ y ∈ t,
        inner ℂ
          (integerKernelVectorConvolution
            (fun i => integerKernelAdjoint (K i)) g y) (f y) := by
  classical
  have hF (i : ι) :
      finiteIntegerSequenceL2 t (fun y => f y i) = fun y => f y i := by
    funext y
    by_cases hy : y ∈ t
    · simp [finiteIntegerSequenceL2_apply, hy]
    · simp [finiteIntegerSequenceL2_apply, hy, hf y hy]
  have hG (i : ι) :
      finiteIntegerSequenceL2 u (fun y => g y i) = fun y => g y i := by
    funext y
    by_cases hy : y ∈ u
    · simp [finiteIntegerSequenceL2_apply, hy]
    · simp [finiteIntegerSequenceL2_apply, hy, hg y hy]
  calc
    (∑ x ∈ u,
      inner ℂ (g x) (integerKernelVectorConvolution K f x)) =
        ∑ x ∈ u, ∑ i : ι,
          integerKernelConvolution (K i) (fun y => f y i) x *
            starRingEnd ℂ (g x i) := by
      rw [mszVectorFinitePairing_eq_coordinates]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro i hi
      simp [integerKernelVectorConvolution]
    _ = ∑ i : ι, ∑ x ∈ u,
        integerKernelConvolution (K i) (fun y => f y i) x *
          starRingEnd ℂ (g x i) := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ y ∈ t,
        f y i * starRingEnd ℂ
          (integerKernelConvolution (integerKernelAdjoint (K i))
            (fun x => g x i) y) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [hF i, hG i] using
        integerKernelFiniteSupportPairing_adjoint (K i) t u
          (fun y => f y i) (fun x => g x i)
    _ = ∑ y ∈ t, ∑ i : ι,
        f y i * starRingEnd ℂ
          (integerKernelConvolution (integerKernelAdjoint (K i))
            (fun x => g x i) y) := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ t,
        inner ℂ
          (integerKernelVectorConvolution
            (fun i => integerKernelAdjoint (K i)) g y) (f y) := by
      symm
      exact mszVectorFinitePairing_eq_coordinates t
        (fun y => integerKernelVectorConvolution
          (fun i => integerKernelAdjoint (K i)) g y) f

/-- Pointwise conversion of the approved ENNReal mixed-norm summand to the
real `r`-power of the `PiLp 2` fiber norm. This is the first bridge needed to
compare the extended mixed norm with Mathlib's sequence-`lp` norm. -/
theorem mszVectorLpTerm_eq_ofReal_rpow
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 ≤ p)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) (x : ℤ) :
    mszVectorLpTerm p F x = ENNReal.ofReal (‖F x‖ ^ p) := by
  rw [mszVectorLpTerm]
  change ENNReal.ofNNReal (‖F x‖₊ ^ p) =
    ENNReal.ofReal (‖F x‖ ^ p)
  calc
    ENNReal.ofNNReal (‖F x‖₊ ^ p) =
        (ENNReal.ofNNReal ‖F x‖₊) ^ p := by
      simpa only [ENNReal.ofNNReal] using
        (ENNReal.coe_rpow_of_nonneg (‖F x‖₊) hp)
    _ = ENNReal.ofReal ((‖F x‖₊ : ℝ) ^ p) := by
      rw [← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_rpow_of_nonneg (NNReal.zero_le_coe) hp]
    _ = ENNReal.ofReal (‖F x‖ ^ p) := by rw [← coe_nnnorm]

/-- The standard sequence-`lp` norm is exactly the approved extended mixed
norm on its pointwise representative. This identity is restricted to the
source's finite exponent range `p>1`; the right-hand side retains the
ENNReal-valued `mszVectorLpNorm` definition. -/
theorem mszVectorLpNorm_eq_lp_norm
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal p)) :
    mszVectorLpNorm p (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) =
      ENNReal.ofReal ‖f‖ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpENN : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp0.le]
    exact hp0
  have hsumENNexp :
      Summable (fun x : ℤ => ‖f x‖ ^ (ENNReal.ofReal p).toReal) :=
    (lp.memℓp f).summable hpENN
  have hsum : Summable (fun x : ℤ => ‖f x‖ ^ p) := by
    simpa [ENNReal.toReal_ofReal hp0.le] using hsumENNexp
  have hterms :
      (∑' x : ℤ, mszVectorLpTerm p
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x) =
        ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ p) := by
    calc
      _ = ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ p) := by
        apply tsum_congr
        intro x
        exact mszVectorLpTerm_eq_ofReal_rpow hp0.le
          (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x
      _ = ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ p) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun x => Real.rpow_nonneg (norm_nonneg (f x)) _)
          hsum).symm
  have hmoment_nonneg : 0 ≤ ∑' x : ℤ, ‖f x‖ ^ p :=
    tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg (f x)) _
  rw [mszVectorLpNorm, hterms, lp.norm_eq_tsum_rpow hpENN f,
    ENNReal.toReal_ofReal hp0.le]
  exact ENNReal.ofReal_rpow_of_nonneg hmoment_nonneg
    (one_div_nonneg.mpr hp0.le)

/-- A finitely supported mixed-vector sequence as an exact member of the
standard sequence-`lp` space. The constructor retains the pointwise
representative. -/
noncomputable def mszFiniteSupportLp
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p)
    (u : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, u x = 0) :
    lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let C : ℝ := ∑ x ∈ s, ‖u x‖ ^ p
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (norm_nonneg _) _
  have hfinite (t : Finset ℤ) :
      ∑ x ∈ t, ‖u x‖ ^ (ENNReal.ofReal p).toReal ≤ C := by
    rw [ENNReal.toReal_ofReal hp0.le]
    dsimp [C]
    calc
      (∑ x ∈ t, ‖u x‖ ^ p) ≤
          ∑ x ∈ s ∪ t, ‖u x‖ ^ p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun x hx hnot => Real.rpow_nonneg (norm_nonneg _) _)
      _ = ∑ x ∈ s, ‖u x‖ ^ p := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro x hx hnot
        rw [hs x hnot]
        simp [Real.zero_rpow hp0.ne']
  exact lpOfUniformFiniteMomentBound
    (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    u hC hfinite

@[simp]
theorem mszFiniteSupportLp_apply
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p)
    (u : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, u x = 0) (x : ℤ) :
    mszFiniteSupportLp hp u s hs x = u x := rfl

/-- Finite mixed-vector Hölder pairing, with the same ENNReal norm
definition as `lm:duality`. -/
theorem mszVectorFinitePairing_le
    {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp : 0 < p) (hq : 0 < q)
    (s : Finset ℤ) (G F : ℤ → PiLp 2 (fun _ : ι => ℂ)) :
    ENNReal.ofReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖ ≤
      mszVectorLpNorm q G * mszVectorLpNorm p F := by
  have hpairNN :
      ‖∑ x ∈ s, inner ℂ (G x) (F x)‖₊ ≤
        ∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊ := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm]
    calc
      ‖∑ x ∈ s, inner ℂ (G x) (F x)‖ ≤
          ∑ x ∈ s, ‖inner ℂ (G x) (F x)‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ s, ‖G x‖ * ‖F x‖ := by
        apply Finset.sum_le_sum
        intro x hx
        exact norm_inner_le_norm _ _
  have hholder :=
    NNReal.inner_le_Lp_mul_Lq s (fun x : ℤ => ‖G x‖₊)
      (fun x : ℤ => ‖F x‖₊) hpq.symm
  have hholderENN :
      ENNReal.ofNNReal (∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊) ≤
        mszVectorFiniteLpNorm q s G * mszVectorFiniteLpNorm p s F := by
    rw [mszVectorFiniteLpNorm_eq_nnreal hq,
      mszVectorFiniteLpNorm_eq_nnreal hp]
    calc
      ENNReal.ofNNReal (∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊) ≤
          ENNReal.ofNNReal
            ((∑ x ∈ s, ‖G x‖₊ ^ q) ^ (1 / q) *
              (∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p)) :=
        ENNReal.coe_le_coe.mpr hholder
      _ = ENNReal.ofNNReal ((∑ x ∈ s, ‖G x‖₊ ^ q) ^ (1 / q)) *
            ENNReal.ofNNReal ((∑ x ∈ s, ‖F x‖₊ ^ p) ^ (1 / p)) := by simp
  rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  calc
    ENNReal.ofNNReal ‖∑ x ∈ s, inner ℂ (G x) (F x)‖₊ ≤
        ENNReal.ofNNReal (∑ x ∈ s, ‖G x‖₊ * ‖F x‖₊) :=
      ENNReal.coe_le_coe.mpr hpairNN
    _ ≤ mszVectorFiniteLpNorm q s G * mszVectorFiniteLpNorm p s F := hholderENN
    _ ≤ mszVectorLpNorm q G * mszVectorLpNorm p F :=
      mul_le_mul (mszVectorFiniteLpNorm_le hq s G)
        (mszVectorFiniteLpNorm_le hp s F) (by positivity) (by positivity)

/-- The finite-support upper-endpoint pairing estimate from `lm:vectorUpper`.
The input and test vector have their exact finite spatial supports; the test
is in the unit ball at `r=2q/(q+1)`. This is the finite-support stage only. -/
theorem integerKernelVectorFiniteSupportUpperPairing_le
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q)
    (K : ι → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (s t : Finset ℤ)
    (f g : ℤ → PiLp 2 (fun _ : ι => ℂ))
    (hf : ∀ x ∉ s, f x = 0) (hg : ∀ x ∉ t, g x = 0)
    (hgNorm : mszVectorLpNorm (2 * q / (q + 1)) g ≤ 1) :
    ENNReal.ofReal ‖∑ x ∈ t,
      inner ℂ (g x) (integerKernelVectorConvolution K f x)‖ ≤
      ENNReal.ofReal (Real.sqrt (E₀ * B)) *
        mszVectorLpNorm (2 * q / (q - 1)) f := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqm1 : 0 < q - 1 := by linarith
  have hqp1 : 0 < q + 1 := by linarith
  have hrpos : 0 < 2 * q / (q + 1) :=
    div_pos (by positivity) hqp1
  have hrone : 1 < 2 * q / (q + 1) := by
    rw [lt_div_iff₀ hqp1]
    nlinarith
  have hrpPos : 0 < 2 * q / (q - 1) :=
    div_pos (by positivity) hqm1
  have hrpOne : 1 < 2 * q / (q - 1) := by
    rw [lt_div_iff₀ hqm1]
    nlinarith
  have hrHolder :
      (2 * q / (q - 1)).HolderConjugate (2 * q / (q + 1)) := by
    rw [Real.holderConjugate_iff_eq_conjExponent hrpOne]
    have hden : 2 * q - (q - 1) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hqm1, ne_of_gt hqp1, hden]
    <;> ring
  let Kstar : ι → IntegerL1Kernel := fun i => integerKernelAdjoint (K i)
  have hmassStar : ∀ i, integerKernelL1Mass (Kstar i) ≤ E₀ := by
    simpa [Kstar] using integerKernelAdjointFamilyL1Mass_le K E₀ hmass
  have hmaxStar := vectorLowerAdjointMaximalBound hq K B hmax
  let gLp := mszFiniteSupportLp hrone g t hg
  have hgRep : (gLp : ℤ → PiLp 2 (fun _ : ι => ℂ)) = g := by
    funext x
    exact mszFiniteSupportLp_apply hrone g t hg x
  have hgBridge :
      mszVectorLpNorm (2 * q / (q + 1)) g = ENNReal.ofReal ‖gLp‖ := by
    have h := mszVectorLpNorm_eq_lp_norm hrone gLp
    rw [hgRep] at h
    exact h
  have hgLpUnitENN : ENNReal.ofReal ‖gLp‖ ≤ 1 := by
    rw [← hgBridge]
    exact hgNorm
  have hgLpUnit : ‖gLp‖ ≤ 1 := ENNReal.ofReal_le_one.mp hgLpUnitENN
  obtain ⟨out, hout, houtNorm⟩ :=
    vectorLower_normBound hq rfl Kstar E₀ B hE₀ hB hmassStar hmaxStar gLp
  have houtFun : (out : ℤ → PiLp 2 (fun _ : ι => ℂ)) =
      integerKernelVectorConvolution Kstar g := by
    funext x
    calc
      out x = integerKernelVectorConvolution Kstar
          (gLp : ℤ → PiLp 2 (fun _ : ι => ℂ)) x := hout x
      _ = integerKernelVectorConvolution Kstar g x := by rw [hgRep]
  have hAdjointNormBridge :
      mszVectorLpNorm (2 * q / (q + 1))
        (integerKernelVectorConvolution Kstar g) = ENNReal.ofReal ‖out‖ := by
    rw [← houtFun]
    exact mszVectorLpNorm_eq_lp_norm hrone out
  have hCnonneg : 0 ≤ Real.sqrt (E₀ * B) := Real.sqrt_nonneg _
  have hCnorm : Real.sqrt (E₀ * B) * ‖gLp‖ ≤ Real.sqrt (E₀ * B) :=
    mul_le_of_le_one_right hCnonneg hgLpUnit
  have hAdjointNorm :
      mszVectorLpNorm (2 * q / (q + 1))
        (integerKernelVectorConvolution Kstar g) ≤
        ENNReal.ofReal (Real.sqrt (E₀ * B)) := by
    rw [hAdjointNormBridge]
    calc
      ENNReal.ofReal ‖out‖ ≤
          ENNReal.ofReal (Real.sqrt (E₀ * B) * ‖gLp‖) :=
        ENNReal.ofReal_le_ofReal (by simpa using houtNorm)
      _ ≤ ENNReal.ofReal (Real.sqrt (E₀ * B)) :=
        ENNReal.ofReal_le_ofReal hCnorm
  have hpair := integerKernelVectorFiniteSupportPairing_adjoint
    K s t f g hf hg
  calc
    ENNReal.ofReal ‖∑ x ∈ t,
        inner ℂ (g x) (integerKernelVectorConvolution K f x)‖ =
        ENNReal.ofReal ‖∑ y ∈ s,
          inner ℂ
            (integerKernelVectorConvolution Kstar g y) (f y)‖ := by
      rw [hpair]
    _ ≤ mszVectorLpNorm (2 * q / (q - 1)) f *
        mszVectorLpNorm (2 * q / (q + 1))
          (integerKernelVectorConvolution Kstar g) :=
      by
        simpa [mul_comm] using
          mszVectorFinitePairing_le hrHolder hrpPos hrpos s
            (integerKernelVectorConvolution Kstar g) f
    _ ≤ ENNReal.ofReal (Real.sqrt (E₀ * B)) *
        mszVectorLpNorm (2 * q / (q - 1)) f :=
      calc
        mszVectorLpNorm (2 * q / (q - 1)) f *
            mszVectorLpNorm (2 * q / (q + 1))
              (integerKernelVectorConvolution Kstar g) =
            mszVectorLpNorm (2 * q / (q + 1))
              (integerKernelVectorConvolution Kstar g) *
            mszVectorLpNorm (2 * q / (q - 1)) f := mul_comm _ _
        _ ≤ ENNReal.ofReal (Real.sqrt (E₀ * B)) *
            mszVectorLpNorm (2 * q / (q - 1)) f :=
          mul_le_mul_of_nonneg_right hAdjointNorm bot_le

/-- The finite-support output norm estimate in `lm:vectorUpper`, obtained
from the exact mixed-norm duality and the checked finite-support adjoint
pairing estimate. The input is spatially finite; the convolution output need
not be spatially finite. -/
theorem integerKernelVectorFiniteSupportUpperNorm_le
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q)
    (K : ι → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (s : Finset ℤ) (f : ℤ → PiLp 2 (fun _ : ι => ℂ))
    (hf : ∀ x ∉ s, f x = 0) :
    mszVectorLpNorm (2 * q / (q - 1))
        (integerKernelVectorConvolution K f) ≤
      ENNReal.ofReal (Real.sqrt (E₀ * B)) *
        mszVectorLpNorm (2 * q / (q - 1)) f := by
  classical
  have hqm1 : 0 < q - 1 := by linarith
  have hqp1 : 0 < q + 1 := by linarith
  have hrpOne : 1 < 2 * q / (q - 1) := by
    rw [lt_div_iff₀ hqm1]
    nlinarith
  have hrHolder :
      (2 * q / (q - 1)).HolderConjugate (2 * q / (q + 1)) := by
    rw [Real.holderConjugate_iff_eq_conjExponent hrpOne]
    have hden : 2 * q - (q - 1) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hqm1, ne_of_gt hqp1, hden]
    <;> ring
  have hdualExponent :
      2 * q / (q + 1) =
        (2 * q / (q - 1)) / ((2 * q / (q - 1)) - 1) :=
    (Real.holderConjugate_iff_eq_conjExponent hrpOne).mp hrHolder
  rw [mszVectorNormDuality_paper (2 * q / (q - 1)) hrpOne
    (integerKernelVectorConvolution K f), ← hdualExponent]
  unfold mszVectorFiniteSupportDualSup
  apply iSup_le
  intro G
  let t : Finset ℤ := G.2.1.toFinset
  have hGsupport : ∀ x ∉ t, G.1 x = 0 := by
    intro x hx
    by_contra hGx
    exact hx (G.2.1.mem_toFinset.mpr (Function.mem_support.mpr hGx))
  have hpair := integerKernelVectorFiniteSupportUpperPairing_le
    hq K E₀ B hE₀ hB hmass hmax s t f G.1 hf hGsupport G.2.2
  simpa [t] using hpair

/-- A finite partial moment is bounded by the corresponding power of the
extended mixed norm. This preserves the ENNReal norm's `+∞` semantics and
uses the exact finite-exhaustion norm already defined for `lm:spaces`. -/
theorem mszVectorLpNorm_finiteMoment_le
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (hF : mszVectorLpNorm p F ≤ ENNReal.ofReal R) (s : Finset ℤ) :
    ∑ x ∈ s, ‖F x‖ ^ p ≤ R ^ p := by
  have hroot : mszVectorFiniteLpNorm p s F ≤ ENNReal.ofReal R :=
    (mszVectorFiniteLpNorm_le hp s F).trans hF
  have hpower :
      (∑ x ∈ s, mszVectorLpTerm p F x) ≤ ENNReal.ofReal (R ^ p) := by
    calc
      (∑ x ∈ s, mszVectorLpTerm p F x) =
          (mszVectorFiniteLpNorm p s F) ^ p := by
        rw [mszVectorFiniteLpNorm, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal R) ^ p :=
        ENNReal.rpow_le_rpow hroot hp.le
      _ = ENNReal.ofReal (R ^ p) :=
        ENNReal.ofReal_rpow_of_nonneg hR hp.le
  have hsum :
      ENNReal.ofReal (∑ x ∈ s, ‖F x‖ ^ p) =
        ∑ x ∈ s, mszVectorLpTerm p F x := by
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun x hx => Real.rpow_nonneg (norm_nonneg (F x)) _)]
    apply Finset.sum_congr rfl
    intro x hx
    exact (mszVectorLpTerm_eq_ofReal_rpow hp.le F x).symm
  apply (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hR _)).mp
  rw [hsum]
  exact hpower

/-- A finite-valued extended mixed-norm bound gives the exact sequence-`lp`
representative and its real norm bound. -/
theorem mszVectorLpNorm_bound_to_lp
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p)
    (F : ℤ → PiLp 2 (fun _ : ι => ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (hF : mszVectorLpNorm p F ≤ ENNReal.ofReal R) :
    ∃ f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal p),
      (∀ x, f x = F x) ∧ ‖f‖ ≤ R := by
  have hpReal : 0 < p := lt_trans zero_lt_one hp
  have hpENNToReal : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hpReal.le]
    exact hpReal
  have hpToReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hpReal.le
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hp)⟩
  have hfinite (s : Finset ℤ) :
      ∑ x ∈ s, ‖F x‖ ^ (ENNReal.ofReal p).toReal ≤
        R ^ (ENNReal.ofReal p).toReal := by
    rw [hpToReal]
    exact mszVectorLpNorm_finiteMoment_le hpReal F R hR hF s
  let out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal p) :=
    lpOfUniformFiniteMomentBound (ENNReal.ofReal_ne_zero_iff.mpr hpReal)
      ENNReal.ofReal_ne_top F (Real.rpow_nonneg hR _) hfinite
  have houtNorm : ‖out‖ ≤ R := by
    apply lp.norm_le_of_forall_sum_le hpENNToReal hR
    intro s
    simpa only [out, lpOfUniformFiniteMomentBound_apply, hpToReal] using
      hfinite s
  refine ⟨out, ?_, houtNorm⟩
  intro x
  rfl

/-- The full arbitrary-input upper-vector endpoint `lm:vectorUpper`. The
finite-support duality estimate is extended by the approved symmetric spatial
truncations; coordinatewise convergence uses the existing scalar Young
continuous-convolution map. -/
theorem vectorUpper_normBound
    {ι : Type*} [Fintype ι] {q : ℝ} (hq : 1 < q)
    (K : ι → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ))
      (ENNReal.ofReal (2 * q / (q - 1)))) :
    ∃ out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ))
        (ENNReal.ofReal (2 * q / (q - 1))),
      (∀ x, out x = integerKernelVectorConvolution K
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x) ∧
      ‖out‖ ≤ Real.sqrt (E₀ * B) * ‖f‖ := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqm1 : 0 < q - 1 := by linarith
  let r' : ℝ := 2 * q / (q - 1)
  have hr'pos : 0 < r' := by
    dsimp [r']
    exact div_pos (by positivity) hqm1
  have hr'one : 1 < r' := by
    dsimp [r']
    rw [lt_div_iff₀ hqm1]
    nlinarith
  let p : ENNReal := ENNReal.ofReal r'
  have hp0 : p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr'pos
  have hpTop : p ≠ ⊤ := ENNReal.ofReal_ne_top
  letI : Fact (1 ≤ p) :=
    ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hr'one)⟩
  let C : ℝ := Real.sqrt (E₀ * B)
  let R : ℝ := C * ‖f‖
  have hC : 0 ≤ C := by dsimp [C]; exact Real.sqrt_nonneg _
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg hC (norm_nonneg _)
  let grid : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ)
  let trunc : ℕ → lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p :=
    fun N => vectorLowerSpatialTruncation f (grid N)
  let truncSeq : ℕ → ℤ → PiLp 2 (fun _ : ι => ℂ) :=
    fun N x => trunc N x
  have htruncRep (N : ℕ) :
      (trunc N : ℤ → PiLp 2 (fun _ : ι => ℂ)) = truncSeq N := by
    funext x
    rfl
  have htruncSupport (N : ℕ) : ∀ x ∉ grid N, truncSeq N x = 0 := by
    intro x hx
    simpa [truncSeq, trunc] using
      vectorLowerSpatialTruncation_supported f (grid N) x hx
  have htruncNorm (N : ℕ) : ‖trunc N‖ ≤ ‖f‖ :=
    vectorLowerSpatialTruncation_norm_le hp0 f (grid N)
  have htruncBridge (N : ℕ) :
      mszVectorLpNorm r' (truncSeq N) = ENNReal.ofReal ‖trunc N‖ := by
    have h := mszVectorLpNorm_eq_lp_norm hr'one (trunc N)
    rw [htruncRep N] at h
    exact h
  have htruncConvolutionNorm (N : ℕ) :
      mszVectorLpNorm r'
        (integerKernelVectorConvolution K (truncSeq N)) ≤ ENNReal.ofReal R := by
    calc
      mszVectorLpNorm r'
          (integerKernelVectorConvolution K (truncSeq N)) ≤
        ENNReal.ofReal C * mszVectorLpNorm r' (truncSeq N) :=
          integerKernelVectorFiniteSupportUpperNorm_le hq K E₀ B hE₀ hB
            hmass hmax (grid N) (truncSeq N) (htruncSupport N)
      _ = ENNReal.ofReal C * ENNReal.ofReal ‖trunc N‖ := by
        rw [htruncBridge N]
      _ = ENNReal.ofReal (C * ‖trunc N‖) := (ENNReal.ofReal_mul hC).symm
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by
        dsimp [R]
        exact mul_le_mul_of_nonneg_left (htruncNorm N) hC)
  let O : ℕ → lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p := fun N =>
    Classical.choose (mszVectorLpNorm_bound_to_lp hr'one
      (integerKernelVectorConvolution K (truncSeq N)) R hR
      (htruncConvolutionNorm N))
  have hOspec (N : ℕ) :
      (∀ x, O N x = integerKernelVectorConvolution K (truncSeq N) x) ∧
        ‖O N‖ ≤ R :=
    Classical.choose_spec (mszVectorLpNorm_bound_to_lp hr'one
      (integerKernelVectorConvolution K (truncSeq N)) R hR
      (htruncConvolutionNorm N))
  have hcoordOutput (x : ℤ) (i : ι) :
      Tendsto (fun N => O N x i) atTop
        (𝓝 (integerKernelVectorConvolution K
          (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x i)) := by
    have hscalar := integerKernelConvolution_vectorLowerSpatialTruncation_tendsto
      (p := p) hp0 hpTop (K i) f i x
    apply hscalar.congr'
    filter_upwards with N
    rw [(hOspec N).1 x]
    simp [integerKernelVectorConvolution, truncSeq, trunc, grid]
  have hcoordVector (x : ℤ) :
      Tendsto (fun N => O N x) atTop
        (𝓝 (integerKernelVectorConvolution K
          (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x)) := by
    have hpi : Tendsto (fun N i => O N x i) atTop
        (𝓝 (fun i => integerKernelVectorConvolution K
          (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x i)) :=
      tendsto_pi_nhds.2 (fun i => hcoordOutput x i)
    have htoLp :=
      (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).tendsto
        (fun i => integerKernelVectorConvolution K
          (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x i) |>.comp hpi
    exact htoLp.congr' (Filter.Eventually.of_forall fun N => by
      apply PiLp.ext
      intro i
      rfl)
  have hpointwise : Tendsto (fun N x => O N x) atTop
      (𝓝 (fun x => integerKernelVectorConvolution K
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x)) :=
    tendsto_pi_nhds.2 hcoordVector
  have hfiniteMoment (t : Finset ℤ) :
      ∑ x ∈ t, ‖integerKernelVectorConvolution K
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x‖ ^ r' ≤ R ^ r' := by
    simpa only [p, ENNReal.toReal_ofReal hr'pos.le] using
      (lp.sum_rpow_le_of_tendsto hpTop
        (Filter.Eventually.of_forall fun N => (hOspec N).2)
        hpointwise t)
  let out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p :=
    lpOfUniformFiniteMomentBound hp0 hpTop
      (fun x => integerKernelVectorConvolution K
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x)
      (Real.rpow_nonneg hR _)
      (fun t => by
        simpa only [p, ENNReal.toReal_ofReal hr'pos.le] using hfiniteMoment t)
  have houtNorm : ‖out‖ ≤ R := by
    apply lp.norm_le_of_forall_sum_le
      (by rw [ENNReal.toReal_ofReal hr'pos.le]; exact hr'pos) hR
    intro t
    simpa [out, lpOfUniformFiniteMomentBound_apply, p,
      ENNReal.toReal_ofReal hr'pos.le] using hfiniteMoment t
  refine ⟨out, ?_, ?_⟩
  · intro x
    simp [out, lpOfUniformFiniteMomentBound_apply]
  · simpa [R, C] using houtNorm

end

end FractionalPrimes.Literature.MSZ

end
