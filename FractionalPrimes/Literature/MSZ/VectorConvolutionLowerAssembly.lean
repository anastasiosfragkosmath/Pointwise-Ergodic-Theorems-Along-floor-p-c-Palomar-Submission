module

public import FractionalPrimes.Literature.MSZ.VectorConvolutionLower
public import FractionalPrimes.Literature.MSZ.VectorConvolutionLowerTonelli
public import FractionalPrimes.GeneralDiscreteLpBridge
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

open scoped ENNReal
open scoped NNReal
open scoped Topology
open Filter
open MeasureTheory

namespace FractionalPrimes.Literature.MSZ

/-- Coordinatewise convolution regarded as a finite-dimensional `ℓ²`-valued
sequence. -/
noncomputable def integerKernelVectorConvolution
    {ι : Type*} [Fintype ι] (K : ι → IntegerL1Kernel)
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (x : ℤ) :
    PiLp 2 (fun _ : ι => ℂ) :=
  WithLp.toLp 2 (fun i => integerKernelConvolution (K i) (fun y => f y i) x)

/-- Each member of a finite family is bounded by its positive-convolution
maximum. -/
theorem integerKernelPositiveConvolution_le_max
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
    (K : ι → IntegerL1Kernel) (h : lp (fun _ : ℤ => ℝ) p)
    (hh : ∀ x, 0 ≤ h x) (i : ι) (x : ℤ) :
    integerKernelPositiveConvolution (K i) h x ≤
      integerKernelPositiveConvolutionMax K h hh x := by
  classical
  let c : ι → ℝ≥0 := fun j =>
    ⟨integerKernelPositiveConvolution (K j) h x,
      integerKernelPositiveConvolution_nonneg (K := K j) (h := h) hh x⟩
  change (c i : ℝ) ≤ ↑(Finset.univ.sup c)
  exact_mod_cast (Finset.le_sup (Finset.mem_univ i))

/-- The scalar factor `h=F^(r/q)` used by the lower vector endpoint. -/
noncomputable def vectorLowerFactorH {ι : Type*} [Fintype ι] (q r : ℝ)
    (v : PiLp 2 (fun _ : ι => ℂ)) : ℝ := ‖v‖ ^ (r / q)

/-- The scalar factor `g_i=|v_i|²/F^(r/q)` on `F>0`, and zero on `F=0`. -/
noncomputable def vectorLowerFactorG {ι : Type*} [Fintype ι] (q r : ℝ)
    (v : PiLp 2 (fun _ : ι => ℂ)) (i : ι) : ℝ :=
  if ‖v‖ = 0 then 0 else ‖v i‖ ^ 2 / vectorLowerFactorH q r v

/-- The scalar sequence `h=F^(r/q)` in the finite-support MSZ proof. -/
noncomputable def vectorLowerHSequence {ι : Type*} [Fintype ι] (q r : ℝ)
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) : ℤ → ℝ :=
  fun x => vectorLowerFactorH q r (f x)

/-- The component sequences `g_i=|f_i|²/F^(r/q)` in the finite-support
MSZ proof. -/
noncomputable def vectorLowerGSequence {ι : Type*} [Fintype ι] (q r : ℝ)
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) : ι → ℤ → ℝ :=
  fun i x => vectorLowerFactorG q r (f x) i

/-- The exact finite-dimensional factorization used in `lm:vectorLower`:
`|v_i|²=g_i h` and `Σ_i g_i=‖v‖ʳ`. -/
theorem vectorLowerFactorization {ι : Type*} [Fintype ι]
    (q r : ℝ) (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (v : PiLp 2 (fun _ : ι => ℂ)) :
    0 ≤ vectorLowerFactorH q r v ∧
      (∀ i, 0 ≤ vectorLowerFactorG q r v i) ∧
      (∀ i, vectorLowerFactorG q r v i * vectorLowerFactorH q r v =
        ‖v i‖ ^ 2) ∧
      (∑ i : ι, vectorLowerFactorG q r v i) = ‖v‖ ^ r := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hrpos : 0 < r := by rw [hr]; positivity
  have hexpPos : 0 < r / q := div_pos hrpos hqpos
  have hFnonneg : 0 ≤ ‖v‖ := norm_nonneg _
  have hpowNonneg : 0 ≤ ‖v‖ ^ (r / q) := Real.rpow_nonneg hFnonneg _
  have hexp : 2 - r / q = r := by
    rw [hr]
    field_simp
    ring
  refine ⟨by simpa [vectorLowerFactorH] using hpowNonneg, ?_, ?_, ?_⟩
  · intro i
    by_cases hz : ‖v‖ = 0
    · simp [vectorLowerFactorG, hz]
    · have hFpos : 0 < ‖v‖ := lt_of_le_of_ne hFnonneg (Ne.symm hz)
      have hden : 0 < vectorLowerFactorH q r v := by
        rw [vectorLowerFactorH]
        exact Real.rpow_pos_of_pos hFpos _
      simp only [vectorLowerFactorG, hz, ↓reduceIte]
      exact div_nonneg (sq_nonneg _) hden.le
  · intro i
    by_cases hz : ‖v‖ = 0
    · have hi : ‖v i‖ = 0 := by
        apply le_antisymm
        · exact (PiLp.norm_apply_le v i).trans_eq hz
        · exact norm_nonneg _
      simp [vectorLowerFactorG, vectorLowerFactorH, hz, hi,
        Real.zero_rpow hexpPos.ne']
    · have hFpos : 0 < ‖v‖ := lt_of_le_of_ne hFnonneg (Ne.symm hz)
      have hden : vectorLowerFactorH q r v ≠ 0 := by
        rw [vectorLowerFactorH]
        exact (Real.rpow_pos_of_pos hFpos _).ne'
      simp only [vectorLowerFactorG, hz, ↓reduceIte]
      exact div_mul_cancel₀ _ hden
  · by_cases hz : ‖v‖ = 0
    · have hi (i : ι) : ‖v i‖ = 0 := by
        apply le_antisymm
        · exact (PiLp.norm_apply_le v i).trans_eq hz
        · exact norm_nonneg _
      simp [vectorLowerFactorG, hz, hi, Real.zero_rpow hrpos.ne']
    · have hFpos : 0 < ‖v‖ := lt_of_le_of_ne hFnonneg (Ne.symm hz)
      calc
        (∑ i : ι, vectorLowerFactorG q r v i) =
            (∑ i : ι, ‖v i‖ ^ 2) / ‖v‖ ^ (r / q) := by
          simp [vectorLowerFactorG, hz, vectorLowerFactorH, Finset.sum_div]
        _ = ‖v‖ ^ 2 / ‖v‖ ^ (r / q) := by
          rw [← PiLp.norm_sq_eq_of_L2]
        _ = ‖v‖ ^ (2 - r / q) := by
          have hnat : ‖v‖ ^ (2 : ℕ) = ‖v‖ ^ (2 : ℝ) :=
            (Real.rpow_natCast ‖v‖ 2).symm
          rw [hnat]
          exact (Real.rpow_sub hFpos (2 : ℝ) (r / q)).symm
        _ = ‖v‖ ^ r := by rw [hexp]

/-- Pointwise factor, positivity, exact finite-family sum, and support
properties of the MSZ scalar sequences. -/
theorem vectorLowerFactorSequences_properties
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) :
    (∀ x, 0 ≤ vectorLowerHSequence q r f x) ∧
      (∀ i x, 0 ≤ vectorLowerGSequence q r f i x) ∧
      (∀ x i, ‖f x i‖ ^ 2 =
        vectorLowerGSequence q r f i x * vectorLowerHSequence q r f x) ∧
      (∀ x, (∑ i : ι, vectorLowerGSequence q r f i x) = ‖f x‖ ^ r) ∧
      (∀ x ∉ s, vectorLowerHSequence q r f x = 0 ∧
        ∀ i, vectorLowerGSequence q r f i x = 0) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hrpos : 0 < r := by rw [hr]; positivity
  have hexpPos : 0 < r / q := div_pos hrpos hqpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (vectorLowerFactorization q r hq hr (f x)).1
  · intro i x
    exact (vectorLowerFactorization q r hq hr (f x)).2.1 i
  · intro x i
    simpa [vectorLowerHSequence, vectorLowerGSequence] using
      ((vectorLowerFactorization q r hq hr (f x)).2.2.1 i).symm
  · intro x
    simpa [vectorLowerHSequence, vectorLowerGSequence] using
      (vectorLowerFactorization q r hq hr (f x)).2.2.2
  · intro x hx
    have hzero : ‖f x‖ = 0 := by simp [hs x hx]
    constructor
    · change ‖f x‖ ^ (r / q) = 0
      rw [hzero]
      exact Real.zero_rpow hexpPos.ne'
    · intro i
      change (if ‖f x‖ = 0 then 0 else
        ‖f x i‖ ^ 2 / vectorLowerFactorH q r (f x)) = 0
      simp [hzero]

/-- The finite-output Hölder step in the MSZ lower vector endpoint, with the
exact exponents `r = 2q/(q+1)`, `2/r`, and `2q/r`. -/
theorem vectorLowerHolderFinite
    {q r : ℝ} (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (U V : ℤ → ℝ) (s : Finset ℤ)
    (hU : ∀ x ∈ s, 0 ≤ U x) (hV : ∀ x ∈ s, 0 ≤ V x) :
    ∑ x ∈ s, (U x * V x) ^ (r / 2) ≤
      (∑ x ∈ s, U x) ^ (r / 2) *
        (∑ x ∈ s, V x ^ q) ^ (r / (2 * q)) := by
  have hrpos : 0 < r := by rw [hr]; positivity
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hqplus : q + 1 ≠ 0 := ne_of_gt (by linarith)
  have htriple : (2 / r).HolderTriple (2 * q / r) 1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hr]
      field_simp [ne_of_gt hqpos, hqplus] <;> ring
    · exact div_pos (by norm_num) hrpos
    · exact div_pos (mul_pos (by norm_num) hqpos) hrpos
  have hholder := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s
    (f := fun x => U x ^ (r / 2)) (g := fun x => V x ^ (r / 2)) htriple
    (fun x hx => Real.rpow_nonneg (hU x hx) _)
    (fun x hx => Real.rpow_nonneg (hV x hx) _)
  have hleft :
      (∑ x ∈ s, ((U x) ^ (r / 2) * (V x) ^ (r / 2)) ^ (1 : ℝ)) =
        ∑ x ∈ s, (U x * V x) ^ (r / 2) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Real.mul_rpow (hU x hx) (hV x hx), Real.rpow_one]
  have hUsum :
      (∑ x ∈ s, ((U x) ^ (r / 2)) ^ (2 / r)) = ∑ x ∈ s, U x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Real.rpow_mul (hU x hx)]
    congr 1
    rw [hr]
    field_simp
    rw [Real.rpow_one]
  have hVsum :
      (∑ x ∈ s, ((V x) ^ (r / 2)) ^ (2 * q / r)) =
        ∑ x ∈ s, V x ^ q := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Real.rpow_mul (hV x hx)]
    congr 1
    rw [hr]
    field_simp <;> ring
  have hexp₁ : 1 / (2 / r) = r / 2 := by field_simp [hrpos.ne']
  have hexp₂ : 1 / (2 * q / r) = r / (2 * q) := by
    field_simp [hrpos.ne', ne_of_gt hq]
  calc
    ∑ x ∈ s, (U x * V x) ^ (r / 2) =
        ∑ x ∈ s, ((U x) ^ (r / 2) * (V x) ^ (r / 2)) ^ (1 : ℝ) := hleft.symm
    _ ≤ (∑ x ∈ s, ((U x) ^ (r / 2)) ^ (2 / r)) ^ (1 / (2 / r)) *
        (∑ x ∈ s, ((V x) ^ (r / 2)) ^ (2 * q / r)) ^ (1 / (2 * q / r)) := hholder
    _ = (∑ x ∈ s, U x) ^ (r / 2) *
        (∑ x ∈ s, V x ^ q) ^ (r / (2 * q)) := by rw [hUsum, hVsum, hexp₁, hexp₂]

/-- Norm domination of convolution by an arbitrary `ℓ¹` kernel, for an
input with finite spatial support. -/
theorem integerKernelConvolution_norm_le_positiveTsum_of_finiteSupport
    (K : IntegerL1Kernel) (f : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ y ∉ s, f y = 0) (x : ℤ) :
    ‖integerKernelConvolution K f x‖ ≤
      ∑' m : ℤ, ‖K.coeff m‖ * ‖f (x - m)‖ := by
  have hexists := integerKernelConvolutionExistsAt_of_finiteInputSupport K f x s hs
  have hterm : Summable fun m : ℤ => ‖K.coeff m * f (x - m)‖ := by
    change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count at hexists
    exact MeasureTheory.integrable_count_iff.mp hexists
  rw [integerKernelConvolution_eq_tsum K f x hexists]
  calc
    ‖∑' m : ℤ, K.coeff m * f (x - m)‖ ≤
        ∑' m : ℤ, ‖K.coeff m * f (x - m)‖ := norm_tsum_le_tsum_norm hterm
    _ = ∑' m : ℤ, ‖K.coeff m‖ * ‖f (x - m)‖ := by
      apply tsum_congr
      intro m
      rw [norm_mul]

/-- Exact pointwise lower-vector factorization: finite support allows the
weighted Cauchy–Schwarz estimate to be applied to the full `ℓ¹` kernel
series. -/
theorem integerKernelConvolution_norm_sq_le_factorized_positiveTsum
    (K : IntegerL1Kernel) (f : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ y ∉ s, f y = 0) (g h : ℤ → ℝ)
    (hgs : ∀ y ∉ s, g y = 0) (hhs : ∀ y ∉ s, h y = 0)
    (hg : ∀ y, 0 ≤ g y) (hh : ∀ y, 0 ≤ h y)
    (hfactor : ∀ y, ‖f y‖ ^ 2 = g y * h y) (x : ℤ) :
    ‖integerKernelConvolution K f x‖ ^ 2 ≤
      (∑' m : ℤ, ‖K.coeff m‖ * g (x - m)) *
        ∑' m : ℤ, ‖K.coeff m‖ * h (x - m) := by
  classical
  let t := s.image fun y : ℤ => x - y
  have houtside (m : ℤ) (hm : m ∉ t) :
      ‖f (x - m)‖ = 0 ∧ g (x - m) = 0 ∧ h (x - m) = 0 := by
    have hnot : x - m ∉ s := by
      intro hmem
      apply hm
      simp only [t, Finset.mem_image]
      exact ⟨x - m, hmem, by omega⟩
    exact ⟨by rw [hs (x - m) hnot]; simp,
      hgs (x - m) hnot, hhs (x - m) hnot⟩
  have hcs := integerKernelWeightedCauchyTsumFiniteSupport K x t
    (fun y => ‖f y‖) g h houtside hg hh hfactor
  have hmajor_nonneg :
      0 ≤ ∑' m : ℤ, ‖K.coeff m‖ * ‖f (x - m)‖ :=
    tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    ‖integerKernelConvolution K f x‖ ^ 2 ≤
        (∑' m : ℤ, ‖K.coeff m‖ * ‖f (x - m)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hmajor_nonneg).2
        (integerKernelConvolution_norm_le_positiveTsum_of_finiteSupport
          K f s hs x)
    _ ≤ (∑' m : ℤ, ‖K.coeff m‖ * g (x - m)) *
          ∑' m : ℤ, ‖K.coeff m‖ * h (x - m) := hcs

/-- The pointwise vector estimate in the finite-support proof of `lm:vectorLower`.
It keeps the exact coordinatewise factorization and the finite-family maximal
function. -/
theorem integerKernelVectorConvolution_norm_sq_le_U_mul_V
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (K : ι → IntegerL1Kernel)
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ y ∉ s, f y = 0)
    (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q))
    (hh : ∀ y, 0 ≤ h y) (hsuppH : ∀ y ∉ s, h y = 0)
    (g : ι → ℤ → ℝ) (hg : ∀ i y, 0 ≤ g i y)
    (hsuppG : ∀ i y, y ∉ s → g i y = 0)
    (hfactor : ∀ y i, ‖f y i‖ ^ 2 = g i y * h y)
    (x : ℤ) :
    ‖integerKernelVectorConvolution K f x‖ ^ 2 ≤
      (∑ i : ι, ∑' m : ℤ, ‖(K i).coeff m‖ * g i (x - m)) *
        integerKernelPositiveConvolutionMax K h hh x := by
  classical
  let A : ι → ℝ := fun i => ∑' m : ℤ, ‖(K i).coeff m‖ * g i (x - m)
  let V : ℝ := integerKernelPositiveConvolutionMax K h hh x
  have hAnonneg (i : ι) : 0 ≤ A i := by
    exact tsum_nonneg fun m => mul_nonneg (norm_nonneg ((K i).coeff m)) (hg i (x - m))
  have hBle (i : ι) : integerKernelPositiveConvolution (K i) h x ≤ V := by
    exact integerKernelPositiveConvolution_le_max K h hh i x
  have hcoord (i : ι) :
      ‖integerKernelConvolution (K i) (fun y => f y i) x‖ ^ 2 ≤
        A i * integerKernelPositiveConvolution (K i) h x := by
    apply integerKernelConvolution_norm_sq_le_factorized_positiveTsum
      (K i) (fun y => f y i) s (fun y hy => by
        simpa [hs y hy])
      (g i) h (hsuppG i) hsuppH (hg i) hh (fun y => hfactor y i) x
  have hcoordMax (i : ι) :
      ‖integerKernelConvolution (K i) (fun y => f y i) x‖ ^ 2 ≤ A i * V :=
    (hcoord i).trans (mul_le_mul_of_nonneg_left (hBle i) (hAnonneg i))
  have hsum :
      (∑ i : ι, ‖integerKernelConvolution (K i) (fun y => f y i) x‖ ^ 2) ≤
        (∑ i : ι, A i) * V := by
    calc
      _ ≤ ∑ i : ι, A i * V := Finset.sum_le_sum fun i hi => hcoordMax i
      _ = (∑ i : ι, A i) * V := (Finset.sum_mul ..).symm
  unfold integerKernelVectorConvolution
  rw [PiLp.norm_sq_eq_of_L2]
  simpa [A, V] using hsum

/-- Finite-output Hölder converts the pointwise square estimate to the exact
`ℓʳ` moment bound used in the lower vector endpoint. -/
theorem vectorLower_finiteOutputMoment
    {ι : Type*} [Fintype ι] {q r : ℝ} (hq : 1 < q)
    (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (U V : ℤ → ℝ)
    (s : Finset ℤ) (hU : ∀ x ∈ s, 0 ≤ U x)
    (hV : ∀ x ∈ s, 0 ≤ V x)
    (hpoint : ∀ x ∈ s, ‖f x‖ ^ 2 ≤ U x * V x) :
    (∑ x ∈ s, ‖f x‖ ^ r) ≤
      (∑ x ∈ s, U x) ^ (r / 2) *
        (∑ x ∈ s, V x ^ q) ^ (r / (2 * q)) := by
  have hrpos : 0 < r := by rw [hr]; positivity
  have hexpPos : 0 < r / 2 := by positivity
  have hterm (x : ℤ) (hx : x ∈ s) :
      ‖f x‖ ^ r ≤ (U x * V x) ^ (r / 2) := by
    have hidentity : ‖f x‖ ^ r = (‖f x‖ ^ 2) ^ (r / 2) := by
      calc
        ‖f x‖ ^ r = ‖f x‖ ^ (2 * (r / 2)) := by congr 1 <;> ring
        _ = (‖f x‖ ^ 2) ^ (r / 2) :=
          Real.rpow_natCast_mul (norm_nonneg _) 2 (r / 2)
    rw [hidentity]
    exact Real.rpow_le_rpow (sq_nonneg _) (hpoint x hx) hexpPos.le
  calc
    ∑ x ∈ s, ‖f x‖ ^ r ≤ ∑ x ∈ s, (U x * V x) ^ (r / 2) :=
      Finset.sum_le_sum fun x hx => hterm x hx
    _ ≤ (∑ x ∈ s, U x) ^ (r / 2) *
        (∑ x ∈ s, V x ^ q) ^ (r / (2 * q)) :=
      vectorLowerHolderFinite hq hr U V s hU hV

/-- A real sequence with finite support defines an element of every finite
positive sequence `ℓᵖ` space. The constructor keeps the original pointwise
values. -/
noncomputable def lpOfRealFiniteSupport
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (u : ℤ → ℝ) (s : Finset ℤ) (hs : ∀ x ∉ s, u x = 0)
    (hu : ∀ x, 0 ≤ u x) : lp (fun _ : ℤ => ℝ) p := by
  let C : ℝ := ∑ x ∈ s, u x ^ p.toReal
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hu x) _
  exact lpOfUniformFiniteMomentBound hp0 hpTop u hC (by
      intro t
      change (∑ x ∈ t, ‖u x‖ ^ p.toReal) ≤ ∑ x ∈ s, u x ^ p.toReal
      calc
        (∑ x ∈ t, ‖u x‖ ^ p.toReal) ≤
            ∑ x ∈ (s ∪ t), ‖u x‖ ^ p.toReal :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
                (fun x hx hnot => Real.rpow_nonneg (norm_nonneg _) _)
      _ = ∑ x ∈ s, ‖u x‖ ^ p.toReal := by
        apply (Finset.sum_subset
          (show s ⊆ s ∪ t from Finset.subset_union_left) ?_).symm
        intro x hx hnot
        rw [hs x hnot]
        simp [Real.zero_rpow hp.ne']
      _ = ∑ x ∈ s, u x ^ p.toReal := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (hu x)])

@[simp] theorem lpOfRealFiniteSupport_apply
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (u : ℤ → ℝ) (s : Finset ℤ) (hs : ∀ x ∉ s, u x = 0)
    (hu : ∀ x, 0 ≤ u x) (x : ℤ) :
    lpOfRealFiniteSupport hp0 hpTop u s hs hu x = u x := rfl

/-- The finite-support factor `h=F^(r/q)` viewed as an element of `ℓ^q`. -/
noncomputable def vectorLowerHInLp
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hprops := vectorLowerFactorSequences_properties hq hr f s hs
  exact lpOfRealFiniteSupport
    (ENNReal.ofReal_ne_zero_iff.mpr hqpos) ENNReal.ofReal_ne_top
    (vectorLowerHSequence q r f) s
    (fun x hx => (hprops.2.2.2.2 x hx).1)
    (fun x => hprops.1 x)

@[simp] theorem vectorLowerHInLp_apply
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) (x : ℤ) :
    vectorLowerHInLp hq hr f s hs x = vectorLowerHSequence q r f x := by
  simp [vectorLowerHInLp, lpOfRealFiniteSupport_apply]

/-- The `ℓ^q` mass of the exact `h` factor is `∑ ‖f x‖ʳ`, as in the
finite-support proof of the lower vector endpoint. -/
theorem vectorLowerHInLp_norm_rpow
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) :
    ‖vectorLowerHInLp hq hr f s hs‖ ^ q =
      ∑ x ∈ s, ‖f x‖ ^ r := by
  classical
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hprops := vectorLowerFactorSequences_properties hq hr f s hs
  let H := vectorLowerHInLp hq hr f s hs
  have htoReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hqpos.le
  have hnormRaw :
      ‖H‖ ^ (ENNReal.ofReal q).toReal =
        ∑' x : ℤ, ‖H x‖ ^ (ENNReal.ofReal q).toReal :=
    lp.norm_rpow_eq_tsum (by rw [htoReal]; exact hqpos) H
  have hnorm : ‖H‖ ^ q = ∑' x : ℤ, ‖H x‖ ^ q := by
    simpa only [htoReal] using hnormRaw
  rw [hnorm]
  rw [tsum_eq_sum (s := s) (fun x hx => by
    rw [vectorLowerHInLp_apply]
    rw [(hprops.2.2.2.2 x hx).1]
    simp [Real.zero_rpow hqpos.ne'])]
  apply Finset.sum_congr rfl
  intro x hx
  rw [vectorLowerHInLp_apply, Real.norm_eq_abs,
    abs_of_nonneg (hprops.1 x)]
  change (‖f x‖ ^ (r / q)) ^ q = ‖f x‖ ^ r
  rw [← Real.rpow_mul (norm_nonneg (f x))]
  congr 1
  field_simp [ne_of_gt hqpos]

/-- The `U` term in the lower vector endpoint is summable and has total mass
at most `E₀` times the total mass of the factor sum. -/
theorem vectorLower_positiveU_mass_bound
    {ι : Type*} [Fintype ι]
    (K : ι → IntegerL1Kernel) (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (g : ι → ℤ → ℝ) (F : ℤ → ℝ) (s : Finset ℤ)
    (hg : ∀ i x, 0 ≤ g i x) (hgsupp : ∀ i x, x ∉ s → g i x = 0)
    (hF : ∀ x, 0 ≤ F x) (hFsupp : ∀ x ∉ s, F x = 0)
    (hgsum : ∀ x, (∑ i : ι, g i x) = F x) :
    Summable (fun x : ℤ => ∑ i : ι,
      ∑' m : ℤ, ‖(K i).coeff m‖ * g i (x - m)) ∧
    (∑' x : ℤ, ∑ i : ι,
      ∑' m : ℤ, ‖(K i).coeff m‖ * g i (x - m)) ≤
      E₀ * ∑ x ∈ s, F x := by
  classical
  let A : ι → ℤ → ℝ := fun i x =>
    ∑' m : ℤ, ‖(K i).coeff m‖ * g i (x - m)
  have hgi (i : ι) : Summable (g i) := by
    apply summable_of_ne_finset_zero (s := s)
    intro x hx
    simp [hgsupp i x hx]
  have hAi (i : ι) : Summable (A i) := by
    dsimp [A]
    exact integerKernelPositiveConvolutionTsum_summable (K i) (g i)
      (hgi i) (hg i)
  have hUs (t : Finset ι) :
      Summable (fun x : ℤ => ∑ i ∈ t, A i x) := by
    induction t using Finset.induction_on with
    | empty => simpa
    | @insert i t hi ih =>
        simpa [Finset.sum_insert, hi] using (hAi i).add ih
  have hU : Summable (fun x : ℤ => ∑ i : ι, A i x) := by
    simpa using hUs Finset.univ
  have htotal :
      (∑' x : ℤ, ∑ i : ι, A i x) =
        ∑ i : ι, (integerKernelL1Mass (K i) * ∑' x : ℤ, g i x) := by
    calc
      _ = ∑ i : ι, ∑' x : ℤ, A i x :=
        Summable.tsum_finsetSum (fun i hi => hAi i)
      _ = ∑ i : ι, (integerKernelL1Mass (K i) * ∑' x : ℤ, g i x) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integerKernelPositiveConvolutionTsum_eq_mass_mul_tsum
          (K i) (g i) (hgi i) (hg i)
  have hsumG : (∑ i : ι, ∑' x : ℤ, g i x) = ∑ x ∈ s, F x := by
    calc
      _ = ∑ i : ι, ∑ x ∈ s, g i x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [tsum_eq_sum (s := s) (fun x hx => by simp [hgsupp i x hx])]
      _ = ∑ x ∈ s, ∑ i : ι, g i x := by rw [Finset.sum_comm]
      _ = ∑ x ∈ s, F x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hgsum x
  refine ⟨by simpa [A] using hU, ?_⟩
  rw [htotal]
  calc
    (∑ i : ι, integerKernelL1Mass (K i) * ∑' x : ℤ, g i x) ≤
        ∑ i : ι, E₀ * ∑' x : ℤ, g i x := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hmass i)
        (tsum_nonneg (hg i))
    _ = E₀ * ∑ i : ι, ∑' x : ℤ, g i x := by rw [Finset.mul_sum]
    _ = E₀ * ∑ x ∈ s, F x := by rw [hsumG]

/-- The finite-support endpoint moment estimate in `lm:vectorLower`.
The maximal hypothesis states exactly that the positive pointwise maximum
belongs to `ℓ^q` with norm at most `B` times the input norm. -/
theorem vectorLower_finiteSupportMomentBound
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (K : ι → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) (t : Finset ℤ) :
    (∑ x ∈ t, ‖integerKernelVectorConvolution K f x‖ ^ r) ≤
      (E₀ * B) ^ (r / 2) * ∑ x ∈ s, ‖f x‖ ^ r := by
  classical
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hrpos : 0 < r := by rw [hr]; positivity
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
  let H := vectorLowerHInLp hq hr f s hs
  let hseq : ℤ → ℝ := vectorLowerHSequence q r f
  let gseq : ι → ℤ → ℝ := vectorLowerGSequence q r f
  let F : ℤ → ℝ := fun x => ‖f x‖ ^ r
  let M₀ : ℝ := ∑ x ∈ s, ‖f x‖ ^ r
  let U : ℤ → ℝ := fun x =>
    ∑ i : ι, ∑' m : ℤ, ‖(K i).coeff m‖ * gseq i (x - m)
  let V : ℤ → ℝ := integerKernelPositiveConvolutionMax K H (by
    intro x
    exact vectorLowerFactorSequences_properties hq hr f s hs |>.1 x)
  have hprops := vectorLowerFactorSequences_properties hq hr f s hs
  have hM₀nonneg : 0 ≤ M₀ := by
    dsimp [M₀]
    exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (norm_nonneg (f x)) _
  have hFnonneg (x : ℤ) : 0 ≤ F x := Real.rpow_nonneg (norm_nonneg (f x)) _
  have hFsupp (x : ℤ) (hx : x ∉ s) : F x = 0 := by
    simp [F, hs x hx, Real.zero_rpow hrpos.ne']
  have hgsupp (i : ι) (x : ℤ) (hx : x ∉ s) : gseq i x = 0 := by
    exact (hprops.2.2.2.2 x hx).2 i
  have hgsum (x : ℤ) : (∑ i : ι, gseq i x) = F x := by
    simpa [F, gseq] using hprops.2.2.2.1 x
  have hUmass := vectorLower_positiveU_mass_bound
    K E₀ hE₀ hmass gseq F s
    (fun i x => hprops.2.1 i x)
    hgsupp hFnonneg hFsupp hgsum
  have hUnonneg (x : ℤ) : 0 ≤ U x := by
    dsimp [U]
    apply Finset.sum_nonneg
    intro i hi
    exact tsum_nonneg fun m =>
      mul_nonneg (norm_nonneg ((K i).coeff m)) (hprops.2.1 i (x - m))
  have hUsumBound : (∑ x ∈ t, U x) ≤ E₀ * M₀ := by
    calc
      ∑ x ∈ t, U x ≤ ∑' x : ℤ, U x :=
        hUmass.1.sum_le_tsum t (fun x hx => hUnonneg x)
      _ ≤ E₀ * M₀ := by
        simpa [U, M₀, F, gseq, hgsum] using hUmass.2
  have hUsumNonneg : 0 ≤ ∑ x ∈ t, U x :=
    Finset.sum_nonneg fun x hx => hUnonneg x
  have hHnonneg (x : ℤ) : 0 ≤ H x := by
    simpa [H, vectorLowerHInLp_apply] using hprops.1 x
  obtain ⟨M, hMpoint, hMnorm⟩ := hmax H hHnonneg
  have hVnonneg (x : ℤ) : 0 ≤ V x := by
    dsimp [V, integerKernelPositiveConvolutionMax]
    positivity
  have hMnonneg (x : ℤ) : 0 ≤ M x := by
    rw [hMpoint x]
    exact hVnonneg x
  have hVsumBound : (∑ x ∈ t, V x ^ q) ≤ B ^ q * M₀ := by
    have hsumV : (∑ x ∈ t, V x ^ q) = ∑ x ∈ t, ‖M x‖ ^ q := by
      apply Finset.sum_congr rfl
      intro x hx
      change (integerKernelPositiveConvolutionMax K H hHnonneg x) ^ q =
        ‖M x‖ ^ q
      rw [← hMpoint x, Real.norm_of_nonneg (hMnonneg x)]
    have hqENN : 0 < (ENNReal.ofReal q).toReal := by
      rw [ENNReal.toReal_ofReal hqpos.le]
      exact hqpos
    calc
      ∑ x ∈ t, V x ^ q = ∑ x ∈ t, ‖M x‖ ^ q := hsumV
      _ ≤ ‖M‖ ^ q := by
        simpa only [ENNReal.toReal_ofReal hqpos.le] using
          (lp.sum_rpow_le_norm_rpow hqENN M t)
      _ ≤ (B * ‖H‖) ^ q :=
        Real.rpow_le_rpow (norm_nonneg M) hMnorm hqpos.le
      _ = B ^ q * M₀ := by
        rw [Real.mul_rpow hB (norm_nonneg H)]
        rw [vectorLowerHInLp_norm_rpow hq hr f s hs]
  have hVsumNonneg : 0 ≤ ∑ x ∈ t, V x ^ q :=
    Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hVnonneg x) _
  have hmoment := vectorLower_finiteOutputMoment hq hr
    (integerKernelVectorConvolution K f) U V t
    (fun x hx => hUnonneg x) (fun x hx => hVnonneg x)
    (fun x hx => by
      simpa [U, V, gseq, H, vectorLowerHInLp_apply] using
        (integerKernelVectorConvolution_norm_sq_le_U_mul_V
          hq hr K f s hs H hHnonneg
          (fun x hx => (hprops.2.2.2.2 x hx).1)
          gseq (fun i x => hprops.2.1 i x) hgsupp
          (fun x i => hprops.2.2.1 x i) x))
  have hUroot :
      (∑ x ∈ t, U x) ^ (r / 2) ≤ (E₀ * M₀) ^ (r / 2) :=
    Real.rpow_le_rpow hUsumNonneg hUsumBound (by positivity)
  have hVroot :
      (∑ x ∈ t, V x ^ q) ^ (r / (2 * q)) ≤
        (B ^ q * M₀) ^ (r / (2 * q)) :=
    Real.rpow_le_rpow hVsumNonneg hVsumBound (by positivity)
  have hrootProduct :
      (∑ x ∈ t, U x) ^ (r / 2) *
          (∑ x ∈ t, V x ^ q) ^ (r / (2 * q)) ≤
        (E₀ * B) ^ (r / 2) * M₀ := by
    have hupperU : 0 ≤ (E₀ * M₀) ^ (r / 2) := Real.rpow_nonneg
      (mul_nonneg hE₀ hM₀nonneg) _
    calc
      _ ≤ (E₀ * M₀) ^ (r / 2) *
          (B ^ q * M₀) ^ (r / (2 * q)) :=
            mul_le_mul hUroot hVroot (Real.rpow_nonneg hVsumNonneg _) hupperU
      _ = (E₀ * B) ^ (r / 2) * M₀ := by
        have hBpow : (B ^ q) ^ (r / (2 * q)) = B ^ (r / 2) := by
          rw [← Real.rpow_mul hB]
          congr 1
          field_simp [ne_of_gt hqpos]
        have ha_pos : 0 < r / 2 := by positivity
        have hb_pos : 0 < r / (2 * q) := by positivity
        have hexp : r / 2 + r / (2 * q) = 1 := by
          rw [hr]
          field_simp [ne_of_gt hqpos,
            ne_of_gt (by linarith : 0 < q + 1)] <;> ring
        calc
          _ = (E₀ ^ (r / 2) * M₀ ^ (r / 2)) *
              ((B ^ q) ^ (r / (2 * q)) * M₀ ^ (r / (2 * q))) := by
                rw [Real.mul_rpow hE₀ hM₀nonneg,
                  Real.mul_rpow (Real.rpow_nonneg hB q) hM₀nonneg]
          _ = (E₀ ^ (r / 2) * B ^ (r / 2)) *
              (M₀ ^ (r / 2) * M₀ ^ (r / (2 * q))) := by
                rw [hBpow]
                ring
          _ = (E₀ * B) ^ (r / 2) * M₀ := by
                rw [← Real.mul_rpow hE₀ hB]
                by_cases hMzero : M₀ = 0
                · simp [hMzero, Real.zero_rpow ha_pos.ne',
                    Real.zero_rpow hb_pos.ne']
                · have hMpos : 0 < M₀ := lt_of_le_of_ne hM₀nonneg (Ne.symm hMzero)
                  rw [← Real.rpow_add hMpos, hexp, Real.rpow_one]
  calc
    ∑ x ∈ t, ‖integerKernelVectorConvolution K f x‖ ^ r ≤
        (∑ x ∈ t, U x) ^ (r / 2) *
          (∑ x ∈ t, V x ^ q) ^ (r / (2 * q)) := hmoment
    _ ≤ (E₀ * B) ^ (r / 2) * M₀ := hrootProduct
    _ = (E₀ * B) ^ (r / 2) * ∑ x ∈ s, ‖f x‖ ^ r := by rfl

/-- A finitely supported mixed `ℓʳ(ℓ²)` input, represented in the sequence
`ℓʳ` space. -/
noncomputable def vectorLowerInputInLp
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) :
    lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal r) := by
  have hrpos : 0 < r := by rw [hr]; positivity
  let C : ℝ := ∑ x ∈ s, ‖f x‖ ^ r
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (norm_nonneg (f x)) _
  have hfiniteReal : ∀ t : Finset ℤ,
      ∑ x ∈ t, ‖f x‖ ^ r ≤ C := by
    intro t
    calc
      ∑ x ∈ t, ‖f x‖ ^ r ≤ ∑ x ∈ s ∪ t, ‖f x‖ ^ r :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun x hx hnot => Real.rpow_nonneg (norm_nonneg (f x)) _)
      _ = ∑ x ∈ s, ‖f x‖ ^ r := by
        apply (Finset.sum_subset (show s ⊆ s ∪ t from Finset.subset_union_left) ?_).symm
        intro x hx hnot
        rw [hs x hnot]
        simp [Real.zero_rpow hrpos.ne']
      _ = C := by rfl
  have hfinite : ∀ t : Finset ℤ,
      ∑ x ∈ t, ‖f x‖ ^ (ENNReal.ofReal r).toReal ≤ C := by
    intro t
    simpa only [ENNReal.toReal_ofReal hrpos.le] using hfiniteReal t
  exact lpOfUniformFiniteMomentBound
    (ENNReal.ofReal_ne_zero_iff.mpr hrpos) ENNReal.ofReal_ne_top
    f hC hfinite

@[simp] theorem vectorLowerInputInLp_apply
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) (x : ℤ) :
    vectorLowerInputInLp hq hr f s hs x = f x := by
  simp [vectorLowerInputInLp]

/-- The norm of the finite-support input is its exact mixed `ℓʳ(ℓ²)` mass. -/
theorem vectorLowerInputInLp_norm_rpow
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) :
    ‖vectorLowerInputInLp hq hr f s hs‖ ^ r =
      ∑ x ∈ s, ‖f x‖ ^ r := by
  classical
  have hrpos : 0 < r := by rw [hr]; positivity
  let I := vectorLowerInputInLp hq hr f s hs
  have htoReal : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hrpos.le
  have hnormRaw :
      ‖I‖ ^ (ENNReal.ofReal r).toReal =
        ∑' x : ℤ, ‖I x‖ ^ (ENNReal.ofReal r).toReal :=
    lp.norm_rpow_eq_tsum (by rw [htoReal]; exact hrpos) I
  have hnorm : ‖I‖ ^ r = ∑' x : ℤ, ‖I x‖ ^ r := by
    simpa only [htoReal] using hnormRaw
  rw [hnorm]
  rw [tsum_eq_sum (s := s) (fun x hx => by
    rw [vectorLowerInputInLp_apply, hs x hx]
    simp [Real.zero_rpow hrpos.ne'])]
  apply Finset.sum_congr rfl
  intro x hx
  rw [vectorLowerInputInLp_apply]

/-- The complete finite-support lower-vector endpoint estimate in `lm:vectorLower`.
It produces the exact output `ℓʳ` sequence and its norm bound. -/
theorem vectorLower_finiteSupportNormBound
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (K : ι → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) (s : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) :
    ∃ out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal r),
      (∀ x, out x = integerKernelVectorConvolution K f x) ∧
      ‖out‖ ≤ Real.sqrt (E₀ * B) *
        ‖vectorLowerInputInLp hq hr f s hs‖ := by
  classical
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrone : 1 < r := by
    rw [hr]
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  letI : Fact (1 ≤ ENNReal.ofReal r) :=
    ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hrone)⟩
  let I := vectorLowerInputInLp hq hr f s hs
  let M₀ : ℝ := ∑ x ∈ s, ‖f x‖ ^ r
  let R : ℝ := Real.sqrt (E₀ * B) * ‖I‖
  have hM₀nonneg : 0 ≤ M₀ := by
    dsimp [M₀]
    exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (norm_nonneg (f x)) _
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg I)
  have hsqrtPow : (Real.sqrt (E₀ * B)) ^ r = (E₀ * B) ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg hE₀ hB)]
    congr 1
    ring
  have hRpow : R ^ r = (E₀ * B) ^ (r / 2) * M₀ := by
    dsimp [R]
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg I), hsqrtPow,
      vectorLowerInputInLp_norm_rpow hq hr f s hs]
  have hfiniteReal : ∀ t : Finset ℤ,
      (∑ x ∈ t, ‖integerKernelVectorConvolution K f x‖ ^ r) ≤ R ^ r := by
    intro t
    calc
      ∑ x ∈ t, ‖integerKernelVectorConvolution K f x‖ ^ r ≤
          (E₀ * B) ^ (r / 2) * ∑ x ∈ s, ‖f x‖ ^ r :=
        vectorLower_finiteSupportMomentBound hq hr K E₀ B hE₀ hB hmass hmax
          f s hs t
      _ = R ^ r := by simpa [M₀] using hRpow.symm
  have hfinite : ∀ t : Finset ℤ,
      (∑ x ∈ t, ‖integerKernelVectorConvolution K f x‖ ^
        (ENNReal.ofReal r).toReal) ≤ R ^ (ENNReal.ofReal r).toReal := by
    intro t
    simpa only [ENNReal.toReal_ofReal hrpos.le] using hfiniteReal t
  let O : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal r) :=
    lpOfUniformFiniteMomentBound
      (ENNReal.ofReal_ne_zero_iff.mpr hrpos) ENNReal.ofReal_ne_top
      (integerKernelVectorConvolution K f) (Real.rpow_nonneg hRnonneg _)
      (by simpa only [ENNReal.toReal_ofReal hrpos.le] using hfinite)
  have hnormO : ‖O‖ ≤ R := by
    apply lp.norm_le_of_forall_sum_le
      (by rw [ENNReal.toReal_ofReal hrpos.le]; exact hrpos) hRnonneg
    intro t
    simpa only [O, lpOfUniformFiniteMomentBound_apply,
      ENNReal.toReal_ofReal hrpos.le] using hfiniteReal t
  refine ⟨O, ?_, hnormO⟩
  · intro x
    simp [O]

/-- Symmetric finite spatial truncation of an arbitrary mixed-sequence `lp`
input. -/
noncomputable def vectorLowerSpatialTruncation
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p)
    (s : Finset ℤ) : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p :=
  ∑ x ∈ s, lp.single p x (f x)

@[simp] theorem vectorLowerSpatialTruncation_apply
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p)
    (s : Finset ℤ) (x : ℤ) :
    vectorLowerSpatialTruncation f s x = if x ∈ s then f x else 0 := by
  classical
  change (∑ y ∈ s, lp.single p y (f y)) x = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]

theorem vectorLowerSpatialTruncation_norm_le
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p) (s : Finset ℤ) :
    ‖vectorLowerSpatialTruncation f s‖ ≤ ‖f‖ := by
  apply lp.norm_mono hp0
  intro x
  rw [vectorLowerSpatialTruncation_apply]
  by_cases hx : x ∈ s <;> simp [hx]

theorem vectorLowerSpatialTruncation_supported
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p)
    (s : Finset ℤ) :
    ∀ x ∉ s, vectorLowerSpatialTruncation f s x = 0 := by
  intro x hx
  simp [vectorLowerSpatialTruncation_apply, hx]

/-- The exact spatial truncations converge in mixed sequence `lp`. The
argument is Mathlib's `lp.hasSum_single` followed by the cofinal symmetric
intervals in `ℤ`. -/
theorem vectorLowerSpatialTruncation_Icc_tendsto
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpTop : p ≠ ∞)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p) :
    Tendsto (fun N : ℕ =>
      vectorLowerSpatialTruncation f (Finset.Icc (-(N : ℤ)) (N : ℤ)))
      atTop (𝓝 f) := by
  classical
  have hsum : HasSum (fun x : ℤ => lp.single p x (f x)) f :=
    lp.hasSum_single hpTop f
  have hmono : Monotone
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro n k hnk
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hnk)
    · exact Int.ofNat_le.mpr hnk
  have hcofinal : ∀ z : ℤ, ∃ N : ℕ,
      z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro z
    refine ⟨z.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    have habs := abs_le.mp (le_rfl : |z| ≤ |z|)
    rw [Int.abs_eq_natAbs] at habs
    exact habs
  have hfilter : Tendsto
      (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    hmono.tendsto_atTop_finset hcofinal
  have hsumFilter : Tendsto
      (fun s : Finset ℤ => ∑ x ∈ s, lp.single p x (f x))
      atTop (𝓝 f) := by
    simpa only [HasSum, SummationFilter.unconditional_filter] using hsum
  have hcomp := hsumFilter.comp hfilter
  apply hcomp.congr'
  filter_upwards with N
  rfl

/-- Projection to one coordinate preserves the pointwise representative and
is contractive on the mixed sequence `lp` space. -/
noncomputable def vectorLowerCoordinateLp
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p) (i : ι) :
    lp (fun _ : ℤ => ℂ) p := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  let C : ℝ := ‖f‖ ^ p.toReal
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg (norm_nonneg f) _
  have hfinite : ∀ s : Finset ℤ,
      ∑ x ∈ s, ‖f x i‖ ^ p.toReal ≤ C := by
    intro s
    calc
      ∑ x ∈ s, ‖f x i‖ ^ p.toReal ≤
          ∑ x ∈ s, ‖f x‖ ^ p.toReal := by
            apply Finset.sum_le_sum
            intro x hx
            exact Real.rpow_le_rpow (norm_nonneg _) (PiLp.norm_apply_le (f x) i) hp.le
      _ ≤ ‖f‖ ^ p.toReal := lp.sum_rpow_le_norm_rpow hp f s
  exact lpOfUniformFiniteMomentBound hp0 hpTop (fun x => f x i) hC hfinite

@[simp] theorem vectorLowerCoordinateLp_apply
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p) (i : ι) (x : ℤ) :
    vectorLowerCoordinateLp hp0 hpTop f i x = f x i := rfl

theorem vectorLowerCoordinateLp_norm_le
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p) (i : ι) :
    ‖vectorLowerCoordinateLp hp0 hpTop f i‖ ≤ ‖f‖ := by
  apply lp.norm_mono hp0
  intro x
  rw [vectorLowerCoordinateLp_apply]
  exact PiLp.norm_apply_le (f x) i

/-- Convolution of one coordinate of the symmetric spatial truncations
converges pointwise to convolution of that coordinate of the original
input. This is the scalar continuity step in the general-input extension of
`lm:vectorLower`. -/
theorem integerKernelConvolution_vectorLowerSpatialTruncation_tendsto
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    [Fact (1 ≤ p)] (K : IntegerL1Kernel)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p)
    (i : ι) (x : ℤ) :
    Tendsto
      (fun N : ℕ => integerKernelConvolution K
        (fun y => vectorLowerSpatialTruncation f
          (Finset.Icc (-(N : ℤ)) (N : ℤ)) y i) x)
      atTop
      (𝓝 (integerKernelConvolution K (fun y => f y i) x)) := by
  classical
  let trunc : ℕ → lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p :=
    fun N => vectorLowerSpatialTruncation f
      (Finset.Icc (-(N : ℤ)) (N : ℤ))
  let coord : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p →
      lp (fun _ : ℤ => ℂ) p :=
    fun F => vectorLowerCoordinateLp hp0 hpTop F i
  let input : ℕ → Lp ℂ p (Measure.count : Measure ℤ) :=
    fun N => generalLpToCountLp hp0 hpTop (coord (trunc N))
  let inputLimit : Lp ℂ p (Measure.count : Measure ℤ) :=
    generalLpToCountLp hp0 hpTop (coord f)
  let T : Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ p (Measure.count : Measure ℤ) :=
    integerKernelLpConvolutionCLM (p := p) K
  let output : ℕ → lp (fun _ : ℤ => ℂ) p :=
    fun N => countLpToGeneralLp hp0 hpTop (T (input N))
  let outputLimit : lp (fun _ : ℤ => ℂ) p :=
    countLpToGeneralLp hp0 hpTop (T inputLimit)
  have htrunc : Tendsto trunc atTop (𝓝 f) := by
    simpa [trunc] using vectorLowerSpatialTruncation_Icc_tendsto hpTop f
  have hcoordDiff (N : ℕ) :
      ‖coord (trunc N) - coord f‖ ≤ ‖trunc N - f‖ := by
    have hEq : coord (trunc N) - coord f = coord (trunc N - f) := by
      apply lp.ext
      funext y
      simp [coord, vectorLowerCoordinateLp_apply]
    rw [hEq]
    exact vectorLowerCoordinateLp_norm_le hp0 hpTop (trunc N - f) i
  have hinput : Tendsto input atTop (𝓝 inputLimit) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hnear := (Metric.tendsto_nhds.mp htrunc) ε hε
    filter_upwards [hnear] with N hN
    have hdist : dist (input N) inputLimit ≤ dist (trunc N) f := by
      rw [dist_eq_norm, dist_eq_norm]
      calc
        ‖input N - inputLimit‖ =
            ‖generalLpToCountLp hp0 hpTop
              (coord (trunc N) - coord f)‖ := by
                simp [input, inputLimit, T, map_sub]
        _ = ‖coord (trunc N) - coord f‖ :=
          generalLpToCountLp_norm hp0 hpTop _
        _ ≤ ‖trunc N - f‖ := hcoordDiff N
    exact lt_of_le_of_lt hdist hN
  have houtput : Tendsto (fun N => T (input N)) atTop (𝓝 (T inputLimit)) :=
    T.continuous.tendsto inputLimit |>.comp hinput
  have houtputCoord (N : ℕ) :
      ‖output N - outputLimit‖ ≤ ‖T (input N) - T inputLimit‖ := by
    have hEq : output N - outputLimit =
        countLpToGeneralLp hp0 hpTop (T (input N) - T inputLimit) := by
      simp [output, outputLimit, map_sub]
    rw [hEq]
    exact countLpToGeneralLp_norm hp0 hpTop _ |>.le
  have hpoint (y : ℤ) :
      Tendsto (fun N => output N y) atTop (𝓝 (outputLimit y)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hnear := (Metric.tendsto_nhds.mp houtput) ε hε
    filter_upwards [hnear] with N hN
    have hEval : dist (output N y) (outputLimit y) ≤
        dist (T (input N)) (T inputLimit) := by
      calc
        dist (output N y) (outputLimit y) =
            ‖output N y - outputLimit y‖ := dist_eq_norm _ _
        _ = ‖(output N - outputLimit) y‖ := by
          simp only [lp.coeFn_sub, Pi.sub_apply]
        _ ≤ ‖output N - outputLimit‖ :=
          lp.norm_apply_le_norm hp0 (output N - outputLimit) y
        _ ≤ ‖T (input N) - T inputLimit‖ := houtputCoord N
        _ = dist (T (input N)) (T inputLimit) := (dist_eq_norm ..).symm
    exact lt_of_le_of_lt hEval hN
  have hpointIdent (N : ℕ) : output N x =
      integerKernelConvolution K
        (fun y => vectorLowerSpatialTruncation f
          (Finset.Icc (-(N : ℤ)) (N : ℤ)) y i) x := by
    change (countLpToGeneralLp hp0 hpTop
      (integerKernelLpConvolutionCLM (p := p) K
        (generalLpToCountLp hp0 hpTop (coord (trunc N)))) : ℤ → ℂ) x = _
    rw [countLpToGeneralLp_apply, integerKernelLpConvolutionCLM_apply,
      integerKernelLpConvolution_apply_eq_integerKernelConvolution]
    change integerKernelConvolution K
      (fun y => (generalLpToCountLp hp0 hpTop
        (coord (trunc N)) : ℤ → ℂ) y) x = _
    congr 1
    funext y
    rw [generalLpToCountLp_apply]
    simp [coord, trunc, vectorLowerSpatialTruncation_apply]
  have hlimitIdent : outputLimit x =
      integerKernelConvolution K (fun y => f y i) x := by
    change (countLpToGeneralLp hp0 hpTop
      (integerKernelLpConvolutionCLM (p := p) K
        (generalLpToCountLp hp0 hpTop (coord f))) : ℤ → ℂ) x = _
    rw [countLpToGeneralLp_apply, integerKernelLpConvolutionCLM_apply,
      integerKernelLpConvolution_apply_eq_integerKernelConvolution]
    change integerKernelConvolution K
      (fun y => (generalLpToCountLp hp0 hpTop
        (coord f) : ℤ → ℂ) y) x = _
    congr 1
    funext y
    rw [generalLpToCountLp_apply]
    simp [coord]
  have hconv := hpoint x
  rw [hlimitIdent] at hconv
  exact hconv.congr' (Filter.Eventually.of_forall fun N => hpointIdent N)

/-- The full lower-vector endpoint estimate `lm:vectorLower`, obtained from
the checked finite-support estimate by the source's spatial truncation and
componentwise continuity argument. -/
theorem vectorLower_normBound
    {ι : Type*} [Fintype ι] {q r : ℝ}
    (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (K : ι → IntegerL1Kernel) (E₀ B : ℝ)
    (hE₀ : 0 ≤ E₀) (hB : 0 ≤ B)
    (hmass : ∀ i, integerKernelL1Mass (K i) ≤ E₀)
    (hmax : ∀ (h : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q)),
      (hh : ∀ x, 0 ≤ h x) →
      ∃ M : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, M x = integerKernelPositiveConvolutionMax K h hh x) ∧
          ‖M‖ ≤ B * ‖h‖)
    (f : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal r)) :
    ∃ out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) (ENNReal.ofReal r),
      (∀ x, out x = integerKernelVectorConvolution K (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x) ∧
        ‖out‖ ≤ Real.sqrt (E₀ * B) * ‖f‖ := by
  classical
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrone : 1 < r := by
    rw [hr]
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  let p : ℝ≥0∞ := ENNReal.ofReal r
  have hp0 : p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hrpos
  have hpTop : p ≠ ∞ := ENNReal.ofReal_ne_top
  letI : Fact (1 ≤ p) := ⟨(ENNReal.one_le_ofReal).2 (le_of_lt hrone)⟩
  let C : ℝ := Real.sqrt (E₀ * B)
  let bound : ℝ := C * ‖f‖
  have hC : 0 ≤ C := by dsimp [C]; exact Real.sqrt_nonneg _
  have hbound : 0 ≤ bound := by
    dsimp [bound]
    exact mul_nonneg hC (norm_nonneg _)
  let grid : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ)
  let trunc : ℕ → lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p :=
    fun N => vectorLowerSpatialTruncation f (grid N)
  let truncSeq : ℕ → ℤ → PiLp 2 (fun _ : ι => ℂ) := fun N x => trunc N x
  have htruncSupport (N : ℕ) : ∀ x ∉ grid N, truncSeq N x = 0 := by
    intro x hx
    simp [truncSeq, trunc, vectorLowerSpatialTruncation_apply, hx]
  have htruncNorm (N : ℕ) : ‖trunc N‖ ≤ ‖f‖ := by
    exact vectorLowerSpatialTruncation_norm_le hp0 f (grid N)
  have hinputId (N : ℕ) :
      vectorLowerInputInLp hq hr (truncSeq N) (grid N) (htruncSupport N) = trunc N := by
    apply lp.ext
    funext x
    simp [truncSeq, vectorLowerInputInLp_apply]
  let O : ℕ → lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p := fun N =>
    Classical.choose (vectorLower_finiteSupportNormBound hq hr K E₀ B hE₀ hB
      hmass hmax (truncSeq N) (grid N) (htruncSupport N))
  have hOspec (N : ℕ) :
      (∀ x, O N x = integerKernelVectorConvolution K (truncSeq N) x) ∧
        ‖O N‖ ≤ C *
          ‖vectorLowerInputInLp hq hr (truncSeq N) (grid N) (htruncSupport N)‖ :=
    Classical.choose_spec (vectorLower_finiteSupportNormBound hq hr K E₀ B hE₀ hB
      hmass hmax (truncSeq N) (grid N) (htruncSupport N))
  have hOnorm (N : ℕ) : ‖O N‖ ≤ bound := by
    calc
      ‖O N‖ ≤ C *
          ‖vectorLowerInputInLp hq hr (truncSeq N) (grid N) (htruncSupport N)‖ :=
        (hOspec N).2
      _ = C * ‖trunc N‖ := by rw [hinputId N]
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_left (htruncNorm N) hC
      _ = bound := rfl
  have hcoordOutput (x : ℤ) (i : ι) :
      Tendsto (fun N => O N x i) atTop
        (𝓝 (integerKernelVectorConvolution K (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x i)) := by
    have hscalar := integerKernelConvolution_vectorLowerSpatialTruncation_tendsto
      (p := p) hp0 hpTop (K i) f i x
    apply hscalar.congr'
    filter_upwards with N
    rw [(hOspec N).1 x]
    simp [integerKernelVectorConvolution, truncSeq, trunc, grid]
  have hcoordVector (x : ℤ) :
      Tendsto (fun N => O N x) atTop
        (𝓝 (integerKernelVectorConvolution K (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x)) := by
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
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x‖ ^ r ≤ bound ^ r := by
    simpa only [p, ENNReal.toReal_ofReal hrpos.le] using
      (lp.sum_rpow_le_of_tendsto hpTop
        (Filter.Eventually.of_forall hOnorm) hpointwise t)
  let out : lp (fun _ : ℤ => PiLp 2 (fun _ : ι => ℂ)) p :=
    lpOfUniformFiniteMomentBound hp0 hpTop
      (fun x => integerKernelVectorConvolution K
        (f : ℤ → PiLp 2 (fun _ : ι => ℂ)) x)
      (Real.rpow_nonneg hbound _)
      (fun t => by simpa only [p, ENNReal.toReal_ofReal hrpos.le] using hfiniteMoment t)
  have houtnorm : ‖out‖ ≤ bound := by
    apply lp.norm_le_of_forall_sum_le
      (by rw [ENNReal.toReal_ofReal hrpos.le]; exact hrpos) hbound
    intro t
    simpa [out, lpOfUniformFiniteMomentBound_apply, p,
      ENNReal.toReal_ofReal hrpos.le] using hfiniteMoment t
  refine ⟨out, ?_, ?_⟩
  · intro x
    simp [out, lpOfUniformFiniteMomentBound_apply]
  · simpa [bound, C] using houtnorm


end FractionalPrimes.Literature.MSZ

end
