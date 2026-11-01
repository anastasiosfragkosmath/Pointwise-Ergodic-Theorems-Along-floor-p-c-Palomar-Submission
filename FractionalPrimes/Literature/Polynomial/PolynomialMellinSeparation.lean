module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Polynomial.PolynomialSmoothMeanDecay
public import FractionalPrimes.Literature.LongArithmetic.IntegrableFourierInversion
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.LongArithmetic
open MeasureTheory
open scoped ContDiff FourierTransform

/-! The first Mellin-separation checkpoint records the associativity bridge
needed to expand a finite product of positive-integer Dirichlet convolutions.
The kernel and finite-sum identity follow in subsequent declarations. -/

theorem mellinSeparation_toComplexArithmeticFunction_convolution
    (f g : ComplexPositiveIntegerFunction) :
    toComplexArithmeticFunction (complexPositiveDirichletConvolution f g) =
      toComplexArithmeticFunction f * toComplexArithmeticFunction g := by
  ext n
  cases n with
  | zero => simp [toComplexArithmeticFunction]
  | succ n => simp [toComplexArithmeticFunction, complexPositiveDirichletConvolution]

theorem mellinSeparation_dirichletConvolution_assoc
    (f g h : ComplexPositiveIntegerFunction) :
    complexPositiveDirichletConvolution
        (complexPositiveDirichletConvolution f g) h =
      complexPositiveDirichletConvolution f
        (complexPositiveDirichletConvolution g h) := by
  have hconv (u v : ComplexPositiveIntegerFunction) :
      toComplexArithmeticFunction (complexPositiveDirichletConvolution u v) =
        toComplexArithmeticFunction u * toComplexArithmeticFunction v :=
    mellinSeparation_toComplexArithmeticFunction_convolution u v
  funext n
  change (toComplexArithmeticFunction (complexPositiveDirichletConvolution f g) *
      toComplexArithmeticFunction h) n.1 =
    (toComplexArithmeticFunction f *
      toComplexArithmeticFunction (complexPositiveDirichletConvolution g h)) n.1
  rw [hconv f g, hconv g h]
  exact congrArg (fun F : ArithmeticFunction ℂ => F n.1) (mul_assoc _ _ _)

/-- The logarithmic form of the fixed outer cutoff used to separate a finite
Dirichlet convolution. -/
noncomputable def mellinSeparationLogKernel (v : ℝ) : ℂ :=
  (polynomialOuterCutoff (Real.exp v) : ℂ)

theorem mellinSeparationLogKernel_contDiff :
    ContDiff ℝ ∞ mellinSeparationLogKernel := by
  change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ fun v : ℝ =>
    polynomialOuterCutoff (Real.exp v))
  apply Complex.ofRealCLM.contDiff.comp
  exact polynomialOuterCutoff_contDiff.comp (by fun_prop)

theorem mellinSeparationLogKernel_support_subset :
    Function.support mellinSeparationLogKernel ⊆
      Set.Icc (Real.log (3 / 4 : ℝ)) (Real.log (5 / 2 : ℝ)) := by
  intro v hv
  rw [Function.mem_support] at hv
  have hcut : polynomialOuterCutoff (Real.exp v) ≠ 0 := by
    intro hz
    apply hv
    simp [mellinSeparationLogKernel, hz]
  have hcutSupport := polynomialOuterCutoff_support_subset
    (by simpa [Function.mem_support] using hcut)
  constructor
  · exact (Real.log_le_iff_le_exp (by norm_num : 0 < (3 / 4 : ℝ))).2
      hcutSupport.1
  · exact (Real.le_log_iff_exp_le (by norm_num : 0 < (5 / 2 : ℝ))).2
      hcutSupport.2

theorem mellinSeparationLogKernel_hasCompactSupport :
    HasCompactSupport mellinSeparationLogKernel := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact mellinSeparationLogKernel_support_subset

/-- The Schwartz representative of the compactly supported logarithmic
outer-cutoff kernel. -/
noncomputable def mellinSeparationLogKernelSchwartz : SchwartzMap ℝ ℂ :=
  mellinSeparationLogKernel_hasCompactSupport.toSchwartzMap
    mellinSeparationLogKernel_contDiff

/-- The angular Fourier transform of `k(v)=ζ(e^v)`, with the source's
`exp(-itu)` sign convention. -/
noncomputable def mellinSeparationLogKernelFourier (t : ℝ) : ℂ :=
  angularFourierTransform mellinSeparationLogKernel t

theorem mellinSeparationLogKernelFourier_eq_fourier (t : ℝ) :
    mellinSeparationLogKernelFourier t =
      𝓕 mellinSeparationLogKernelSchwartz (t / (2 * Real.pi)) := by
  unfold mellinSeparationLogKernelFourier angularFourierTransform
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  have hexp :
      Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)) =
        Complex.exp (↑(-2 * Real.pi * u * (t / (2 * Real.pi))) * Complex.I) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hexp]
  simpa [mellinSeparationLogKernelSchwartz] using
    (mul_comm (mellinSeparationLogKernel u)
      (Complex.exp (↑(-2 * Real.pi * u * (t / (2 * Real.pi))) * Complex.I)))

theorem mellinSeparationLogKernelFourier_integrable :
    Integrable mellinSeparationLogKernelFourier := by
  have hFourier : Integrable (fun t : ℝ =>
      (𝓕 mellinSeparationLogKernelSchwartz : SchwartzMap ℝ ℂ) t) :=
    (𝓕 mellinSeparationLogKernelSchwartz : SchwartzMap ℝ ℂ).integrable
  have h₂π_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hscale := hFourier.comp_div h₂π_ne
  exact hscale.congr (ae_of_all _ fun t =>
    (mellinSeparationLogKernelFourier_eq_fourier t).symm)

theorem mellinSeparationLogKernel_fourier_inversion (v : ℝ) :
    mellinSeparationLogKernel v =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, mellinSeparationLogKernelFourier t *
          Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)) := by
  exact integrableFourierInversion
    mellinSeparationLogKernelSchwartz.integrable
    mellinSeparationLogKernelFourier_integrable
    (mellinSeparationLogKernel_contDiff.continuous.continuousAt)

/-- One finitely supported factor in the finite Dirichlet product occurring
in `lup:mellin-separation`. -/
abbrev MellinSeparationFactor := PositiveInteger →₀ ℂ

/-- The finite set of tuples whose coordinates lie in the respective factor
supports. -/
noncomputable def mellinSeparationTupleSupport {r : ℕ}
    (α : Fin r → MellinSeparationFactor) : Finset (Fin r → PositiveInteger) := by
  classical
  exact Fintype.piFinset fun j => (α j).support

/-- The positive integer represented by a tuple of factor indices. -/
def mellinSeparationTupleProduct {r : ℕ} (x : Fin r → PositiveInteger) :
    PositiveInteger :=
  ⟨∏ j, (x j).1, Finset.prod_pos fun j _ => (x j).2⟩

/-- A nonzero outer cutoff forces each positive factor index below the
source's truncation threshold `3X`. -/
theorem mellinSeparationTupleFactor_le_threeX_of_outerCutoff_ne_zero
    {r : ℕ} {X : ℝ} (hX : 0 < X) (x : Fin r → PositiveInteger)
    (j : Fin r)
    (hcut : polynomialOuterCutoff
      (((mellinSeparationTupleProduct x).1 : ℝ) / X) ≠ 0) :
    ((x j).1 : ℝ) ≤ 3 * X := by
  have hsupport : (((mellinSeparationTupleProduct x).1 : ℝ) / X) ∈
      Function.support polynomialOuterCutoff := by
    rw [Function.mem_support]
    exact hcut
  have hupper :=
    (polynomialOuterCutoff_support_subset hsupport).2
  have hprod : ((mellinSeparationTupleProduct x).1 : ℝ) ≤ (5 / 2) * X := by
    rw [div_le_iff₀ hX] at hupper
    exact hupper
  have hcoordNat : (x j).1 ≤ ∏ i ∈ Finset.univ, (x i).1 :=
    Finset.single_le_prod (s := Finset.univ) (f := fun i => (x i).1)
      (fun i hi => Nat.one_le_iff_ne_zero.mpr (x i).2.ne') (Finset.mem_univ j)
  have hcoordNat' : (x j).1 ≤ (mellinSeparationTupleProduct x).1 := by
    change (x j).1 ≤ ∏ i, (x i).1
    exact hcoordNat
  have hcoord : ((x j).1 : ℝ) ≤ (mellinSeparationTupleProduct x).1 := by
    exact_mod_cast hcoordNat'
  linarith

/-- The factor truncation at the source's `3X` threshold. -/
noncomputable def mellinSeparationTruncateFactor (X : ℝ)
    (f : ComplexPositiveIntegerFunction) :
    ComplexPositiveIntegerFunction :=
  fun n => if (n.1 : ℝ) ≤ 3 * X then f n else 0

/-- Arithmetic-function products depend at `n` only on factor values at
integers at most `n`. -/
private theorem mellinSeparation_arithmeticProduct_local
    {r : ℕ} (F G : Fin r → ArithmeticFunction ℂ) (n : ℕ)
    (hFG : ∀ j m, m ≤ n → F j m = G j m) :
    (∏ j, F j) n = (∏ j, G j) n := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro ab hab
      have hab' : ab.1 * ab.2 = n ∧ n ≠ 0 :=
        Nat.mem_divisorsAntidiagonal.mp hab
      have habne : ab.1 * ab.2 ≠ 0 := by
        rw [hab'.1]
        exact hab'.2
      have hab1 : ab.1 ≠ 0 := by
        intro hz
        apply habne
        simp [hz]
      have hab2 : ab.2 ≠ 0 := by
        intro hz
        apply habne
        simp [hz]
      have h₁ : ab.1 ≤ n := by
        calc
          ab.1 ≤ ab.2 * ab.1 :=
            Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hab2)
          _ = ab.1 * ab.2 := Nat.mul_comm _ _
          _ = n := hab'.1
      have h₂ : ab.2 ≤ n := by
        calc
          ab.2 ≤ ab.1 * ab.2 :=
            Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hab1)
          _ = n := hab'.1
      rw [hFG 0 ab.1 h₁]
      rw [ih (F := fun j => F j.succ) (G := fun j => G j.succ)
        (n := ab.2) (by intro j m hm; exact hFG j.succ m (hm.trans h₂))]

/-- If the outer cutoff at `n` is nonzero, replacing every factor by its
restriction to indices `m ≤ 3X` leaves the coefficientwise Dirichlet product
at `n` unchanged. This is the truncation clause for arbitrary factors. -/
theorem mellinSeparationTruncateFactor_arithmeticProduct_apply
    {r : ℕ} {X : ℝ} (hX : 0 < X)
    (β : Fin r → ComplexPositiveIntegerFunction) (n : PositiveInteger)
    (hcut : polynomialOuterCutoff ((n.1 : ℝ) / X) ≠ 0) :
    (∏ j, toComplexArithmeticFunction (β j)) n.1 =
      (∏ j, toComplexArithmeticFunction
        (mellinSeparationTruncateFactor X (β j))) n.1 := by
  have hsupport : ((n.1 : ℝ) / X) ∈ Function.support polynomialOuterCutoff := by
    rw [Function.mem_support]
    exact hcut
  have hupper := (polynomialOuterCutoff_support_subset hsupport).2
  have hn : (n.1 : ℝ) ≤ 3 * X := by
    have hle := (div_le_iff₀ hX).1 hupper
    linarith
  apply mellinSeparation_arithmeticProduct_local
  intro j m hm
  by_cases hm0 : m = 0
  · subst m
    simp [toComplexArithmeticFunction, mellinSeparationTruncateFactor]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    let p : PositiveInteger := ⟨m, hmpos⟩
    have hmreal : (m : ℝ) ≤ (n.1 : ℝ) := by exact_mod_cast hm
    have hpbound : (p.1 : ℝ) ≤ 3 * X := by
      dsimp [p]
      exact hmreal.trans hn
    have hβ := toComplexArithmeticFunction_apply (β j) p
    have htrunc := toComplexArithmeticFunction_apply
      (mellinSeparationTruncateFactor X (β j)) p
    calc
      toComplexArithmeticFunction (β j) m = β j p := by simpa [p] using hβ
      _ = mellinSeparationTruncateFactor X (β j) p := by
        simp [mellinSeparationTruncateFactor, hpbound]
      _ = toComplexArithmeticFunction
          (mellinSeparationTruncateFactor X (β j)) m := by
        simpa [p] using htrunc.symm

/-- The coefficient carried by a tuple of factor indices. -/
def mellinSeparationTupleCoefficient {r : ℕ}
    (α : Fin r → MellinSeparationFactor) (x : Fin r → PositiveInteger) : ℂ :=
  ∏ j, α j (x j)

/-- The arithmetic-function point mass at a positive integer. -/
noncomputable def mellinSeparationArithmeticSingle
    (n : PositiveInteger) (c : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun m => if m = n.1 then c else 0, by
    change (if 0 = n.1 then c else 0) = 0
    rw [if_neg (by omega)]⟩

@[simp]
theorem mellinSeparationArithmeticSingle_apply
    (n : PositiveInteger) (c : ℂ) (m : ℕ) :
    mellinSeparationArithmeticSingle n c m = if m = n.1 then c else 0 := rfl

/-- Convolution of two arithmetic-function point masses multiplies both
indices and coefficients. -/
theorem mellinSeparationArithmeticSingle_mul
    (n m : PositiveInteger) (c d : ℂ) :
    mellinSeparationArithmeticSingle n c * mellinSeparationArithmeticSingle m d =
      mellinSeparationArithmeticSingle
        ⟨n.1 * m.1, Nat.mul_pos n.2 m.2⟩ (c * d) := by
  ext k
  rw [ArithmeticFunction.mul_apply]
  by_cases hk : n.1 * m.1 = k
  · have hmem : (n.1, m.1) ∈ Nat.divisorsAntidiagonal k := by
      rw [Nat.mem_divisorsAntidiagonal]
      have hkpos : 0 < k := by rw [← hk]; exact Nat.mul_pos n.2 m.2
      exact ⟨hk, Nat.ne_of_gt hkpos⟩
    rw [Finset.sum_eq_single_of_mem (n.1, m.1) hmem]
    · simp [mellinSeparationArithmeticSingle, hk, eq_comm]
    · intro y hy hne
      have hcoord : y.1 ≠ n.1 ∨ y.2 ≠ m.1 := by
        by_cases h₁ : y.1 = n.1
        · by_cases h₂ : y.2 = m.1
          · exact False.elim (hne (Prod.ext h₁ h₂))
          · exact Or.inr h₂
        · exact Or.inl h₁
      rcases hcoord with hcoord | hcoord
      · simp [mellinSeparationArithmeticSingle, hcoord]
      · simp [mellinSeparationArithmeticSingle, hcoord]
  · rw [Finset.sum_eq_zero]
    · have hk' : k ≠ n.1 * m.1 := fun he => hk he.symm
      simp [mellinSeparationArithmeticSingle, hk', eq_comm]
    · intro y hy
      by_cases h₁ : y.1 = n.1
      · by_cases h₂ : y.2 = m.1
        · have hprod := (Nat.mem_divisorsAntidiagonal.mp hy).1
          have hEq : n.1 * m.1 = k := by simpa [h₁, h₂] using hprod
          exact False.elim (hk hEq)
        · simp [mellinSeparationArithmeticSingle, h₁, h₂]
      · simp [mellinSeparationArithmeticSingle, h₁]

/-- The arithmetic-function extension of a finitely supported factor is the
finite sum of its point masses. -/
theorem mellinSeparation_toComplexArithmeticFunction_eq_sum_single
    (f : MellinSeparationFactor) :
    toComplexArithmeticFunction f =
      ∑ n ∈ f.support, mellinSeparationArithmeticSingle n (f n) := by
  classical
  ext m
  by_cases hm : 0 < m
  · let n : PositiveInteger := ⟨m, hm⟩
    have hleft : toComplexArithmeticFunction f m = f n := by
      simpa [n] using (toComplexArithmeticFunction_apply f n)
    have hsum_apply :
        (∑ k ∈ f.support, mellinSeparationArithmeticSingle k (f k)) m =
          ∑ k ∈ f.support, mellinSeparationArithmeticSingle k (f k) m := by
      induction f.support using Finset.induction_on with
      | empty => simp
      | @insert k S hk ih => simp [Finset.sum_insert, hk, ih]
    rw [hleft, hsum_apply]
    simp only [mellinSeparationArithmeticSingle_apply]
    by_cases hn : n ∈ f.support
    · rw [Finset.sum_eq_single_of_mem n hn]
      · simp [n]
      · intro k hk hkn
        have hval : m ≠ k.1 := by
          intro he
          apply hkn
          exact Subtype.ext (by simpa [n] using he.symm)
        simp [hval]
    · have hfzero : f n = 0 := by
        by_contra hf
        exact hn (Finsupp.mem_support_iff.mpr hf)
      rw [Finset.sum_eq_zero]
      · exact hfzero
      · intro k hk
        have hval : m ≠ k.1 := by
          intro he
          have hnk : n = k := Subtype.ext (by simpa [n] using he)
          exact hn (hnk ▸ hk)
        simp [hval]
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [toComplexArithmeticFunction, mellinSeparationArithmeticSingle]

/-- The coefficient function of the finite product of Dirichlet factors,
written as its exact finite sum over factor tuples. -/
noncomputable def mellinSeparationConvolutionProduct {r : ℕ}
    (α : Fin r → MellinSeparationFactor) : MellinSeparationFactor := by
  classical
  exact ∑ x ∈ mellinSeparationTupleSupport α,
    Finsupp.single (mellinSeparationTupleProduct x)
      (mellinSeparationTupleCoefficient α x)

/-- Expanding the tuple-sum coefficient recovers the finite factorization
sum over tuples with the prescribed product. -/
theorem mellinSeparationConvolutionProduct_apply {r : ℕ}
    (α : Fin r → MellinSeparationFactor) (n : PositiveInteger) :
    mellinSeparationConvolutionProduct α n =
      ∑ x ∈ (mellinSeparationTupleSupport α).filter
          (fun x => mellinSeparationTupleProduct x = n),
        mellinSeparationTupleCoefficient α x := by
  classical
  simp [mellinSeparationConvolutionProduct, Finsupp.sum_apply,
    Finsupp.single_apply, Finset.sum_filter]

/-- Evaluation commutes with finite sums of arithmetic functions. -/
theorem mellinSeparationArithmeticFinsetSum_apply {ι : Type*}
    (S : Finset ι) (g : ι → ArithmeticFunction ℂ) (n : ℕ) :
    (∑ i ∈ S, g i) n = ∑ i ∈ S, g i n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert, hi, ih]

/-- The arithmetic-function extension of the finite tuple convolution is the
sum of its point masses, before equal products are collected. -/
theorem mellinSeparationConvolutionProduct_toArithmeticFunction
    {r : ℕ} (α : Fin r → MellinSeparationFactor) :
    toComplexArithmeticFunction (mellinSeparationConvolutionProduct α) =
      ∑ x ∈ mellinSeparationTupleSupport α,
        mellinSeparationArithmeticSingle (mellinSeparationTupleProduct x)
          (mellinSeparationTupleCoefficient α x) := by
  classical
  ext m
  by_cases hm : 0 < m
  · let n : PositiveInteger := ⟨m, hm⟩
    have hleft :
        toComplexArithmeticFunction (mellinSeparationConvolutionProduct α) m =
          mellinSeparationConvolutionProduct α n := by
      simpa [n] using toComplexArithmeticFunction_apply
        (mellinSeparationConvolutionProduct α) n
    rw [hleft, mellinSeparationConvolutionProduct_apply,
      mellinSeparationArithmeticFinsetSum_apply]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hp : mellinSeparationTupleProduct x = n
    · have hmval : m = (mellinSeparationTupleProduct x).1 := by
        have hval := congrArg Subtype.val hp
        simpa [n] using hval.symm
      simp [mellinSeparationArithmeticSingle, hp, hmval]
    · have hmval : m ≠ (mellinSeparationTupleProduct x).1 := by
        intro hval
        apply hp
        exact Subtype.ext (by simpa [n] using hval.symm)
      simp [mellinSeparationArithmeticSingle, hp, hmval]
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [toComplexArithmeticFunction, mellinSeparationArithmeticSingle]

/-- The product of point masses indexed by a tuple is the point mass at the
product integer with coefficient equal to the tuple coefficient. -/
theorem mellinSeparationArithmeticSingle_tupleProduct {r : ℕ}
    (α : Fin r → MellinSeparationFactor) (x : Fin r → PositiveInteger) :
    ∏ j, mellinSeparationArithmeticSingle (x j) (α j (x j)) =
      mellinSeparationArithmeticSingle (mellinSeparationTupleProduct x)
        (mellinSeparationTupleCoefficient α x) := by
  induction r with
  | zero =>
      change (1 : ArithmeticFunction ℂ) =
        mellinSeparationArithmeticSingle (mellinSeparationTupleProduct x)
          (mellinSeparationTupleCoefficient α x)
      have hx : mellinSeparationTupleProduct x = 1 := by
        apply Subtype.ext
        change (∏ j : Fin 0, (x j).1) = 1
        simp
      have hc : mellinSeparationTupleCoefficient α x = 1 := by
        simp [mellinSeparationTupleCoefficient]
      rw [hx, hc]
      ext n
      simp [mellinSeparationArithmeticSingle, ArithmeticFunction.one_apply]
  | succ r ih =>
      rw [Fin.prod_univ_succ]
      rw [ih (fun j => α j.succ) (fun j => x j.succ)]
      have hprod : mellinSeparationTupleProduct x =
          ⟨(x 0).1 *
            (mellinSeparationTupleProduct (fun j : Fin r => x j.succ)).1,
            Nat.mul_pos (x 0).2
              (mellinSeparationTupleProduct (fun j : Fin r => x j.succ)).2⟩ := by
        apply Subtype.ext
        simp [mellinSeparationTupleProduct, Fin.prod_univ_succ]
      have hcoeff : mellinSeparationTupleCoefficient α x =
          α 0 (x 0) *
            mellinSeparationTupleCoefficient (fun j : Fin r => α j.succ)
              (fun j : Fin r => x j.succ) := by
        simp [mellinSeparationTupleCoefficient, Fin.prod_univ_succ]
      rw [hprod, hcoeff]
      exact mellinSeparationArithmeticSingle_mul (x 0)
        (mellinSeparationTupleProduct (fun j : Fin r => x j.succ))
        (α 0 (x 0))
        (mellinSeparationTupleCoefficient (fun j : Fin r => α j.succ)
          (fun j : Fin r => x j.succ))

/-- The ordered product in Mathlib's arithmetic-function convolution algebra
equals the finite tuple convolution used in the Mellin formula. -/
noncomputable def mellinSeparationArithmeticProduct {r : ℕ}
    (α : Fin r → MellinSeparationFactor) : ArithmeticFunction ℂ :=
  ∏ j, toComplexArithmeticFunction (α j)

theorem mellinSeparationArithmeticProduct_eq_tupleConvolution {r : ℕ}
    (α : Fin r → MellinSeparationFactor) :
    mellinSeparationArithmeticProduct α =
      toComplexArithmeticFunction (mellinSeparationConvolutionProduct α) := by
  classical
  calc
    mellinSeparationArithmeticProduct α =
        ∏ j, ∑ n ∈ (α j).support,
          mellinSeparationArithmeticSingle n (α j n) := by
      unfold mellinSeparationArithmeticProduct
      apply Finset.prod_congr rfl
      intro j hj
      exact mellinSeparation_toComplexArithmeticFunction_eq_sum_single (α j)
    _ = ∑ x ∈ mellinSeparationTupleSupport α,
          ∏ j, mellinSeparationArithmeticSingle (x j) (α j (x j)) := by
      simp only [mellinSeparationTupleSupport]
      rw [Finset.prod_univ_sum]
    _ = ∑ x ∈ mellinSeparationTupleSupport α,
          mellinSeparationArithmeticSingle (mellinSeparationTupleProduct x)
            (mellinSeparationTupleCoefficient α x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact mellinSeparationArithmeticSingle_tupleProduct α x
    _ = toComplexArithmeticFunction (mellinSeparationConvolutionProduct α) := by
      exact (mellinSeparationConvolutionProduct_toArithmeticFunction α).symm

/-- The complex Dirichlet monomial `n^{-s}` written using the real logarithm
of the positive integer `n`. -/
noncomputable def mellinSeparationMonomial (n : PositiveInteger) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (n.1 : ℝ) : ℂ))

/-- The cutoff-weighted Dirichlet summand is unchanged by the factor
truncation, including for arbitrary coefficient functions. -/
theorem mellinSeparationTruncateFactor_weightedTerm
    {r : ℕ} {X : ℝ} (hX : 0 < X)
    (β : Fin r → ComplexPositiveIntegerFunction) (n : PositiveInteger)
    (s : ℂ) :
    (∏ j, toComplexArithmeticFunction (β j)) n.1 *
        (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) *
        mellinSeparationMonomial n s =
      (∏ j, toComplexArithmeticFunction
        (mellinSeparationTruncateFactor X (β j))) n.1 *
        (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) *
        mellinSeparationMonomial n s := by
  by_cases hcut : polynomialOuterCutoff ((n.1 : ℝ) / X) = 0
  · simp [hcut]
  · rw [mellinSeparationTruncateFactor_arithmeticProduct_apply hX β n hcut]

/-- The monomial of a product is the product of the factor monomials. -/
theorem mellinSeparationMonomial_tupleProduct {r : ℕ}
    (x : Fin r → PositiveInteger) (s : ℂ) :
    mellinSeparationMonomial (mellinSeparationTupleProduct x) s =
      ∏ j, mellinSeparationMonomial (x j) s := by
  classical
  have hlog :
      Real.log ((∏ j, (x j).1 : ℕ) : ℝ) = ∑ j, Real.log ((x j).1 : ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod (s := Finset.univ) (f := fun j => (x j).1)
      (by intro j hj; exact_mod_cast (x j).2.ne')
  have hlogC :
      (Real.log ((∏ j, (x j).1 : ℕ) : ℝ) : ℂ) =
        ∑ j, (Real.log ((x j).1 : ℝ) : ℂ) := by
    rw [hlog]
    simp
  simp only [mellinSeparationMonomial, mellinSeparationTupleProduct]
  rw [hlogC]
  rw [Finset.mul_sum (Finset.univ : Finset (Fin r))
    (fun j => (Real.log ((x j).1 : ℝ) : ℂ)) (-s), Complex.exp_sum]

/-- The finite Dirichlet polynomial in one prescribed residue class. -/
noncomputable def mellinSeparationFactorPolynomial {r : ℕ}
    (α : Fin r → MellinSeparationFactor) (q : ℕ) (j : Fin r)
    (b : Fin q) (s : ℂ) : ℂ :=
  ∑ n ∈ (α j).support.filter
      (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) (b.1 : ℤ)),
    α j n * mellinSeparationMonomial n s

/-- The scale factor `X^{-iu}` in the angular Mellin inversion formula. -/
noncomputable def mellinSeparationScaleFactor (X u : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (u : ℂ) * (Real.log X : ℂ))

/-- Fourier inversion at `log(n/X)`, with the scale phase separated exactly. -/
theorem mellinSeparationKernelInversion_at {X : ℝ} (hX : 0 < X)
    (n : PositiveInteger) :
    (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ u : ℝ, mellinSeparationLogKernelFourier u *
          mellinSeparationScaleFactor X u *
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) := by
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hnX : 0 < (n.1 : ℝ) / X := div_pos hn hX
  have hkernel :
      mellinSeparationLogKernel (Real.log ((n.1 : ℝ) / X)) =
        (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) := by
    simp [mellinSeparationLogKernel, Real.exp_log hnX]
  have hphase (u : ℝ) :
      Complex.exp (Complex.I * (u : ℂ) *
          (Real.log ((n.1 : ℝ) / X) : ℂ)) =
        mellinSeparationScaleFactor X u *
          Complex.exp (Complex.I * (u : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) := by
    rw [Real.log_div hn.ne' hX.ne']
    unfold mellinSeparationScaleFactor
    calc
      _ = Complex.exp
          ((-Complex.I * (u : ℂ) * (Real.log X : ℂ)) +
            (Complex.I * (u : ℂ) * (Real.log (n.1 : ℝ) : ℂ))) := by
              congr 1
              push_cast
              ring
      _ = _ := by rw [Complex.exp_add]
  calc
    (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) =
        mellinSeparationLogKernel (Real.log ((n.1 : ℝ) / X)) := hkernel.symm
    _ = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ u : ℝ, mellinSeparationLogKernelFourier u *
          Complex.exp (Complex.I * (u : ℂ) *
            (Real.log ((n.1 : ℝ) / X) : ℂ)) :=
      mellinSeparationLogKernel_fourier_inversion _
    _ = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ u : ℝ, mellinSeparationLogKernelFourier u *
          mellinSeparationScaleFactor X u *
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      rw [hphase u]
      ring

/-- Expanding the product of the finite residue-class Dirichlet polynomials
gives the corresponding finite sum over tuples. -/
theorem mellinSeparationFactorProduct_expand {r q : ℕ}
    (α : Fin r → MellinSeparationFactor) (b : Fin r → Fin q) (s : ℂ) :
    (∏ j, mellinSeparationFactorPolynomial α q j (b j) s) =
      ∑ x ∈ Fintype.piFinset (fun j : Fin r =>
          (α j).support.filter
            (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) ((b j).1 : ℤ))),
        ∏ j, α j (x j) * mellinSeparationMonomial (x j) s := by
  classical
  simp only [mellinSeparationFactorPolynomial]
  rw [Finset.prod_univ_sum]

/-- The tuple terms in the product expansion carry the coefficient of the
integer product and its exact Mellin monomial. -/
theorem mellinSeparationFactorProduct_expand_coeff {r q : ℕ}
    (α : Fin r → MellinSeparationFactor) (b : Fin r → Fin q) (s : ℂ) :
    (∏ j, mellinSeparationFactorPolynomial α q j (b j) s) =
      ∑ x ∈ Fintype.piFinset (fun j : Fin r =>
          (α j).support.filter
            (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) ((b j).1 : ℤ))),
        mellinSeparationTupleCoefficient α x *
          mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
  rw [mellinSeparationFactorProduct_expand]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib, ← mellinSeparationMonomial_tupleProduct]
  rfl

/-- The canonical representative in `Fin q` of a positive integer residue. -/
def mellinSeparationResidue {q : ℕ} (hq : 0 < q) (n : PositiveInteger) : Fin q :=
  ⟨n.1 % q, Nat.mod_lt _ hq⟩

/-- The coordinatewise residue tuple of a positive-integer factor tuple. -/
def mellinSeparationTupleResidue {r q : ℕ} (hq : 0 < q)
    (x : Fin r → PositiveInteger) : Fin r → Fin q :=
  fun j => mellinSeparationResidue hq (x j)

/-- Residue tuples whose product lies in the prescribed integer residue class. -/
noncomputable def mellinSeparationAllowedResidues {r q : ℕ} (a : ℤ) :
    Finset (Fin r → Fin q) := by
  classical
  exact (Finset.univ : Finset (Fin r → Fin q)).filter fun b =>
    Int.ModEq (q : ℤ) ((∏ j, (b j).1 : ℕ) : ℤ) a

/-- A positive integer is congruent to its canonical residue representative. -/
theorem mellinSeparationResidue_modEq {q : ℕ} (hq : 0 < q)
    (n : PositiveInteger) :
    Int.ModEq (q : ℤ) (n.1 : ℤ)
      ((mellinSeparationResidue hq n).1 : ℤ) := by
  apply Int.ModEq.symm
  simpa [mellinSeparationResidue, Int.natCast_mod] using
    (Int.mod_modEq (n.1 : ℤ) (q : ℤ))

/-- The canonical residue representative is the unique representative in
`Fin q` of the same integer residue class. -/
theorem mellinSeparationResidue_eq_iff {q : ℕ} (hq : 0 < q)
    (n : PositiveInteger) (b : Fin q) :
    mellinSeparationResidue hq n = b ↔
      Int.ModEq (q : ℤ) (n.1 : ℤ) (b.1 : ℤ) := by
  constructor
  · intro h
    rw [← h]
    exact mellinSeparationResidue_modEq hq n
  · intro h
    apply Fin.ext
    have heq := h.eq
    have hcast : ((n.1 % q : ℕ) : ℤ) = ((b.1 % q : ℕ) : ℤ) := by
      simpa only [← Int.natCast_mod] using heq
    have hnat : n.1 % q = b.1 % q := by exact_mod_cast hcast
    have hnat' : n.1 % q = b.1 := by simpa [Nat.mod_eq_of_lt b.2] using hnat
    simpa [mellinSeparationResidue] using hnat'

/-- The factor-support product with fixed coordinate residues is the fiber of
the canonical tuple-residue map. -/
theorem mellinSeparationTupleSupport_residueFiber {r q : ℕ}
    (α : Fin r → MellinSeparationFactor) (hq : 0 < q) (b : Fin r → Fin q) :
    Fintype.piFinset (fun j : Fin r =>
        (α j).support.filter
          (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) ((b j).1 : ℤ))) =
      (mellinSeparationTupleSupport α).filter
        (fun x => mellinSeparationTupleResidue hq x = b) := by
  classical
  ext x
  simp only [Fintype.mem_piFinset, Finset.mem_filter, mellinSeparationTupleSupport]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro j
      exact (hx j).1
    · funext j
      exact (mellinSeparationResidue_eq_iff hq (x j) (b j)).2 (hx j).2
  · rintro ⟨hx, hb⟩ j
    refine ⟨hx j, ?_⟩
    apply (mellinSeparationResidue_eq_iff hq (x j) (b j)).1
    exact congrFun hb j

/-- Multiplying the coordinate congruences gives the exact product residue. -/
theorem mellinSeparationTupleProduct_modEq {r q : ℕ} (hq : 0 < q)
    (x : Fin r → PositiveInteger) :
    Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ)
      ((∏ j, (mellinSeparationTupleResidue hq x j).1 : ℕ) : ℤ) := by
  classical
  have hprod (s : Finset (Fin r)) :
      Int.ModEq (q : ℤ)
        (∏ j ∈ s, (x j).1 : ℤ)
        (∏ j ∈ s, ((mellinSeparationTupleResidue hq x j).1 : ℤ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi]
        exact (mellinSeparationResidue_modEq hq (x i)).mul ih
  simpa [mellinSeparationTupleProduct, mellinSeparationTupleResidue,
    mellinSeparationResidue, Nat.cast_prod] using hprod Finset.univ

/-- The product of a tuple is in a residue class precisely when its canonical
coordinatewise residue tuple is among the approved product residues. -/
theorem mellinSeparationTupleResidue_mem_allowed {r q : ℕ} (hq : 0 < q)
    (x : Fin r → PositiveInteger) (a : ℤ) :
    Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ) a ↔
      mellinSeparationTupleResidue hq x ∈ mellinSeparationAllowedResidues a := by
  classical
  constructor
  · intro hx
    rw [mellinSeparationAllowedResidues, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (mellinSeparationTupleProduct_modEq hq x).symm.trans hx
  · intro hb
    rw [mellinSeparationAllowedResidues, Finset.mem_filter] at hb
    exact (mellinSeparationTupleProduct_modEq hq x).trans hb.2

/-- Summing the residue-class factor products is exactly summing the
factor-tuple terms whose product lies in the prescribed residue class. -/
theorem mellinSeparationAllowedFactorProducts_eq_tupleSum {r q : ℕ}
    (α : Fin r → MellinSeparationFactor) (hq : 0 < q) (a : ℤ) (s : ℂ) :
    ∑ b ∈ mellinSeparationAllowedResidues a,
      ∏ j, mellinSeparationFactorPolynomial α q j (b j) s =
    ∑ x ∈ (mellinSeparationTupleSupport α).filter
        (fun x => Int.ModEq (q : ℤ)
          ((mellinSeparationTupleProduct x).1 : ℤ) a),
      mellinSeparationTupleCoefficient α x *
        mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
  classical
  let S := (mellinSeparationTupleSupport α).filter fun x =>
    Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ) a
  let T : Finset (Fin r → Fin q) :=
    mellinSeparationAllowedResidues (r := r) (q := q) a
  let g : (Fin r → PositiveInteger) → (Fin r → Fin q) :=
    mellinSeparationTupleResidue hq
  let term (x : Fin r → PositiveInteger) :=
    mellinSeparationTupleCoefficient α x *
      mellinSeparationMonomial (mellinSeparationTupleProduct x) s
  have hmap : ∀ x ∈ S, g x ∈ T := by
    intro x hx
    exact (mellinSeparationTupleResidue_mem_allowed hq x a).mp
      (Finset.mem_filter.mp hx).2
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmap term
  have hfiber (b : Fin r → Fin q) (hb : b ∈ T) :
      S.filter (fun x => g x = b) =
        (mellinSeparationTupleSupport α).filter (fun x => g x = b) := by
    ext x
    simp only [Finset.mem_filter, S]
    constructor
    · rintro ⟨⟨hx, _⟩, hxb⟩
      exact ⟨hx, hxb⟩
    · rintro ⟨hx, hxb⟩
      refine ⟨⟨hx, ?_⟩, hxb⟩
      have hallowed : g x ∈ T := by simpa [hxb] using hb
      exact (mellinSeparationTupleResidue_mem_allowed hq x a).mpr hallowed
  calc
    ∑ b ∈ T, ∏ j, mellinSeparationFactorPolynomial α q j (b j) s =
        ∑ b ∈ T, ∑ x ∈ S with g x = b, term x := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [mellinSeparationFactorProduct_expand_coeff α b s,
        mellinSeparationTupleSupport_residueFiber α hq b]
      rw [← hfiber b hb]
    _ = ∑ x ∈ S, term x := hgroup
    _ = ∑ x ∈ (mellinSeparationTupleSupport α).filter
        (fun x => Int.ModEq (q : ℤ)
          ((mellinSeparationTupleProduct x).1 : ℤ) a),
        mellinSeparationTupleCoefficient α x *
          mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
      rfl

/-- The coefficient-weighted finite sum on a prescribed integer residue class,
with the source's smooth outer cutoff and Dirichlet monomial. -/
noncomputable def mellinSeparationResidueMellinSum
    (f : MellinSeparationFactor) (q : ℕ) (a : ℤ) (X : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ f.support.filter (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) a),
    f n * (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) *
      mellinSeparationMonomial n s

/-- Expand the source residue-class sum into its finite factor tuples. -/
theorem mellinSeparationResidueMellinSum_eq_tupleSum {r q : ℕ}
    (α : Fin r → MellinSeparationFactor) (a : ℤ) (X : ℝ) (s : ℂ) :
    mellinSeparationResidueMellinSum (mellinSeparationConvolutionProduct α)
        q a X s =
      ∑ x ∈ (mellinSeparationTupleSupport α).filter
          (fun x => Int.ModEq (q : ℤ)
            ((mellinSeparationTupleProduct x).1 : ℤ) a),
        mellinSeparationTupleCoefficient α x *
          (polynomialOuterCutoff
            (((mellinSeparationTupleProduct x).1 : ℝ) / X) : ℂ) *
          mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
  classical
  let w : PositiveInteger → ℂ := fun n =>
    if Int.ModEq (q : ℤ) (n.1 : ℤ) a then
      (polynomialOuterCutoff ((n.1 : ℝ) / X) : ℂ) *
        mellinSeparationMonomial n s
    else 0
  have hsource :
      mellinSeparationResidueMellinSum (mellinSeparationConvolutionProduct α)
          q a X s =
        (mellinSeparationConvolutionProduct α).sum fun n c => c * w n := by
    simp [mellinSeparationResidueMellinSum, w, Finsupp.sum,
      Finset.sum_filter, mul_assoc]
  have hsingle (x : Fin r → PositiveInteger) :
      (Finsupp.single (mellinSeparationTupleProduct x)
        (mellinSeparationTupleCoefficient α x)).sum (fun n c => c * w n) =
        if Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ) a then
          mellinSeparationTupleCoefficient α x *
            ((polynomialOuterCutoff
              (((mellinSeparationTupleProduct x).1 : ℝ) / X) : ℂ) *
              mellinSeparationMonomial (mellinSeparationTupleProduct x) s)
        else 0 := by
    by_cases hc : mellinSeparationTupleCoefficient α x = 0
    · simp [Finsupp.sum, Finsupp.single_apply, hc, w]
    · simp [Finsupp.sum, Finsupp.single_apply, hc, w, mul_assoc]
  rw [hsource, mellinSeparationConvolutionProduct]
  calc
    _ = ∑ x ∈ mellinSeparationTupleSupport α,
        if Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ) a then
          mellinSeparationTupleCoefficient α x *
            ((polynomialOuterCutoff
              (((mellinSeparationTupleProduct x).1 : ℝ) / X) : ℂ) *
              mellinSeparationMonomial (mellinSeparationTupleProduct x) s)
        else 0 := by
          rw [Finsupp.sum_finsetSum
            (f := fun x => Finsupp.single (mellinSeparationTupleProduct x)
              (mellinSeparationTupleCoefficient α x))
            (s := mellinSeparationTupleSupport α)
            (g := fun n c => c * w n)
            (by intro n; simp)
            (by intro n c₁ c₂; ring)]
          exact Finset.sum_congr rfl fun x hx => hsingle x
    _ = ∑ x ∈ (mellinSeparationTupleSupport α).filter
          (fun x => Int.ModEq (q : ℤ)
            ((mellinSeparationTupleProduct x).1 : ℤ) a),
        mellinSeparationTupleCoefficient α x *
          (polynomialOuterCutoff
            (((mellinSeparationTupleProduct x).1 : ℝ) / X) : ℂ) *
          mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
          rw [Finset.sum_filter]
          simp only [mul_assoc]

/-- Shifting a Dirichlet monomial vertically introduces the expected angular
phase. -/
theorem mellinSeparationMonomial_shift (n : PositiveInteger) (s : ℂ) (u : ℝ) :
    mellinSeparationMonomial n (s - Complex.I * (u : ℂ)) =
      mellinSeparationMonomial n s *
        Complex.exp (Complex.I * (u : ℂ) *
          (Real.log (n.1 : ℝ) : ℂ)) := by
  unfold mellinSeparationMonomial
  congr 1
  rw [show -(s - Complex.I * (u : ℂ)) *
      (Real.log (n.1 : ℝ) : ℂ) =
        (-s * (Real.log (n.1 : ℝ) : ℂ)) +
          Complex.I * (u : ℂ) * (Real.log (n.1 : ℝ) : ℂ) by ring,
    Complex.exp_add]

/-- Every pure imaginary exponential in the Mellin phases has modulus one. -/
theorem mellinSeparationExpPhase_norm (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (v : ℂ))‖ = 1 := by
  have harg : Complex.I * (u : ℂ) * (v : ℂ) = ((u * v : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The scale factor in Mellin inversion has modulus one. -/
theorem mellinSeparationScaleFactor_norm (X u : ℝ) :
    ‖mellinSeparationScaleFactor X u‖ = 1 := by
  unfold mellinSeparationScaleFactor
  have harg : -Complex.I * (u : ℂ) * (Real.log X : ℂ) =
      ((-u * Real.log X : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Each individual factor-tuple term in the separated Mellin integral is
absolutely integrable. -/
theorem mellinSeparationTupleTerm_integrable {r : ℕ}
    (α : Fin r → MellinSeparationFactor) (x : Fin r → PositiveInteger)
    (X : ℝ) (s : ℂ) :
    Integrable (fun u : ℝ => mellinSeparationLogKernelFourier u *
      mellinSeparationScaleFactor X u *
        (mellinSeparationTupleCoefficient α x *
          mellinSeparationMonomial (mellinSeparationTupleProduct x)
            (s - Complex.I * (u : ℂ)))) := by
  let p := mellinSeparationTupleProduct x
  let c := mellinSeparationTupleCoefficient α x * mellinSeparationMonomial p s
  let phase (u : ℝ) := mellinSeparationScaleFactor X u *
    Complex.exp (Complex.I * (u : ℂ) * (Real.log (p.1 : ℝ) : ℂ))
  have hbase : Integrable (fun u : ℝ => mellinSeparationLogKernelFourier u * c) :=
    mellinSeparationLogKernelFourier_integrable.mul_const c
  have hphase_meas : AEStronglyMeasurable phase := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun u : ℝ =>
      Complex.exp (-Complex.I * (u : ℂ) * (Real.log X : ℂ)) *
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (p.1 : ℝ) : ℂ)))
    fun_prop
  have hphase_bound : ∀ᵐ u : ℝ ∂volume, ‖phase u‖ ≤ 1 := by
    filter_upwards with u
    have hp : ‖phase u‖ = 1 := by
      dsimp [phase]
      rw [norm_mul, mellinSeparationScaleFactor_norm,
        mellinSeparationExpPhase_norm]
      norm_num
    rw [hp]
  have hmul := hbase.mul_bdd hphase_meas hphase_bound
  apply hmul.congr
  filter_upwards with u
  dsimp [phase, c, p]
  rw [mellinSeparationMonomial_shift]
  ring

/-- The full product integrand for a fixed residue tuple is absolutely
integrable, by its finite expansion into the tuple terms above. -/
theorem mellinSeparationFactorProduct_integrable {r q : ℕ}
    (α : Fin r → MellinSeparationFactor) (b : Fin r → Fin q)
    (X : ℝ) (s : ℂ) :
    Integrable (fun u : ℝ => mellinSeparationLogKernelFourier u *
      mellinSeparationScaleFactor X u *
        ∏ j, mellinSeparationFactorPolynomial α q j (b j)
          (s - Complex.I * (u : ℂ))) := by
  classical
  let S := Fintype.piFinset (fun j : Fin r =>
    (α j).support.filter
      (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) ((b j).1 : ℤ)))
  have hsum : Integrable (fun u : ℝ =>
      ∑ x ∈ S, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          (mellinSeparationTupleCoefficient α x *
            mellinSeparationMonomial (mellinSeparationTupleProduct x)
              (s - Complex.I * (u : ℂ)))) := by
    apply integrable_finsetSum
    intro x hx
    exact mellinSeparationTupleTerm_integrable α x X s
  apply hsum.congr
  filter_upwards with u
  dsimp [S]
  rw [mellinSeparationFactorProduct_expand_coeff]
  rw [← Finset.mul_sum]

/-- Summing the residue-product integrals is exactly summing the corresponding
factor-tuple integrals. -/
theorem mellinSeparationResidueProducts_integral_eq_tupleIntegrals
    {r q : ℕ} (α : Fin r → MellinSeparationFactor) (hq : 0 < q)
    (a : ℤ) (X : ℝ) (s : ℂ) :
    (∑ b ∈ mellinSeparationAllowedResidues a,
      ∫ u : ℝ, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          ∏ j, mellinSeparationFactorPolynomial α q j (b j)
            (s - Complex.I * (u : ℂ))) =
    ∑ x ∈ (mellinSeparationTupleSupport α).filter
        (fun x => Int.ModEq (q : ℤ)
          ((mellinSeparationTupleProduct x).1 : ℤ) a),
      ∫ u : ℝ, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          (mellinSeparationTupleCoefficient α x *
            mellinSeparationMonomial (mellinSeparationTupleProduct x)
              (s - Complex.I * (u : ℂ))) := by
  classical
  let B := mellinSeparationAllowedResidues (r := r) (q := q) a
  let T := (mellinSeparationTupleSupport α).filter fun x =>
    Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ) a
  have hB : ∀ b ∈ B, Integrable (fun u : ℝ =>
      mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          ∏ j, mellinSeparationFactorPolynomial α q j (b j)
            (s - Complex.I * (u : ℂ))) := by
    intro b hb
    exact mellinSeparationFactorProduct_integrable α b X s
  have hT : ∀ x ∈ T, Integrable (fun u : ℝ =>
      mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          (mellinSeparationTupleCoefficient α x *
            mellinSeparationMonomial (mellinSeparationTupleProduct x)
              (s - Complex.I * (u : ℂ)))) := by
    intro x hx
    exact mellinSeparationTupleTerm_integrable α x X s
  calc
    (∑ b ∈ B, ∫ u : ℝ, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          ∏ j, mellinSeparationFactorPolynomial α q j (b j)
            (s - Complex.I * (u : ℂ))) =
      ∫ u : ℝ, ∑ b ∈ B, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          ∏ j, mellinSeparationFactorPolynomial α q j (b j)
            (s - Complex.I * (u : ℂ)) := by
      symm
      rw [integral_finsetSum]
      intro b hb
      exact hB b hb
    _ = ∫ u : ℝ, ∑ x ∈ T, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          (mellinSeparationTupleCoefficient α x *
            mellinSeparationMonomial (mellinSeparationTupleProduct x)
              (s - Complex.I * (u : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [B, T]
      calc
        (∑ b ∈ mellinSeparationAllowedResidues a,
            mellinSeparationLogKernelFourier u *
              mellinSeparationScaleFactor X u *
                ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                  (s - Complex.I * (u : ℂ))) =
          (mellinSeparationLogKernelFourier u *
              mellinSeparationScaleFactor X u) *
            ∑ b ∈ mellinSeparationAllowedResidues a,
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (s - Complex.I * (u : ℂ)) := by
          rw [← Finset.mul_sum]
        _ = (mellinSeparationLogKernelFourier u *
              mellinSeparationScaleFactor X u) *
            ∑ x ∈ (mellinSeparationTupleSupport α).filter
                (fun x => Int.ModEq (q : ℤ)
                  ((mellinSeparationTupleProduct x).1 : ℤ) a),
              mellinSeparationTupleCoefficient α x *
                mellinSeparationMonomial (mellinSeparationTupleProduct x)
                  (s - Complex.I * (u : ℂ)) := by
          rw [mellinSeparationAllowedFactorProducts_eq_tupleSum α hq a
            (s - Complex.I * (u : ℂ))]
        _ = _ := by rw [Finset.mul_sum]
    _ = ∑ x ∈ T, ∫ u : ℝ, mellinSeparationLogKernelFourier u *
        mellinSeparationScaleFactor X u *
          (mellinSeparationTupleCoefficient α x *
            mellinSeparationMonomial (mellinSeparationTupleProduct x)
              (s - Complex.I * (u : ℂ))) := by
      symm
      rw [integral_finsetSum]
      intro x hx
      exact hT x hx

/-- The exact finite Mellin separation identity for a finite convolution,
with the source's angular Fourier normalization and residue-product condition.
The tuple convolution is the finite coefficientwise expansion of the ordered
product of the factors. -/
theorem separateSmoothConvolutionMellin {r q : ℕ}
    (_hr : 0 < r) (α : Fin r → MellinSeparationFactor) (hq : 0 < q)
    (a : ℤ) (X : ℝ) (hX : 0 < X) (s : ℂ) :
    mellinSeparationResidueMellinSum
        (mellinSeparationConvolutionProduct α) q a X s =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ b ∈ mellinSeparationAllowedResidues a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (s - Complex.I * (u : ℂ)) := by
  classical
  let T := (mellinSeparationTupleSupport α).filter fun x =>
    Int.ModEq (q : ℤ) ((mellinSeparationTupleProduct x).1 : ℤ) a
  have hterm (x : Fin r → PositiveInteger) (hx : x ∈ T) :
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              (mellinSeparationTupleCoefficient α x *
                mellinSeparationMonomial (mellinSeparationTupleProduct x)
                  (s - Complex.I * (u : ℂ))) =
        mellinSeparationTupleCoefficient α x *
          (polynomialOuterCutoff
            (((mellinSeparationTupleProduct x).1 : ℝ) / X) : ℂ) *
          mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
    let p := mellinSeparationTupleProduct x
    let c := mellinSeparationTupleCoefficient α x * mellinSeparationMonomial p s
    have hi :
        ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              (mellinSeparationTupleCoefficient α x *
                mellinSeparationMonomial p (s - Complex.I * (u : ℂ))) =
          c * ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              Complex.exp (Complex.I * (u : ℂ) * (Real.log (p.1 : ℝ) : ℂ)) := by
      calc
        _ = ∫ u : ℝ, c * (mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              Complex.exp (Complex.I * (u : ℂ) * (Real.log (p.1 : ℝ) : ℂ))) := by
          apply integral_congr_ae
          filter_upwards with u
          rw [mellinSeparationMonomial_shift]
          dsimp [c]
          ring
        _ = _ := integral_const_mul c _
    have hk := mellinSeparationKernelInversion_at hX p
    calc
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              (mellinSeparationTupleCoefficient α x *
                mellinSeparationMonomial p (s - Complex.I * (u : ℂ))) =
        c * ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              Complex.exp (Complex.I * (u : ℂ) * (Real.log (p.1 : ℝ) : ℂ))) := by
        rw [hi]
        ring
      _ = mellinSeparationTupleCoefficient α x *
          (polynomialOuterCutoff ((p.1 : ℝ) / X) : ℂ) *
            mellinSeparationMonomial p s := by
        rw [← hk]
        dsimp [c]
        ring
  calc
    mellinSeparationResidueMellinSum
        (mellinSeparationConvolutionProduct α) q a X s =
      ∑ x ∈ T, mellinSeparationTupleCoefficient α x *
        (polynomialOuterCutoff
          (((mellinSeparationTupleProduct x).1 : ℝ) / X) : ℂ) *
        mellinSeparationMonomial (mellinSeparationTupleProduct x) s := by
      exact mellinSeparationResidueMellinSum_eq_tupleSum α a X s
    _ = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ x ∈ T, ∫ u : ℝ, mellinSeparationLogKernelFourier u *
          mellinSeparationScaleFactor X u *
            (mellinSeparationTupleCoefficient α x *
              mellinSeparationMonomial (mellinSeparationTupleProduct x)
                (s - Complex.I * (u : ℂ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      exact (hterm x hx).symm
    _ = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ b ∈ mellinSeparationAllowedResidues a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (s - Complex.I * (u : ℂ)) := by
      congr 1
      exact (mellinSeparationResidueProducts_integral_eq_tupleIntegrals
        α hq a X s).symm

#print axioms mellinSeparation_toComplexArithmeticFunction_convolution
#print axioms mellinSeparation_dirichletConvolution_assoc
#print axioms mellinSeparationTupleFactor_le_threeX_of_outerCutoff_ne_zero
#print axioms mellinSeparationTruncateFactor_arithmeticProduct_apply
#print axioms mellinSeparationTruncateFactor_weightedTerm
#print axioms mellinSeparationArithmeticSingle_mul
#print axioms mellinSeparationConvolutionProduct_toArithmeticFunction
#print axioms mellinSeparationArithmeticSingle_tupleProduct
#print axioms mellinSeparationArithmeticProduct_eq_tupleConvolution
#print axioms mellinSeparationTupleTerm_integrable
#print axioms mellinSeparationFactorProduct_integrable
#print axioms mellinSeparationResidueProducts_integral_eq_tupleIntegrals
#print axioms separateSmoothConvolutionMellin

end FractionalPrimes.Literature.Polynomial

end
