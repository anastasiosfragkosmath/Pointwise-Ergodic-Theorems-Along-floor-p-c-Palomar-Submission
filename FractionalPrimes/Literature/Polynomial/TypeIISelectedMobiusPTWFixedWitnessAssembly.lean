module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWActualBlockIdentity
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusAllocatedFirstFactorMUF
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusAllocatedUncapped
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedDyadicPTWSourceAssembly
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWDyadicWindowIntegral
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWLogBudget
public import Mathlib.Tactic
@[expose] public section

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

/-! Same-witness assembly of the actual finite allocation identity with the
MUF first-factor estimate, followed by the checked allocated-scale uncapped
bound. The source decomposition is selected once; its `I/J/J'/i` are passed
unchanged through both branches. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- The finite allocated Dirichlet polynomial on a common source cutoff. -/
def selectedMobiusPTWCommonCutoffPolynomial
    {Q : ℕ} (a : ArithmeticFunction ℂ) (r q P : ℕ)
    (χ : BlueprintCharacter Q) (T t : ℝ) : ℂ :=
  finiteAllocatedDirichletPolynomial a r q (Finset.Icc 1 P) χ
    ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))

/-- One allocated source dyadic window at level `j` and quotient coordinate
`r`, with the source's exact denominator `4*C*r`. -/
def selectedMobiusPTWAllocatedWindowPolynomial
    {Q : ℕ} (a : ArithmeticFunction ℂ) (r q : ℕ)
    (M : ℝ) (j : ℕ) (χ : BlueprintCharacter Q) (T t : ℝ) : ℂ :=
  finiteAllocatedDirichletPolynomial a r q
    (factorExtractionRealInterval
      ((2 : ℝ) ^ j * (M / (4 * decompositionC * (r : ℝ))))
      (2 * ((2 : ℝ) ^ j * (M / (4 * decompositionC * (r : ℝ)))))) χ
    ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))

/-- The exact product of the three allocated finite Mellin polynomials in one
source dyadic cell, before its logarithmic reparameterization by the quotient
base. -/
def selectedMobiusPTWActualAllocatedWindowTerm
    {X z : ℝ} (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T : ℝ) (γ η η' : ℝ)
    (j k l : ℕ) (t : ℝ) : ℂ :=
  selectedMobiusPTWAllocatedWindowPolynomial
      (toComplexArithmeticFunction (groupedDyadicFactor z c fs₁))
      (r.1 0).1 (q / orderedAllocationPrefix r.1 0) (X ^ γ) j χ T t *
    selectedMobiusPTWAllocatedWindowPolynomial
      (toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₂))
      (r.1 1).1 (q / orderedAllocationPrefix r.1 1) (X ^ η) k χ T t *
    selectedMobiusPTWAllocatedWindowPolynomial
      (toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₃))
      (r.1 2).1 (q / orderedAllocationPrefix r.1 2) (X ^ η') l χ T t

/-- Exact source finite expansion at fixed selected groups. This abbreviated
proposition is the common-cutoff identity from the approved factorization,
with each of its `J₀³` summands written as an allocated window product. -/
def selectedMobiusPTWActualAllocationExpansionAt
    {X z c : ℝ} (fs : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T t γ η η' : ℝ)
    (I J J' : Finset (Fin fs.length)) : Prop :=
  let M₁ : ℝ := X ^ γ
  let M₂ : ℝ := X ^ η
  let M₃ : ℝ := X ^ η'
  let P₁ : ℕ := Nat.ceil (decompositionC * M₁)
  let P₂ : ℕ := Nat.ceil (decompositionC * M₂)
  let P₃ : ℕ := Nat.ceil (decompositionC * M₃)
  let P : ℕ := P₁ * P₂ * P₃
  let r₁ : ℕ := (r.1 0).1
  let r₂ : ℕ := (r.1 1).1
  let r₃ : ℕ := (r.1 2).1
  let q₁ : ℕ := q / orderedAllocationPrefix r.1 0
  let q₂ : ℕ := q / orderedAllocationPrefix r.1 1
  let q₃ : ℕ := q / orderedAllocationPrefix r.1 2
  let a₁ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
  let a₂ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
  let a₃ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
  selectedMobiusPTWCommonCutoffPolynomial a₁ r₁ q₁ P χ T t *
    selectedMobiusPTWCommonCutoffPolynomial a₂ r₂ q₂ P χ T t *
    selectedMobiusPTWCommonCutoffPolynomial a₃ r₃ q₃ P χ T t =
    ∑ i ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∑ j ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
        ∑ k ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
          selectedMobiusPTWAllocatedWindowPolynomial a₁ r₁ q₁ M₁ i χ T t *
            selectedMobiusPTWAllocatedWindowPolynomial a₂ r₂ q₂ M₂ j χ T t *
            selectedMobiusPTWAllocatedWindowPolynomial a₃ r₃ q₃ M₃ k χ T t

/-- The common-cutoff product appearing on the left side of the fixed-group
source allocation identity. -/
def selectedMobiusPTWActualCommonCutoffTerm
    {X z c : ℝ} (fs : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T t γ η η' : ℝ)
    (I J J' : Finset (Fin fs.length)) : ℂ :=
  let M₁ : ℝ := X ^ γ
  let M₂ : ℝ := X ^ η
  let M₃ : ℝ := X ^ η'
  let P₁ : ℕ := Nat.ceil (decompositionC * M₁)
  let P₂ : ℕ := Nat.ceil (decompositionC * M₂)
  let P₃ : ℕ := Nat.ceil (decompositionC * M₃)
  let P : ℕ := P₁ * P₂ * P₃
  let r₁ : ℕ := (r.1 0).1
  let r₂ : ℕ := (r.1 1).1
  let r₃ : ℕ := (r.1 2).1
  let q₁ : ℕ := q / orderedAllocationPrefix r.1 0
  let q₂ : ℕ := q / orderedAllocationPrefix r.1 1
  let q₃ : ℕ := q / orderedAllocationPrefix r.1 2
  let a₁ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
  let a₂ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
  let a₃ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
  selectedMobiusPTWCommonCutoffPolynomial a₁ r₁ q₁ P χ T t *
    selectedMobiusPTWCommonCutoffPolynomial a₂ r₂ q₂ P χ T t *
      selectedMobiusPTWCommonCutoffPolynomial a₃ r₃ q₃ P χ T t

/-- The actual finite allocation identity and fixed-index MUF estimate share
the exact `I/J/J'/i` supplied by the source type-II decomposition. The MUF
estimate is uniform in every divisor allocation, residual character, source
block length, and frequency in its stated window. -/
theorem selectedMobiusPTW_actualAllocationIdentity_with_MUF
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (α : Fin (mobiusLabelFactors ν).length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin (mobiusLabelFactors ν).length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((mobiusLabelFactors ν).get j) ∧
        dyadicFactorScale ((mobiusLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j)
    (hNoIα : ∀ j, α j < (3 / 8 : ℝ))
    (hdata : largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
      (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
      (groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ) (mobiusLabelFactors ν))
      (mobiusLabelFactors ν) α)
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
    (T t : ℝ) :
    ∃ (I J J' : Finset (Fin (mobiusLabelFactors ν).length))
      (i : Fin (mobiusLabelFactors ν).length) (γ η η' : ℝ),
      i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := dyadicMobiusCutoff X) (c := dyadicBinomialCoefficient ν.1)
        (mobiusLabelFactors ν) r χ T t γ η η' I J J' ∧
      ∀ (r' : divisorFactorTuples 3 d) (χ' : BlueprintCharacter Q)
        (N₁ : ℝ), 0 < N₁ → ∀ (s : ℝ),
          (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
          ‖∑ n ∈ factorExtractionRealInterval
              (N₁ / ((r'.1 0).1 : ℝ))
              (2 * N₁ / ((r'.1 0).1 : ℝ)),
            toComplexArithmeticFunction
                (groupedDyadicFactor (dyadicMobiusCutoff X)
                  (dyadicBinomialCoefficient ν.1 : ℂ)
                  (selectedDyadicFactors (mobiusLabelFactors ν) I))
                ((r'.1 0).1 * n) *
              factorExtractionMellinWeight
                (selectedPTWAllocationCharacterWeight q r' χ' 0) s n‖ ≤
            (Real.log X) ^ (-20 * a) *
              Real.sqrt (N₁ / ((r'.1 0).1 : ℝ)) := by
  classical
  have hXthree : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  obtain ⟨I, J, J', i, γ, η, η', hiI, hiAlpha, hidentity⟩ :=
    selectedMobiusPTW_actualTypeII_finiteAllocation_eq_dyadicBlockSum
      (X := X) (z := dyadicMobiusCutoff X)
      (c := dyadicBinomialCoefficient ν.1) (δ := decompositionDelta X)
      (f := groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ) (mobiusLabelFactors ν))
      (fs := mobiusLabelFactors ν) (α := α) (q := q)
      hXthree hdata r χ T t
  have hExpansion :
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := dyadicMobiusCutoff X) (c := dyadicBinomialCoefficient ν.1)
        (mobiusLabelFactors ν) r χ T t γ η η' I J J' := by
    simpa [selectedMobiusPTWActualAllocationExpansionAt,
      selectedMobiusPTWCommonCutoffPolynomial,
      selectedMobiusPTWAllocatedWindowPolynomial] using hidentity
  refine ⟨I, J, J', i, γ, η, η', hiI, hiAlpha, hExpansion, ?_⟩
  intro r' χ' N₁ hN₁ s hslo hshi
  exact selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex
    hMUF ha hXlarge hXorig hXabsorb ν α hα hsum hscale hNoIα
    I i hiI hiAlpha hd hQ hqfactor hqlog r' hN₁ χ' s hslo hshi

private theorem selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
    {n : ℕ} (hn : 0 < n) : 1 ≤ divisorCoefficient 2 n := by
  have heq : divisorCoefficient 2 n = n.divisors.card := by
    change (ArithmeticFunction.zeta ^ 2) n = n.divisors.card
    rw [show (2 : ℕ) = 1 + 1 by omega, pow_succ, pow_one,
      ArithmeticFunction.mul_zeta_apply]
    calc
      (∑ d ∈ n.divisors, ArithmeticFunction.zeta d) =
          ∑ d ∈ n.divisors, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact ArithmeticFunction.zeta_apply_ne
          (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
      _ = n.divisors.card := by simp
  rw [heq]
  have hmem : 1 ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd n, Nat.ne_of_gt hn⟩
  exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1, hmem⟩)

/-- The finite block expansion with explicit source groups and support
witnesses. This version fixes the source `I/J/J'/i` once, so it can be used
uniformly in the time variable alongside the fixed-index MUF estimate. -/
theorem selectedMobiusPTW_fixedActualAllocationExpansion_of_sourceWitness
    {X z c δ : ℝ} (hX : 3 ≤ X)
    {fs : List (DyadicArithmeticFactor X)}
    {α : Fin fs.length → ℝ}
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T t : ℝ)
    (I J J' : Finset (Fin fs.length))
    (i : Fin fs.length) (γ η η' : ℝ)
    (hiI : i ∈ I) (hαi : (1 / 80 : ℝ) ≤ α i)
    {v a b1 : ComplexPositiveIntegerFunction}
    (hv : v = groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
    (ha : a = dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
    (hb1 : b1 = dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
    (hvSupport : complexPositiveSupportedOnInterval v
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (haSupport : complexPositiveSupportedOnInterval a
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hb1Support : complexPositiveSupportedOnInterval b1
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η')) :
    i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := z) (c := c) fs r χ T t γ η η' I J J' := by
  classical
  let M₁ : ℝ := X ^ γ
  let M₂ : ℝ := X ^ η
  let M₃ : ℝ := X ^ η'
  let P₁ : ℕ := Nat.ceil (decompositionC * M₁)
  let P₂ : ℕ := Nat.ceil (decompositionC * M₂)
  let P₃ : ℕ := Nat.ceil (decompositionC * M₃)
  let P : ℕ := P₁ * P₂ * P₃
  let r₁ : ℕ := (r.1 0).1
  let r₂ : ℕ := (r.1 1).1
  let r₃ : ℕ := (r.1 2).1
  let q₁ : ℕ := q / orderedAllocationPrefix r.1 0
  let q₂ : ℕ := q / orderedAllocationPrefix r.1 1
  let q₃ : ℕ := q / orderedAllocationPrefix r.1 2
  let a₁ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
  let a₂ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
  let a₃ : ArithmeticFunction ℂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
  have hXpos : 0 < X := by linarith
  have hC : 1 ≤ decompositionC := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    change (1 : ℝ) ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hM₁ : 0 < M₁ := by dsimp [M₁]; exact Real.rpow_pos_of_pos hXpos γ
  have hM₂ : 0 < M₂ := by dsimp [M₂]; exact Real.rpow_pos_of_pos hXpos η
  have hM₃ : 0 < M₃ := by dsimp [M₃]; exact Real.rpow_pos_of_pos hXpos η'
  have hr₁pos : 0 < r₁ := by dsimp [r₁]; exact (r.1 0).2
  have hr₂pos : 0 < r₂ := by dsimp [r₂]; exact (r.1 1).2
  have hr₃pos : 0 < r₃ := by dsimp [r₃]; exact (r.1 2).2
  have hr₁one : 1 ≤ r₁ := Nat.succ_le_iff.mpr hr₁pos
  have hr₂one : 1 ≤ r₂ := Nat.succ_le_iff.mpr hr₂pos
  have hr₃one : 1 ≤ r₃ := Nat.succ_le_iff.mpr hr₃pos
  have hP₁pos : 0 < P₁ := by
    dsimp [P₁]
    apply Nat.ceil_pos.mpr
    exact mul_pos (lt_of_lt_of_le (by norm_num) hC) hM₁
  have hP₂pos : 0 < P₂ := by
    dsimp [P₂]
    apply Nat.ceil_pos.mpr
    exact mul_pos (lt_of_lt_of_le (by norm_num) hC) hM₂
  have hP₃pos : 0 < P₃ := by
    dsimp [P₃]
    apply Nat.ceil_pos.mpr
    exact mul_pos (lt_of_lt_of_le (by norm_num) hC) hM₃
  have hP₁one : 1 ≤ P₁ := Nat.succ_le_iff.mpr hP₁pos
  have hP₂one : 1 ≤ P₂ := Nat.succ_le_iff.mpr hP₂pos
  have hP₃one : 1 ≤ P₃ := Nat.succ_le_iff.mpr hP₃pos
  have hP₁le : P₁ ≤ P := by
    dsimp [P]
    exact (Nat.le_mul_of_pos_right _ hP₂pos).trans
      (Nat.le_mul_of_pos_right _ hP₃pos)
  have hP₂le : P₂ ≤ P := by
    dsimp [P]
    calc
      P₂ ≤ P₁ * P₂ := Nat.le_mul_of_pos_left _ hP₁pos
      _ ≤ (P₁ * P₂) * P₃ := Nat.le_mul_of_pos_right _ hP₃pos
  have hP₃le : P₃ ≤ P := by
    dsimp [P]
    calc
      P₃ ≤ P₂ * P₃ := Nat.le_mul_of_pos_left _ hP₂pos
      _ ≤ P₁ * (P₂ * P₃) := Nat.le_mul_of_pos_left _ hP₁pos
      _ = P₁ * P₂ * P₃ := by ring
  have hvSupport' : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * M₁) (decompositionC * M₁) := by
    simpa only [← hv] using hvSupport
  have haSupport' : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * M₂) (decompositionC * M₂) := by
    simpa only [← ha] using haSupport
  have hb1Support' : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * M₃) (decompositionC * M₃) := by
    simpa only [← hb1] using hb1Support
  have hsupport₁ : ∀ n, a₁ (r₁ * n) ≠ 0 →
      M₁ / decompositionC ≤ ((r₁ * n : ℕ) : ℝ) ∧
        ((r₁ * n : ℕ) : ℝ) ≤ decompositionC * M₁ := by
    intro n hn
    exact selectedMobiusPTW_allocated_support_of_group_support hC
      hvSupport' hn
  have hsupport₂ : ∀ n, a₂ (r₂ * n) ≠ 0 →
      M₂ / decompositionC ≤ ((r₂ * n : ℕ) : ℝ) ∧
        ((r₂ * n : ℕ) : ℝ) ≤ decompositionC * M₂ := by
    intro n hn
    exact selectedMobiusPTW_allocated_support_of_group_support hC
      haSupport' hn
  have hsupport₃ : ∀ n, a₃ (r₃ * n) ≠ 0 →
      M₃ / decompositionC ≤ ((r₃ * n : ℕ) : ℝ) ∧
        ((r₃ * n : ℕ) : ℝ) ≤ decompositionC * M₃ := by
    intro n hn
    exact selectedMobiusPTW_allocated_support_of_group_support hC
      hb1Support' hn
  have hcutoff₁ : ∀ n, a₁ (r₁ * n) ≠ 0 → n ≤ P := by
    intro n hn
    exact (selectedMobiusPTW_allocated_cutoff_of_group_support hC hr₁one
      hvSupport' hn).trans hP₁le
  have hcutoff₂ : ∀ n, a₂ (r₂ * n) ≠ 0 → n ≤ P := by
    intro n hn
    exact (selectedMobiusPTW_allocated_cutoff_of_group_support hC hr₂one
      haSupport' hn).trans hP₂le
  have hcutoff₃ : ∀ n, a₃ (r₃ * n) ≠ 0 → n ≤ P := by
    intro n hn
    exact (selectedMobiusPTW_allocated_cutoff_of_group_support hC hr₃one
      hb1Support' hn).trans hP₃le
  have hB₁ : 0 < selectedPTWFactorScale X r₁ := by
    have hlog : 0 < Real.log (8 * X) := by
      exact lt_trans (by norm_num) (log_eightX_gt_one hX)
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one hr₁pos
    have hdiv : 1 ≤ (divisorCoefficient 2 r₁ : ℝ) := by exact_mod_cast hdivNat
    have hpow : 0 < (divisorCoefficient 2 r₁ : ℝ) ^ 20 :=
      lt_of_lt_of_le (by norm_num) (one_le_pow₀ hdiv)
    unfold selectedPTWFactorScale
    exact mul_pos (mul_pos (by positivity) hlog) hpow
  have hB₂ : 0 < selectedPTWFactorScale X r₂ := by
    have hlog : 0 < Real.log (8 * X) := by
      exact lt_trans (by norm_num) (log_eightX_gt_one hX)
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one hr₂pos
    have hdiv : 1 ≤ (divisorCoefficient 2 r₂ : ℝ) := by exact_mod_cast hdivNat
    have hpow : 0 < (divisorCoefficient 2 r₂ : ℝ) ^ 20 :=
      lt_of_lt_of_le (by norm_num) (one_le_pow₀ hdiv)
    unfold selectedPTWFactorScale
    exact mul_pos (mul_pos (by positivity) hlog) hpow
  have hB₃ : 0 < selectedPTWFactorScale X r₃ := by
    have hlog : 0 < Real.log (8 * X) := by
      exact lt_trans (by norm_num) (log_eightX_gt_one hX)
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one hr₃pos
    have hdiv : 1 ≤ (divisorCoefficient 2 r₃ : ℝ) := by exact_mod_cast hdivNat
    have hpow : 0 < (divisorCoefficient 2 r₃ : ℝ) ^ 20 :=
      lt_of_lt_of_le (by norm_num) (one_le_pow₀ hdiv)
    unfold selectedPTWFactorScale
    exact mul_pos (mul_pos (by positivity) hlog) hpow
  have hcover := selectedMobiusPTWDyadicBlockCount_covers hC
  have hχcut₁ : ∀ n, selectedPTWAllocationCharacterWeight q r χ 0 n =
      if Nat.Coprime n q₁ then evalInt χ (n : ℤ) else 0 := by
    intro n
    rfl
  have hχcut₂ : ∀ n, selectedPTWAllocationCharacterWeight q r χ 1 n =
      if Nat.Coprime n q₂ then evalInt χ (n : ℤ) else 0 := by
    intro n
    rfl
  have hχcut₃ : ∀ n, selectedPTWAllocationCharacterWeight q r χ 2 n =
      if Nat.Coprime n q₃ then evalInt χ (n : ℤ) else 0 := by
    intro n
    rfl
  have hblocks := selectedGroupTripleCutoffProduct_eq_allocatedBlockSum_of_scaledSupport
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    (C₁ := decompositionC) (C₂ := decompositionC) (C₃ := decompositionC)
    (B₁ := selectedPTWFactorScale X r₁)
    (B₂ := selectedPTWFactorScale X r₂)
    (B₃ := selectedPTWFactorScale X r₃)
    (T := T) (t := t)
    (r₁ := r₁) (r₂ := r₂) (r₃ := r₃)
    (q₁ := q₁) (q₂ := q₂) (q₃ := q₃) (Q := Q)
    (k₁ := selectedMobiusPTWDyadicBlockCount decompositionC)
    (k₂ := selectedMobiusPTWDyadicBlockCount decompositionC)
    (k₃ := selectedMobiusPTWDyadicBlockCount decompositionC)
    (P₁ := P) (P₂ := P) (P₃ := P)
    hM₁ hM₂ hM₃ hC hC hC hr₁pos hr₂pos hr₃pos
    hcover hcover hcover hB₁ hB₂ hB₃ a₁ a₂ a₃ χ
    (selectedPTWAllocationCharacterWeight q r χ 0)
    (selectedPTWAllocationCharacterWeight q r χ 1)
    (selectedPTWAllocationCharacterWeight q r χ 2)
    hχcut₁ hχcut₂ hχcut₃ hcutoff₁ hcutoff₂ hcutoff₃
    hsupport₁ hsupport₂ hsupport₃
  refine ⟨hiI, hαi, ?_⟩
  simpa [selectedMobiusPTWActualAllocationExpansionAt,
    selectedMobiusPTWCommonCutoffPolynomial,
    selectedMobiusPTWAllocatedWindowPolynomial,
    M₁, M₂, M₃, P₁, P₂, P₃, P, r₁, r₂, r₃,
    q₁, q₂, q₃, a₁, a₂, a₃] using hblocks

/-! The source existential is eliminated once here. Both the all-frequency
finite expansion and the MUF estimate retain the very same selected groups
and distinguished factor. -/
theorem selectedMobiusPTW_actualSourceWitness_allTimes_from_MUF
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (α : Fin (mobiusLabelFactors ν).length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin (mobiusLabelFactors ν).length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((mobiusLabelFactors ν).get j) ∧
        dyadicFactorScale ((mobiusLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j)
    (hNoIα : ∀ j, α j < (3 / 8 : ℝ))
    (hdata : largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
      (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
      (groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ) (mobiusLabelFactors ν))
      (mobiusLabelFactors ν) α)
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a) :
    ∃ (I J J' : Finset (Fin (mobiusLabelFactors ν).length))
      (i : Fin (mobiusLabelFactors ν).length) (γ η η' : ℝ),
      i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
      γ + η + η' = 1 ∧ (1 / 4 : ℝ) ≤ γ ∧ γ ≤ 1 / 2 ∧
      0 ≤ η ∧ 0 ≤ η' ∧ |η - η'| ≤ 1 / 4 ∧
      complexPositiveSupportedOnInterval
        (groupedDyadicFactor (dyadicMobiusCutoff X)
          (dyadicBinomialCoefficient ν.1 : ℂ)
          (selectedDyadicFactors (mobiusLabelFactors ν) I))
        (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ) ∧
      complexPositiveSupportedOnInterval
        (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
          (selectedDyadicFactors (mobiusLabelFactors ν) J))
        (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η) ∧
      complexPositiveSupportedOnInterval
        (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
          (selectedDyadicFactors (mobiusLabelFactors ν) J'))
        (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η') ∧
      (∀ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
        (T t : ℝ),
        selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
          (z := dyadicMobiusCutoff X)
          (c := dyadicBinomialCoefficient ν.1) (mobiusLabelFactors ν)
          r χ T t γ η η' I J J') ∧
      (∀ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
        (N₁ : ℝ), 0 < N₁ → ∀ (s : ℝ),
          (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
          ‖∑ n ∈ factorExtractionRealInterval
              (N₁ / ((r.1 0).1 : ℝ))
              (2 * N₁ / ((r.1 0).1 : ℝ)),
            toComplexArithmeticFunction
                (groupedDyadicFactor (dyadicMobiusCutoff X)
                  (dyadicBinomialCoefficient ν.1 : ℂ)
                  (selectedDyadicFactors (mobiusLabelFactors ν) I))
                ((r.1 0).1 * n) *
              factorExtractionMellinWeight
                (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
            (Real.log X) ^ (-20 * a) *
              Real.sqrt (N₁ / ((r.1 0).1 : ℝ))) := by
  classical
  have hXthree : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  rcases hdata with ⟨Aminus, Aplus, v, a₁, a₂, γ, η, η', I, J, J', i,
    htypeII, hfactor, hv, ha₁, ha₂, hAminus1, hAminusAplus,
    hAminusLow, hAplusHigh, hgammasum, hgammaLo, hgammaHi, hmajorGap,
    hvSupport, ha₁Support, ha₂Support, hiI, hiAlpha⟩
  have hISupport :
      complexPositiveSupportedOnInterval
        (groupedDyadicFactor (dyadicMobiusCutoff X)
          (dyadicBinomialCoefficient ν.1 : ℂ)
          (selectedDyadicFactors (mobiusLabelFactors ν) I))
        (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ) := by
    simpa only [← hv] using hvSupport
  have hJSupport :
      complexPositiveSupportedOnInterval
        (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
          (selectedDyadicFactors (mobiusLabelFactors ν) J))
        (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η) := by
    simpa only [← ha₁] using ha₁Support
  have hJ'Support :
      complexPositiveSupportedOnInterval
        (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
          (selectedDyadicFactors (mobiusLabelFactors ν) J'))
        (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η') := by
    simpa only [← ha₂] using ha₂Support
  have heta0 : 0 ≤ η := by
    have hgap := abs_le.mp hmajorGap
    have hsumEta : (1 / 2 : ℝ) ≤ η + η' := by linarith
    nlinarith
  have heta'0 : 0 ≤ η' := by
    have hgap := abs_le.mp hmajorGap
    have hsumEta : (1 / 2 : ℝ) ≤ η + η' := by linarith
    nlinarith
  refine ⟨I, J, J', i, γ, η, η', hiI, hiAlpha,
    hgammasum, hgammaLo, hgammaHi, heta0, heta'0, hmajorGap,
    hISupport, hJSupport, hJ'Support, ?_, ?_⟩
  · intro r χ T t
    exact (selectedMobiusPTW_fixedActualAllocationExpansion_of_sourceWitness
      (δ := decompositionDelta X) hXthree r χ T t I J J' i γ η η' hiI hiAlpha hv ha₁ ha₂
      hvSupport ha₁Support ha₂Support).2.2
  · intro r χ N₁ hN₁ s hslo hshi
    exact selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex
      hMUF ha hXlarge hXorig hXabsorb ν α hα hsum hscale hNoIα
      I i hiI hiAlpha hd hQ hqfactor hqlog r hN₁ χ s hslo hshi

/-- One summand in the exact allocated-window expansion is precisely the
source-normalized PTW factor product at its quotient lengths. The lengths are
the literal 2^j X^γ/(4 C rᵢ) windows; the geometry supplies their exact
logarithmic reparameterization by Y. -/
theorem selectedMobiusPTW_actualAllocatedWindowProduct_eq_sourceTerm
    {X z Y eps U : ℝ} (hXsrc : 3 ≤ X) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T t : ℝ)
    (j k l : ℕ)
    (geometry : SelectedMobiusPTWAllocatedGeometry eps Y U)
    (hM₁ : geometry.uncapped.M =
      (2 : ℝ) ^ j * (X ^ geometry.uncapped.alpha /
        (4 * decompositionC * ((r.1 0).1 : ℝ))))
    (hM₂ : geometry.M₂ =
      (2 : ℝ) ^ k * (X ^ geometry.uncapped.beta /
        (4 * decompositionC * ((r.1 1).1 : ℝ))))
    (hM₃ : geometry.M₃ =
      (2 : ℝ) ^ l * (X ^ geometry.uncapped.gamma /
        (4 * decompositionC * ((r.1 2).1 : ℝ)))) :
    selectedMobiusPTWAllocatedWindowPolynomial
        (toComplexArithmeticFunction (groupedDyadicFactor z c fs₁))
        (r.1 0).1 (q / orderedAllocationPrefix r.1 0)
        (X ^ geometry.uncapped.alpha) j χ T t *
      selectedMobiusPTWAllocatedWindowPolynomial
        (toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs₂))
        (r.1 1).1 (q / orderedAllocationPrefix r.1 1)
        (X ^ geometry.uncapped.beta) k χ T t *
      selectedMobiusPTWAllocatedWindowPolynomial
        (toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs₃))
        (r.1 2).1 (q / orderedAllocationPrefix r.1 2)
        (X ^ geometry.uncapped.gamma) l χ T t =
      selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
        geometry.uncapped.alpha geometry.uncapped.beta
        geometry.uncapped.gamma T r χ t := by
  have hM₁pow :
      (2 : ℝ) ^ j * (X ^ geometry.uncapped.alpha /
        (4 * decompositionC * ((r.1 0).1 : ℝ))) =
        Y ^ geometry.uncapped.alpha := by
    calc
      _ = geometry.uncapped.M := hM₁.symm
      _ = Y ^ geometry.uncapped.alpha := geometry.uncapped.hMpow
  have hM₂pow :
      (2 : ℝ) ^ k * (X ^ geometry.uncapped.beta /
        (4 * decompositionC * ((r.1 1).1 : ℝ))) =
        Y ^ geometry.uncapped.beta := by
    calc
      _ = geometry.M₂ := hM₂.symm
      _ = Y ^ geometry.uncapped.beta := geometry.hM₂
  have hM₃pow :
      (2 : ℝ) ^ l * (X ^ geometry.uncapped.gamma /
        (4 * decompositionC * ((r.1 2).1 : ℝ))) =
        Y ^ geometry.uncapped.gamma := by
    calc
      _ = geometry.M₃ := hM₃.symm
      _ = Y ^ geometry.uncapped.gamma := geometry.hM₃
  have hM₁pos : 0 <
      (2 : ℝ) ^ j * (X ^ geometry.uncapped.alpha /
        (4 * decompositionC * ((r.1 0).1 : ℝ))) := by
    rw [← hM₁]
    exact geometry.uncapped.hM
  have hM₂pos : 0 <
      (2 : ℝ) ^ k * (X ^ geometry.uncapped.beta /
        (4 * decompositionC * ((r.1 1).1 : ℝ))) := by
    have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXsrc
    have hC : 1 ≤ decompositionC := by
      change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    have hCpos : 0 < decompositionC := lt_of_lt_of_le (by norm_num) hC
    have hrpos : 0 < ((r.1 1).1 : ℝ) := by exact_mod_cast (r.1 1).2
    exact mul_pos (by positivity)
      (div_pos (Real.rpow_pos_of_pos hXpos _) (by positivity))
  have hM₃pos : 0 <
      (2 : ℝ) ^ l * (X ^ geometry.uncapped.gamma /
        (4 * decompositionC * ((r.1 2).1 : ℝ))) := by
    have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXsrc
    have hC : 1 ≤ decompositionC := by
      change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    have hCpos : 0 < decompositionC := lt_of_lt_of_le (by norm_num) hC
    have hrpos : 0 < ((r.1 2).1 : ℝ) := by exact_mod_cast (r.1 2).2
    exact mul_pos (by positivity)
      (div_pos (Real.rpow_pos_of_pos hXpos _) (by positivity))
  have hB₁ : 0 < selectedPTWFactorScale X (r.1 0).1 := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 0).2
    have hdiv : 1 ≤ (divisorCoefficient 2 (r.1 0).1 : ℝ) := by
      exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hB₂ : 0 < selectedPTWFactorScale X (r.1 1).1 := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 1).2
    have hdiv : 1 ≤ (divisorCoefficient 2 (r.1 1).1 : ℝ) := by
      exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hB₃ : 0 < selectedPTWFactorScale X (r.1 2).1 := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 2).2
    have hdiv : 1 ≤ (divisorCoefficient 2 (r.1 2).1 : ℝ) := by
      exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hsource := selectedMobiusPTW_allocatedWindowProduct_eq_sourceTerm
    (X := X) (Y := Y) (z := z) (d := d) (Q := Q) (q := q)
    (c := c) fs₁ fs₂ fs₃ r χ
    (T := T) (t := t)
    (alpha := geometry.uncapped.alpha)
    (beta := geometry.uncapped.beta)
    (gamma := geometry.uncapped.gamma)
    (M₁ := (2 : ℝ) ^ j *
      (X ^ geometry.uncapped.alpha /
        (4 * decompositionC * ((r.1 0).1 : ℝ))))
    (M₂ := (2 : ℝ) ^ k *
      (X ^ geometry.uncapped.beta /
        (4 * decompositionC * ((r.1 1).1 : ℝ))))
    (M₃ := (2 : ℝ) ^ l *
      (X ^ geometry.uncapped.gamma /
        (4 * decompositionC * ((r.1 2).1 : ℝ))))
    hM₁pow hM₂pow hM₃pow hM₁pos hM₂pos hM₃pos hB₁ hB₂ hB₃
  simpa [selectedMobiusPTWAllocatedWindowPolynomial] using hsource

/-- Each exact allocated window product is represented by the normalized
source allocation term with base `2` and logarithmic exponents. This identity
is purely finite and does not assert that the cell is retained for the
analytic estimate. -/
theorem selectedMobiusPTW_actualAllocatedCell_eq_baseTwoTerm
    {X z : ℝ} (hXsrc : 3 ≤ X) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T t γ η η' : ℝ) (j k l : ℕ) :
    selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c fs₁ fs₂ fs₃
        r χ T γ η η' j k l t =
      selectedDyadicPTWAllocationTerm q X z 2 c fs₁ fs₂ fs₃
        (Real.log ((2 : ℝ) ^ j *
          (X ^ γ / (4 * decompositionC * ((r.1 0).1 : ℝ)))) /
            Real.log 2)
        (Real.log ((2 : ℝ) ^ k *
          (X ^ η / (4 * decompositionC * ((r.1 1).1 : ℝ)))) /
            Real.log 2)
        (Real.log ((2 : ℝ) ^ l *
          (X ^ η' / (4 * decompositionC * ((r.1 2).1 : ℝ)))) /
            Real.log 2)
        T r χ t := by
  classical
  let r₁ := (r.1 0).1
  let r₂ := (r.1 1).1
  let r₃ := (r.1 2).1
  let M₁ : ℝ := (2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC * (r₁ : ℝ)))
  let M₂ : ℝ := (2 : ℝ) ^ k * (X ^ η / (4 * decompositionC * (r₂ : ℝ)))
  let M₃ : ℝ := (2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC * (r₃ : ℝ)))
  have hC : 0 < decompositionC := by
    change 0 < (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    exact mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hr₁pos : 0 < (r₁ : ℝ) := by exact_mod_cast (r.1 0).2
  have hr₂pos : 0 < (r₂ : ℝ) := by exact_mod_cast (r.1 1).2
  have hr₃pos : 0 < (r₃ : ℝ) := by exact_mod_cast (r.1 2).2
  have hXpos : 0 < X := by linarith
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  have hM₂ : 0 < M₂ := by dsimp [M₂]; positivity
  have hM₃ : 0 < M₃ := by dsimp [M₃]; positivity
  have hYtwo : (1 : ℝ) < 2 := by norm_num
  let α := Real.log M₁ / Real.log 2
  let β := Real.log M₂ / Real.log 2
  let ζ := Real.log M₃ / Real.log 2
  have hscale₁ : (2 : ℝ) ^ α = M₁ := by
    dsimp [α]
    exact selectedMobiusPTW_length_eq_rpow_log hYtwo hM₁
  have hscale₂ : (2 : ℝ) ^ β = M₂ := by
    dsimp [β]
    exact selectedMobiusPTW_length_eq_rpow_log hYtwo hM₂
  have hscale₃ : (2 : ℝ) ^ ζ = M₃ := by
    dsimp [ζ]
    exact selectedMobiusPTW_length_eq_rpow_log hYtwo hM₃
  have hB₁ : 0 < selectedPTWFactorScale X r₁ := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 0).2
    have hdiv : 1 ≤ (divisorCoefficient 2 r₁ : ℝ) := by exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hB₂ : 0 < selectedPTWFactorScale X r₂ := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 1).2
    have hdiv : 1 ≤ (divisorCoefficient 2 r₂ : ℝ) := by exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hB₃ : 0 < selectedPTWFactorScale X r₃ := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 2).2
    have hdiv : 1 ≤ (divisorCoefficient 2 r₃ : ℝ) := by exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hsource := selectedMobiusPTW_allocatedWindowProduct_eq_sourceTerm
    (X := X) (Y := 2) (z := z) (q := q) c fs₁ fs₂ fs₃ r χ
    (alpha := α) (beta := β) (gamma := ζ) (T := T) (t := t)
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
    hscale₁.symm hscale₂.symm hscale₃.symm hM₁ hM₂ hM₃ hB₁ hB₂ hB₃
  simpa [selectedMobiusPTWActualAllocatedWindowTerm,
    selectedMobiusPTWAllocatedWindowPolynomial,
    M₁, M₂, M₃, r₁, r₂, r₃, α, β, ζ] using hsource

/-- A nonzero finite allocated Dirichlet polynomial has a nonzero source
coefficient in its finite index set. -/
theorem finiteAllocatedDirichletPolynomial_nonzero_has_nonzero_coefficient
    {Q : ℕ} (a : ArithmeticFunction ℂ) (r q : ℕ) (S : Finset ℕ)
    (χ : BlueprintCharacter Q) (s : ℂ)
    (hpoly : finiteAllocatedDirichletPolynomial a r q S χ s ≠ 0) :
    ∃ n ∈ S, a (r * n) ≠ 0 := by
  classical
  unfold finiteAllocatedDirichletPolynomial at hpoly
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpoly
  refine ⟨n, hn, ?_⟩
  intro hzero
  simp [hzero] at hterm

/-- Any nonempty coefficient window of a selected Möbius first group has its
source dyadic length in the retained range. This is the exact support input
used when constructing the allocated quotient-scale geometry. -/
theorem selectedMobiusPTW_actualAllocatedWindow_retainedScale
    {X z : ℝ} (hXpos : 0 < X) (c : ℂ)
    (fs : List (DyadicArithmeticFactor X))
    (I : Finset (Fin fs.length)) (γ : ℝ)
    {r n : ℕ} (hr : 0 < r) (j : ℕ)
    (hsupport : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hcoeff : toComplexArithmeticFunction
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
        (r * n) ≠ 0)
    (hwindow : n ∈ factorExtractionRealInterval
      ((2 : ℝ) ^ j *
        (X ^ γ / (4 * decompositionC * (r : ℝ))))
      (2 * ((2 : ℝ) ^ j *
        (X ^ γ / (4 * decompositionC * (r : ℝ)))))) :
    X ^ γ / (2 * decompositionC) ≤
        (2 : ℝ) ^ j * X ^ γ / (4 * decompositionC) ∧
      (2 : ℝ) ^ j * X ^ γ / (4 * decompositionC) ≤
        (2 * decompositionC) * X ^ γ := by
  have hC : 1 ≤ decompositionC := by
    change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 :=
      one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 :=
      one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hsupport' :=
    selectedMobiusPTW_allocated_support_of_group_support
      hC hsupport hcoeff
  exact selectedMobiusPTW_retained_block_scale
    (Real.rpow_pos_of_pos hXpos γ) hC hr hsupport' hwindow

/-- The retained-scale consequence for any supported arithmetic group, not
just the distinguished grouped factor. -/
theorem selectedMobiusPTW_actualAllocatedFunctionWindow_retainedScale
    {X : ℝ} (hXpos : 0 < X) (f : ComplexPositiveIntegerFunction)
    (γ : ℝ) {r n : ℕ} (hr : 0 < r) (j : ℕ)
    (hsupport : complexPositiveSupportedOnInterval f
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hcoeff : toComplexArithmeticFunction f (r * n) ≠ 0)
    (hwindow : n ∈ factorExtractionRealInterval
      ((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC * (r : ℝ))))
      (2 * ((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC * (r : ℝ)))))) :
    X ^ γ / (2 * decompositionC) ≤
        (2 : ℝ) ^ j * X ^ γ / (4 * decompositionC) ∧
      (2 : ℝ) ^ j * X ^ γ / (4 * decompositionC) ≤
        (2 * decompositionC) * X ^ γ := by
  have hC : 1 ≤ decompositionC := by
    change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hsupport' := selectedMobiusPTW_allocated_support_of_group_support
    hC hsupport hcoeff
  exact selectedMobiusPTW_retained_block_scale
    (Real.rpow_pos_of_pos hXpos γ) hC hr hsupport' hwindow

set_option maxHeartbeats 2000000 in
/-- A nonzero triple finite-window product forces all three source group
windows to be nonempty. Their nonzero coefficients and the exact source
support intervals give the three retained-scale inequalities. -/
theorem selectedMobiusPTW_actualAllocatedCell_retainedScales_of_live
    {X z : ℝ} (hXpos : 0 < X) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (I : Finset (Fin fs₁.length))
    (J : Finset (Fin fs₂.length)) (J' : Finset (Fin fs₃.length))
    (γ η η' : ℝ)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs₁ I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs₂ J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs₃ J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T : ℝ) (j k l : ℕ) (t : ℝ)
    (hLive : selectedMobiusPTWActualAllocatedWindowTerm
      (z := z) (q := q) c
      (selectedDyadicFactors fs₁ I)
      (selectedDyadicFactors fs₂ J)
      (selectedDyadicFactors fs₃ J') r χ T γ η η' j k l t ≠ 0) :
    X ^ γ / (2 * decompositionC) ≤
        (2 : ℝ) ^ j * X ^ γ / (4 * decompositionC) ∧
      (2 : ℝ) ^ j * X ^ γ / (4 * decompositionC) ≤
        (2 * decompositionC) * X ^ γ ∧
      X ^ η / (2 * decompositionC) ≤
        (2 : ℝ) ^ k * X ^ η / (4 * decompositionC) ∧
      (2 : ℝ) ^ k * X ^ η / (4 * decompositionC) ≤
        (2 * decompositionC) * X ^ η ∧
      X ^ η' / (2 * decompositionC) ≤
        (2 : ℝ) ^ l * X ^ η' / (4 * decompositionC) ∧
      (2 : ℝ) ^ l * X ^ η' / (4 * decompositionC) ≤
        (2 * decompositionC) * X ^ η' := by
  classical
  let r₁ := (r.1 0).1
  let r₂ := (r.1 1).1
  let r₃ := (r.1 2).1
  let M₁ : ℝ := (2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC * (r₁ : ℝ)))
  let M₂ : ℝ := (2 : ℝ) ^ k * (X ^ η / (4 * decompositionC * (r₂ : ℝ)))
  let M₃ : ℝ := (2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC * (r₃ : ℝ)))
  let a₁ := toComplexArithmeticFunction
    (groupedDyadicFactor z c (selectedDyadicFactors fs₁ I))
  let a₂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs₂ J))
  let a₃ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs₃ J'))
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)
  let S₁ := factorExtractionRealInterval M₁ (2 * M₁)
  let S₂ := factorExtractionRealInterval M₂ (2 * M₂)
  let S₃ := factorExtractionRealInterval M₃ (2 * M₃)
  have hC : 0 < decompositionC := by
    dsimp [decompositionC]
    positivity
  have hr₁pos : 0 < (r₁ : ℝ) := by exact_mod_cast (r.1 0).2
  have hr₂pos : 0 < (r₂ : ℝ) := by exact_mod_cast (r.1 1).2
  have hr₃pos : 0 < (r₃ : ℝ) := by exact_mod_cast (r.1 2).2
  have hM₁ : 0 < M₁ := by
    dsimp [M₁]
    positivity
  have hM₂ : 0 < M₂ := by
    dsimp [M₂]
    positivity
  have hM₃ : 0 < M₃ := by
    dsimp [M₃]
    positivity
  have hproduct :
      finiteAllocatedDirichletPolynomial a₁ r₁
          (q / orderedAllocationPrefix r.1 0) S₁ χ s *
        finiteAllocatedDirichletPolynomial a₂ r₂
          (q / orderedAllocationPrefix r.1 1) S₂ χ s *
        finiteAllocatedDirichletPolynomial a₃ r₃
          (q / orderedAllocationPrefix r.1 2) S₃ χ s ≠ 0 := by
    simpa [selectedMobiusPTWActualAllocatedWindowTerm,
      selectedMobiusPTWAllocatedWindowPolynomial,
      a₁, a₂, a₃, S₁, S₂, S₃, s, r₁, r₂, r₃, M₁, M₂, M₃] using hLive
  have hP₁ : finiteAllocatedDirichletPolynomial a₁ r₁
      (q / orderedAllocationPrefix r.1 0) S₁ χ s ≠ 0 := by
    intro hz
    apply hproduct
    simp [hz]
  have hP₂ : finiteAllocatedDirichletPolynomial a₂ r₂
      (q / orderedAllocationPrefix r.1 1) S₂ χ s ≠ 0 := by
    intro hz
    apply hproduct
    simp [hz]
  have hP₃ : finiteAllocatedDirichletPolynomial a₃ r₃
      (q / orderedAllocationPrefix r.1 2) S₃ χ s ≠ 0 := by
    intro hz
    apply hproduct
    simp [hz]
  obtain ⟨n₁, hn₁, hcoeff₁⟩ :=
    finiteAllocatedDirichletPolynomial_nonzero_has_nonzero_coefficient
      a₁ r₁ (q / orderedAllocationPrefix r.1 0) S₁ χ s hP₁
  obtain ⟨n₂, hn₂, hcoeff₂⟩ :=
    finiteAllocatedDirichletPolynomial_nonzero_has_nonzero_coefficient
      a₂ r₂ (q / orderedAllocationPrefix r.1 1) S₂ χ s hP₂
  obtain ⟨n₃, hn₃, hcoeff₃⟩ :=
    finiteAllocatedDirichletPolynomial_nonzero_has_nonzero_coefficient
      a₃ r₃ (q / orderedAllocationPrefix r.1 2) S₃ χ s hP₃
  have hret₁ := selectedMobiusPTW_actualAllocatedFunctionWindow_retainedScale
    hXpos (groupedDyadicFactor z c (selectedDyadicFactors fs₁ I)) γ
    (r.1 0).2 j hSupport₁
    (by simpa [a₁, r₁] using hcoeff₁) (by simpa [S₁, M₁, r₁] using hn₁)
  have hret₂ := selectedMobiusPTW_actualAllocatedFunctionWindow_retainedScale
    hXpos (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs₂ J)) η
    (r.1 1).2 k hSupport₂
    (by simpa [a₂, r₂] using hcoeff₂) (by simpa [S₂, M₂, r₂] using hn₂)
  have hret₃ := selectedMobiusPTW_actualAllocatedFunctionWindow_retainedScale
    hXpos (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs₃ J')) η'
    (r.1 2).2 l hSupport₃
    (by simpa [a₃, r₃] using hcoeff₃) (by simpa [S₃, M₃, r₃] using hn₃)
  exact ⟨by simpa [M₁, r₁] using hret₁.1,
    by simpa [M₁, r₁] using hret₁.2,
    by simpa [M₂, r₂] using hret₂.1,
    by simpa [M₂, r₂] using hret₂.2,
    by simpa [M₃, r₃] using hret₃.1,
    by simpa [M₃, r₃] using hret₃.2⟩

/-- The fixed-index MUF block estimate at source length N₁ is exactly the
distinguished-factor hypothesis required by ldm:uncapped at quotient
length N₁/r₁. No scale or endpoint is changed. -/
theorem selectedMobiusPTW_actualAllocatedBlock_uncapped_from_MUF
    {X Y U eps a Tfreq z N₁ : ℝ} (hXsrc : 3 ≤ X)
    (c : ℂ) (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q)
    (geometry : SelectedMobiusPTWAllocatedGeometry eps Y U)
    (hM₁ : geometry.uncapped.M =
      N₁ / ((r.1 0).1 : ℝ))
    (hN₁ : 0 < N₁)
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : fs₁.length ≤ 20) (hlen₂ : fs₂.length ≤ 20)
    (hlen₃ : fs₃.length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight fs₁ ≤ Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight fs₂ ≤ Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight fs₃ ≤ Real.log (8 * X))
    (hY : (2 : ℝ) ^ 16 ≤ Y)
    (hδ0 : 0 < (Real.log X) ^ (-20 * a))
    (hδ : (Real.log X) ^ (-20 * a) ≤ 1)
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (hN₁ : 0 < N₁) (s : ℝ),
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval
          (N₁ / ((r.1 0).1 : ℝ))
          (2 * N₁ / ((r.1 0).1 : ℝ)),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
            ((r.1 0).1 * n) *
          factorExtractionMellinWeight
            (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
        (Real.log X) ^ (-20 * a) *
          Real.sqrt (N₁ / ((r.1 0).1 : ℝ))) :
    (∫ t in Set.Icc (-U) U,
      ‖selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
        geometry.uncapped.alpha geometry.uncapped.beta
        geometry.uncapped.gamma Tfreq r χ t‖ ∂volume) ≤
      selectedPTWFactorScale X (r.1 0).1 *
        selectedPTWFactorScale X (r.1 1).1 *
          selectedPTWFactorScale X (r.1 2).1 *
            selectedDyadicPTWUncappedKernel X Y a eps := by
  classical
  let r₁ := (r.1 0).1
  let r₂ := (r.1 1).1
  let r₃ := (r.1 2).1
  have hinterval :
      factorExtractionRealInterval geometry.uncapped.M
          (2 * geometry.uncapped.M) =
        factorExtractionRealInterval
          (N₁ / ((r.1 0).1 : ℝ))
          (2 * N₁ / ((r.1 0).1 : ℝ)) := by
    rw [hM₁]
    congr 1
    ring
  have hblock : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval
          geometry.uncapped.M (2 * geometry.uncapped.M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
            ((r.1 0).1 * n) *
          factorExtractionMellinWeight
            (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
        (Real.log X) ^ (-20 * a) *
          Real.sqrt geometry.uncapped.M := by
    intro s hslo hshi
    have h := hMUFblock hN₁ s hslo hshi
    have hsum :
        (∑ n ∈ factorExtractionRealInterval
            geometry.uncapped.M (2 * geometry.uncapped.M),
          toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n) =
          ∑ n ∈ factorExtractionRealInterval
            (N₁ / ((r.1 0).1 : ℝ))
            (2 * N₁ / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n := by
      rw [hinterval]
    rw [hsum]
    have hsqrt : Real.sqrt (N₁ / ((r.1 0).1 : ℝ)) =
        Real.sqrt geometry.uncapped.M := by rw [← hM₁]
    simpa [hsqrt] using h
  have hχ₁ : ∀ n,
      ‖selectedPTWAllocationCharacterWeight q r χ 0 n‖ ≤ 1 := by
    intro n
    unfold selectedPTWAllocationCharacterWeight
    split_ifs
    · exact evalInt_norm_le_one χ _
    · simp
  have hχ₂ : ∀ n,
      ‖selectedPTWAllocationCharacterWeight q r χ 1 n‖ ≤ 1 := by
    intro n
    unfold selectedPTWAllocationCharacterWeight
    split_ifs
    · exact evalInt_norm_le_one χ _
    · simp
  have hχ₃ : ∀ n,
      ‖selectedPTWAllocationCharacterWeight q r χ 2 n‖ ≤ 1 := by
    intro n
    unfold selectedPTWAllocationCharacterWeight
    split_ifs
    · exact evalInt_norm_le_one χ _
    · simp
  have hr₁ : 1 ≤ r₁ := Nat.succ_le_iff.mpr (r.1 0).2
  have hr₂ : 1 ≤ r₂ := Nat.succ_le_iff.mpr (r.1 1).2
  have hr₃ : 1 ≤ r₃ := Nat.succ_le_iff.mpr (r.1 2).2
  have hB₁ : 0 < selectedPTWFactorScale X r₁ := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 0).2
    have hdiv : 1 ≤ (divisorCoefficient 2 r₁ : ℝ) := by exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hB₂ : 0 < selectedPTWFactorScale X r₂ := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 1).2
    have hdiv : 1 ≤ (divisorCoefficient 2 r₂ : ℝ) := by exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have hB₃ : 0 < selectedPTWFactorScale X r₃ := by
    have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
      (r.1 2).2
    have hdiv : 1 ≤ (divisorCoefficient 2 r₃ : ℝ) := by exact_mod_cast hdivNat
    have hlog : 0 < Real.log (8 * X) :=
      lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
    unfold selectedPTWFactorScale
    positivity
  have huncapped := selectedMobiusPTW_allocated_block_uncapped
    c fs₁ fs₂ fs₃ r₁ r₂ r₃
    (selectedPTWAllocationCharacterWeight q r χ 0)
    (selectedPTWAllocationCharacterWeight q r χ 1)
    (selectedPTWAllocationCharacterWeight q r χ 2)
    geometry hXsrc hc hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃
    hr₁ hr₂ hr₃ hY hδ0 hδ hχ₁ hχ₂ hχ₃ hfreq hblock
  simpa [selectedDyadicPTWAllocationTerm, selectedDyadicPTWUncappedKernel,
    r₁, r₂, r₃, abs_of_pos hB₁, abs_of_pos hB₂, abs_of_pos hB₃] using huncapped

/-- Möbius selected groups contain at most twenty source factors, and their
mass weight is exactly one (the list has no logarithm factor). -/
theorem selectedMobiusPTW_fixedGroup_length_mass
    {X : ℝ} (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length)) :
    (selectedDyadicFactors (mobiusLabelFactors ν) I).length ≤ 20 ∧
      dyadicFactorsMassWeight
          (selectedDyadicFactors (mobiusLabelFactors ν) I) = 1 := by
  have hlength :
      (selectedDyadicFactors (mobiusLabelFactors ν) I).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    have hcard : I.card ≤ (mobiusLabelFactors ν).length := by
      simpa [Fintype.card_fin] using Finset.card_le_univ I
    exact hcard.trans (mobiusLabelFactorCount ν).2
  have hselected :
      dyadicFactorsMassWeight (selectedDyadicFactors (mobiusLabelFactors ν) I) =
        ∏ i ∈ I, dyadicFactorMassWeight ((mobiusLabelFactors ν).get i) := by
    simp [dyadicFactorsMassWeight, selectedDyadicFactors,
      List.map_map, Function.comp_def, Finset.prod_map_toList]
  have hfactor : ∀ i : Fin (mobiusLabelFactors ν).length,
      dyadicFactorMassWeight ((mobiusLabelFactors ν).get i) = 1 := by
    intro i
    cases hkind : (mobiusLabelFactors ν).get i with
    | one j => simp [dyadicFactorMassWeight]
    | mobius j => simp [dyadicFactorMassWeight]
    | logarithm j =>
        have hmem : DyadicArithmeticFactor.logarithm j ∈
            mobiusLabelFactors ν := by
          rw [← hkind]
          exact List.get_mem (mobiusLabelFactors ν) i
        simp [mobiusLabelFactors] at hmem
  rw [hselected]
  refine ⟨hlength, ?_⟩
  exact Finset.prod_eq_one fun i hi => hfactor i

/-- For one retained triple of source windows, the fixed-witness MUF block
estimate feeds the exact allocated-scale `ldm:uncapped` geometry for every
divisor tuple. The finite window product is then transferred, without a
coefficient or endpoint change, to the source-normalized character/allocation
integral. The geometry and three quotient-scale identities are explicit so
that an outer active-window argument can construct them from the same source
block witness. -/
theorem selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_from_MUF
    {X Y U eps a Tfreq z : ℝ} (hXsrc : 3 ≤ X)
    (c : ℂ) (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (rchar : ℤ) (hrchar : IsCoprime rchar (Q : ℤ))
    (γ η η' : ℝ) (j k l : ℕ)
    (N₁ N₂ N₃ : ℝ)
    (geometry : ∀ r : divisorFactorTuples 3 d,
      SelectedMobiusPTWAllocatedGeometry eps Y U)
    (hN₁eq : N₁ = (2 : ℝ) ^ j *
      (X ^ γ / (4 * decompositionC)))
    (hN₂eq : N₂ = (2 : ℝ) ^ k *
      (X ^ η / (4 * decompositionC)))
    (hN₃eq : N₃ = (2 : ℝ) ^ l *
      (X ^ η' / (4 * decompositionC)))
    (hM₁ : ∀ r, (geometry r).uncapped.M =
      N₁ / ((r.1 0).1 : ℝ))
    (hM₂ : ∀ r, (geometry r).M₂ = N₂ / ((r.1 1).1 : ℝ))
    (hM₃ : ∀ r, (geometry r).M₃ = N₃ / ((r.1 2).1 : ℝ))
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 < N₃)
    (hY : (2 : ℝ) ^ 16 ≤ Y)
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : fs₁.length ≤ 20) (hlen₂ : fs₂.length ≤ 20)
    (hlen₃ : fs₃.length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight fs₁ ≤ Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight fs₂ ≤ Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight fs₃ ≤ Real.log (8 * X))
    (hδ0 : 0 < (Real.log X) ^ (-20 * a))
    (hδ : (Real.log X) ^ (-20 * a) ≤ 1)
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ))) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) c fs₁ fs₂ fs₃ r χ Tfreq γ η η'
                j k l t‖ ∂volume) ≤
      (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          ((selectedPTWFactorScale X d *
              selectedPTWFactorScale X d * selectedPTWFactorScale X d) *
            selectedDyadicPTWUncappedKernel X Y a eps) := by
  classical
  let G : ∀ r : divisorFactorTuples 3 d,
      SelectedPTWAllocationGeometry eps Y U := fun r => (geometry r).uncapped
  have hblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (s : ℝ),
      (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
      ‖∑ n ∈ factorExtractionRealInterval
          (G r).M (2 * (G r).M),
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
            ((r.1 0).1 * n) *
          factorExtractionMellinWeight
            (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (G r).M := by
    intro r χ s hslo hshi
    have hsum :
        (∑ n ∈ factorExtractionRealInterval
            (G r).M (2 * (G r).M),
          toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n) =
          ∑ n ∈ factorExtractionRealInterval
            (N₁ / ((r.1 0).1 : ℝ))
            (2 * N₁ / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n := by
      have hinterval :
          factorExtractionRealInterval (G r).M (2 * (G r).M) =
            factorExtractionRealInterval
              (N₁ / ((r.1 0).1 : ℝ))
              (2 * N₁ / ((r.1 0).1 : ℝ)) := by
        rw [show (G r).M = N₁ / ((r.1 0).1 : ℝ) by exact hM₁ r]
        congr 1
        ring
      rw [hinterval]
    rw [hsum]
    have h := hMUFblock r χ N₁ hN₁ s hslo hshi
    have hsqrt :
        Real.sqrt (N₁ / ((r.1 0).1 : ℝ)) = Real.sqrt (G r).M := by
      rw [← hM₁ r]
    simpa [hsqrt] using h
  have hsource := selectedDyadicPTWCharacterAllocationIntegral_bound
    hd hQ rchar hrchar X z Y U a eps Tfreq c fs₁ fs₂ fs₃
    hXsrc hY hc hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃
    hδ0 hδ G hfreq hblock
  have hwindowEq : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c fs₁ fs₂ fs₃ r χ Tfreq γ η η' j k l t =
        selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
          (G r).alpha (G r).beta (G r).gamma Tfreq r χ t := by
    intro r χ t
    let M₁ : ℝ := (2 : ℝ) ^ j *
      (X ^ γ / (4 * decompositionC * ((r.1 0).1 : ℝ)))
    let M₂ : ℝ := (2 : ℝ) ^ k *
      (X ^ η / (4 * decompositionC * ((r.1 1).1 : ℝ)))
    let M₃ : ℝ := (2 : ℝ) ^ l *
      (X ^ η' / (4 * decompositionC * ((r.1 2).1 : ℝ)))
    have hM₁pow : M₁ = Y ^ (G r).alpha := by
      calc
        M₁ = N₁ / ((r.1 0).1 : ℝ) := by
          dsimp [M₁]
          rw [hN₁eq]
          ring
        _ = (geometry r).uncapped.M := (hM₁ r).symm
        _ = Y ^ (G r).alpha := (G r).hMpow
    have hM₂pow : M₂ = Y ^ (G r).beta := by
      calc
        M₂ = N₂ / ((r.1 1).1 : ℝ) := by
          dsimp [M₂]
          rw [hN₂eq]
          ring
        _ = (geometry r).M₂ := (hM₂ r).symm
        _ = Y ^ (G r).beta := (geometry r).hM₂
    have hM₃pow : M₃ = Y ^ (G r).gamma := by
      calc
        M₃ = N₃ / ((r.1 2).1 : ℝ) := by
          dsimp [M₃]
          rw [hN₃eq]
          ring
        _ = (geometry r).M₃ := (hM₃ r).symm
        _ = Y ^ (G r).gamma := (geometry r).hM₃
    have hXpos : 0 < X := by linarith
    have hCpos : 0 < decompositionC := by
      unfold decompositionC
      positivity
    have hr₁pos : 0 < ((r.1 0).1 : ℝ) := by
      exact_mod_cast (r.1 0).2
    have hr₂pos : 0 < ((r.1 1).1 : ℝ) := by
      exact_mod_cast (r.1 1).2
    have hr₃pos : 0 < ((r.1 2).1 : ℝ) := by
      exact_mod_cast (r.1 2).2
    have hM₁pos : 0 < M₁ := by
      dsimp [M₁]
      exact mul_pos (by positivity)
        (div_pos (Real.rpow_pos_of_pos hXpos γ) (by positivity))
    have hM₂pos : 0 < M₂ := by
      dsimp [M₂]
      exact mul_pos (by positivity)
        (div_pos (Real.rpow_pos_of_pos hXpos η) (by positivity))
    have hM₃pos : 0 < M₃ := by
      dsimp [M₃]
      exact mul_pos (by positivity)
        (div_pos (Real.rpow_pos_of_pos hXpos η') (by positivity))
    have hB₁ : 0 < selectedPTWFactorScale X (r.1 0).1 := by
      have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
        (r.1 0).2
      have hdiv : 1 ≤ (divisorCoefficient 2 (r.1 0).1 : ℝ) := by
        exact_mod_cast hdivNat
      have hlog : 0 < Real.log (8 * X) :=
        lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
      unfold selectedPTWFactorScale
      positivity
    have hB₂ : 0 < selectedPTWFactorScale X (r.1 1).1 := by
      have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
        (r.1 1).2
      have hdiv : 1 ≤ (divisorCoefficient 2 (r.1 1).1 : ℝ) := by
        exact_mod_cast hdivNat
      have hlog : 0 < Real.log (8 * X) :=
        lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
      unfold selectedPTWFactorScale
      positivity
    have hB₃ : 0 < selectedPTWFactorScale X (r.1 2).1 := by
      have hdivNat := selectedMobiusPTWFixed_divisorCoefficient_two_ge_one
        (r.1 2).2
      have hdiv : 1 ≤ (divisorCoefficient 2 (r.1 2).1 : ℝ) := by
        exact_mod_cast hdivNat
      have hlog : 0 < Real.log (8 * X) :=
        lt_trans (by norm_num) (log_eightX_gt_one hXsrc)
      unfold selectedPTWFactorScale
      positivity
    have hterm := selectedMobiusPTW_allocatedWindowProduct_eq_sourceTerm
      (q := q) (z := z) (c := c) fs₁ fs₂ fs₃ r χ
      (alpha := (G r).alpha) (beta := (G r).beta) (gamma := (G r).gamma)
      (T := Tfreq) (t := t) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)
      hM₁pow hM₂pow hM₃pow hM₁pos hM₂pos hM₃pos hB₁ hB₂ hB₃
    simpa [selectedMobiusPTWActualAllocatedWindowTerm,
      selectedMobiusPTWAllocatedWindowPolynomial, M₁, M₂, M₃, G] using hterm
  have hsumEq (t : ℝ) :
      (∑ r : divisorFactorTuples 3 d,
        ∑ χ : BlueprintCharacter Q,
          star (evalInt χ rchar) *
            selectedMobiusPTWActualAllocatedWindowTerm
              (z := z) (q := q) c fs₁ fs₂ fs₃ r χ Tfreq γ η η' j k l t) =
       ∑ r : divisorFactorTuples 3 d,
        ∑ χ : BlueprintCharacter Q,
          star (evalInt χ rchar) *
            selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
              (G r).alpha (G r).beta (G r).gamma Tfreq r χ t := by
    simp_rw [hwindowEq]
  have hpoint (t : ℝ) :
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) c fs₁ fs₂ fs₃ r χ Tfreq γ η η' j k l t‖ =
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
                (G r).alpha (G r).beta (G r).gamma Tfreq r χ t‖ := by
    rw [hsumEq t]
  calc
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) c fs₁ fs₂ fs₃ r χ Tfreq γ η η' j k l t‖
        ∂volume) =
      ∫ t in Set.Icc (-U) U,
        ‖((d : ℂ) ^
            (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
            (Q.totient : ℂ)) *
          ∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              star (evalInt χ rchar) *
                selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
                  (G r).alpha (G r).beta (G r).gamma Tfreq r χ t‖
          ∂volume := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          ((selectedPTWFactorScale X d *
              selectedPTWFactorScale X d * selectedPTWFactorScale X d) *
            selectedDyadicPTWUncappedKernel X Y a eps) := hsource

/-- Retained source block scales construct the exact allocated quotient
geometry simultaneously for every ordered divisor tuple. The input
`hUsource` has the larger source-base range `X^(3/8-2eps)`; the explicit
allocated log-deviation premise supplies the margin needed for
`U ≤ Y^(3/8-eps)`. -/
def selectedMobiusPTW_actualAllocatedGeometry_of_retainedSourceScales
    {X Y U eps a : ℝ} {d Q q : ℕ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hU0 : 2 ≤ U)
    (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (γ η η' : ℝ) (hγsum : γ + η + η' = 1)
    (hγlo : 1 / 4 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hηlo : 0 ≤ η) (hη'lo : 0 ≤ η')
    (hgap : |η - η'| ≤ 1 / 4)
    (j k l : ℕ) (N₁ N₂ N₃ : ℝ)
    (hN₁eq : N₁ = (2 : ℝ) ^ j *
      (X ^ γ / (4 * decompositionC)))
    (hN₂eq : N₂ = (2 : ℝ) ^ k *
      (X ^ η / (4 * decompositionC)))
    (hN₃eq : N₃ = (2 : ℝ) ^ l *
      (X ^ η' / (4 * decompositionC)))
    (hN₁lower : (2 * decompositionC)⁻¹ * X ^ γ ≤ N₁)
    (hN₁upper : N₁ ≤ (2 * decompositionC) * X ^ γ)
    (hN₂lower : (2 * decompositionC)⁻¹ * X ^ η ≤ N₂)
    (hN₂upper : N₂ ≤ (2 * decompositionC) * X ^ η)
    (hN₃lower : (2 * decompositionC)⁻¹ * X ^ η' ≤ N₃)
    (hN₃upper : N₃ ≤ (2 * decompositionC) * X ^ η')
    (hYsource : Y = (N₁ * N₂ * N₃) / (d : ℝ))
    (hE : 3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X) ≤ Real.log X / 2)
    (hdev : 2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300)
    (hYlarge : (2 : ℝ) ^ 16 ≤ Y) :
    ∀ r : divisorFactorTuples 3 d,
      SelectedMobiusPTWAllocatedGeometry eps Y U := by
  classical
  intro r
  let r₁ : ℝ := (r.1 0).1
  let r₂ : ℝ := (r.1 1).1
  let r₃ : ℝ := (r.1 2).1
  let M₁ : ℝ := N₁ / r₁
  let M₂ : ℝ := N₂ / r₂
  let M₃ : ℝ := N₃ / r₃
  have hXpos : 0 < X := by
    have hbase : 0 < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans
      (by
        have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
        exact h3.trans hXlarge)
  have hCge : 1 ≤ decompositionC := by
    change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hC0 : 1 ≤ 2 * decompositionC := by nlinarith
  have hQoneNat : 1 ≤ Q := Nat.succ_le_iff.mpr hQ
  have hQone : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQoneNat
  have hqfactReal : (d : ℝ) * (Q : ℝ) = (q : ℝ) := by
    exact_mod_cast hqfactor
  have hdleq : (d : ℝ) ≤ (q : ℝ) := by
    rw [← hqfactReal]
    have hdNonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith [hdNonneg]
  have hdbound : (d : ℝ) ≤ (Real.log X) ^ a := hdleq.trans hqlog
  have hd1Nat : 1 ≤ d := Nat.succ_le_iff.mpr hd
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd1Nat
  have hr₁Nat : 0 < (r.1 0).1 := (r.1 0).2
  have hr₂Nat : 0 < (r.1 1).1 := (r.1 1).2
  have hr₃Nat : 0 < (r.1 2).1 := (r.1 2).2
  have hr₁ : 0 < r₁ := by dsimp [r₁]; exact_mod_cast hr₁Nat
  have hr₂ : 0 < r₂ := by dsimp [r₂]; exact_mod_cast hr₂Nat
  have hr₃ : 0 < r₃ := by dsimp [r₃]; exact_mod_cast hr₃Nat
  have hr₁oneNat : 1 ≤ (r.1 0).1 := Nat.succ_le_iff.mpr hr₁Nat
  have hr₂oneNat : 1 ≤ (r.1 1).1 := Nat.succ_le_iff.mpr hr₂Nat
  have hr₃oneNat : 1 ≤ (r.1 2).1 := Nat.succ_le_iff.mpr hr₃Nat
  have hr₁one : 1 ≤ r₁ := by dsimp [r₁]; exact_mod_cast hr₁oneNat
  have hr₂one : 1 ≤ r₂ := by dsimp [r₂]; exact_mod_cast hr₂oneNat
  have hr₃one : 1 ≤ r₃ := by dsimp [r₃]; exact_mod_cast hr₃oneNat
  have hdiv₁ : (r.1 0).1 ∣ d := by
    calc
      (r.1 0).1 ∣ ∏ i : Fin 3, (r.1 i).1 :=
        Finset.dvd_prod_of_mem (fun i : Fin 3 => (r.1 i).1)
          (Finset.mem_univ 0)
      _ = d := r.2
  have hdiv₂ : (r.1 1).1 ∣ d := by
    calc
      (r.1 1).1 ∣ ∏ i : Fin 3, (r.1 i).1 :=
        Finset.dvd_prod_of_mem (fun i : Fin 3 => (r.1 i).1)
          (Finset.mem_univ 1)
      _ = d := r.2
  have hdiv₃ : (r.1 2).1 ∣ d := by
    calc
      (r.1 2).1 ∣ ∏ i : Fin 3, (r.1 i).1 :=
        Finset.dvd_prod_of_mem (fun i : Fin 3 => (r.1 i).1)
          (Finset.mem_univ 2)
      _ = d := r.2
  have hr₁dNat : (r.1 0).1 ≤ d := Nat.le_of_dvd hd hdiv₁
  have hr₂dNat : (r.1 1).1 ≤ d := Nat.le_of_dvd hd hdiv₂
  have hr₃dNat : (r.1 2).1 ≤ d := Nat.le_of_dvd hd hdiv₃
  have hr₁d : r₁ ≤ (d : ℝ) := by dsimp [r₁]; exact_mod_cast hr₁dNat
  have hr₂d : r₂ ≤ (d : ℝ) := by dsimp [r₂]; exact_mod_cast hr₂dNat
  have hr₃d : r₃ ≤ (d : ℝ) := by dsimp [r₃]; exact_mod_cast hr₃dNat
  have hallocNat : (r.1 0).1 * (r.1 1).1 * (r.1 2).1 = d := by
    simpa [Fin.prod_univ_succ, mul_assoc] using r.2
  have halloc : r₁ * r₂ * r₃ = (d : ℝ) := by
    dsimp [r₁, r₂, r₃]
    exact_mod_cast hallocNat
  have hN₁pos : 0 < N₁ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hC0))
        (Real.rpow_pos_of_pos hXpos γ)) hN₁lower
  have hN₂pos : 0 < N₂ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hC0))
        (Real.rpow_pos_of_pos hXpos η)) hN₂lower
  have hN₃pos : 0 < N₃ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hC0))
        (Real.rpow_pos_of_pos hXpos η')) hN₃lower
  have hM₁ : M₁ = N₁ / r₁ := rfl
  have hM₂ : M₂ = N₂ / r₂ := rfl
  have hM₃ : M₃ = N₃ / r₃ := rfl
  have hYprod : Y = M₁ * M₂ * M₃ := by
    have hquotient : M₁ * M₂ * M₃ = (N₁ * N₂ * N₃) / (d : ℝ) :=
      selectedMobiusPTW_quotient_length_product
      hN₁pos hN₂pos hN₃pos hr₁ hr₂ hr₃ (by exact_mod_cast hd)
      halloc hM₁ hM₂ hM₃ rfl
    exact hYsource.trans hquotient.symm
  have hlogGeom := selectedMobiusPTW_allocated_length_log_geometry
    (X := X) (C₀ := 2 * decompositionC) (ℓ := Real.log X)
    (a := a) (γ₁ := γ) (γ₂ := η) (γ₃ := η')
    (N₁ := N₁) (N₂ := N₂) (N₃ := N₃)
    (r₁ := r₁) (r₂ := r₂) (r₃ := r₃) (d := (d : ℝ))
    (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (Y := Y)
    hXone rfl hlogXone ha hC0 hγsum
    hN₁lower hN₁upper hN₂lower hN₂upper hN₃lower hN₃upper
    hr₁ hr₂ hr₃ hr₁one hr₂one hr₃one hd1 halloc hr₁d hr₂d hr₃d
    hdbound (le_trans (by norm_num) hγlo) hηlo hη'lo
    hM₁ hM₂ hM₃ hYprod hE
  have hYone : 1 < Y := by
    have hXhalf : 1 < X ^ (1 / 2 : ℝ) := by
      exact Real.one_lt_rpow hXone (by norm_num)
    exact lt_of_lt_of_le hXhalf hlogGeom.2.1
  have hlogYpos : 0 < Real.log Y := Real.log_pos hYone
  have hEbound :
      3 * Real.log (2 * decompositionC) +
          a * Real.log (Real.log X) ≤ eps / 600 * Real.log Y := by
    have hmul := (div_le_iff₀ hlogYpos).mp hdev
    calc
      _ = (2 * (3 * Real.log (2 * decompositionC) +
          a * Real.log (Real.log X))) / 2 := by ring
      _ ≤ (eps / 300 * Real.log Y) / 2 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = eps / 600 * Real.log Y := by ring
  have hlogXle : Real.log X ≤ (1 + eps / 600) * Real.log Y := by
    have hdiff := abs_le.mp hlogGeom.2.2.1
    have hEupper : Real.log X ≤ Real.log Y +
        (3 * Real.log (2 * decompositionC) +
          a * Real.log (Real.log X)) := by linarith
    calc
      Real.log X ≤ Real.log Y +
          (3 * Real.log (2 * decompositionC) +
            a * Real.log (Real.log X)) := hEupper
      _ ≤ Real.log Y + eps / 600 * Real.log Y :=
        add_le_add le_rfl hEbound
      _ = (1 + eps / 600) * Real.log Y := by ring
  have hexpCoeff :
      (3 / 8 - 2 * eps) * (1 + eps / 600) ≤ 3 / 8 - eps := by
    have hple : 3 / 8 - 2 * eps ≤ 600 := by
      have hple' : 3 / 8 - 2 * eps ≤ 3 / 8 := by linarith [heps0.le]
      exact hple'.trans (by norm_num)
    have hpe := mul_le_mul_of_nonneg_right hple (le_of_lt heps0)
    calc
      (3 / 8 - 2 * eps) * (1 + eps / 600) =
          (3 / 8 - 2 * eps) +
            (3 / 8 - 2 * eps) * eps / 600 := by ring
      _ ≤ (3 / 8 - 2 * eps) + eps := by
        have hsmall : (3 / 8 - 2 * eps) * eps / 600 ≤ eps := by
          exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 600)).2 (by nlinarith [hpe])
        simpa [add_comm] using add_le_add_right hsmall (3 / 8 - 2 * eps)
      _ = 3 / 8 - eps := by ring
  have hexpLog :
      (3 / 8 - 2 * eps) * Real.log X ≤
        (3 / 8 - eps) * Real.log Y := by
    have hp0 : 0 ≤ 3 / 8 - 2 * eps := by nlinarith [heps]
    have hmid := mul_le_mul_of_nonneg_left hlogXle hp0
    have hcoefNonneg : 0 ≤ Real.log Y := le_of_lt hlogYpos
    calc
      (3 / 8 - 2 * eps) * Real.log X ≤
          (3 / 8 - 2 * eps) * ((1 + eps / 600) * Real.log Y) := hmid
      _ = ((3 / 8 - 2 * eps) * (1 + eps / 600)) * Real.log Y := by ring
      _ ≤ (3 / 8 - eps) * Real.log Y :=
        mul_le_mul_of_nonneg_right hexpCoeff hcoefNonneg
  have hpowSource : X ^ (3 / 8 - 2 * eps) ≤
      Y ^ (3 / 8 - eps) := by
    rw [Real.rpow_def_of_pos hXpos, Real.rpow_def_of_pos
      (lt_trans (by norm_num) hYone)]
    simpa [mul_comm] using Real.exp_le_exp.mpr hexpLog
  have hU : U ≤ Y ^ (3 / 8 - eps) := hUsource.trans hpowSource
  let alpha : ℝ := Real.log M₁ / Real.log Y
  let beta : ℝ := Real.log M₂ / Real.log Y
  let gamma : ℝ := Real.log M₃ / Real.log Y
  have hM₁pos : 0 < M₁ := by rw [hM₁]; exact div_pos hN₁pos hr₁
  have hM₂pos : 0 < M₂ := by rw [hM₂]; exact div_pos hN₂pos hr₂
  have hM₃pos : 0 < M₃ := by rw [hM₃]; exact div_pos hN₃pos hr₃
  have hαdev : |alpha - γ| ≤ eps / 300 := by
    dsimp [alpha]
    exact hlogGeom.2.2.2.2.1.trans hdev
  have hβdev : |beta - η| ≤ eps / 300 := by
    dsimp [beta]
    exact hlogGeom.2.2.2.2.2.1.trans hdev
  have hγdev : |gamma - η'| ≤ eps / 300 := by
    dsimp [gamma]
    exact hlogGeom.2.2.2.2.2.2.trans hdev
  have hηlower : 1 / 8 ≤ η := by
    have hgap' := abs_le.mp hgap
    have hsumEta : (1 / 2 : ℝ) ≤ η + η' := by linarith [hγsum, hγhi]
    nlinarith [hsumEta, hgap'.1]
  have hη'lower : 1 / 8 ≤ η' := by
    have hgap' := abs_le.mp hgap
    have hsumEta : (1 / 2 : ℝ) ≤ η + η' := by linarith [hγsum, hγhi]
    nlinarith [hsumEta, hgap'.2]
  have hepssmall : eps / 300 ≤ 1 / 8 := by nlinarith [heps]
  have hα0 : 0 ≤ alpha := by
    have hdev' := abs_le.mp hαdev
    linarith [hγlo]
  have hβ0 : 0 ≤ beta := by
    have hdev' := abs_le.mp hβdev
    linarith [hηlower]
  have hγ0 : 0 ≤ gamma := by
    have hdev' := abs_le.mp hγdev
    linarith [hη'lower]
  have hαlow : 1 / 4 - eps / 100 ≤ alpha := by
    have hdev' := abs_le.mp hαdev
    linarith [hγlo, heps0]
  have hαhigh : alpha ≤ 1 / 2 + eps / 100 := by
    have hdev' := abs_le.mp hαdev
    linarith [hγhi, heps0]
  have hβγ : |beta - gamma| ≤ 1 / 4 + eps / 100 := by
    have hβ' := abs_le.mp hβdev
    have hγ' := abs_le.mp hγdev
    have hgap' := abs_le.mp hgap
    rw [abs_le]
    constructor <;> linarith [heps0]
  have hsum' : alpha + beta + gamma = 1 := by
    dsimp [alpha, beta, gamma]
    exact hlogGeom.2.2.2.1
  have hM₁pow : M₁ = Y ^ alpha := by
    dsimp [alpha]
    exact (selectedMobiusPTW_length_eq_rpow_log hYone hM₁pos).symm
  have hM₂pow : M₂ = Y ^ beta := by
    dsimp [beta]
    exact (selectedMobiusPTW_length_eq_rpow_log hYone hM₂pos).symm
  have hM₃pow : M₃ = Y ^ gamma := by
    dsimp [gamma]
    exact (selectedMobiusPTW_length_eq_rpow_log hYone hM₃pos).symm
  refine ⟨?_, M₂, M₃, ?_, ?_⟩
  · exact ⟨alpha, beta, gamma, M₁, hM₁pos, hM₁pow,
      heps0, heps, hU0, hU, hα0, hβ0, hγ0, hsum', hαlow, hαhigh, hβγ⟩
  · simpa [beta] using hM₂pow
  · simpa [gamma] using hM₃pow

/-- A live source triple window supplies the retained scales needed to
reparameterize every divisor allocation by its actual quotient length. This
is the allocated-base block estimate with the same selected source groups and
the exact `d^{-1/2} d₃(d)` normalization. The source log-deviation and lower
quotient threshold remain explicit. -/
theorem selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_of_live
    {X U eps a Tfreq z : ℝ} {d Q q : ℕ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hU0 : 2 ≤ U) (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (rchar : ℤ) (hrchar : IsCoprime rchar (Q : ℤ))
    (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (γ η η' : ℝ) (j k l : ℕ)
    (hγsum : γ + η + η' = 1)
    (hγlo : 1 / 4 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hηlo : 0 ≤ η) (hη'lo : 0 ≤ η')
    (hgap : |η - η'| ≤ 1 / 4)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hE : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2)
    (hdev : ∀ Y : ℝ, Y =
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) →
      2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300)
    (hYlarge : (2 : ℝ) ^ 16 ≤
      (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
        ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
        ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ))
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : (selectedDyadicFactors fs I).length ≤ 20)
    (hlen₂ : (selectedDyadicFactors fs J).length ≤ 20)
    (hlen₃ : (selectedDyadicFactors fs J').length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight (selectedDyadicFactors fs I) ≤
      Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight (selectedDyadicFactors fs J) ≤
      Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight (selectedDyadicFactors fs J') ≤
      Real.log (8 * X))
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor z c (selectedDyadicFactors fs I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)))
    (hLive : ∃ (r : divisorFactorTuples 3 d)
        (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c
        (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
        (selectedDyadicFactors fs J') r χ Tfreq γ η η' j k l t ≠ 0) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ Tfreq γ η η' j k l t‖
        ∂volume) ≤
      (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          ((selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            selectedDyadicPTWUncappedKernel X
              ((((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
                ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
                ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ))
              a eps) := by
  classical
  let fs₁ := selectedDyadicFactors fs I
  let fs₂ := selectedDyadicFactors fs J
  let fs₃ := selectedDyadicFactors fs J'
  let N₁ : ℝ := ((2 : ℝ) ^ j * X ^ γ) / (4 * decompositionC)
  let N₂ : ℝ := ((2 : ℝ) ^ k * X ^ η) / (4 * decompositionC)
  let N₃ : ℝ := ((2 : ℝ) ^ l * X ^ η') / (4 * decompositionC)
  let Y : ℝ := (N₁ * N₂ * N₃) / (d : ℝ)
  obtain ⟨r₀, χ₀, t₀, hLive₀⟩ := hLive
  have hXpos : 0 < X := by
    exact lt_of_lt_of_le (by positivity) hXlarge
  have hret := selectedMobiusPTW_actualAllocatedCell_retainedScales_of_live
    hXpos c fs fs fs I J J' γ η η' hSupport₁ hSupport₂ hSupport₃ r₀ χ₀
    Tfreq j k l t₀ hLive₀
  rcases hret with ⟨hN₁lower', hN₁upper', hN₂lower', hN₂upper',
    hN₃lower', hN₃upper'⟩
  have hCpos : 0 < decompositionC := by
    unfold decompositionC
    positivity
  have hN₁lower : (2 * decompositionC)⁻¹ * X ^ γ ≤ N₁ := by
    have heq : (2 * decompositionC)⁻¹ * X ^ γ =
        X ^ γ / (2 * decompositionC) := by
      rw [div_eq_mul_inv]
      ring
    calc
      (2 * decompositionC)⁻¹ * X ^ γ = X ^ γ / (2 * decompositionC) := heq
      _ ≤ ((2 : ℝ) ^ j * X ^ γ) / (4 * decompositionC) := hN₁lower'
      _ = N₁ := rfl
  have hN₁upper : N₁ ≤ (2 * decompositionC) * X ^ γ := by
    simpa [N₁] using hN₁upper'
  have hN₂lower : (2 * decompositionC)⁻¹ * X ^ η ≤ N₂ := by
    have heq : (2 * decompositionC)⁻¹ * X ^ η =
        X ^ η / (2 * decompositionC) := by
      rw [div_eq_mul_inv]
      ring
    calc
      (2 * decompositionC)⁻¹ * X ^ η = X ^ η / (2 * decompositionC) := heq
      _ ≤ ((2 : ℝ) ^ k * X ^ η) / (4 * decompositionC) := hN₂lower'
      _ = N₂ := rfl
  have hN₂upper : N₂ ≤ (2 * decompositionC) * X ^ η := by
    simpa [N₂] using hN₂upper'
  have hN₃lower : (2 * decompositionC)⁻¹ * X ^ η' ≤ N₃ := by
    have heq : (2 * decompositionC)⁻¹ * X ^ η' =
        X ^ η' / (2 * decompositionC) := by
      rw [div_eq_mul_inv]
      ring
    calc
      (2 * decompositionC)⁻¹ * X ^ η' = X ^ η' / (2 * decompositionC) := heq
      _ ≤ ((2 : ℝ) ^ l * X ^ η') / (4 * decompositionC) := hN₃lower'
      _ = N₃ := rfl
  have hN₃upper : N₃ ≤ (2 * decompositionC) * X ^ η' := by
    simpa [N₃] using hN₃upper'
  have hN₁eq : N₁ = (2 : ℝ) ^ j *
      (X ^ γ / (4 * decompositionC)) := by
    dsimp [N₁]
    have hd : (4 : ℝ) * decompositionC ≠ 0 :=
      ne_of_gt (by positivity)
    field_simp [hd]
  have hN₂eq : N₂ = (2 : ℝ) ^ k *
      (X ^ η / (4 * decompositionC)) := by
    dsimp [N₂]
    have hd : (4 : ℝ) * decompositionC ≠ 0 :=
      ne_of_gt (by positivity)
    field_simp [hd]
  have hN₃eq : N₃ = (2 : ℝ) ^ l *
      (X ^ η' / (4 * decompositionC)) := by
    dsimp [N₃]
    have hd : (4 : ℝ) * decompositionC ≠ 0 :=
      ne_of_gt (by positivity)
    field_simp [hd]
  have hYblocks : Y =
      (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
        ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
        ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) := by
    dsimp [Y]
    rw [hN₁eq, hN₂eq, hN₃eq]
  have hYsource : Y = (N₁ * N₂ * N₃) / (d : ℝ) := rfl
  have hYlarge' : (2 : ℝ) ^ 16 ≤ Y := by
    calc
      (2 : ℝ) ^ 16 ≤
          (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
            ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
            ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) := hYlarge
      _ = Y := hYblocks.symm
  have hdev' : 2 * (3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300 := by
    exact hdev Y hYblocks
  let hgeometry : ∀ r : divisorFactorTuples 3 d,
      SelectedMobiusPTWAllocatedGeometry eps Y U :=
    selectedMobiusPTW_actualAllocatedGeometry_of_retainedSourceScales
    hXlarge ha heps0 heps hU0 hUsource hd hQ hqfactor hqlog γ η η'
    hγsum hγlo hγhi hηlo hη'lo hgap j k l N₁ N₂ N₃
    hN₁eq hN₂eq hN₃eq hN₁lower hN₁upper hN₂lower hN₂upper
    hN₃lower hN₃upper hYsource hE hdev' hYlarge'
  have hM₁ : ∀ r : divisorFactorTuples 3 d,
      (hgeometry r).uncapped.M = N₁ / ((r.1 0).1 : ℝ) := by
    intro r
    rfl
  have hM₂ : ∀ r : divisorFactorTuples 3 d,
      (hgeometry r).M₂ = N₂ / ((r.1 1).1 : ℝ) := by
    intro r
    rfl
  have hM₃ : ∀ r : divisorFactorTuples 3 d,
      (hgeometry r).M₃ = N₃ / ((r.1 2).1 : ℝ) := by
    intro r
    rfl
  have hlogXone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans
      (by
        have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
        exact h3.trans hXlarge)
  have hlogXpos : 0 < Real.log X := lt_of_lt_of_le (by norm_num) hlogXone
  have hδ0 : 0 < (Real.log X) ^ (-20 * a) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hδ : (Real.log X) ^ (-20 * a) ≤ 1 := by
    have hpow : 1 ≤ (Real.log X) ^ (20 * a) :=
      Real.one_le_rpow hlogXone (by positivity)
    rw [show -20 * a = -(20 * a) by ring, Real.rpow_neg hlogXpos.le]
    exact inv_le_one_of_one_le₀ hpow
  have hN₁pos : 0 < N₁ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hCpos))
        (Real.rpow_pos_of_pos hXpos γ)) hN₁lower
  have hN₂pos : 0 < N₂ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hCpos))
        (Real.rpow_pos_of_pos hXpos η)) hN₂lower
  have hN₃pos : 0 < N₃ := by
    exact lt_of_lt_of_le
      (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hCpos))
        (Real.rpow_pos_of_pos hXpos η')) hN₃lower
  have hsource := selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_from_MUF
    (by
      have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
      exact h3.trans hXlarge)
    c fs₁ fs₂ fs₃ hd hQ hqfactor rchar hrchar γ η η' j k l
    N₁ N₂ N₃ hgeometry hN₁eq hN₂eq hN₃eq hM₁ hM₂ hM₃
    hN₁pos hN₂pos hN₃pos hYlarge' hc hlen₁ hlen₂ hlen₃
    hweight₁ hweight₂ hweight₃ hδ0 hδ hfreq hMUFblock
  rw [hYblocks] at hsource
  simpa only [fs₁, fs₂, fs₃] using hsource

/-- The fixed-witness allocation identity is exactly the pointwise finite
triple-block decomposition of the weighted source sum. The same source
groups, exponents, and block indices are retained in every summand. -/
theorem selectedMobiusPTW_actualWeightedSource_eq_tripleBlockSum
    {X z c : ℝ} {d Q q : ℕ}
    (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (rchar : ℤ) (scalar : ℝ → ℂ)
    (T γ η η' : ℝ)
    (hExpansion : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := z) (c := c) fs r χ T t γ η η' I J J')
    (t : ℝ) :
    scalar t *
      (∑ r : divisorFactorTuples 3 d,
        ∑ χ : BlueprintCharacter Q,
          star (evalInt χ rchar) *
            selectedMobiusPTWActualCommonCutoffTerm
              (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J') =
      ∑ j ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
        ∑ k ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
          ∑ l ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
            ∑ r : divisorFactorTuples 3 d,
              ∑ χ : BlueprintCharacter Q,
                scalar t * (star (evalInt χ rchar) *
                  selectedMobiusPTWActualAllocatedWindowTerm
                    (z := z) (q := q) (c : ℂ)
                    (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                    (selectedDyadicFactors fs J') r χ T γ η η' j k l t) := by
  classical
  let G : divisorFactorTuples 3 d → BlueprintCharacter Q → ℝ → ℂ :=
    fun r χ s => selectedMobiusPTWActualCommonCutoffTerm
      (z := z) (c := c) fs (q := q) r χ T s γ η η' I J J'
  let F : ℕ → ℕ → ℕ → divisorFactorTuples 3 d →
      BlueprintCharacter Q → ℝ → ℂ := fun j k l r χ s =>
    selectedMobiusPTWActualAllocatedWindowTerm
      (z := z) (q := q) (c : ℂ)
      (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
      (selectedDyadicFactors fs J') r χ T γ η η' j k l s
  have hdecomp : ∀ r χ s,
      G r χ s =
        ∑ j ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
          ∑ k ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
            ∑ l ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
              F j k l r χ s := by
    intro r χ s
    simpa [G, F, selectedMobiusPTWActualCommonCutoffTerm,
      selectedMobiusPTWActualAllocatedWindowTerm,
      selectedMobiusPTWActualAllocationExpansionAt,
      selectedMobiusPTWCommonCutoffPolynomial] using hExpansion r χ s
  simpa [G, F] using
    weightedAllocationSource_eq_tripleDyadicBlockSum
      (R := divisorFactorTuples 3 d) (Q := Q)
      (selectedMobiusPTWDyadicBlockCount decompositionC)
      (selectedMobiusPTWDyadicBlockCount decompositionC)
      (selectedMobiusPTWDyadicBlockCount decompositionC)
      scalar (fun r χ => star (evalInt χ rchar)) G F hdecomp t

/-- Integrating the exact selected-Möbius common-cutoff source sum and using
the checked finite triple-block transfer costs exactly `J₀³`, where
`J₀=selectedMobiusPTWDyadicBlockCount decompositionC`. The per-cell bound is
left as the allocated-base estimate, so its `d₃(d)/d`, coefficient-scale,
and quotient-kernel factors remain explicit. -/
theorem selectedMobiusPTW_actualSourceIntegral_le_of_tripleBlockBounds
    {X z c U K : ℝ} {d Q q : ℕ}
    (hd : 0 < d) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (rchar : ℤ) (scalar : ℝ → ℂ)
    (T γ η η' : ℝ)
    (hExpansion : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := z) (c := c) fs r χ T t γ η η' I J J')
    (hcont : ∀ j k l,
      Continuous (fun t : ℝ =>
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            scalar t * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c : ℂ)
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ T γ η η' j k l t)))
    (hblock : ∀ j ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ k ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ l ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              scalar t * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) (c : ℂ)
                  (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                  (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) ≤ K)
    (hK : 0 ≤ K) :
    (∫ t in Set.Icc (-U) U,
      ‖scalar t *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J')‖
      ∂volume) ≤
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 * K := by
  classical
  let G : divisorFactorTuples 3 d → BlueprintCharacter Q → ℝ → ℂ :=
    fun r χ s => selectedMobiusPTWActualCommonCutoffTerm
      (z := z) (c := c) fs (q := q) r χ T s γ η η' I J J'
  let F : ℕ → ℕ → ℕ → divisorFactorTuples 3 d →
      BlueprintCharacter Q → ℝ → ℂ := fun j k l r χ s =>
    selectedMobiusPTWActualAllocatedWindowTerm
      (z := z) (q := q) (c : ℂ)
      (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
      (selectedDyadicFactors fs J') r χ T γ η η' j k l s
  have hdecomp : ∀ r χ s,
      G r χ s =
        ∑ j ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
          ∑ k ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
            ∑ l ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
              F j k l r χ s := by
    intro r χ s
    simpa [G, F, selectedMobiusPTWActualCommonCutoffTerm,
      selectedMobiusPTWActualAllocatedWindowTerm,
      selectedMobiusPTWActualAllocationExpansionAt,
      selectedMobiusPTWCommonCutoffPolynomial] using hExpansion r χ s
  exact integral_norm_weightedAllocationSource_le_of_count_bound
    (selectedMobiusPTWDyadicBlockCount decompositionC)
    (selectedMobiusPTWDyadicBlockCount decompositionC)
    (selectedMobiusPTWDyadicBlockCount decompositionC)
    (selectedMobiusPTWDyadicBlockCount decompositionC)
    U K scalar (fun r χ => star (evalInt χ rchar)) G F hdecomp hcont hblock
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hK

/-- The two source savings in the uncapped PTW kernel combine to the exact
`(log X)^(-5a/4)` factor once the allocated quotient's second term is below
that scale. The logarithm is compared on the source interval
`log(4Y) ≤ 2 log X`; constants and the complete logarithmic exponent are
retained. -/
theorem selectedDyadicPTWUncappedKernel_le_of_log_window
    {X Y a eps : ℝ}
    (hlogX : 0 < Real.log X)
    (hY : (2 : ℝ) ^ 16 ≤ Y)
    (hlog4Y : Real.log (4 * Y) ≤ 2 * Real.log X)
    (hYsave : Y ^ (-eps / 16 : ℝ) ≤
      (Real.log X) ^ (-5 * a / 4)) :
    selectedDyadicPTWUncappedKernel X Y a eps ≤
      2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
          Real.sqrt Y * (Real.log X) ^ (-5 * a / 4) := by
  have hYpos : 0 < Y := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 16 := by positivity
    exact lt_of_lt_of_le hbase hY
  have h4Yone : 1 < 4 * Y := by nlinarith
  have hlog4Ypos : 0 < Real.log (4 * Y) := Real.log_pos h4Yone
  have hlogXnonneg : 0 ≤ Real.log X := hlogX.le
  have hpowZ :
      (Real.log (4 * Y)) ^ (2 ^ 20 - 1) ≤
        (2 * Real.log X) ^ (2 ^ 20 - 1) :=
    pow_le_pow_left₀ hlog4Ypos.le hlog4Y (2 ^ 20 - 1)
  have hZ : Z 20 Y ≤
      (2 : ℝ) ^ (2 ^ 20 + 1) *
        (2 * Real.log X) ^ (2 ^ 20 - 1) := by
    rw [Z]
    exact mul_le_mul_of_nonneg_left hpowZ (by positivity)
  have hZnonneg : 0 ≤ Z 20 Y := by
    rw [Z]
    positivity
  have hZcube := pow_le_pow_left₀ hZnonneg hZ 3
  have hZcube' : Z 20 Y ^ 3 ≤
      (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
        (2 * Real.log X) ^ (3 * (2 ^ 20 - 1)) := by
    calc
      Z 20 Y ^ 3 ≤
          ((2 : ℝ) ^ (2 ^ 20 + 1) *
            (2 * Real.log X) ^ (2 ^ 20 - 1)) ^ 3 := hZcube
      _ = (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ (3 * (2 ^ 20 - 1)) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> omega
  have hlogpow :
      (Real.log (4 * Y)) ^ (b 20 + 3) ≤
        (2 * Real.log X) ^ (b 20 + 3) :=
    pow_le_pow_left₀ hlog4Ypos.le hlog4Y (b 20 + 3)
  have hdelta :
      ((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) =
        (Real.log X) ^ (-5 * a / 4 : ℝ) := by
    rw [← Real.rpow_mul hlogX.le (-20 * a) (1 / 16 : ℝ)]
    congr 1
    ring
  have hsave :
      ((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
          Y ^ (-eps / 16 : ℝ) ≤
        2 * (Real.log X) ^ (-5 * a / 4 : ℝ) := by
    rw [hdelta]
    calc
      (Real.log X) ^ (-5 * a / 4 : ℝ) +
          Y ^ (-eps / 16 : ℝ) ≤
        (Real.log X) ^ (-5 * a / 4 : ℝ) +
          (Real.log X) ^ (-5 * a / 4 : ℝ) :=
        add_le_add le_rfl hYsave
      _ = 2 * (Real.log X) ^ (-5 * a / 4 : ℝ) := by ring
  have hexp :
      3 * (2 ^ 20 - 1) + (b 20 + 3) = selectedMobiusPTWLogExponent := by
    unfold selectedMobiusPTWLogExponent
    omega
  have hlogProduct :
      Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) ≤
        (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
          (2 * Real.log X) ^ selectedMobiusPTWLogExponent := by
    calc
      Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3) ≤
          ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ (3 * (2 ^ 20 - 1))) *
              (Real.log (4 * Y)) ^ (b 20 + 3) :=
        mul_le_mul_of_nonneg_right hZcube' (by positivity)
      _ ≤ ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ (3 * (2 ^ 20 - 1))) *
              (2 * Real.log X) ^ (b 20 + 3) :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ = (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^
              (3 * (2 ^ 20 - 1) + (b 20 + 3)) := by
        rw [mul_assoc, ← pow_add]
      _ = _ := by rw [hexp]
  have hsaveTerm :
      0 ≤ ((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
        Y ^ (-eps / 16 : ℝ) := by positivity
  have hrootNonneg : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg _
  have hlogProdNonneg :
      0 ≤ (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
        (2 * Real.log X) ^ selectedMobiusPTWLogExponent := by positivity
  have hkernelProduct :
      (Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3)) *
          (Real.sqrt Y *
            (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ))) ≤
        ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent) *
          (Real.sqrt Y * (2 * (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
    calc
      _ ≤ ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent) *
          (Real.sqrt Y *
            (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
              Y ^ (-eps / 16 : ℝ))) :=
        mul_le_mul_of_nonneg_right hlogProduct
          (mul_nonneg hrootNonneg hsaveTerm)
      _ ≤ ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent) *
          (Real.sqrt Y * (2 * (Real.log X) ^ (-5 * a / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsave hrootNonneg)
          hlogProdNonneg
  unfold selectedDyadicPTWUncappedKernel
  let P : ℝ := (2 * Real.log X) ^ selectedMobiusPTWLogExponent
  let S : ℝ := (Real.log X) ^ (-5 * a / 4 : ℝ)
  have hJnonneg : 0 ≤ J 20 := by
    unfold J K
    positivity
  calc
    _ = J 20 * (Z 20 Y ^ 3 * (Real.log (4 * Y)) ^ (b 20 + 3)) *
        (Real.sqrt Y *
          (((Real.log X) ^ (-20 * a)) ^ (1 / 16 : ℝ) +
            Y ^ (-eps / 16 : ℝ))) := by
      simp only [mul_assoc]
    _ ≤ J 20 *
          ((2 : ℝ) ^ (3 * (2 ^ 20 + 1)) * P) *
            (Real.sqrt Y * (2 * S)) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hkernelProduct hJnonneg)
    _ = 2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) * P *
        Real.sqrt Y * S := by ring
    _ = 2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
          Real.sqrt Y * (Real.log X) ^ (-5 * a / 4) := by rfl

/-- The source retained-scale geometry supplies the logarithmic window and
the second saving needed by the uncapped kernel. The only eventual absorption
left explicit is exactly the blueprint condition
`X^(-eps/32) ≤ (log X)^(-5a/4)`. -/
theorem selectedDyadicPTWUncappedKernel_le_of_quotientSourceGeometry
    {X Y C₀ d a eps : ℝ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps : 0 < eps)
    (hE : 3 * Real.log C₀ + a * Real.log (Real.log X) ≤
      Real.log X / 2)
    (hC₀ : 1 ≤ C₀) (hd : 1 ≤ d)
    (hYlower : X ^ (1 / 2 : ℝ) ≤ Y)
    (hYupper : Y ≤ C₀ ^ 3 * X / d)
    (hXeps : X ^ (-eps / 32 : ℝ) ≤
      (Real.log X) ^ (-5 * a / 4 : ℝ)) :
    selectedDyadicPTWUncappedKernel X Y a eps ≤
      2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
          Real.sqrt Y * (Real.log X) ^ (-5 * a / 4) := by
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans
      (by
        have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
        exact h3.trans hXlarge)
  have hloglog : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogXone
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
  have hC₀log : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hE₀ : 3 * Real.log C₀ ≤ Real.log X / 2 := by
    have hterm : 0 ≤ a * Real.log (Real.log X) := mul_nonneg ha hloglog
    linarith
  have hC₀cube : C₀ ^ 3 ≤ Real.sqrt X := by
    apply (Real.log_le_log_iff (by positivity)
      (Real.sqrt_pos.2 hXpos)).mp
    rw [Real.log_pow C₀ 3, Real.log_sqrt hXpos.le]
    nlinarith [hE₀]
  have hYpos : 0 < Y := by
    have hpowpos : 0 < X ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpowpos hYlower
  have hYle : Y ≤ Real.sqrt X * X := by
    have hA : 0 ≤ C₀ ^ 3 * X := by positivity
    have hdiv : C₀ ^ 3 * X / d ≤ C₀ ^ 3 * X :=
      div_le_self hA hd
    calc
      Y ≤ C₀ ^ 3 * X / d := hYupper
      _ ≤ C₀ ^ 3 * X := hdiv
      _ ≤ Real.sqrt X * X := by
        exact mul_le_mul_of_nonneg_right hC₀cube hXpos.le
  have hrootLower : 4 ≤ Real.sqrt X := by
    have h16 : (2 : ℝ) ^ 16 ≤ Real.sqrt X := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      have hpow : ((2 : ℝ) ^ 16) ^ 2 ≤ X := by
        have h32 : (2 : ℝ) ^ 32 ≤ (2 : ℝ) ^ 120 := by norm_num
        calc
          ((2 : ℝ) ^ 16) ^ 2 = (2 : ℝ) ^ 32 := by norm_num
          _ ≤ X := h32.trans hXlarge
      exact hpow
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
    exact h4.trans h16
  have hsqrtle : 4 * Real.sqrt X ≤ X := by
    have hmul := mul_le_mul_of_nonneg_left hrootLower
      (Real.sqrt_nonneg X)
    have hsqrtSq : Real.sqrt X * Real.sqrt X = X := by
      nlinarith [Real.sq_sqrt hXpos.le]
    nlinarith [hmul, hsqrtSq]
  have h4Yle : 4 * Y ≤ X ^ 2 := by
    calc
      4 * Y ≤ 4 * (Real.sqrt X * X) :=
        mul_le_mul_of_nonneg_left hYle (by norm_num)
      _ = (4 * Real.sqrt X) * X := by ring
      _ ≤ X * X := mul_le_mul_of_nonneg_right hsqrtle hXpos.le
      _ = X ^ 2 := by ring
  have hlog4Y : Real.log (4 * Y) ≤ 2 * Real.log X := by
    have hlog := Real.log_le_log (by positivity) h4Yle
    rw [Real.log_pow X 2] at hlog
    simpa [two_mul] using hlog
  have hYlarge : (2 : ℝ) ^ 16 ≤ Y := by
    have hroot : (2 : ℝ) ^ 16 ≤ Real.sqrt X := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      have hpow : ((2 : ℝ) ^ 16) ^ 2 ≤ X := by
        have h32 : (2 : ℝ) ^ 32 ≤ (2 : ℝ) ^ 120 := by norm_num
        calc
          ((2 : ℝ) ^ 16) ^ 2 = (2 : ℝ) ^ 32 := by norm_num
          _ ≤ X := h32.trans hXlarge
      exact hpow
    have hrootEq : Real.sqrt X = X ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow X
    rw [hrootEq] at hroot
    exact hroot.trans hYlower
  have hhalfpos : 0 < X ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hXpos _
  have hsave0 : -eps / 16 ≤ 0 := by linarith
  have hYsave₀ : Y ^ (-eps / 16 : ℝ) ≤
      (X ^ (1 / 2 : ℝ)) ^ (-eps / 16 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hhalfpos hYlower hsave0
  have hYsaveEq : (X ^ (1 / 2 : ℝ)) ^ (-eps / 16 : ℝ) =
      X ^ (-eps / 32 : ℝ) := by
    rw [← Real.rpow_mul hXpos.le (1 / 2 : ℝ) (-eps / 16 : ℝ)]
    congr 1
    ring
  have hYsave : Y ^ (-eps / 16 : ℝ) ≤
      (Real.log X) ^ (-5 * a / 4 : ℝ) :=
    hYsaveEq ▸ hYsave₀ |>.trans hXeps
  exact selectedDyadicPTWUncappedKernel_le_of_log_window
    hlogXpos hYlarge hlog4Y hYsave

/-- The allocated quotient upper bound contributes the source factor
`d^(-1/2) sqrt(Y) ≤ C₀^(3/2) sqrt(X)/d` exactly. -/
theorem selectedMobiusPTW_sqrtQuotient_le_sourceScale
    {X Y C₀ d : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hC₀ : 0 ≤ C₀) (hd : 0 < d)
    (hYupper : Y ≤ C₀ ^ 3 * X / d) :
    d ^ (-(1 / 2 : ℝ)) * Real.sqrt Y ≤
      C₀ ^ (3 / 2 : ℝ) * Real.sqrt X / d := by
  have hdInvSq : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
    rw [(Real.rpow_mul_natCast hd.le (-(1 / 2 : ℝ)) 2).symm]
    rw [show (-(1 / 2 : ℝ)) * (↑(2 : ℕ) : ℝ) = (-1 : ℝ) by norm_num,
      Real.rpow_neg_one]
  have hC₀Sq : (C₀ ^ (3 / 2 : ℝ)) ^ 2 = C₀ ^ 3 := by
    rw [(Real.rpow_mul_natCast hC₀ (3 / 2 : ℝ) 2).symm]
    norm_num [Real.rpow_natCast]
  have hleftSq :
      (d ^ (-(1 / 2 : ℝ)) * Real.sqrt Y) ^ 2 = d⁻¹ * Y := by
    rw [mul_pow, hdInvSq, Real.sq_sqrt hY.le]
  have hrightSq :
      (C₀ ^ (3 / 2 : ℝ) * Real.sqrt X / d) ^ 2 =
        C₀ ^ 3 * X / d ^ 2 := by
    rw [div_pow, mul_pow, hC₀Sq, Real.sq_sqrt hX.le]
  have hsq :
      (d ^ (-(1 / 2 : ℝ)) * Real.sqrt Y) ^ 2 ≤
        (C₀ ^ (3 / 2 : ℝ) * Real.sqrt X / d) ^ 2 := by
    rw [hleftSq, hrightSq]
    calc
      d⁻¹ * Y ≤ d⁻¹ * (C₀ ^ 3 * X / d) :=
        mul_le_mul_of_nonneg_left hYupper (inv_nonneg.mpr hd.le)
      _ = C₀ ^ 3 * X / d ^ 2 := by field_simp [ne_of_gt hd]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

/-- After inserting the allocated quotient estimate, the uncapped kernel has
the source normalization `d^(-1/2) sqrt(Y) ≤ C₀^(3/2) sqrt(X)/d`. This
retains the exact kernel constant, log exponent, and saving. -/
theorem selectedMobiusPTWUncappedKernel_sourceScale
    {X Y C₀ d a eps : ℝ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps : 0 < eps)
    (hE : 3 * Real.log C₀ + a * Real.log (Real.log X) ≤
      Real.log X / 2)
    (hC₀ : 1 ≤ C₀) (hd : 1 ≤ d)
    (hYlower : X ^ (1 / 2 : ℝ) ≤ Y)
    (hYupper : Y ≤ C₀ ^ 3 * X / d)
    (hXeps : X ^ (-eps / 32 : ℝ) ≤
      (Real.log X) ^ (-5 * a / 4 : ℝ)) :
    d ^ (-(1 / 2 : ℝ)) * selectedDyadicPTWUncappedKernel X Y a eps ≤
      2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) * C₀ ^ (3 / 2 : ℝ) *
        (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
          Real.sqrt X / d * (Real.log X) ^ (-5 * a / 4 : ℝ) := by
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hYpos : 0 < Y := by
    have hroot : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hroot hYlower
  have hkernel := selectedDyadicPTWUncappedKernel_le_of_quotientSourceGeometry
    hXlarge ha heps hE hC₀ hd hYlower hYupper hXeps
  have hscale := selectedMobiusPTW_sqrtQuotient_le_sourceScale
    hXpos hYpos (by linarith) (by linarith) hYupper
  let A : ℝ := 2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1)))
  let P : ℝ := (2 * Real.log X) ^ selectedMobiusPTWLogExponent
  let S : ℝ := (Real.log X) ^ (-5 * a / 4 : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold J K
    positivity
  have hP : 0 ≤ P := by
    dsimp [P]
    exact pow_nonneg (by positivity : 0 ≤ 2 * Real.log X) _
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Real.rpow_nonneg hlogXpos.le _
  have hhalf : 0 ≤ d ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by linarith : 0 ≤ d) _
  have hcoef : 0 ≤ A * P * S := by positivity
  calc
    d ^ (-(1 / 2 : ℝ)) * selectedDyadicPTWUncappedKernel X Y a eps ≤
        d ^ (-(1 / 2 : ℝ)) *
          (A * P * Real.sqrt Y * S) := by
      apply mul_le_mul_of_nonneg_left _ hhalf
      simpa [A, P, S, mul_assoc] using hkernel
    _ = (A * P * S) *
          (d ^ (-(1 / 2 : ℝ)) * Real.sqrt Y) := by ring
    _ ≤ (A * P * S) *
          (C₀ ^ (3 / 2 : ℝ) * Real.sqrt X / d) :=
      mul_le_mul_of_nonneg_left hscale hcoef
    _ = 2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          C₀ ^ (3 / 2 : ℝ) * P * Real.sqrt X / d * S := by
      dsimp [A]
      ring
    _ = 2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          C₀ ^ (3 / 2 : ℝ) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / d * (Real.log X) ^ (-5 * a / 4 : ℝ) := by
      rfl

/-- Scalar coefficient transfer for the actual source integral bound: the
external `d^(-1/2)` combines with the allocated quotient kernel to leave the
source divisor cost `D/d`, with all three factor scales unchanged. -/
theorem selectedMobiusPTW_sourceCoefficient_cost_of_kernel_bound
    {X Y C₀ d D B a eps K : ℝ}
    (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hK : K ≤ d ^ (-(1 / 2 : ℝ)) * D *
      ((B * B * B) * selectedDyadicPTWUncappedKernel X Y a eps))
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps : 0 < eps)
    (hE : 3 * Real.log C₀ + a * Real.log (Real.log X) ≤
      Real.log X / 2)
    (hC₀ : 1 ≤ C₀) (hd : 1 ≤ d)
    (hYlower : X ^ (1 / 2 : ℝ) ≤ Y)
    (hYupper : Y ≤ C₀ ^ 3 * X / d)
    (hXeps : X ^ (-eps / 32 : ℝ) ≤
      (Real.log X) ^ (-5 * a / 4 : ℝ)) :
    K ≤ D * (B * B * B) *
      (2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        C₀ ^ (3 / 2 : ℝ) *
          (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
            Real.sqrt X / d * (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
  have hkernel := selectedMobiusPTWUncappedKernel_sourceScale
    hXlarge ha heps hE hC₀ hd hYlower hYupper hXeps
  have hDscale : 0 ≤ D * (B * B * B) := by
    positivity
  calc
    K ≤ d ^ (-(1 / 2 : ℝ)) * D *
          ((B * B * B) * selectedDyadicPTWUncappedKernel X Y a eps) := hK
    _ = D * (B * B * B) *
          (d ^ (-(1 / 2 : ℝ)) *
            selectedDyadicPTWUncappedKernel X Y a eps) := by ring
    _ ≤ D * (B * B * B) *
          (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
              (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
            C₀ ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                Real.sqrt X / d * (Real.log X) ^ (-5 * a / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hkernel hDscale

/-- The explicit logarithmic threshold needed to absorb the uncapped
second-saving term in the allocated quotient proof. -/
noncomputable def selectedMobiusPTWUncappedSavingThreshold
    (a eps : ℝ) : ℝ :=
  Real.exp ((2 / (eps / 32)) *
    Real.log (logAbsorptionM (eps / 32) (5 * a / 4)))

/-- Above the explicit source threshold, the power/log comparison used in the
uncapped kernel is available with exactly the blueprint exponents. -/
theorem selectedMobiusPTWUncappedSavingThreshold_absorption
    {X a eps : ℝ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps : 0 < eps)
    (hX : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X) :
    X ^ (-eps / 32 : ℝ) ≤ (Real.log X) ^ (-5 * a / 4 : ℝ) := by
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 ≤ X := by
    have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hXgtone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXgtone
  have hlarge :
      (2 / (eps / 32)) *
        Real.log (1 * logAbsorptionM (eps / 32) (5 * a / 4)) ≤
      Real.log X := by
    have hle :
        Real.exp ((2 / (eps / 32)) *
          Real.log (logAbsorptionM (eps / 32) (5 * a / 4))) ≤
        Real.exp (Real.log X) := by
      simpa [selectedMobiusPTWUncappedSavingThreshold,
        Real.exp_log hXpos] using hX
    have hexp := Real.exp_le_exp.mp hle
    simpa only [one_mul] using hexp
  have hpow : (Real.log X) ^ (5 * a / 4 : ℝ) ≤ X ^ (eps / 32 : ℝ) := by
    simpa only [one_mul] using
      (log_absorption_bound (a := eps / 32) (b := 5 * a / 4) (K := 1)
        (X := X) (by positivity) (by positivity) (by norm_num) hXone hlarge)
  have hlogpowpos : 0 < (Real.log X) ^ (5 * a / 4 : ℝ) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hXpowpos : 0 < X ^ (eps / 32 : ℝ) :=
    Real.rpow_pos_of_pos hXpos _
  rw [show -eps / 32 = -(eps / 32 : ℝ) by ring,
    Real.rpow_neg hXpos.le,
    show -5 * a / 4 = -(5 * a / 4 : ℝ) by ring,
    Real.rpow_neg hlogXpos.le]
  exact (inv_le_inv₀ hXpowpos hlogpowpos).2 hpow

/-- Once each actual allocated cell has been normalized to the source scale,
the fixed-source common-cutoff integral incurs exactly `J₀³`. Each cell's own
allocated base has already been absorbed into `√X/d`; no common quotient base
is imposed across distinct dyadic indices. -/
theorem selectedMobiusPTW_actualSourceIntegral_le_of_sourceScaleBlockBounds
    {X z c U C₀ a : ℝ} {d Q q : ℕ}
    (hd : 0 < d) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (rchar : ℤ) (scalar : ℝ → ℂ)
    (T γ η η' : ℝ)
    (hExpansion : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := z) (c := c) fs r χ T t γ η η' I J J')
    (hcont : ∀ j k l,
      Continuous (fun t : ℝ =>
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            scalar t * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c : ℂ)
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ T γ η η' j k l t)))
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hC₀ : 1 ≤ C₀)
    (hblock : ∀ j ∈ Finset.range
        (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ k ∈ Finset.range
        (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ l ∈ Finset.range
        (selectedMobiusPTWDyadicBlockCount decompositionC),
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              scalar t * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) (c : ℂ)
                  (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                  (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) ≤
          (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
              C₀ ^ (3 / 2 : ℝ) *
                (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                  Real.sqrt X / (d : ℝ) *
                    (Real.log X) ^ (-5 * a / 4 : ℝ))) :
    (∫ t in Set.Icc (-U) U,
      ‖scalar t *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J')‖
      ∂volume) ≤
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
        ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
            selectedPTWFactorScale X d) *
          (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
              (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
            C₀ ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                Real.sqrt X / (d : ℝ) *
                  (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
  classical
  let D : ℝ := (divisorFunction 3 ⟨d, hd⟩ : ℝ)
  let B : ℝ := selectedPTWFactorScale X d
  let Ksource : ℝ := D * (B * B * B) *
    (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
        (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
      C₀ ^ (3 / 2 : ℝ) *
        (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
          Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ))
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have h8X : 1 < 8 * X := by nlinarith [hXlarge]
  have hlog8X : 0 < Real.log (8 * X) := Real.log_pos h8X
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by
    dsimp [B, selectedPTWFactorScale]
    positivity
  have hJ20 : 0 ≤ FractionalPrimes.Literature.DirichletMean.J 20 := by
    unfold FractionalPrimes.Literature.DirichletMean.J
    unfold FractionalPrimes.Literature.DirichletMean.K
    positivity
  have hKsource : 0 ≤ Ksource := by
    dsimp [Ksource]
    positivity
  have hsum := selectedMobiusPTW_actualSourceIntegral_le_of_tripleBlockBounds
    hd fs I J J' rchar scalar T γ η η' hExpansion hcont
    (by
      intro j hj k hk l hl
      simpa [Ksource, D, B, mul_assoc] using hblock j hj k hk l hl)
    hKsource
  simpa [Ksource, D, B, mul_assoc] using hsum

/-- If a fixed selected triple window vanishes for every allocation,
character, and time, then its weighted source integral is exactly zero. This
is the empty-cell branch paired with the retained-scale `of_live` theorem. -/
theorem selectedMobiusPTW_actualAllocatedBlock_integral_eq_zero_of_allTermsZero
    {X z : ℝ} {U : ℝ} {d Q q : ℕ}
    (scalar : ℝ → ℂ)
    (c : ℂ) (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (rchar : ℤ) (T γ η η' : ℝ) (j k l : ℕ)
    (hzero : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm
        (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t = 0) :
    (∫ t in Set.Icc (-U) U,
      ‖scalar t *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t)‖
      ∂volume) = 0 := by
  classical
  have hsum (t : ℝ) :
      ∑ r : divisorFactorTuples 3 d,
        ∑ χ : BlueprintCharacter Q,
          star (evalInt χ rchar) *
            selectedMobiusPTWActualAllocatedWindowTerm
              (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro χ hχ
    simp [hzero r χ t]
  have hintegrand :
      (fun t : ℝ => ‖scalar t *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t)‖) =
      fun _ => (0 : ℝ) := by
    funext t
    rw [hsum t]
    simp
  rw [hintegrand]
  simp

/-- Cellwise live/zero adapter. The selected source groups and their labels
are fixed parameters; only the witness `(r, χ, t)` varies with this cell.
Quotient geometry is requested conditionally on a live cell, while an empty
cell is discharged by exact vanishing. -/
theorem selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_liveOrZero
    {X z U Y C₀ a eps : ℝ} {d Q q : ℕ}
    (hd : 0 < d) (scalar : ℝ → ℂ)
    (c : ℂ) (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (rchar : ℤ) (T γ η η' : ℝ) (j k l : ℕ)
    (hLiveBound :
      (∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ),
        selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t ≠ 0) →
      (∫ t in Set.Icc (-U) U,
        ‖scalar t *
          (∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t)‖
        ∂volume) ≤
        (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            ((selectedPTWFactorScale X d * selectedPTWFactorScale X d *
                selectedPTWFactorScale X d) *
              selectedDyadicPTWUncappedKernel X Y a eps))
    (hLiveGeometry :
      (∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ),
        selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t ≠ 0) →
      X ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ C₀ ^ 3 * X / (d : ℝ))
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps : 0 < eps)
    (hE : 3 * Real.log C₀ + a * Real.log (Real.log X) ≤
      Real.log X / 2)
    (hC₀ : 1 ≤ C₀) (hdreal : 1 ≤ (d : ℝ))
    (hXsave : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X) :
    (∫ t in Set.Icc (-U) U,
      ‖scalar t *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t)‖
      ∂volume) ≤
      (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
        (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
          selectedPTWFactorScale X d) *
        (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
            (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          C₀ ^ (3 / 2 : ℝ) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) *
                (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
  classical
  let D : ℝ := (divisorFunction 3 ⟨d, hd⟩ : ℝ)
  let B : ℝ := selectedPTWFactorScale X d
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have h8X : 1 < 8 * X := by nlinarith [hXlarge]
  have hlog8X : 0 < Real.log (8 * X) := Real.log_pos h8X
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by
    dsimp [B, selectedPTWFactorScale]
    positivity
  have hJ20 : 0 ≤ FractionalPrimes.Literature.DirichletMean.J 20 := by
    unfold FractionalPrimes.Literature.DirichletMean.J
    unfold FractionalPrimes.Literature.DirichletMean.K
    positivity
  have hKsource :
      0 ≤ D * (B * B * B) *
        (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
            (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          C₀ ^ (3 / 2 : ℝ) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) *
                (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
    positivity
  by_cases hL : ∃ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm
        (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t ≠ 0
  · have hXeps := selectedMobiusPTWUncappedSavingThreshold_absorption
      hXlarge ha heps hXsave
    have hcost := selectedMobiusPTW_sourceCoefficient_cost_of_kernel_bound
      hD hB (hLiveBound hL) hXlarge ha heps hE hC₀ hdreal
      (hLiveGeometry hL).1 (hLiveGeometry hL).2 hXeps
    simpa [D, B, mul_assoc] using hcost
  · have hzero : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm
        (z := z) (q := q) c fs₁ fs₂ fs₃ r χ T γ η η' j k l t = 0 := by
      intro r χ t
      by_contra hne
      exact hL ⟨r, χ, t, hne⟩
    rw [selectedMobiusPTW_actualAllocatedBlock_integral_eq_zero_of_allTermsZero
      scalar c fs₁ fs₂ fs₃ rchar T γ η η' j k l hzero]
    simpa [D, B, mul_assoc] using hKsource

/-- A live selected source cell supplies its own quotient-base geometry.
The same fixed `I/J/J'` and exponents are used to extract all three retained
scales. The lower quotient bound uses `d ≤ q ≤ (log X)^a` and the displayed
source logarithmic budget; the upper bound is the product of the three
retained upper scales. -/
theorem selectedMobiusPTW_actualAllocatedCell_sourceQuotientGeometry_of_live
    {X z : ℝ} {d Q q : ℕ} (a γ η η' : ℝ)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X) (ha : 0 ≤ a)
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (hE : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2)
    (hγsum : γ + η + η' = 1)
    (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length)) (T : ℝ) (j k l : ℕ)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hLive : ∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
      (t : ℝ),
      selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c
        (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
        (selectedDyadicFactors fs J') r χ T γ η η' j k l t ≠ 0) :
    X ^ (1 / 2 : ℝ) ≤
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) ∧
      (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
        ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
        ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) ≤
          (2 * decompositionC) ^ 3 * X / (d : ℝ) := by
  classical
  let C₀ : ℝ := 2 * decompositionC
  let N₁ : ℝ := (2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))
  let N₂ : ℝ := (2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))
  let N₃ : ℝ := (2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC))
  let Y : ℝ := (N₁ * N₂ * N₃) / (d : ℝ)
  have hXpos : 0 < X := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXone : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans
      (by
        have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
        exact h3.trans hXlarge)
  have hlogXpos : 0 < Real.log X := lt_of_lt_of_le (by norm_num) hlogXone
  have hdecompositionCpos : 0 < decompositionC := by
    dsimp [decompositionC]
    positivity
  have hdecompositionCge : 1 ≤ decompositionC := by
    change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
    have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul h2 h81 (by norm_num) (by positivity)
  have hC₀ : 1 ≤ C₀ := by
    dsimp [C₀]
    nlinarith [hdecompositionCge]
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) hdreal
  have hQone : 1 ≤ Q := Nat.succ_le_iff.mpr hQ
  have hdq : d ≤ q := by
    calc
      d = d * 1 := by simp
      _ ≤ d * Q := Nat.mul_le_mul_left d hQone
      _ = q := hqfactor
  have hdlog : (d : ℝ) ≤ (Real.log X) ^ a := by
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact hdq'.trans hqlog
  have hlogdle : Real.log (d : ℝ) ≤ a * Real.log (Real.log X) := by
    calc
      Real.log (d : ℝ) ≤ Real.log ((Real.log X) ^ a) :=
        Real.log_le_log hdpos hdlog
      _ = a * Real.log (Real.log X) := by rw [Real.log_rpow hlogXpos]
  have hlogprod : Real.log (C₀ ^ 3 * (d : ℝ)) =
      3 * Real.log C₀ + Real.log (d : ℝ) := by
    rw [Real.log_mul (pow_ne_zero 3 hC₀pos.ne') hdpos.ne', Real.log_pow]
    ring
  have hrootpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hlogprod_le : Real.log (C₀ ^ 3 * (d : ℝ)) ≤ Real.log (Real.sqrt X) := by
    rw [hlogprod, Real.log_sqrt hXpos.le]
    nlinarith [hE, hlogdle]
  have hC₀cubeD : C₀ ^ 3 * (d : ℝ) ≤ Real.sqrt X :=
    (Real.log_le_log_iff (by positivity) hrootpos).mp hlogprod_le
  have hLive' := hLive
  obtain ⟨r₀, χ₀, t₀, hLive₀⟩ := hLive'
  have hret := selectedMobiusPTW_actualAllocatedCell_retainedScales_of_live
    hXpos c fs fs fs I J J' γ η η' hSupport₁ hSupport₂ hSupport₃
    r₀ χ₀ T j k l t₀ hLive₀
  rcases hret with ⟨hN₁lower, hN₁upper, hN₂lower, hN₂upper,
    hN₃lower, hN₃upper⟩
  have hN₁eq : N₁ = ((2 : ℝ) ^ j * X ^ γ) / (4 * decompositionC) := by
    dsimp [N₁]
    rw [mul_div_assoc]
  have hN₂eq : N₂ = ((2 : ℝ) ^ k * X ^ η) / (4 * decompositionC) := by
    dsimp [N₂]
    rw [mul_div_assoc]
  have hN₃eq : N₃ = ((2 : ℝ) ^ l * X ^ η') / (4 * decompositionC) := by
    dsimp [N₃]
    rw [mul_div_assoc]
  have hN₁lower' : X ^ γ / C₀ ≤ N₁ := by
    rw [hN₁eq]
    simpa [C₀] using hN₁lower
  have hN₁upper' : N₁ ≤ C₀ * X ^ γ := by
    rw [hN₁eq]
    simpa [C₀] using hN₁upper
  have hN₂lower' : X ^ η / C₀ ≤ N₂ := by
    rw [hN₂eq]
    simpa [C₀] using hN₂lower
  have hN₂upper' : N₂ ≤ C₀ * X ^ η := by
    rw [hN₂eq]
    simpa [C₀] using hN₂upper
  have hN₃lower' : X ^ η' / C₀ ≤ N₃ := by
    rw [hN₃eq]
    simpa [C₀] using hN₃lower
  have hN₃upper' : N₃ ≤ C₀ * X ^ η' := by
    rw [hN₃eq]
    simpa [C₀] using hN₃upper
  have hN₁pos : 0 < N₁ := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos hXpos γ) hC₀pos) hN₁lower'
  have hN₂pos : 0 < N₂ := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos hXpos η) hC₀pos) hN₂lower'
  have hN₃pos : 0 < N₃ := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos hXpos η') hC₀pos) hN₃lower'
  have hpow : X ^ γ * X ^ η * X ^ η' = X := by
    calc
      X ^ γ * X ^ η * X ^ η' = X ^ (γ + η) * X ^ η' := by
        rw [← Real.rpow_add hXpos]
      _ = X ^ ((γ + η) + η') := by rw [← Real.rpow_add hXpos]
      _ = X := by rw [hγsum, Real.rpow_one]
  have hprodLower : X / C₀ ^ 3 ≤ N₁ * N₂ * N₃ := by
    have hmul₁ : (X ^ γ / C₀) * (X ^ η / C₀) ≤ N₁ * N₂ :=
      mul_le_mul hN₁lower' hN₂lower' (by positivity) (by positivity)
    have hmul₂ : ((X ^ γ / C₀) * (X ^ η / C₀)) * (X ^ η' / C₀) ≤
        (N₁ * N₂) * N₃ :=
      mul_le_mul hmul₁ hN₃lower' (by positivity) (by positivity)
    have hleft :
        (X ^ γ / C₀) * (X ^ η / C₀) * (X ^ η' / C₀) = X / C₀ ^ 3 := by
      field_simp [ne_of_gt hC₀pos]
      rw [hpow]
    simpa [mul_assoc] using hleft.symm.le.trans hmul₂
  have hprodUpper : N₁ * N₂ * N₃ ≤ C₀ ^ 3 * X := by
    have hmul₁ : N₁ * N₂ ≤ (C₀ * X ^ γ) * (C₀ * X ^ η) :=
      mul_le_mul hN₁upper' hN₂upper' (by positivity) (by positivity)
    have hmul₂ : (N₁ * N₂) * N₃ ≤
        ((C₀ * X ^ γ) * (C₀ * X ^ η)) * (C₀ * X ^ η') :=
      mul_le_mul hmul₁ hN₃upper' (by positivity) (by positivity)
    have hright :
        ((C₀ * X ^ γ) * (C₀ * X ^ η)) * (C₀ * X ^ η') = C₀ ^ 3 * X := by
      calc
        ((C₀ * X ^ γ) * (C₀ * X ^ η)) * (C₀ * X ^ η') =
            C₀ ^ 3 * (X ^ γ * X ^ η * X ^ η') := by ring
        _ = C₀ ^ 3 * X := by rw [hpow]
    simpa [mul_assoc] using hmul₂.trans_eq hright
  have hfracLower : Real.sqrt X ≤ X / (C₀ ^ 3 * (d : ℝ)) :=
    (le_div_iff₀ (mul_pos (by positivity) hdpos)).2 (by
      calc
        Real.sqrt X * (C₀ ^ 3 * (d : ℝ)) ≤ Real.sqrt X * Real.sqrt X :=
          mul_le_mul_of_nonneg_left hC₀cubeD (Real.sqrt_nonneg X)
        _ = X := by nlinarith [Real.sq_sqrt hXpos.le])
  have hfracEq : X / (C₀ ^ 3 * (d : ℝ)) = X / C₀ ^ 3 / (d : ℝ) := by
    field_simp [ne_of_gt hC₀pos, ne_of_gt hdpos]
  have hprodDiv : X / C₀ ^ 3 / (d : ℝ) ≤
      (N₁ * N₂ * N₃) / (d : ℝ) :=
    div_le_div_of_nonneg_right hprodLower hdpos.le
  have hYlower : X ^ (1 / 2 : ℝ) ≤ Y := by
    rw [← Real.sqrt_eq_rpow]
    dsimp [Y]
    calc
      Real.sqrt X ≤ X / (C₀ ^ 3 * (d : ℝ)) := hfracLower
      _ = X / C₀ ^ 3 / (d : ℝ) := hfracEq
      _ ≤ (N₁ * N₂ * N₃) / (d : ℝ) := hprodDiv
  have hYupper : Y ≤ C₀ ^ 3 * X / (d : ℝ) := by
    dsimp [Y]
    exact div_le_div_of_nonneg_right hprodUpper hdpos.le
  constructor
  · simpa [Y, N₁, N₂, N₃] using hYlower
  · simpa [Y, C₀, N₁, N₂, N₃] using hYupper

/-- Source-data instantiation of the cellwise live/zero estimate. For a live
cell, the existing fixed-witness MUF theorem supplies the allocated kernel
bound and the same live witness supplies this cell's quotient geometry. -/
theorem selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_MUF
    {X U eps a Tfreq z : ℝ} {d Q q : ℕ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hU0 : 2 ≤ U) (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (rchar : ℤ) (hrchar : IsCoprime rchar (Q : ℤ))
    (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (γ η η' : ℝ) (j k l : ℕ)
    (hγsum : γ + η + η' = 1)
    (hγlo : 1 / 4 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hηlo : 0 ≤ η) (hη'lo : 0 ≤ η')
    (hgap : |η - η'| ≤ 1 / 4)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hE : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2)
    (hdev : ∀ Y : ℝ, Y =
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) →
      2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300)
    (hYlarge : (2 : ℝ) ^ 16 ≤
      (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
        ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
        ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ))
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : (selectedDyadicFactors fs I).length ≤ 20)
    (hlen₂ : (selectedDyadicFactors fs J).length ≤ 20)
    (hlen₃ : (selectedDyadicFactors fs J').length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight (selectedDyadicFactors fs I) ≤
      Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight (selectedDyadicFactors fs J) ≤
      Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight (selectedDyadicFactors fs J') ≤
      Real.log (8 * X))
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor z c (selectedDyadicFactors fs I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)))
    (hXsave : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ Tfreq γ η η' j k l t‖
        ∂volume) ≤
      (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
        (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
          selectedPTWFactorScale X d) *
        (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
            (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          (2 * decompositionC) ^ (3 / 2 : ℝ) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
  classical
  let Y : ℝ :=
    (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
      ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
      ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ)
  let scalar : ℝ → ℂ := fun t =>
    ((d : ℂ) ^
      (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
      (Q.totient : ℂ))
  have hC₀ : 1 ≤ (2 * decompositionC : ℝ) := by
    have hC : 1 ≤ decompositionC := by
      change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    nlinarith
  have hdreal : 1 ≤ (d : ℝ) :=
    by exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hLiveBound :
      (∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ),
        selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c (selectedDyadicFactors fs I)
          (selectedDyadicFactors fs J) (selectedDyadicFactors fs J')
          r χ Tfreq γ η η' j k l t ≠ 0) →
      (∫ t in Set.Icc (-U) U,
        ‖scalar t *
          (∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) c (selectedDyadicFactors fs I)
                  (selectedDyadicFactors fs J) (selectedDyadicFactors fs J')
                  r χ Tfreq γ η η' j k l t)‖ ∂volume) ≤
        (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            ((selectedPTWFactorScale X d * selectedPTWFactorScale X d *
                selectedPTWFactorScale X d) *
              selectedDyadicPTWUncappedKernel X Y a eps) := by
    intro hLive
    have hkernel := selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_of_live
      hXlarge ha heps0 heps hU0 hUsource hd hQ hqfactor hqlog rchar hrchar c
      fs I J J' γ η η' j k l hγsum hγlo hγhi hηlo hη'lo hgap
      hSupport₁ hSupport₂ hSupport₃ hE hdev hYlarge hc hlen₁ hlen₂ hlen₃
      hweight₁ hweight₂ hweight₃ hfreq hMUFblock hLive
    simpa [Y, scalar] using hkernel
  have hLiveGeometry :
      (∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ),
        selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c (selectedDyadicFactors fs I)
          (selectedDyadicFactors fs J) (selectedDyadicFactors fs J')
          r χ Tfreq γ η η' j k l t ≠ 0) →
      X ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ (2 * decompositionC) ^ 3 * X / (d : ℝ) := by
    intro hLive
    simpa [Y] using
      selectedMobiusPTW_actualAllocatedCell_sourceQuotientGeometry_of_live
        a γ η η' hXlarge ha hd hQ hqfactor hqlog hE hγsum c fs I J J'
        Tfreq j k l hSupport₁ hSupport₂ hSupport₃ hLive
  have hsource := selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_liveOrZero
    (X := X) (z := z) (U := U) (Y := Y) (C₀ := 2 * decompositionC)
    hd scalar c (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
    (selectedDyadicFactors fs J') rchar Tfreq γ η η' j k l
    hLiveBound hLiveGeometry hXlarge ha heps0 hE hC₀ hdreal hXsave
  simpa [Y, scalar] using hsource

set_option maxHeartbeats 6000000 in
/-- Finite selected-Möbius source transfer with source-data cell estimates.
Each triple block uses its own quotient base, and the exact finite allocation
identity is accumulated with the source factor `J₀^3`. The common selected
groups and exponents are fixed throughout; no geometry is imposed on empty
cells. -/
theorem selectedMobiusPTW_actualSourceIntegral_le_of_MUF_cellBounds
    {X z c U a eps : ℝ} {d Q q : ℕ}
    (hd : 0 < d) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (rchar : ℤ) (T γ η η' : ℝ)
    (hExpansion : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := z) (c := c) fs r χ T t γ η η' I J J')
    (hcont : ∀ j k l,
      Continuous (fun t : ℝ =>
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            (((d : ℂ) ^
                (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
                (Q.totient : ℂ)) * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c : ℂ)
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ T γ η η' j k l t))))
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hU0 : 2 ≤ U) (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (hrchar : IsCoprime rchar (Q : ℤ))
    (hγsum : γ + η + η' = 1)
    (hγlo : 1 / 4 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hηlo : 0 ≤ η) (hη'lo : 0 ≤ η')
    (hgap : |η - η'| ≤ 1 / 4)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hE : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2)
    (hdev : ∀ j k l : ℕ, ∀ Y : ℝ, Y =
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) →
      2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) / Real.log Y ≤ eps / 300)
    (hYlarge : ∀ j k l : ℕ, (2 : ℝ) ^ 16 ≤
      (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
        ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
        ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ))
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : (selectedDyadicFactors fs I).length ≤ 20)
    (hlen₂ : (selectedDyadicFactors fs J).length ≤ 20)
    (hlen₃ : (selectedDyadicFactors fs J').length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight (selectedDyadicFactors fs I) ≤
      Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight (selectedDyadicFactors fs J) ≤
      Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight (selectedDyadicFactors fs J') ≤
      Real.log (8 * X))
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |T - t| ∧ |T - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor z c (selectedDyadicFactors fs I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)))
    (hXsave : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J')‖
      ∂volume) ≤
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
        ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
            selectedPTWFactorScale X d) *
          (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
              (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
            (2 * decompositionC) ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                Real.sqrt X / (d : ℝ) *
                  (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
  classical
  let scalar : ℝ → ℂ := fun t =>
    ((d : ℂ) ^
      (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
      (Q.totient : ℂ))
  have hC₀ : 1 ≤ (2 * decompositionC : ℝ) := by
    have hC : 1 ≤ decompositionC := by
      change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    nlinarith
  have hcComplex : ‖(c : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hc
  have hblock : ∀ j ∈ Finset.range
      (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ k ∈ Finset.range
      (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ l ∈ Finset.range
      (selectedMobiusPTWDyadicBlockCount decompositionC),
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              scalar t * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) (c : ℂ)
                  (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                  (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) ≤
          (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
              (2 * decompositionC) ^ (3 / 2 : ℝ) *
                (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                  Real.sqrt X / (d : ℝ) *
                    (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
    intro j hj k hk l hl
    have hcell := selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_MUF
      hXlarge ha heps0 heps hU0 hUsource hd hQ hqfactor hqlog
      rchar hrchar c fs I J J' γ η η' j k l hγsum hγlo hγhi hηlo hη'lo hgap
      hSupport₁ hSupport₂ hSupport₃ hE (hdev j k l) (hYlarge j k l)
      hcComplex hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃ hfreq hMUFblock hXsave
    have hsum (t : ℝ) :
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            scalar t * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c : ℂ)
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ T γ η η' j k l t) =
          scalar t *
            (∑ r : divisorFactorTuples 3 d,
              ∑ χ : BlueprintCharacter Q,
                star (evalInt χ rchar) *
                  selectedMobiusPTWActualAllocatedWindowTerm
                    (z := z) (q := q) (c : ℂ)
                    (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                    (selectedDyadicFactors fs J') r χ T γ η η' j k l t) := by
      simp only [Finset.mul_sum]
    have hintegral :
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              scalar t * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) (c : ℂ)
                  (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                  (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) =
        (∫ t in Set.Icc (-U) U,
          ‖scalar t *
            (∑ r : divisorFactorTuples 3 d,
              ∑ χ : BlueprintCharacter Q,
                star (evalInt χ rchar) *
                  selectedMobiusPTWActualAllocatedWindowTerm
                    (z := z) (q := q) (c : ℂ)
                    (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                    (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) := by
      apply integral_congr_ae
      filter_upwards with t
      exact congrArg norm (hsum t)
    rw [hintegral]
    exact hcell
  exact selectedMobiusPTW_actualSourceIntegral_le_of_sourceScaleBlockBounds
    hd fs I J J' rchar scalar T γ η η' hExpansion hcont hXlarge hC₀ hblock

#print axioms selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_from_MUF
#print axioms selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_of_live
#print axioms selectedMobiusPTW_actualAllocatedGeometry_of_retainedSourceScales
#print axioms selectedMobiusPTW_actualWeightedSource_eq_tripleBlockSum
#print axioms selectedMobiusPTW_actualSourceIntegral_le_of_tripleBlockBounds
#print axioms selectedDyadicPTWUncappedKernel_le_of_log_window
#print axioms selectedDyadicPTWUncappedKernel_le_of_quotientSourceGeometry
#print axioms selectedMobiusPTW_sqrtQuotient_le_sourceScale
#print axioms selectedMobiusPTWUncappedKernel_sourceScale
#print axioms selectedMobiusPTW_sourceCoefficient_cost_of_kernel_bound
#print axioms selectedMobiusPTWUncappedSavingThreshold_absorption
#print axioms selectedMobiusPTW_actualSourceIntegral_le_of_sourceScaleBlockBounds
#print axioms selectedMobiusPTW_actualAllocatedBlock_integral_eq_zero_of_allTermsZero
#print axioms selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_liveOrZero
#print axioms selectedMobiusPTW_actualAllocatedCell_sourceQuotientGeometry_of_live
#print axioms selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_MUF
#print axioms selectedMobiusPTW_actualSourceIntegral_le_of_MUF_cellBounds

#print axioms selectedMobiusPTW_actualAllocationIdentity_with_MUF
#print axioms selectedMobiusPTW_fixedActualAllocationExpansion_of_sourceWitness
#print axioms selectedMobiusPTW_actualSourceWitness_allTimes_from_MUF
#print axioms selectedMobiusPTW_actualAllocatedWindowProduct_eq_sourceTerm
#print axioms finiteAllocatedDirichletPolynomial_nonzero_has_nonzero_coefficient
#print axioms selectedMobiusPTW_actualAllocatedWindow_retainedScale
#print axioms selectedMobiusPTW_actualAllocatedBlock_uncapped_from_MUF
#print axioms selectedMobiusPTW_fixedGroup_length_mass

end FractionalPrimes.Literature.DirichletMean

end
