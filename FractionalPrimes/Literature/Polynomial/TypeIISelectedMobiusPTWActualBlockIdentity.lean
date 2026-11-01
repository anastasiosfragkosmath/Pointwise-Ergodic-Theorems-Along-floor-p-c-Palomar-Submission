module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWRetainedBlocks
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFactorAllocationIdentity
public import FractionalPrimes.Literature.Polynomial.PolynomialMellinSeparation
public import Mathlib.Tactic

/-! The type-II source support data gives the exact finite cutoff and dyadic
block expansion for the three selected Möbius groups after a fixed gcd
allocation. This is finite bookkeeping only; it contains no cancellation
estimate. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open FractionalPrimes.Literature.Polynomial
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

private theorem selectedMobiusPTW_divisorCoefficient_two_ge_one
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

/-- One exact allocated block product is the source allocation term at its
quotient scales. The only scale inputs are the literal equalities
`Mᵢ=Y^αᵢ`; all character cutoffs and source normalizations are unchanged. -/
theorem selectedMobiusPTW_allocatedWindowProduct_eq_sourceTerm
    {X Y z : ℝ} (c : ℂ) (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    {d Q q : ℕ} (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
    {alpha beta gamma T t M₁ M₂ M₃ : ℝ}
    (hM₁ : M₁ = Y ^ alpha) (hM₂ : M₂ = Y ^ beta)
    (hM₃ : M₃ = Y ^ gamma)
    (hM₁pos : 0 < M₁) (hM₂pos : 0 < M₂) (hM₃pos : 0 < M₃)
    (hB₁ : 0 < selectedPTWFactorScale X (r.1 0).1)
    (hB₂ : 0 < selectedPTWFactorScale X (r.1 1).1)
    (hB₃ : 0 < selectedPTWFactorScale X (r.1 2).1) :
    let a₁ := toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
    let a₂ := toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₂)
    let a₃ := toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₃)
    finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
        (q / orderedAllocationPrefix r.1 0)
        (factorExtractionRealInterval M₁ (2 * M₁)) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
      finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
        (q / orderedAllocationPrefix r.1 1)
        (factorExtractionRealInterval M₂ (2 * M₂)) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
      finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
        (q / orderedAllocationPrefix r.1 2)
        (factorExtractionRealInterval M₃ (2 * M₃)) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) =
      selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
        alpha beta gamma T r χ t := by
  classical
  let B₁ := selectedPTWFactorScale X (r.1 0).1
  let B₂ := selectedPTWFactorScale X (r.1 1).1
  let B₃ := selectedPTWFactorScale X (r.1 2).1
  let a₁ := toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
  let a₂ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z fs₂)
  let a₃ := toComplexArithmeticFunction
    (dyadicConvolutionPositiveComplex z fs₃)
  let χ₁ := selectedPTWAllocationCharacterWeight q r χ 0
  let χ₂ := selectedPTWAllocationCharacterWeight q r χ 1
  let χ₃ := selectedPTWAllocationCharacterWeight q r χ 2
  let p₁ := factorPolynomial M₁
    (selectedGroupTrilinearCoeff B₁ (r.1 0).1 (fun n => a₁ n) χ₁ T) t
  let p₂ := factorPolynomial M₂
    (selectedGroupTrilinearCoeff B₂ (r.1 1).1 (fun n => a₂ n) χ₂ T) t
  let p₃ := factorPolynomial M₃
    (selectedGroupTrilinearCoeff B₃ (r.1 2).1 (fun n => a₃ n) χ₃ T) t
  have hχcut₁ : ∀ n, χ₁ n =
      if Nat.Coprime n (q / orderedAllocationPrefix r.1 0) then
        evalInt χ (n : ℤ) else 0 := by intro n; rfl
  have hχcut₂ : ∀ n, χ₂ n =
      if Nat.Coprime n (q / orderedAllocationPrefix r.1 1) then
        evalInt χ (n : ℤ) else 0 := by intro n; rfl
  have hχcut₃ : ∀ n, χ₃ n =
      if Nat.Coprime n (q / orderedAllocationPrefix r.1 2) then
        evalInt χ (n : ℤ) else 0 := by intro n; rfl
  have hblock₁ := selectedGroupFactorPolynomial_eq_allocatedFactorWindow
    (r := (r.1 0).1) (q := q / orderedAllocationPrefix r.1 0)
    (Q := Q) (T := T) (t := t) hM₁pos hB₁ a₁ χ χ₁ hχcut₁
  have hblock₂ := selectedGroupFactorPolynomial_eq_allocatedFactorWindow
    (r := (r.1 1).1) (q := q / orderedAllocationPrefix r.1 1)
    (Q := Q) (T := T) (t := t) hM₂pos hB₂ a₂ χ χ₂ hχcut₂
  have hblock₃ := selectedGroupFactorPolynomial_eq_allocatedFactorWindow
    (r := (r.1 2).1) (q := q / orderedAllocationPrefix r.1 2)
    (Q := Q) (T := T) (t := t) hM₃pos hB₃ a₃ χ χ₃ hχcut₃
  dsimp
  change
    finiteAllocatedDirichletPolynomial a₁ (r.1 0).1
      (q / orderedAllocationPrefix r.1 0)
      (factorExtractionRealInterval M₁ (2 * M₁)) χ
      ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
    finiteAllocatedDirichletPolynomial a₂ (r.1 1).1
      (q / orderedAllocationPrefix r.1 1)
      (factorExtractionRealInterval M₂ (2 * M₂)) χ
      ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
    finiteAllocatedDirichletPolynomial a₃ (r.1 2).1
      (q / orderedAllocationPrefix r.1 2)
      (factorExtractionRealInterval M₃ (2 * M₃)) χ
      ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) = _
  calc
    _ = (B₁ * p₁) * (B₂ * p₂) * (B₃ * p₃) := by
      rw [← hblock₁, ← hblock₂, ← hblock₃]
    _ = ((B₁ * B₂ * B₃ : ℝ) : ℂ) * (p₁ * p₂ * p₃) := by
      push_cast
      ring
    _ = selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
          alpha beta gamma T r χ t := by
      dsimp [selectedDyadicPTWAllocationTerm, B₁, B₂, B₃,
        a₁, a₂, a₃, χ₁, χ₂, χ₃, p₁, p₂, p₃]
      rw [← hM₁, ← hM₂, ← hM₃]


/-- The actual type-II convolution identity becomes the exact ordered product
of the three selected-group arithmetic functions. This is the coefficient
identity needed before inserting the finite nonunit character allocation. -/
theorem selectedMobiusPTW_actualTypeII_sourceCoefficient_eq_selectedGroupProduct
    {X z c δ : ℝ}
    {f : ComplexPositiveIntegerFunction}
    {fs : List (DyadicArithmeticFactor X)}
    {α : Fin fs.length → ℝ}
    (hdata : largeTypeIIDyadicComponentData z c δ f fs α) :
    ∃ (I J J' : Finset (Fin fs.length)),
      toComplexArithmeticFunction f =
        toComplexArithmeticFunction
            (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I)) *
          toComplexArithmeticFunction
            (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J)) *
          toComplexArithmeticFunction
            (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J')) := by
  rcases hdata with ⟨_Aminus, _Aplus, v, a, b1, _γ, _η, _η',
    I, J, J', _i, _htypeII, hfactor, hv, ha, hb1,
    _hAminus1, _hAminusAplus, _hAminusLow, _hAplusHigh,
    _hsum, _hγlo, _hγhi, _hgap,
    _hvSupport, _haSupport, _hb1Support, _hiI, _hαi⟩
  refine ⟨I, J, J', ?_⟩
  have hleft := mellinSeparation_toComplexArithmeticFunction_convolution
    v (complexPositiveDirichletConvolution a b1)
  have hright := mellinSeparation_toComplexArithmeticFunction_convolution a b1
  calc
    toComplexArithmeticFunction f =
        toComplexArithmeticFunction
          (complexPositiveDirichletConvolution v
            (complexPositiveDirichletConvolution a b1)) := by rw [hfactor]
    _ = toComplexArithmeticFunction v *
          toComplexArithmeticFunction (complexPositiveDirichletConvolution a b1) :=
      hleft
    _ = toComplexArithmeticFunction v *
          (toComplexArithmeticFunction a * toComplexArithmeticFunction b1) := by
      rw [hright]
    _ = toComplexArithmeticFunction v * toComplexArithmeticFunction a *
          toComplexArithmeticFunction b1 := by ring
    _ = _ := by rw [hv, ha, hb1]

/-- For the selected groups in actual type-II source data, the product of the
three finite allocated Dirichlet polynomials on the common source cutoff is
exactly the finite sum of its dyadic-window products. The block count is the
approved `J₀=2⌈log₂(2C)⌉+3`; each coefficient support and quotient cutoff is
derived from the source group's retained support interval. -/
theorem selectedMobiusPTW_actualTypeII_finiteAllocation_eq_dyadicBlockSum
    {X z c δ : ℝ} (hX : 3 ≤ X)
    {f : ComplexPositiveIntegerFunction}
    {fs : List (DyadicArithmeticFactor X)}
    {α : Fin fs.length → ℝ}
    (hdata : largeTypeIIDyadicComponentData z c δ f fs α)
    {d Q q : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q) (T t : ℝ) :
    ∃ (I J J' : Finset (Fin fs.length))
      (i : Fin fs.length) (γ η η' : ℝ),
      i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
      let M₁ := X ^ γ
      let M₂ := X ^ η
      let M₃ := X ^ η'
      let P₁ := Nat.ceil (decompositionC * M₁)
      let P₂ := Nat.ceil (decompositionC * M₂)
      let P₃ := Nat.ceil (decompositionC * M₃)
      let P := P₁ * P₂ * P₃
      let r₁ := (r.1 0).1
      let r₂ := (r.1 1).1
      let r₃ := (r.1 2).1
      let q₁ := q / orderedAllocationPrefix r.1 0
      let q₂ := q / orderedAllocationPrefix r.1 1
      let q₃ := q / orderedAllocationPrefix r.1 2
      let a₁ := toComplexArithmeticFunction
        (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
      let a₂ := toComplexArithmeticFunction
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      let a₃ := toComplexArithmeticFunction
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      finiteAllocatedDirichletPolynomial a₁ r₁ q₁ (Finset.Icc 1 P) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
        finiteAllocatedDirichletPolynomial a₂ r₂ q₂ (Finset.Icc 1 P) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
        finiteAllocatedDirichletPolynomial a₃ r₃ q₃ (Finset.Icc 1 P) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) =
      ∑ i ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
        ∑ j ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
          ∑ k ∈ Finset.range (selectedMobiusPTWDyadicBlockCount decompositionC),
            finiteAllocatedDirichletPolynomial a₁ r₁ q₁
                (factorExtractionRealInterval
                  ((2 : ℝ) ^ i * (M₁ /
                    (4 * decompositionC * (r₁ : ℝ))))
                  (2 * ((2 : ℝ) ^ i * (M₁ /
                    (4 * decompositionC * (r₁ : ℝ)))))) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₂ r₂ q₂
                (factorExtractionRealInterval
                  ((2 : ℝ) ^ j * (M₂ /
                    (4 * decompositionC * (r₂ : ℝ))))
                  (2 * ((2 : ℝ) ^ j * (M₂ /
                    (4 * decompositionC * (r₂ : ℝ)))))) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₃ r₃ q₃
                (factorExtractionRealInterval
                  ((2 : ℝ) ^ k * (M₃ /
                    (4 * decompositionC * (r₃ : ℝ))))
                  (2 * ((2 : ℝ) ^ k * (M₃ /
                    (4 * decompositionC * (r₃ : ℝ)))))) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  classical
  rcases hdata with ⟨_Aminus, _Aplus, v, a, b1, γ, η, η',
    I, J, J', i, _htypeII, _hfactor, hv, ha, hb1,
    _hAminus1, _hAminusAplus, _hAminusLow, _hAplusHigh,
    _hsum, _hγlo, _hγhi, _hgap,
    hvSupport, haSupport, hb1Support, hiI, hαi⟩
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
    have hdivNat := selectedMobiusPTW_divisorCoefficient_two_ge_one hr₁pos
    have hdiv : 1 ≤ (divisorCoefficient 2 r₁ : ℝ) := by exact_mod_cast hdivNat
    have hpow : 0 < (divisorCoefficient 2 r₁ : ℝ) ^ 20 :=
      lt_of_lt_of_le (by norm_num) (one_le_pow₀ hdiv)
    unfold selectedPTWFactorScale
    exact mul_pos (mul_pos (by positivity) hlog) hpow
  have hB₂ : 0 < selectedPTWFactorScale X r₂ := by
    have hlog : 0 < Real.log (8 * X) := by
      exact lt_trans (by norm_num) (log_eightX_gt_one hX)
    have hdivNat := selectedMobiusPTW_divisorCoefficient_two_ge_one hr₂pos
    have hdiv : 1 ≤ (divisorCoefficient 2 r₂ : ℝ) := by exact_mod_cast hdivNat
    have hpow : 0 < (divisorCoefficient 2 r₂ : ℝ) ^ 20 :=
      lt_of_lt_of_le (by norm_num) (one_le_pow₀ hdiv)
    unfold selectedPTWFactorScale
    exact mul_pos (mul_pos (by positivity) hlog) hpow
  have hB₃ : 0 < selectedPTWFactorScale X r₃ := by
    have hlog : 0 < Real.log (8 * X) := by
      exact lt_trans (by norm_num) (log_eightX_gt_one hX)
    have hdivNat := selectedMobiusPTW_divisorCoefficient_two_ge_one hr₃pos
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
  refine ⟨I, J, J', i, γ, η, η', hiI, hαi, ?_⟩
  simpa [M₁, M₂, M₃, P₁, P₂, P₃, P, r₁, r₂, r₃,
    q₁, q₂, q₃, a₁, a₂, a₃] using hblocks

#print axioms selectedMobiusPTW_actualTypeII_finiteAllocation_eq_dyadicBlockSum
#print axioms selectedMobiusPTW_actualTypeII_sourceCoefficient_eq_selectedGroupProduct
#print axioms selectedMobiusPTW_allocatedWindowProduct_eq_sourceTerm

end FractionalPrimes.Literature.DirichletMean

end
