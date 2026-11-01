module

public import FractionalPrimes.Literature.Polynomial.TypeIIGroupedFactorTrilinearBridge
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedDyadicPTWSourceAssembly
public import Mathlib.Tactic

/-! Exact finite bridge from a selected-group factor polynomial to the
allocated Dirichlet polynomial used in the nonunit character expansion. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- Multiplying the normalized selected-group factor polynomial by its exact
source scale gives the finite allocated Mellin sum, provided the coefficient
support is precisely contained in the factor's `(M,2M]` extraction interval.
This support premise is the finite condition that must be checked for an
actual selected group before using the identity. -/
theorem selectedGroupFactorPolynomial_eq_allocatedFinitePolynomial
    {M B T t : ℝ} {r q P Q : ℕ}
    (hM : 0 < M) (hB : 0 < B)
    (a : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q)
    (χcut : ℕ → ℂ)
    (hχcut : ∀ n, χcut n =
      if Nat.Coprime n q then evalInt χ (n : ℤ) else 0)
    (hinterval : factorExtractionRealInterval M (2 * M) ⊆ Finset.Icc 1 P)
    (hsupport : ∀ n ∈ Finset.Icc 1 P,
      n ∉ factorExtractionRealInterval M (2 * M) → a (r * n) = 0) :
    (B : ℂ) * factorPolynomial M
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
      finiteAllocatedDirichletPolynomial a r q (Finset.Icc 1 P) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  classical
  let A := factorExtractionRealInterval M (2 * M)
  let S := Finset.Icc 1 P
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)
  let allocatedTerm : ℕ → ℂ := fun n =>
    a (r * n) * (if Nat.Coprime n q then 1 else 0) *
      evalInt χ (n : ℤ) * (n : ℂ) ^ (-s)
  let extractedTerm : ℕ → ℂ := fun n =>
    a (r * n) * factorExtractionMellinWeight χcut (t - T) n
  have hterm : ∀ n ∈ A, allocatedTerm n = extractedTerm n := by
    intro n hn
    have hnpos : 0 < n := by
      have hn' := (mem_factorExtractionRealInterval hM.le (by positivity) n).1 hn
      have hnR : 0 < (n : ℝ) := lt_trans hM hn'.1
      exact_mod_cast hnR
    have hexp :
        ((-(1 / 2 : ℂ)) - Complex.I * ((t - T : ℝ) : ℂ)) = -s := by
      dsimp [s]
      ring
    unfold allocatedTerm extractedTerm factorExtractionMellinWeight
    rw [dif_pos hnpos, hχcut n, hexp]
    by_cases hcop : Nat.Coprime n q
    · simp only [if_pos hcop, one_mul]
      ring
    · simp only [if_neg hcop, zero_mul, mul_zero]
  have hzero : ∀ n ∈ S, n ∉ A → extractedTerm n = 0 := by
    intro n hn hnA
    have hcoeff : a (r * n) = 0 := hsupport n hn hnA
    simp [extractedTerm, hcoeff]
  have hsum :
      finiteAllocatedDirichletPolynomial a r q S χ s =
        ∑ n ∈ A, extractedTerm n := by
    calc
      finiteAllocatedDirichletPolynomial a r q S χ s =
          ∑ n ∈ S, allocatedTerm n := by
        simp [finiteAllocatedDirichletPolynomial, allocatedTerm, S, s]
      _ = ∑ n ∈ S, extractedTerm n := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hnA : n ∈ A
        · exact hterm n hnA
        · have hcoeff : a (r * n) = 0 := hsupport n hn hnA
          simp [allocatedTerm, extractedTerm, hcoeff]
      _ = ∑ n ∈ A, extractedTerm n :=
        (Finset.sum_subset hinterval hzero).symm
  have hblock := factorPolynomial_eq_selectedGroupMellinBlock
    (t := t) (T := T) hM hB r (fun n => a n) χcut
  calc
    (B : ℂ) * factorPolynomial M
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
        ∑ n ∈ A, extractedTerm n := by
      rw [hblock]
      dsimp [A, extractedTerm]
      field_simp [Complex.ofReal_ne_zero.mpr hB.ne']
    _ = finiteAllocatedDirichletPolynomial a r q S χ s := hsum.symm

set_option maxHeartbeats 1500000 in
/-- The selected dyadic three-group allocation term is the product of the
three exact finite allocated Dirichlet polynomials, provided each selected
group coefficient has the precise quotient support `(Y^alpha,2Y^alpha]` used
by its factorPolynomial. -/
theorem selectedDyadicPTWAllocationTerm_eq_allocatedTriple
    {d Q q P : ℕ} (r : divisorFactorTuples 3 d)
    (χ : BlueprintCharacter Q)
    (X z Y : ℝ) (c : ℂ)
    (fs₁ fs₂ fs₃ : List (DyadicArithmeticFactor X))
    (alpha beta gamma T t : ℝ)
    (hM₁ : 0 < Y ^ alpha) (hM₂ : 0 < Y ^ beta)
    (hM₃ : 0 < Y ^ gamma)
    (hB₁ : 0 < selectedPTWFactorScale X (r.1 0).1)
    (hB₂ : 0 < selectedPTWFactorScale X (r.1 1).1)
    (hB₃ : 0 < selectedPTWFactorScale X (r.1 2).1)
    (hA₁ : factorExtractionRealInterval (Y ^ alpha) (2 * Y ^ alpha) ⊆
      Finset.Icc 1 P)
    (hA₂ : factorExtractionRealInterval (Y ^ beta) (2 * Y ^ beta) ⊆
      Finset.Icc 1 P)
    (hA₃ : factorExtractionRealInterval (Y ^ gamma) (2 * Y ^ gamma) ⊆
      Finset.Icc 1 P)
    (hsupport₁ : ∀ n ∈ Finset.Icc 1 P,
      n ∉ factorExtractionRealInterval (Y ^ alpha) (2 * Y ^ alpha) →
        toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
          ((r.1 0).1 * n) = 0)
    (hsupport₂ : ∀ n ∈ Finset.Icc 1 P,
      n ∉ factorExtractionRealInterval (Y ^ beta) (2 * Y ^ beta) →
        toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs₂) ((r.1 1).1 * n) = 0)
    (hsupport₃ : ∀ n ∈ Finset.Icc 1 P,
      n ∉ factorExtractionRealInterval (Y ^ gamma) (2 * Y ^ gamma) →
        toComplexArithmeticFunction
          (dyadicConvolutionPositiveComplex z fs₃) ((r.1 2).1 * n) = 0) :
    selectedDyadicPTWAllocationTerm q X z Y c fs₁ fs₂ fs₃
        alpha beta gamma T r χ t =
      finiteAllocatedDirichletPolynomial
          (toComplexArithmeticFunction (groupedDyadicFactor z c fs₁))
          (r.1 0).1 (q / orderedAllocationPrefix r.1 0)
          (Finset.Icc 1 P) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
        finiteAllocatedDirichletPolynomial
          (toComplexArithmeticFunction
            (dyadicConvolutionPositiveComplex z fs₂))
          (r.1 1).1 (q / orderedAllocationPrefix r.1 1)
          (Finset.Icc 1 P) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
        finiteAllocatedDirichletPolynomial
          (toComplexArithmeticFunction
            (dyadicConvolutionPositiveComplex z fs₃))
          (r.1 2).1 (q / orderedAllocationPrefix r.1 2)
          (Finset.Icc 1 P) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  let r₁ := (r.1 0).1
  let r₂ := (r.1 1).1
  let r₃ := (r.1 2).1
  let B₁ := selectedPTWFactorScale X r₁
  let B₂ := selectedPTWFactorScale X r₂
  let B₃ := selectedPTWFactorScale X r₃
  let a₁ := toComplexArithmeticFunction (groupedDyadicFactor z c fs₁)
  let a₂ := toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₂)
  let a₃ := toComplexArithmeticFunction (dyadicConvolutionPositiveComplex z fs₃)
  let χ₁ := selectedPTWAllocationCharacterWeight q r χ 0
  let χ₂ := selectedPTWAllocationCharacterWeight q r χ 1
  let χ₃ := selectedPTWAllocationCharacterWeight q r χ 2
  let p₁ := factorPolynomial (Y ^ alpha)
    (selectedGroupTrilinearCoeff B₁ r₁ (fun n => a₁ n) χ₁ T) t
  let p₂ := factorPolynomial (Y ^ beta)
    (selectedGroupTrilinearCoeff B₂ r₂ (fun n => a₂ n) χ₂ T) t
  let p₃ := factorPolynomial (Y ^ gamma)
    (selectedGroupTrilinearCoeff B₃ r₃ (fun n => a₃ n) χ₃ T) t
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)
  have hχ₁ : ∀ n, χ₁ n =
      if Nat.Coprime n (q / orderedAllocationPrefix r.1 0) then
        evalInt χ (n : ℤ) else 0 := by
    intro n
    rfl
  have hχ₂ : ∀ n, χ₂ n =
      if Nat.Coprime n (q / orderedAllocationPrefix r.1 1) then
        evalInt χ (n : ℤ) else 0 := by
    intro n
    rfl
  have hχ₃ : ∀ n, χ₃ n =
      if Nat.Coprime n (q / orderedAllocationPrefix r.1 2) then
        evalInt χ (n : ℤ) else 0 := by
    intro n
    rfl
  have hscale₁ := selectedGroupFactorPolynomial_eq_allocatedFinitePolynomial
    (M := Y ^ alpha) (B := B₁) (T := T) (t := t)
    (r := r₁) (q := q / orderedAllocationPrefix r.1 0) (P := P)
    hM₁ hB₁ a₁ χ χ₁ hχ₁ hA₁ hsupport₁
  have hscale₂ := selectedGroupFactorPolynomial_eq_allocatedFinitePolynomial
    (M := Y ^ beta) (B := B₂) (T := T) (t := t)
    (r := r₂) (q := q / orderedAllocationPrefix r.1 1) (P := P)
    hM₂ hB₂ a₂ χ χ₂ hχ₂ hA₂ hsupport₂
  have hscale₃ := selectedGroupFactorPolynomial_eq_allocatedFinitePolynomial
    (M := Y ^ gamma) (B := B₃) (T := T) (t := t)
    (r := r₃) (q := q / orderedAllocationPrefix r.1 2) (P := P)
    hM₃ hB₃ a₃ χ χ₃ hχ₃ hA₃ hsupport₃
  change ((B₁ * B₂ * B₃ : ℝ) : ℂ) * (p₁ * p₂ * p₃) = _
  calc
    ((B₁ * B₂ * B₃ : ℝ) : ℂ) * (p₁ * p₂ * p₃) =
        ((B₁ : ℂ) * p₁) * ((B₂ : ℂ) * p₂) * ((B₃ : ℂ) * p₃) := by
      push_cast
      ring
    _ =
        finiteAllocatedDirichletPolynomial a₁ r₁
            (q / orderedAllocationPrefix r.1 0) (Finset.Icc 1 P) χ s *
          finiteAllocatedDirichletPolynomial a₂ r₂
            (q / orderedAllocationPrefix r.1 1) (Finset.Icc 1 P) χ s *
          finiteAllocatedDirichletPolynomial a₃ r₃
            (q / orderedAllocationPrefix r.1 2) (Finset.Icc 1 P) χ s := by
      rw [hscale₁, hscale₂, hscale₃]
    _ = _ := by
      rfl

#print axioms selectedGroupFactorPolynomial_eq_allocatedFinitePolynomial
#print axioms selectedDyadicPTWAllocationTerm_eq_allocatedTriple

end FractionalPrimes.Literature.DirichletMean

end
