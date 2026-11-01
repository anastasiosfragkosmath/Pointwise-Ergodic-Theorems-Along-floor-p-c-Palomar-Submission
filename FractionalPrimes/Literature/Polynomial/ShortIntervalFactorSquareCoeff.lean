module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalNormalizedMeanSquare
public import FractionalPrimes.Literature.Polynomial.ShortIntervalNormalizedLargeValues
public import FractionalPrimes.Literature.Polynomial.DirichletMeanConstants
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! The exact finite divisor convolution for squaring a divisor-bounded
Dirichlet factor, isolated from the still-pending normalized level estimate.

Blueprint prerequisite: `expanded-blueprint.tex:5724-5745`, for
`ldm:power-levels`. Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-mean-closure.tex:33-62`.
-/

@[expose] public section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

noncomputable section

/-- The coefficient convolution appearing in the square of a factor supported
on `(N,2N]`, written as a single divisor sum. -/
def factorSquareConvolutionCoefficient (N : ℝ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ u ∈ m.divisors,
    if u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
        m / u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N then
      b u * b (m / u)
    else 0

private lemma divisorCoefficient_two_eq_divisors_card (m : ℕ) :
    FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m = m.divisors.card := by
  change (ArithmeticFunction.zeta ^ 2) m = m.divisors.card
  rw [show (2 : ℕ) = 1 + 1 by omega, pow_succ, pow_one,
    ArithmeticFunction.mul_zeta_apply]
  calc
    (∑ d ∈ m.divisors, ArithmeticFunction.zeta d) =
        ∑ d ∈ m.divisors, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact ArithmeticFunction.zeta_apply_ne
        (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
    _ = m.divisors.card := by simp

private lemma divisorCoefficient_two_mono_of_dvd {u m : ℕ}
    (hum : u ∣ m) (hm : m ≠ 0) :
    FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 u ≤
      FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m := by
  rw [divisorCoefficient_two_eq_divisors_card,
    divisorCoefficient_two_eq_divisors_card]
  apply Finset.card_le_card
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdu, _⟩
  exact Nat.mem_divisors.mpr ⟨dvd_trans hdu hum, hm⟩

private lemma factorSquareTerm_norm_bound
    (C : ℕ) (N : ℝ) (b : ℕ → ℂ) (m u : ℕ)
    (hu : u ∈ m.divisors)
    (hcondition : u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
      m / u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N)
    (hcoeff : ∀ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
      ‖b n‖ ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) :
    ‖b u * b (m / u)‖ ≤
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ (2 * C) := by
  have hum : u ∣ m := (Nat.mem_divisors.mp hu).1
  have hmne : m ≠ 0 := (Nat.mem_divisors.mp hu).2
  have hv : m / u ∣ m := Nat.div_dvd_of_dvd hum
  have hdu := divisorCoefficient_two_mono_of_dvd hum hmne
  have hdv := divisorCoefficient_two_mono_of_dvd hv hmne
  have hduPow :
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 u : ℝ) ^ C ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ C :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hdu) C
  have hdvPow :
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 (m / u) : ℝ) ^ C ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ C :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hdv) C
  have hproduct := mul_le_mul
    (hcoeff u hcondition.1) (hcoeff (m / u) hcondition.2)
    (norm_nonneg (b (m / u))) (pow_nonneg (Nat.cast_nonneg _) C)
  have hdivisorProduct := mul_le_mul hduPow hdvPow
    (pow_nonneg (Nat.cast_nonneg _) C) (pow_nonneg (Nat.cast_nonneg _) C)
  calc
    ‖b u * b (m / u)‖ = ‖b u‖ * ‖b (m / u)‖ := norm_mul _ _
    _ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 u : ℝ) ^ C *
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 (m / u) : ℝ) ^ C :=
      hproduct
    _ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ C *
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ C :=
      hdivisorProduct
    _ = (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ (2 * C) := by
      rw [← pow_add]
      congr 1
      omega

/-- The exact divisor bound for coefficients of the square polynomial. -/
theorem factorSquareConvolutionCoefficient_bound
    (C : ℕ) (N : ℝ) (b : ℕ → ℂ) (m : ℕ)
    (hcoeff : ∀ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
      ‖b n‖ ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) :
    ‖factorSquareConvolutionCoefficient N b m‖ ≤
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ (2 * C + 1) := by
  classical
  let D : ℝ :=
    (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ)
  have hterm (u : ℕ) (hu : u ∈ m.divisors) :
      ‖(if u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
          m / u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N then
        b u * b (m / u) else 0)‖ ≤ D ^ (2 * C) := by
    by_cases hcondition : u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
        m / u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N
    · simp only [if_pos hcondition]
      simpa [D] using factorSquareTerm_norm_bound C N b m u hu hcondition hcoeff
    · simp [hcondition, D]
  have hcard :
      (m.divisors.card : ℝ) =
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) := by
    exact_mod_cast (divisorCoefficient_two_eq_divisors_card m).symm
  unfold factorSquareConvolutionCoefficient
  calc
    ‖∑ u ∈ m.divisors,
        if u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
            m / u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N then
          b u * b (m / u) else 0‖ ≤
      ∑ u ∈ m.divisors,
        ‖if u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
            m / u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N then
          b u * b (m / u) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ m.divisors, D ^ (2 * C) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hterm u hu
    _ = (m.divisors.card : ℝ) * D ^ (2 * C) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = D * D ^ (2 * C) := by rw [hcard]
    _ = D ^ (2 * C + 1) := by
      calc
        D * D ^ (2 * C) = D ^ (2 * C) * D := by ring
        _ = D ^ (2 * C + 1) := by rw [pow_succ]
    _ = (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ (2 * C + 1) := by
      rfl

private lemma factorSquareConvolutionCoefficient_eq_antidiagonal
    (N : ℝ) (coeff : ℕ → ℂ) (m : ℕ) :
    factorSquareConvolutionCoefficient N coeff m =
      ∑ p ∈ m.divisorsAntidiagonal,
        if p.1 ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
            p.2 ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N then
          coeff p.1 * coeff p.2 else 0 := by
  classical
  unfold factorSquareConvolutionCoefficient
  rw [← Nat.sum_divisorsAntidiagonal
    (f := fun u v =>
      if u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
          v ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N then
        coeff u * coeff v else 0)]

private lemma dirichletIndices_mem_iff {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ↔
      N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  classical
  rw [FractionalPrimes.Literature.LargeValues.dirichletIndices,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, hleft⟩
    have hfloor : (n : ℝ) ≤ Nat.floor (2 * N) := by
      exact_mod_cast (Nat.le_of_lt_succ hn)
    exact ⟨hleft, le_trans hfloor (Nat.floor_le (by positivity))⟩
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, hleft⟩
    have hfloor : n ≤ Nat.floor (2 * N) := Nat.le_floor hright
    omega

private lemma factorSquareConvolutionCoefficient_eq_pairFiber
    (N : ℝ) (coeff : ℕ → ℂ) (m : ℕ) (hN : 0 ≤ N) :
    factorSquareConvolutionCoefficient N coeff m =
      ∑ p ∈ ((FractionalPrimes.Literature.LargeValues.dirichletIndices N) ×ˢ
        (FractionalPrimes.Literature.LargeValues.dirichletIndices N)).filter
          (fun p => p.1 * p.2 = m), coeff p.1 * coeff p.2 := by
  classical
  rw [factorSquareConvolutionCoefficient_eq_antidiagonal]
  have hsets :
      m.divisorsAntidiagonal.filter
          (fun p => p.1 ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N ∧
            p.2 ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N) =
        ((FractionalPrimes.Literature.LargeValues.dirichletIndices N) ×ˢ
          (FractionalPrimes.Literature.LargeValues.dirichletIndices N)).filter
          (fun p => p.1 * p.2 = m) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal,
      Finset.mem_product]
    constructor
    · rintro ⟨⟨hprod, hmne⟩, hpI, hqI⟩
      exact ⟨⟨hpI, hqI⟩, hprod⟩
    · rintro ⟨⟨hpI, hqI⟩, hprod⟩
      have hpPos : 0 < p.1 := by
        have := (dirichletIndices_mem_iff hN p.1).mp hpI
        exact_mod_cast (lt_of_le_of_lt hN this.1)
      have hqPos : 0 < p.2 := by
        have := (dirichletIndices_mem_iff hN p.2).mp hqI
        exact_mod_cast (lt_of_le_of_lt hN this.1)
      exact ⟨⟨hprod, by
        intro heq
        have : p.1 * p.2 = 0 := by simpa [heq] using hprod
        exact (Nat.mul_pos hpPos hqPos).ne' this⟩, hpI, hqI⟩
  rw [← Finset.sum_filter, hsets]

private lemma factorSquare_product_mem_blocks
    {N : ℝ} (hN : 2 ≤ N) {u v : ℕ}
    (hu : u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N)
    (hv : v ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N) :
    u * v ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices (N ^ 2) ∪
      FractionalPrimes.Literature.LargeValues.dirichletIndices (2 * N ^ 2) := by
  have hN0 : 0 ≤ N := by linarith
  rcases (dirichletIndices_mem_iff hN0 u).mp hu with ⟨huLo, huHi⟩
  rcases (dirichletIndices_mem_iff hN0 v).mp hv with ⟨hvLo, hvHi⟩
  have huPos : 0 < (u : ℝ) := lt_trans (by linarith) huLo
  have hvPos : 0 < (v : ℝ) := lt_trans (by linarith) hvLo
  have hNpos : 0 < N := by linarith
  have hprodLo : N ^ 2 < (u * v : ℝ) := by
    have h1 : N * N < N * (v : ℝ) :=
      mul_lt_mul_of_pos_left hvLo hNpos
    have h2 : N * (v : ℝ) < (u : ℝ) * v :=
      mul_lt_mul_of_pos_right huLo hvPos
    calc
      N ^ 2 = N * N := by ring
      _ < N * (v : ℝ) := h1
      _ < (u : ℝ) * v := h2
  have hprodHi : (u * v : ℝ) ≤ 4 * N ^ 2 := by
    have h := mul_le_mul huHi hvHi (le_of_lt hvPos) (by positivity : 0 ≤ 2 * N)
    nlinarith [show (u * v : ℝ) = (u : ℝ) * (v : ℝ) by norm_num]
  by_cases hmid : (u * v : ℝ) ≤ 2 * N ^ 2
  · apply Finset.mem_union.mpr
    left
    apply (dirichletIndices_mem_iff (sq_nonneg N) (u * v)).mpr
    exact ⟨by simpa [Nat.cast_mul] using hprodLo,
      by simpa [Nat.cast_mul] using hmid⟩
  · apply Finset.mem_union.mpr
    right
    apply (dirichletIndices_mem_iff (by positivity : 0 ≤ 2 * N ^ 2) (u * v)).mpr
    constructor
    · simpa [Nat.cast_mul] using (lt_of_not_ge hmid)
    · have hupper : (u * v : ℝ) ≤ 2 * (2 * N ^ 2) := by nlinarith [hprodHi]
      simpa [Nat.cast_mul] using hupper

private lemma factorSquarePairTerm_eq
    (N : ℝ) (coeff : ℕ → ℂ) (u v m : ℕ) (t : ℝ)
    (hN : 0 ≤ N)
    (hu : u ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N)
    (hv : v ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N)
    (hprod : u * v = m) :
    FractionalPrimes.Literature.LargeValues.dirichletTerm
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) u t *
      FractionalPrimes.Literature.LargeValues.dirichletTerm
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) v t =
      (coeff u * coeff v / (Real.sqrt (m : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) := by
  have huBounds := (dirichletIndices_mem_iff hN u).mp hu
  have hvBounds := (dirichletIndices_mem_iff hN v).mp hv
  have huPos : 0 < (u : ℝ) := lt_of_le_of_lt hN huBounds.1
  have hvPos : 0 < (v : ℝ) := lt_of_le_of_lt hN hvBounds.1
  have hmCast : (m : ℝ) = (u : ℝ) * (v : ℝ) := by
    exact_mod_cast hprod.symm
  have hroot : Real.sqrt (m : ℝ) =
      Real.sqrt (u : ℝ) * Real.sqrt (v : ℝ) := by
    rw [hmCast, Real.sqrt_mul (le_of_lt huPos)]
  have hlog : Real.log (m : ℝ) =
      Real.log (u : ℝ) + Real.log (v : ℝ) := by
    rw [hmCast, Real.log_mul huPos.ne' hvPos.ne']
  have hcoef :
      (coeff u / (Real.sqrt (u : ℝ) : ℂ)) *
          (coeff v / (Real.sqrt (v : ℝ) : ℂ)) =
        coeff u * coeff v / (Real.sqrt (m : ℝ) : ℂ) := by
    rw [hroot]
    have huRoot : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.2 huPos
    have hvRoot : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvPos
    field_simp [ne_of_gt huRoot, ne_of_gt hvRoot]
    <;> push_cast
    <;> ring
  have hphase :
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log (u : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * (t : ℂ) * (Real.log (v : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hlog]
    push_cast
    ring
  change
    (coeff u / (Real.sqrt (u : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (u : ℝ) : ℂ))) *
      (coeff v / (Real.sqrt (v : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (v : ℝ) : ℂ))) = _
  calc
    _ =
        ((coeff u / (Real.sqrt (u : ℝ) : ℂ)) *
          (coeff v / (Real.sqrt (v : ℝ) : ℂ))) *
          (Complex.exp (-Complex.I * (t : ℂ) * (Real.log (u : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * (t : ℂ) * (Real.log (v : ℝ) : ℂ))) := by ring
    _ = _ := by rw [hcoef, hphase]

private lemma factorSquareFiberTerm_eq
    (N : ℝ) (coeff : ℕ → ℂ) (m : ℕ) (t : ℝ) (hN : 2 ≤ N)
    (hm : m ∈
      FractionalPrimes.Literature.LargeValues.dirichletIndices (N ^ 2) ∪
        FractionalPrimes.Literature.LargeValues.dirichletIndices (2 * N ^ 2)) :
    (∑ p ∈ ((FractionalPrimes.Literature.LargeValues.dirichletIndices N) ×ˢ
        (FractionalPrimes.Literature.LargeValues.dirichletIndices N)).filter
          (fun p => p.1 * p.2 = m),
      FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
          p.1 t *
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
          p.2 t) =
      FractionalPrimes.Literature.LargeValues.dirichletTerm
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
          (factorSquareConvolutionCoefficient N coeff)) m t := by
  classical
  have hNpos : 0 < N := by linarith
  have hmpos : 0 < (m : ℝ) := by
    rcases Finset.mem_union.mp hm with hm | hm
    · have hm' := (dirichletIndices_mem_iff (sq_nonneg N) m).mp hm
      exact lt_trans (pow_pos hNpos 2) hm'.1
    · have hm' :=
        (dirichletIndices_mem_iff (by positivity : 0 ≤ 2 * N ^ 2) m).mp hm
      exact lt_trans (by positivity : 0 < 2 * N ^ 2) hm'.1
  have hcoeffFiber := factorSquareConvolutionCoefficient_eq_pairFiber
    N coeff m (by linarith)
  let F := ((FractionalPrimes.Literature.LargeValues.dirichletIndices N) ×ˢ
    (FractionalPrimes.Literature.LargeValues.dirichletIndices N)).filter
      (fun p => p.1 * p.2 = m)
  let phase := Complex.exp (-Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ))
  have hterm (p : ℕ × ℕ) (hp : p ∈ F) :
      FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
          p.1 t *
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
          p.2 t =
        (coeff p.1 * coeff p.2 / (Real.sqrt (m : ℝ) : ℂ)) * phase := by
    have hp' := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hp'.1 with ⟨hpI, hqI⟩
    simpa [phase] using factorSquarePairTerm_eq N coeff p.1 p.2 m t
      (by linarith [hN]) hpI hqI hp'.2
  calc
    _ = ∑ p ∈ F,
        (coeff p.1 * coeff p.2 / (Real.sqrt (m : ℝ) : ℂ)) * phase := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm p hp
    _ = (∑ p ∈ F, coeff p.1 * coeff p.2 /
          (Real.sqrt (m : ℝ) : ℂ)) * phase := by
      rw [← Finset.sum_mul]
    _ = ((∑ p ∈ F, coeff p.1 * coeff p.2) /
          (Real.sqrt (m : ℝ) : ℂ)) * phase := by
      rw [← Finset.sum_div]
    _ = (factorSquareConvolutionCoefficient N coeff m /
          (Real.sqrt (m : ℝ) : ℂ)) * phase := by
      rw [← hcoeffFiber]
    _ = FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (factorSquareConvolutionCoefficient N coeff)) m t := by
      simp [phase, FractionalPrimes.Literature.LargeValues.dirichletTerm,
        FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff]

private lemma factorPolynomial_square_eq_twoBlocks
    (N : ℝ) (coeff : ℕ → ℂ) (t : ℝ) (hN : 2 ≤ N) :
    factorPolynomial N coeff t ^ 2 =
      FractionalPrimes.Literature.LargeValues.dirichletPolynomial (N ^ 2)
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (factorSquareConvolutionCoefficient N coeff)) t +
        FractionalPrimes.Literature.LargeValues.dirichletPolynomial (2 * N ^ 2)
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (factorSquareConvolutionCoefficient N coeff)) t := by
  classical
  let I := FractionalPrimes.Literature.LargeValues.dirichletIndices N
  let M := FractionalPrimes.Literature.LargeValues.dirichletIndices (N ^ 2) ∪
    FractionalPrimes.Literature.LargeValues.dirichletIndices (2 * N ^ 2)
  let g : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let pairTerm (p : ℕ × ℕ) :=
    FractionalPrimes.Literature.LargeValues.dirichletTerm
      (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) p.1 t *
    FractionalPrimes.Literature.LargeValues.dirichletTerm
      (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) p.2 t
  have hmaps : ∀ p ∈ I ×ˢ I, g p ∈ M := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    exact factorSquare_product_mem_blocks hN hp1 hp2
  have hexpand : factorPolynomial N coeff t ^ 2 =
      ∑ p ∈ I ×ˢ I, pairTerm p := by
    unfold factorPolynomial
    unfold FractionalPrimes.Literature.LargeValues.dirichletPolynomial
    change
      (∑ n ∈ I,
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) n t) ^ 2 = _
    calc
      _ =
          (∑ n ∈ I,
            FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) n t) *
          (∑ n ∈ I,
            FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) n t) := by
        ring
      _ = ∑ n ∈ I, ∑ m ∈ I,
          FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) n t *
            FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) m t := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
      _ = ∑ p ∈ I ×ˢ I,
          FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) p.1 t *
            FractionalPrimes.Literature.LargeValues.dirichletTerm
              (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) p.2 t := by
        rw [Finset.sum_product]
      _ = ∑ p ∈ I ×ˢ I, pairTerm p := by rfl
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := I ×ˢ I) (t := M) (g := g) hmaps pairTerm
  have hfiber (m : ℕ) (hm : m ∈ M) :
      (∑ p ∈ I ×ˢ I with g p = m, pairTerm p) =
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (factorSquareConvolutionCoefficient N coeff)) m t := by
    change
      (∑ p ∈ (I ×ˢ I).filter (fun p => p.1 * p.2 = m), pairTerm p) = _
    simpa [M, I, pairTerm] using
      factorSquareFiberTerm_eq N coeff m t hN hm
  have hdisj :
      Disjoint
        (FractionalPrimes.Literature.LargeValues.dirichletIndices (N ^ 2))
        (FractionalPrimes.Literature.LargeValues.dirichletIndices (2 * N ^ 2)) := by
    apply Finset.disjoint_left.mpr
    intro m hm₁ hm₂
    have h₁ := (dirichletIndices_mem_iff (sq_nonneg N) m).mp hm₁
    have h₂ :=
      (dirichletIndices_mem_iff (by positivity : 0 ≤ 2 * N ^ 2) m).mp hm₂
    linarith
  calc
    factorPolynomial N coeff t ^ 2 = ∑ p ∈ I ×ˢ I, pairTerm p := hexpand
    _ = ∑ m ∈ M, ∑ p ∈ I ×ˢ I with g p = m, pairTerm p := hgroup.symm
    _ = ∑ m ∈ M,
        FractionalPrimes.Literature.LargeValues.dirichletTerm
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
            (factorSquareConvolutionCoefficient N coeff)) m t := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hfiber m hm
    _ =
        (∑ m ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices (N ^ 2),
          FractionalPrimes.Literature.LargeValues.dirichletTerm
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
              (factorSquareConvolutionCoefficient N coeff)) m t) +
        ∑ m ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices (2 * N ^ 2),
          FractionalPrimes.Literature.LargeValues.dirichletTerm
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff
              (factorSquareConvolutionCoefficient N coeff)) m t := by
      simp only [M]
      rw [Finset.sum_union hdisj]
    _ = _ := by
      simp [FractionalPrimes.Literature.LargeValues.dirichletPolynomial]

private theorem normalizedLevelSetMeasureBound_empty
    (D : ℕ) (M T W : ℝ) (coeff : ℕ → ℂ)
    (hM : 2 ≤ M) (hT : 2 ≤ T) (hW : 0 < W)
    (hcoeff : ∀ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices M,
      ‖coeff n‖ ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ D) :
    MeasureTheory.volume.real
        (FractionalPrimes.Literature.LargeValues.dirichletLevelSet M T W
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≤
      2 * (2 : ℝ) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent D + 28) *
        Real.log (4 * M * T) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent D + 1) *
        (M / W ^ 2 + T * min (1 / W ^ 2) (M / W ^ 6)) := by
  have hbound := FractionalPrimes.Literature.LargeValues.normalizedDivisorBound
    D M T W coeff 0 Fin.elim0 hM hT hW
    (by intro j; exact Fin.elim0 j)
    (by intro i j hij; exact Fin.elim0 i)
    hcoeff (by intro j; exact Fin.elim0 j)
  simpa [mul_assoc] using hbound.2.2

private lemma log_fourNT_le_three_log_fourX
    (X N T : ℝ) (hX : 2 ^ 16 ≤ X) (hNX : N ≤ X) (hTX : T ≤ X)
    (hN : 0 < N) (hT : 0 < T) :
    Real.log (4 * N * T) ≤ 3 * Real.log (4 * X) := by
  have hXpos : 0 < X := by positivity
  have hNT : N * T ≤ X * X :=
    mul_le_mul hNX hTX (le_of_lt hT) (le_of_lt hXpos)
  have hargPos : 0 < 4 * N * T := by positivity
  have hbigPos : 0 < (4 * X) ^ 2 := by positivity
  have harg : 4 * N * T ≤ (4 * X) ^ 2 := by nlinarith [hNT]
  have hlog := Real.log_le_log hargPos harg
  have hpow : Real.log ((4 * X) ^ 2) = 2 * Real.log (4 * X) := by
    rw [Real.log_pow]
    norm_num
  have hL : 0 ≤ Real.log (4 * X) :=
    Real.log_nonneg (by nlinarith [hX])
  rw [hpow] at hlog
  nlinarith

private lemma log_eightN2T_le_three_log_fourX
    (X N T : ℝ) (hX : 2 ^ 16 ≤ X) (hNX : N ≤ X) (hTX : T ≤ X)
    (hN : 0 < N) (hT : 0 < T) :
    Real.log (8 * N ^ 2 * T) ≤ 3 * Real.log (4 * X) := by
  have hXpos : 0 < X := by positivity
  have hN2 : N ^ 2 ≤ X ^ 2 := by
    nlinarith [sq_nonneg (X - N), hNX]
  have hN2T : N ^ 2 * T ≤ X ^ 2 * X :=
    mul_le_mul hN2 hTX (le_of_lt hT) (sq_nonneg X)
  have hargPos : 0 < 8 * N ^ 2 * T := by positivity
  have hbigPos : 0 < (4 * X) ^ 3 := by positivity
  have harg : 8 * N ^ 2 * T ≤ (4 * X) ^ 3 := by nlinarith [hN2T]
  have hlog := Real.log_le_log hargPos harg
  have hpow : Real.log ((4 * X) ^ 3) = 3 * Real.log (4 * X) := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hlog
  exact hlog

private lemma K_dominates_singleLevelLogPrefactor (C : ℕ) :
    2 * (2 : ℝ) ^
        (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) *
        (3 : ℝ) ^ b C ≤ K C := by
  have hexp :
      3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 29 ≤
        b C + 40 := by
    have hD := normalizedDivisorExponent_le_E C
    dsimp [b]
    omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  calc
    2 * (2 : ℝ) ^
        (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) *
        (3 : ℝ) ^ b C =
        (2 : ℝ) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 29) *
          (3 : ℝ) ^ b C := by rw [pow_succ]; ring
    _ ≤ (2 : ℝ) ^ (b C + 40) * (3 : ℝ) ^ b C :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = K C := rfl

private lemma factorSquareThresholdKernel_bound
    (N T V : ℝ) (hV : 0 < V) (hT : 0 ≤ T) :
    (N ^ 2 / (V ^ 2 / 2) ^ 2 +
      T * min (1 / (V ^ 2 / 2) ^ 2) (N ^ 2 / (V ^ 2 / 2) ^ 6)) +
      (2 * N ^ 2 / (V ^ 2 / 2) ^ 2 +
        T * min (1 / (V ^ 2 / 2) ^ 2) (2 * N ^ 2 / (V ^ 2 / 2) ^ 6)) ≤
      192 * (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
  have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV.ne'
  have hV4 : V ^ 4 ≠ 0 := pow_ne_zero 4 hV.ne'
  have hV12 : V ^ 12 ≠ 0 := pow_ne_zero 12 hV.ne'
  have hW2 : (V ^ 2 / 2) ^ 2 = V ^ 4 / 4 := by ring
  have hW6 : (V ^ 2 / 2) ^ 6 = V ^ 12 / 64 := by ring
  have hInv2 : 1 / (V ^ 2 / 2) ^ 2 = 4 / V ^ 4 := by
    rw [hW2]
    field_simp [hV4]
  have hInv6₁ : N ^ 2 / (V ^ 2 / 2) ^ 6 = 64 * N ^ 2 / V ^ 12 := by
    rw [hW6]
    field_simp [hV12]
  have hInv6₂ : 2 * N ^ 2 / (V ^ 2 / 2) ^ 6 = 128 * N ^ 2 / V ^ 12 := by
    rw [hW6]
    field_simp [hV12]
    <;> ring
  have hFirst₁ : N ^ 2 / (V ^ 2 / 2) ^ 2 = 4 * N ^ 2 / V ^ 4 := by
    rw [hW2]
    field_simp [hV4]
  have hFirst₂ : 2 * N ^ 2 / (V ^ 2 / 2) ^ 2 = 8 * N ^ 2 / V ^ 4 := by
    rw [hW2]
    field_simp [hV4]
    <;> ring
  let a : ℝ := 4 / V ^ 4
  let b' : ℝ := 64 * N ^ 2 / V ^ 12
  let c' : ℝ := 128 * N ^ 2 / V ^ 12
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b' := by dsimp [b']; positivity
  have hc : 0 ≤ c' := by dsimp [c']; positivity
  have hminSum : min a b' + min a c' ≤ min (2 * a) (b' + c') := by
    apply le_min
    · calc
        min a b' + min a c' ≤ a + a := add_le_add (min_le_left a b') (min_le_left a c')
        _ = 2 * a := by ring
    · exact add_le_add (min_le_right a b') (min_le_right a c')
  have hscaledMin :
      min (2 * a) (b' + c') ≤ 192 * min (1 / V ^ 4) (N ^ 2 / V ^ 12) := by
    have htwice : 2 * a = 8 / V ^ 4 := by dsimp [a]; ring
    have hsum : b' + c' = 192 * (N ^ 2 / V ^ 12) := by dsimp [b', c']; ring
    rw [htwice, hsum]
    have hleft : min (8 / V ^ 4) (192 * (N ^ 2 / V ^ 12)) ≤
        192 * (1 / V ^ 4) := by
      calc
        min (8 / V ^ 4) (192 * (N ^ 2 / V ^ 12)) ≤ 8 / V ^ 4 := min_le_left _ _
        _ ≤ 192 * (1 / V ^ 4) := by
          calc
            8 / V ^ 4 = 8 * (1 / V ^ 4) := by ring
            _ ≤ 192 * (1 / V ^ 4) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hright : min (8 / V ^ 4) (192 * (N ^ 2 / V ^ 12)) ≤
        192 * (N ^ 2 / V ^ 12) := min_le_right _ _
    have hminMul :
        min (192 * (1 / V ^ 4)) (192 * (N ^ 2 / V ^ 12)) =
          192 * min (1 / V ^ 4) (N ^ 2 / V ^ 12) := by
      rcases le_total (1 / V ^ 4) (N ^ 2 / V ^ 12) with hxy | hyx
      · rw [min_eq_left (mul_le_mul_of_nonneg_left hxy (by norm_num)),
          min_eq_left hxy]
      · rw [min_eq_right (mul_le_mul_of_nonneg_left hyx (by norm_num)),
          min_eq_right hyx]
    exact (le_min hleft hright).trans_eq hminMul
  rw [hInv2, hInv6₁, hInv6₂, hFirst₁, hFirst₂]
  have hminTarget :
      min (4 / V ^ 4) (64 * N ^ 2 / V ^ 12) +
        min (4 / V ^ 4) (128 * N ^ 2 / V ^ 12) ≤
        192 * min (1 / V ^ 4) (N ^ 2 / V ^ 12) := by
    have hmin' := hminSum.trans hscaledMin
    simpa [a, b', c'] using hmin'
  have hNnonneg : 0 ≤ N ^ 2 / V ^ 4 := by positivity
  have hTmin' := mul_le_mul_of_nonneg_left hminTarget hT
  calc
    _ = 12 * (N ^ 2 / V ^ 4) +
        T * (min (4 / V ^ 4) (64 * N ^ 2 / V ^ 12) +
          min (4 / V ^ 4) (128 * N ^ 2 / V ^ 12)) := by
      ring
    _ ≤ 12 * (N ^ 2 / V ^ 4) +
        T * (192 * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
      nlinarith [hTmin']
    _ ≤ 192 * (N ^ 2 / V ^ 4 +
        T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by nlinarith

private lemma log_fourX_ge_one (X : ℝ) (hX : 2 ^ 16 ≤ X) :
    1 ≤ Real.log (4 * X) := by
  have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
    have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ)) (by norm_num)
    norm_num at h
    linarith
  have h4X : 4 ≤ 4 * X := by nlinarith [hX]
  exact hlog4.trans (Real.log_le_log (by norm_num) (by nlinarith [h4X]))

private lemma power_le_threeL_power
    (A L : ℝ) (e b' : ℕ) (hA : 0 ≤ A) (hA3 : A ≤ 3 * L)
    (hL : 1 ≤ L) (he : e ≤ b') :
    A ^ e ≤ (3 * L) ^ b' := by
  have h3L : 1 ≤ 3 * L := by linarith
  calc
    A ^ e ≤ (3 * L) ^ e := pow_le_pow_left₀ hA hA3 e
    _ ≤ (3 * L) ^ b' := pow_le_pow_right₀ h3L he

private theorem factorLevelSetBound_k1
    (C : ℕ) (N T X V : ℝ) (coeff : ℕ → ℂ)
    (hX : 2 ^ 16 ≤ X) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hNX : N ≤ X) (hTX : T ≤ X) (hV : 0 < V)
    (hcoeff : factorCoefficientBound C N coeff) :
    MeasureTheory.volume.real
        (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≤
      K C * Real.log (4 * X) ^ b C *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
  have hnorm := normalizedLevelSetMeasureBound_empty C N T V coeff hN hT hV hcoeff
  have hNpos : 0 < N := by linarith
  have hTpos : 0 < T := by linarith
  have hlog := log_fourNT_le_three_log_fourX X N T hX hNX hTX hNpos hTpos
  have hL : 1 ≤ Real.log (4 * X) := log_fourX_ge_one X hX
  have hArg : 1 ≤ 4 * N * T := by nlinarith [hN, hT]
  have hArgLog : 0 ≤ Real.log (4 * N * T) := Real.log_nonneg hArg
  have hExp := (normalizedLogExponent_bounds C).1
  have hlogpow := power_le_threeL_power (Real.log (4 * N * T))
    (Real.log (4 * X))
    (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 1)
    (b C) hArgLog hlog hL hExp
  have hkernel : 0 ≤ N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6) := by positivity
  have hconst := K_dominates_singleLevelLogPrefactor C
  have hprefNonneg : 0 ≤ 2 * (2 : ℝ) ^
      (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) := by
    positivity
  calc
    _ ≤ 2 * (2 : ℝ) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) *
        Real.log (4 * N * T) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 1) *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := hnorm
    _ ≤ 2 * (2 : ℝ) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) *
        (3 * Real.log (4 * X)) ^ b C *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
      apply mul_le_mul_of_nonneg_right _ hkernel
      exact mul_le_mul_of_nonneg_left hlogpow hprefNonneg
    _ = (2 * (2 : ℝ) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) *
          (3 : ℝ) ^ b C) * Real.log (4 * X) ^ b C *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
      rw [mul_pow]
      ring
    _ ≤ K C * Real.log (4 * X) ^ b C *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity)

private theorem factorLevelSetBound_k2
    (C : ℕ) (N T X V : ℝ) (coeff : ℕ → ℂ)
    (hX : 2 ^ 16 ≤ X) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hNX : N ≤ X) (hTX : T ≤ X) (hV : 0 < V)
    (hcoeff : factorCoefficientBound C N coeff) :
    MeasureTheory.volume.real
        (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≤
      K C * Real.log (4 * X) ^ b C *
        (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
  classical
  let c := factorSquareConvolutionCoefficient N coeff
  let ac := FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff c
  let W := V ^ 2 / 2
  let E₀ := FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
    (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
  let E₁ := FractionalPrimes.Literature.LargeValues.dirichletLevelSet (N ^ 2) T W ac
  let E₂ := FractionalPrimes.Literature.LargeValues.dirichletLevelSet (2 * N ^ 2) T W ac
  have hNpos : 0 < N := by linarith
  have hTpos : 0 < T := by linarith
  have hW : 0 < W := by dsimp [W]; positivity
  have hcBound : ∀ m ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices (N ^ 2),
      ‖c m‖ ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ (2 * C + 1) := by
    intro m hm
    exact factorSquareConvolutionCoefficient_bound C N coeff m hcoeff
  have hcBound₂ : ∀ m ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices (2 * N ^ 2),
      ‖c m‖ ≤
        (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 m : ℝ) ^ (2 * C + 1) := by
    intro m hm
    exact factorSquareConvolutionCoefficient_bound C N coeff m hcoeff
  have hNsq : 2 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - 2)]
  have h2Nsq : 2 ≤ 2 * N ^ 2 := by nlinarith [sq_nonneg N]
  have hblock₁ := normalizedLevelSetMeasureBound_empty
    (2 * C + 1) (N ^ 2) T W c hNsq hT hW hcBound
  have hblock₂ := normalizedLevelSetMeasureBound_empty
    (2 * C + 1) (2 * N ^ 2) T W c h2Nsq hT hW hcBound₂
  have hEexp :
      FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent (2 * C + 1) = E C :=
    (E_eq_normalizedDivisorExponent_square C).symm
  have hLogExponent :
      3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent (2 * C + 1) + 1 =
        b C := by
    rw [hEexp]
    rfl
  have hblock₁' :
      MeasureTheory.volume.real E₁ ≤
        2 * (2 : ℝ) ^ (3 * E C + 28) *
          Real.log (4 * N ^ 2 * T) ^ (3 * E C + 1) *
            (N ^ 2 / W ^ 2 + T * min (1 / W ^ 2) (N ^ 2 / W ^ 6)) := by
    simpa [E₁, ac, c, hEexp] using hblock₁
  have hblock₂' :
      MeasureTheory.volume.real E₂ ≤
        2 * (2 : ℝ) ^ (3 * E C + 28) *
          Real.log (8 * N ^ 2 * T) ^ (3 * E C + 1) *
            (2 * N ^ 2 / W ^ 2 + T * min (1 / W ^ 2) (2 * N ^ 2 / W ^ 6)) := by
    have harg : 4 * (2 * N ^ 2) * T = 8 * N ^ 2 * T := by ring
    simpa [E₂, ac, c, hEexp, harg] using hblock₂
  have hlogblock := log_eightN2T_le_three_log_fourX X N T hX hNX hTX hNpos hTpos
  have hlogblock' : Real.log (8 * N ^ 2 * T) ≤ 3 * Real.log (4 * X) := by
    convert hlogblock using 1 <;> congr 1 <;> ring
  have hlog₁arg : 0 < 4 * N ^ 2 * T := by positivity
  have hlog₂arg : 0 < 8 * N ^ 2 * T := by positivity
  have hlog₁base : 0 ≤ Real.log (4 * N ^ 2 * T) :=
    Real.log_nonneg (by nlinarith [hN, hT])
  have hlog₂base : 0 ≤ Real.log (8 * N ^ 2 * T) :=
    Real.log_nonneg (by nlinarith [hN, hT])
  have hlog₁le : Real.log (4 * N ^ 2 * T) ≤ Real.log (8 * N ^ 2 * T) :=
    Real.log_le_log hlog₁arg (by nlinarith [hlog₁arg])
  have hL : 1 ≤ Real.log (4 * X) := log_fourX_ge_one X hX
  have hlogpow₁ : Real.log (4 * N ^ 2 * T) ^ (3 * E C + 1) ≤
      (3 * Real.log (4 * X)) ^ (3 * E C + 1) := by
    calc
      Real.log (4 * N ^ 2 * T) ^ (3 * E C + 1) ≤ Real.log (8 * N ^ 2 * T) ^ (3 * E C + 1) :=
        pow_le_pow_left₀ hlog₁base hlog₁le (3 * E C + 1)
      _ ≤ (3 * Real.log (4 * X)) ^ (3 * E C + 1) :=
        pow_le_pow_left₀ hlog₂base hlogblock' (3 * E C + 1)
  have hlogpow₂ : Real.log (8 * N ^ 2 * T) ^ (3 * E C + 1) ≤
      (3 * Real.log (4 * X)) ^ (3 * E C + 1) :=
    pow_le_pow_left₀ hlog₂base hlogblock' (3 * E C + 1)
  let ker₁ := N ^ 2 / W ^ 2 + T * min (1 / W ^ 2) (N ^ 2 / W ^ 6)
  let ker₂ := 2 * N ^ 2 / W ^ 2 + T * min (1 / W ^ 2) (2 * N ^ 2 / W ^ 6)
  let pref := 2 * (2 : ℝ) ^ (3 * E C + 28)
  have hker₁ : 0 ≤ ker₁ := by dsimp [ker₁]; positivity
  have hker₂ : 0 ≤ ker₂ := by dsimp [ker₂]; positivity
  have hblocks : MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ ≤
      pref * (3 * Real.log (4 * X)) ^ (3 * E C + 1) * (ker₁ + ker₂) := by
    calc
      _ ≤ pref * Real.log (4 * N ^ 2 * T) ^ (3 * E C + 1) * ker₁ +
          pref * Real.log (8 * N ^ 2 * T) ^ (3 * E C + 1) * ker₂ :=
        add_le_add hblock₁' hblock₂'
      _ ≤ pref * (3 * Real.log (4 * X)) ^ (3 * E C + 1) * ker₁ +
          pref * (3 * Real.log (4 * X)) ^ (3 * E C + 1) * ker₂ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogpow₁ (by positivity)) hker₁
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogpow₂ (by positivity)) hker₂
      _ = pref * (3 * Real.log (4 * X)) ^ (3 * E C + 1) * (ker₁ + ker₂) := by ring
  have hEsubset : E₀ ⊆ E₁ ∪ E₂ := by
    intro t ht
    change t ∈ Set.Icc (-T) T ∧
      V ≤ ‖FractionalPrimes.Literature.LargeValues.dirichletPolynomial N
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) t‖ at ht
    have hlargeSq : V ^ 2 ≤ ‖factorPolynomial N coeff t ^ 2‖ := by
      rw [norm_pow]
      change V ^ 2 ≤
        ‖FractionalPrimes.Literature.LargeValues.dirichletPolynomial N
          (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) t‖ ^ 2
      exact pow_le_pow_left₀ (le_of_lt hV) ht.2 2
    have hdecomp := factorPolynomial_square_eq_twoBlocks N coeff t hN
    rw [hdecomp] at hlargeSq
    by_cases h₁ : W ≤ ‖FractionalPrimes.Literature.LargeValues.dirichletPolynomial
        (N ^ 2) ac t‖
    · change t ∈ E₁ ∪ E₂
      apply Or.inl
      change t ∈ Set.Icc (-T) T ∧ _
      exact ⟨ht.1, h₁⟩
    · by_cases h₂ : W ≤ ‖FractionalPrimes.Literature.LargeValues.dirichletPolynomial
          (2 * N ^ 2) ac t‖
      · change t ∈ E₁ ∪ E₂
        apply Or.inr
        change t ∈ Set.Icc (-T) T ∧ _
        exact ⟨ht.1, h₂⟩
      · have h₁lt :
          ‖FractionalPrimes.Literature.LargeValues.dirichletPolynomial (N ^ 2) ac t‖ < W :=
            lt_of_not_ge h₁
        have h₂lt :
          ‖FractionalPrimes.Literature.LargeValues.dirichletPolynomial (2 * N ^ 2) ac t‖ < W :=
            lt_of_not_ge h₂
        have htri := norm_add_le
          (FractionalPrimes.Literature.LargeValues.dirichletPolynomial (N ^ 2) ac t)
          (FractionalPrimes.Literature.LargeValues.dirichletPolynomial (2 * N ^ 2) ac t)
        dsimp [W] at h₁lt h₂lt
        linarith
  have hfinite : MeasureTheory.volume (E₁ ∪ E₂) ≠ ⊤ := by
    have hbounded : E₁ ∪ E₂ ⊆ Set.Icc (-T) T := by
      intro t ht
      rcases ht with ht₁ | ht₂
      · exact ht₁.1
      · exact ht₂.1
    apply ne_of_lt
    have hle : MeasureTheory.volume (E₁ ∪ E₂) ≤
        MeasureTheory.volume (Set.Icc (-T) T) := MeasureTheory.measure_mono hbounded
    exact lt_of_le_of_lt hle (by simp [Real.volume_Icc])
  have hmeasure : MeasureTheory.volume.real E₀ ≤
      MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := by
    calc
      MeasureTheory.volume.real E₀ ≤ MeasureTheory.volume.real (E₁ ∪ E₂) :=
        MeasureTheory.measureReal_mono hEsubset hfinite
      _ ≤ MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ :=
        MeasureTheory.measureReal_union_le E₁ E₂
  have hkernel := factorSquareThresholdKernel_bound N T V hV (by linarith [hT])
  have htargetNonneg :
      0 ≤ N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12) := by positivity
  let pref₃ := 2 * (2 : ℝ) ^ (3 * E C + 28) * (3 : ℝ) ^ (3 * E C + 1)
  have hpref₃ : 192 * pref₃ ≤ K C := by
    simpa [pref₃, b, mul_assoc] using K_dominates_squareLevelConstant C
  have hcommon :
      pref₃ * Real.log (4 * X) ^ (3 * E C + 1) * (ker₁ + ker₂) ≤
        K C * Real.log (4 * X) ^ (3 * E C + 1) *
          (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
    calc
      pref₃ * Real.log (4 * X) ^ (3 * E C + 1) * (ker₁ + ker₂) ≤
          pref₃ * Real.log (4 * X) ^ (3 * E C + 1) *
            (192 * (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12))) :=
        mul_le_mul_of_nonneg_left hkernel (by positivity)
      _ = (192 * pref₃) * Real.log (4 * X) ^ (3 * E C + 1) *
          (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by ring
      _ ≤ K C * Real.log (4 * X) ^ (3 * E C + 1) *
          (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
        calc
          (192 * pref₃) * Real.log (4 * X) ^ (3 * E C + 1) *
              (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) =
            (192 * pref₃) *
              (Real.log (4 * X) ^ (3 * E C + 1) *
                (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12))) := by ring
          _ ≤ K C *
              (Real.log (4 * X) ^ (3 * E C + 1) *
                (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12))) :=
            mul_le_mul_of_nonneg_right hpref₃ (by positivity)
          _ = K C * Real.log (4 * X) ^ (3 * E C + 1) *
              (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by ring
  have hlogfactor :
      pref * (3 * Real.log (4 * X)) ^ (3 * E C + 1) =
        pref₃ * Real.log (4 * X) ^ (3 * E C + 1) := by
    dsimp [pref, pref₃]
    rw [mul_pow]
    ring
  calc
    MeasureTheory.volume.real E₀ ≤
        MeasureTheory.volume.real E₁ + MeasureTheory.volume.real E₂ := hmeasure
    _ ≤ pref * (3 * Real.log (4 * X)) ^ (3 * E C + 1) * (ker₁ + ker₂) := hblocks
    _ = pref₃ * Real.log (4 * X) ^ (3 * E C + 1) * (ker₁ + ker₂) := by rw [hlogfactor]
    _ ≤ K C * Real.log (4 * X) ^ (3 * E C + 1) *
        (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := hcommon
    _ = K C * Real.log (4 * X) ^ b C *
        (N ^ 2 / V ^ 4 + T * min (1 / V ^ 4) (N ^ 2 / V ^ 12)) := by
      simp [b]

/-- Mean square of the factor polynomial on the source interval `[-T,T]`.
The integrand is `Complex.normSq F`, exactly the real quantity `|F|^2`. -/
theorem factorMeanSquareBound
    (C : ℕ) (N T X : ℝ) (coeff : ℕ → ℂ)
    (hX : 2 ^ 16 ≤ X) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hNX : N ≤ X) (hTX : T ≤ X)
    (hcoeff : factorCoefficientBound C N coeff) :
    (∫ t in (-T)..T, Complex.normSq (factorPolynomial N coeff t)) ≤
      K C * Real.log (4 * X) ^ b C * (T + N) := by
  have hNpos : 0 < N := by linarith
  have hTpos : 0 < T := by linarith
  have hL : 1 ≤ Real.log (4 * X) := log_fourX_ge_one X hX
  have hlog2N : Real.log (2 * N) ≤ Real.log (4 * X) := by
    apply Real.log_le_log (by positivity)
    nlinarith [hNX, hX]
  have hlogmean : 1 + Real.log (2 * N) ≤ 2 * Real.log (4 * X) := by
    linarith
  have hmeanFactor :
      2 * T + 8 * N * (1 + Real.log (2 * N)) ≤
        16 * (T + N) * Real.log (4 * X) := by
    have hTpart : 2 * T ≤ 16 * T * Real.log (4 * X) := by
      nlinarith [hTpos, hL]
    have hNpart :
        8 * N * (1 + Real.log (2 * N)) ≤
          16 * N * Real.log (4 * X) := by
      calc
        8 * N * (1 + Real.log (2 * N)) ≤
            8 * N * (2 * Real.log (4 * X)) :=
          mul_le_mul_of_nonneg_left hlogmean (by positivity)
        _ = 16 * N * Real.log (4 * X) := by ring
    nlinarith [hTpart, hNpart]
  have henergy := FractionalPrimes.Literature.LargeValues.normalizedDivisorEnergyBound
    C N T coeff hN hT hcoeff
  let e := FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C
  have hePlus : e + 1 ≤ b C := by
    have heq : e + 1 = 2 ^ (2 * C) := by
      dsimp [e, FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent]
      exact Nat.sub_add_cancel
        (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
    rw [heq]
    exact (normalizedLogExponent_bounds C).2
  have hlogNT : Real.log (4 * N * T) ≤ 3 * Real.log (4 * X) :=
    log_fourNT_le_three_log_fourX X N T hX hNX hTX hNpos hTpos
  have hlogNTnonneg : 0 ≤ Real.log (4 * N * T) :=
    Real.log_nonneg (by nlinarith [hN, hT])
  have hLnonneg : 0 ≤ Real.log (4 * X) := le_trans (by norm_num) hL
  have hlogPower :
      Real.log (4 * N * T) ^ e * Real.log (4 * X) ≤
        (3 : ℝ) ^ e * Real.log (4 * X) ^ (e + 1) := by
    have hp := pow_le_pow_left₀ hlogNTnonneg hlogNT e
    calc
      Real.log (4 * N * T) ^ e * Real.log (4 * X) ≤
          (3 * Real.log (4 * X)) ^ e * Real.log (4 * X) :=
        mul_le_mul_of_nonneg_right hp hLnonneg
      _ = (3 : ℝ) ^ e * Real.log (4 * X) ^ (e + 1) := by
        rw [mul_pow]
        rw [pow_succ]
        ring
  have hlogPower' :
      Real.log (4 * N * T) ^ e * Real.log (4 * X) ≤
        (3 : ℝ) ^ e * Real.log (4 * X) ^ b C := by
    calc
      _ ≤ (3 : ℝ) ^ e * Real.log (4 * X) ^ (e + 1) := hlogPower
      _ ≤ (3 : ℝ) ^ e * Real.log (4 * X) ^ b C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hL hePlus
  have heLeB : e ≤ b C := by
    have heLePow : e ≤ 2 ^ (2 * C) := by
      dsimp [e, FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent]
      exact Nat.sub_le _ _
    exact heLePow.trans (normalizedLogExponent_bounds C).2
  have hpref : 32 * (3 : ℝ) ^ e ≤ K C := by
    have h3 : (3 : ℝ) ^ e ≤ (3 : ℝ) ^ b C :=
      pow_le_pow_right₀ (by norm_num) heLeB
    have hb : 5 ≤ b C + 40 := by omega
    have h2 : (32 : ℝ) ≤ (2 : ℝ) ^ (b C + 40) := by
      calc
        (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
        _ ≤ (2 : ℝ) ^ (b C + 40) :=
          pow_le_pow_right₀ (by norm_num) hb
    calc
      32 * (3 : ℝ) ^ e ≤ (2 : ℝ) ^ (b C + 40) * (3 : ℝ) ^ b C :=
        mul_le_mul h2 h3 (pow_nonneg (by norm_num) _) (by positivity)
      _ = K C := rfl
  have henergyNonneg :
      0 ≤ FractionalPrimes.Literature.LargeValues.dirichletEnergy N
        (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) := by
    unfold FractionalPrimes.Literature.LargeValues.dirichletEnergy
    positivity
  have hmeanSquare := FractionalPrimes.Literature.LargeValues.meanSquareBound
    N (-T) (2 * T)
    (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)
    hN (by positivity)
  have hinterval : -T + 2 * T = T := by ring
  have hmeanSquare' :
      (∫ t in (-T)..T,
        Complex.normSq (factorPolynomial N coeff t)) ≤
        (2 * T + 8 * N * (1 + Real.log (2 * N))) *
          FractionalPrimes.Literature.LargeValues.dirichletEnergy N
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) := by
    simpa [factorPolynomial, hinterval] using hmeanSquare
  have hraw :
      (2 * T + 8 * N * (1 + Real.log (2 * N))) *
          FractionalPrimes.Literature.LargeValues.dirichletEnergy N
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) ≤
        32 * (T + N) * (3 : ℝ) ^ e * Real.log (4 * X) ^ b C := by
    calc
      _ ≤ 16 * (T + N) * Real.log (4 * X) *
          (2 * Real.log (4 * N * T) ^ e) := by
        calc
          _ ≤ (16 * (T + N) * Real.log (4 * X)) *
              FractionalPrimes.Literature.LargeValues.dirichletEnergy N
                (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) :=
            mul_le_mul_of_nonneg_right hmeanFactor henergyNonneg
          _ ≤ (16 * (T + N) * Real.log (4 * X)) *
              (2 * Real.log (4 * N * T) ^ e) :=
            mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = 32 * (T + N) *
          (Real.log (4 * N * T) ^ e * Real.log (4 * X)) := by ring
      _ ≤ 32 * (T + N) * ((3 : ℝ) ^ e * Real.log (4 * X) ^ b C) := by
        apply mul_le_mul_of_nonneg_left hlogPower' (by positivity)
      _ = 32 * (T + N) * (3 : ℝ) ^ e * Real.log (4 * X) ^ b C := by ring
  calc
    (∫ t in (-T)..T, Complex.normSq (factorPolynomial N coeff t)) ≤ _ := hmeanSquare'
    _ ≤ 32 * (T + N) * (3 : ℝ) ^ e * Real.log (4 * X) ^ b C := hraw
    _ ≤ K C * Real.log (4 * X) ^ b C * (T + N) := by
      calc
        32 * (T + N) * (3 : ℝ) ^ e * Real.log (4 * X) ^ b C =
            (32 * (3 : ℝ) ^ e) * Real.log (4 * X) ^ b C * (T + N) := by ring
        _ = (32 * (3 : ℝ) ^ e) *
            (Real.log (4 * X) ^ b C * (T + N)) := by ring
        _ ≤ K C * (Real.log (4 * X) ^ b C * (T + N)) :=
          mul_le_mul_of_nonneg_right hpref (by positivity)
        _ = K C * Real.log (4 * X) ^ b C * (T + N) := by ring

/-- Exact power-level package for a divisor-bounded factor. It gives both
level-set bounds `k=1,2` and the factor mean-square estimate. -/
theorem factorAndSquareLevelBounds
    (C : ℕ) (N T X V : ℝ) (coeff : ℕ → ℂ)
    (hX : 2 ^ 16 ≤ X) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hNX : N ≤ X) (hTX : T ≤ X) (hV : 0 < V)
    (hcoeff : factorCoefficientBound C N coeff) :
    (∀ k : ℕ, k = 1 ∨ k = 2 →
      MeasureTheory.volume.real
          (FractionalPrimes.Literature.LargeValues.dirichletLevelSet N T V
            (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)) ≤
        K C * Real.log (4 * X) ^ b C *
          (N ^ k / V ^ (2 * k) +
            T * min (1 / V ^ (2 * k)) (N ^ k / V ^ (6 * k)))) ∧
      (∫ t in (-T)..T,
        Complex.normSq (factorPolynomial N coeff t)) ≤
        K C * Real.log (4 * X) ^ b C * (T + N) := by
  constructor
  · intro k hk
    rcases hk with hk | hk
    · subst k
      simpa using factorLevelSetBound_k1 C N T X V coeff hX hN hT hNX hTX hV hcoeff
    · subst k
      simpa using factorLevelSetBound_k2 C N T X V coeff hX hN hT hNX hTX hV hcoeff
  · exact factorMeanSquareBound C N T X coeff hX hN hT hNX hTX hcoeff

end

end FractionalPrimes.Literature.DirichletMean

end

#print axioms FractionalPrimes.Literature.DirichletMean.factorSquareConvolutionCoefficient_bound
#print axioms FractionalPrimes.Literature.DirichletMean.factorMeanSquareBound
#print axioms FractionalPrimes.Literature.DirichletMean.factorAndSquareLevelBounds
