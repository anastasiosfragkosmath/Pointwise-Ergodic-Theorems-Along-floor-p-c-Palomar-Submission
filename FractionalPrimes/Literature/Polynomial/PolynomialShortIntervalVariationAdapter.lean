module

public import FractionalPrimes.Literature.Polynomial.PolynomialResiduePrefixTest
public import FractionalPrimes.Literature.Uniformity.SmallBinomialMultipleVariation

/-!
# Polynomial variation as a short-interval residue-prefix test

This file joins the checked global residue-variation estimate from
`lu:small-binomial-tv` to the finite short-interval Abel estimate
`lup:residue-test`.  The interval is the exact integer set `(X,X+H]`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators ENNReal

noncomputable section

/-- A finite residue variation on a finite interval is bounded by the
extended residue variation on any set containing that interval. -/
theorem finiteResidueClassVariation_le_of_subset
    (I : FiniteIntegerInterval) (P : Set ℤ) (g : ℤ → ℂ) (q : ℕ)
    (hq : 0 < q) (hpoints : ∀ n ∈ I.points, n ∈ P) :
    ENNReal.ofReal (finiteResidueClassVariation I g q) ≤
      residueClassTotalVariation P g q hq := by
  classical
  have hnonneg : ∀ a ∈ Finset.range q,
      0 ≤ finiteOrderedTotalVariation
        (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g := by
    intro a ha
    exact finiteOrderedTotalVariation_nonneg _ _
  calc
    ENNReal.ofReal (finiteResidueClassVariation I g q) =
        ∑ a ∈ Finset.range q,
          ENNReal.ofReal (finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]) g) := by
      rw [finiteResidueClassVariation, ENNReal.ofReal_sum_of_nonneg hnonneg]
    _ ≤ ∑ a ∈ Finset.range q,
          orderedTotalVariation (P ∩ integerResidueClass q a) g := by
      apply Finset.sum_le_sum
      intro a ha
      unfold orderedTotalVariation
      let F : {F : Finset ℤ //
          ∀ n ∈ F, n ∈ P ∩ integerResidueClass q a} :=
        ⟨I.points.filter (fun n => n ≡ (a : ℤ) [ZMOD (q : ℤ)]), by
          intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hnI, hmod⟩
          refine ⟨hpoints n hnI, ?_⟩
          exact Int.modEq_iff_add_fac.mp hmod.symm⟩
      exact le_iSup_of_le F le_rfl
    _ = residueClassTotalVariation P g q hq := by
      rfl

/-- The finite interval in the residue-prefix test is exactly the integer
points of `(X,X+H]` when `H` is positive. -/
private theorem shortIntervalResiduePoints_eq_Ioc
    (X H : ℕ) (hH : 0 < H) :
    (residuePrefixFiniteInterval X H).points =
      Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
  have hprog := arithmeticProgressionPoints_eq_Ioc_filter_modEq
    ((X : ℤ) + 1) 1 (by norm_num) H hH
  have hleft : ((X : ℤ) + 1) - 1 = (X : ℤ) := by omega
  have hright : ((X : ℤ) + 1) + ((H - 1 : ℕ) : ℤ) * (1 : ℤ) =
      ((X + H : ℕ) : ℤ) := by
    have hH' : H - 1 + 1 = H := Nat.sub_add_cancel (by omega)
    norm_cast
    omega
  have hright' : ((X : ℤ) + 1) + ((H - 1 : ℕ) : ℤ) =
      ((X + H : ℕ) : ℤ) := by
    simpa using hright
  rw [show (residuePrefixFiniteInterval X H).points =
      arithmeticProgressionPoints ((X : ℤ) + 1) 1 (by norm_num) H by rfl]
  rw [hprog, hleft]
  simp only [Int.natCast_one, mul_one]
  rw [hright']
  ext n
  simp [Int.ModEq]

/-- The integer points of the finite prefix-test interval lie in the exact
real interval used by the global variation theorem. -/
private theorem shortIntervalResiduePoints_subset_logPhase
    (X H : ℕ) (hH : 0 < H) :
    ∀ n ∈ (residuePrefixFiniteInterval X H).points,
      n ∈ logPhaseIntegerInterval (X : ℝ) (H : ℝ) := by
  intro n hn
  have hnIoc := Finset.mem_Ioc.mp
    ((shortIntervalResiduePoints_eq_Ioc X H hH).symm ▸ hn)
  change (X : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (X : ℝ) + (H : ℝ)
  constructor
  · exact_mod_cast hnIoc.1
  · exact_mod_cast hnIoc.2

/-- Exact short-interval Abel bound for a polynomial phase whose multiple
has the approved binomial coefficient norm.  The denominator is
`r.toNat * d!`, and the variation cost is exactly the one in
`lu:small-binomial-tv`. -/
theorem polynomialPhase_testByResiduePrefixes_of_smallBinomialNorm
    (d X H : ℕ) (hd : 1 ≤ d) (hX : 0 < X) (hH : 0 < H)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (r : ℤ) (hr : 1 ≤ r) (B Q : ℝ) (hB : 0 ≤ B)
    (hmodulus : ((r.toNat * d.factorial : ℕ) : ℝ) ≤ Q)
    (hnorm : binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
      (X : ℤ) (H : ℝ) ≤ B)
    (w : ℤ → ℂ) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
      residuePrefixEnvelope X H w Q *
        ((d.factorial : ℝ) *
          ((r : ℝ) + 2 * Real.pi * binomialVariationConstant d * B)) := by
  classical
  let q := r.toNat * d.factorial
  let g : ℤ → ℂ := fun n => unitFrequencyPhase (P.eval (n : ℝ))
  let C : ℝ := (d.factorial : ℝ) *
    ((r : ℝ) + 2 * Real.pi * binomialVariationConstant d * B)
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.mul_pos (by omega) (Nat.factorial_pos _)
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hH)
  obtain ⟨_hperiod, hglobal⟩ := smallBinomialMultipleVariation
    d r hd hr P hP (X : ℤ) (H : ℝ) B hHreal hB hnorm
  have hglobal' : residueClassTotalVariation
      (logPhaseIntegerInterval (X : ℝ) (H : ℝ)) g q hq ≤
        ENNReal.ofReal C := by
    simpa [q, g, C] using hglobal
  have hfiniteENN : ENNReal.ofReal
      (finiteResidueClassVariation (residuePrefixFiniteInterval X H) g q) ≤
        ENNReal.ofReal C :=
    (finiteResidueClassVariation_le_of_subset
      (residuePrefixFiniteInterval X H)
      (logPhaseIntegerInterval (X : ℝ) (H : ℝ)) g q hq
      (shortIntervalResiduePoints_subset_logPhase X H hH)).trans hglobal'
  have hC : 0 ≤ C := by
    dsimp [C]
    have hrreal : 0 ≤ (r : ℝ) := by
      exact_mod_cast (show 0 ≤ r by omega)
    exact mul_nonneg (Nat.cast_nonneg d.factorial)
      (add_nonneg hrreal
        (mul_nonneg (mul_nonneg (by positivity)
          (binomialVariationConstant_nonneg d)) hB))
  have hfinite :
      finiteResidueClassVariation (residuePrefixFiniteInterval X H) g q ≤ C :=
    (ENNReal.ofReal_le_ofReal_iff hC).mp hfiniteENN
  have hqQ : (q : ℝ) ≤ Q := by simpa [q] using hmodulus
  have htest := testByResiduePrefixes q X H Q w g hq hX hH hqQ
  have hEnv : 0 ≤ residuePrefixEnvelope X H w Q := by
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  calc
    _ ≤ residuePrefixEnvelope X H w Q *
        finiteResidueClassVariation (residuePrefixFiniteInterval X H) g q := htest
    _ ≤ residuePrefixEnvelope X H w Q * C :=
      mul_le_mul_of_nonneg_left hfinite hEnv
    _ = _ := by simp [C]

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.finiteResidueClassVariation_le_of_subset
#print axioms FractionalPrimes.Literature.Polynomial.polynomialPhase_testByResiduePrefixes_of_smallBinomialNorm
