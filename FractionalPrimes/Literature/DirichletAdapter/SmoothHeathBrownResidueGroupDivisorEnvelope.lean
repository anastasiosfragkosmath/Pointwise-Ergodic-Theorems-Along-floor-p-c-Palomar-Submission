module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownMobiusSelectedGroupSourceBridge
public import FractionalPrimes.Literature.Twisted.DivisorTwentyBound
public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupedFactorBounds
public import Mathlib.Tactic
@[expose] public section

/-! A source-facing divisor envelope for the finite coefficients of an actual
residue-restricted smooth Heath--Brown group. This is the discrete coefficient
input needed before applying the scalar trilinear theorem to the three groups.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

private theorem smoothHeathBrownResidueFactor_norm_le_one
    {X z : ℝ} (hX : 3 ≤ X) (q b : ℕ)
    (f : SmoothHeathBrownFactor X) (n : ℕ) :
    ‖smoothHeathBrownResidueFactorArithmeticFunction (z := z) q b f n‖ ≤ 1 := by
  change ‖(if n % q = b then
      (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ)
    else 0)‖ ≤ 1
  split_ifs with hres
  · by_cases hzero : smoothHeathBrownNormalizedFactorCoefficient (z := z) f n = 0
    · simp [hzero]
    · have hmem : n ∈ smoothHeathBrownFactorFiniteSupport f :=
        smoothHeathBrownNormalizedFactorCoefficient_support (z := z) f hzero
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact smoothHeathBrownNormalizedFactorCoefficient_abs_le_one hX f hmem
  · simp

private theorem arithmeticFunctionFinProduct_norm_le_divisorCoefficient
    (k : ℕ) (f : Fin k → ArithmeticFunction ℂ)
    (hf : ∀ i n, ‖f i n‖ ≤ 1) (n : ℕ) :
    ‖(∏ i : Fin k, f i) n‖ ≤ (divisorCoefficient k n : ℝ) := by
  revert n
  induction k with
  | zero =>
      intro n
      by_cases hn : n = 1
      · subst n
        simp [divisorCoefficient, ArithmeticFunction.one_apply]
      · simp [divisorCoefficient, ArithmeticFunction.one_apply, hn]
  | succ k ih =>
      intro n
      rw [Fin.prod_univ_succ]
      change ‖(f 0 * (∏ i : Fin k, f i.succ)) n‖ ≤ _
      rw [mul_comm, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (f := fun a b => (∏ i : Fin k, f i.succ) a * f 0 b)]
      calc
        ‖∑ d ∈ n.divisors,
            (∏ i : Fin k, f i.succ) d * f 0 (n / d)‖ ≤
          ∑ d ∈ n.divisors,
            ‖(∏ i : Fin k, f i.succ) d * f 0 (n / d)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ d ∈ n.divisors, (divisorCoefficient k d : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [norm_mul]
          have htail := ih (fun i => f i.succ) (by
            intro i m
            exact hf i.succ m) d
          have hhead := hf 0 (n / d)
          have hdivnonneg : 0 ≤ (divisorCoefficient k d : ℝ) := Nat.cast_nonneg _
          calc
            ‖(∏ i : Fin k, f i.succ) d‖ * ‖f 0 (n / d)‖ ≤
                (divisorCoefficient k d : ℝ) * 1 :=
              mul_le_mul htail hhead (norm_nonneg _) (by norm_num)
            _ = (divisorCoefficient k d : ℝ) := by ring
        _ = (divisorCoefficient (k + 1) n : ℝ) := by
          rw [← Nat.cast_sum, divisorCoefficient_succ_divisor_sum]

private theorem arithmeticFunctionSubsetProduct_norm_le_divisorCoefficient
    {K : ℕ} (I : Finset (Fin K)) (f : Fin K → ArithmeticFunction ℂ)
    (hf : ∀ i n, ‖f i n‖ ≤ 1) (n : ℕ) :
    ‖(∏ i : I, f i.val) n‖ ≤ (divisorCoefficient I.card n : ℝ) := by
  classical
  let e : Fin I.card ≃ I := (I.orderIsoOfFin rfl).toEquiv
  have hprod :
      (∏ i : I, f i.val) = ∏ j : Fin I.card, f (e j).val := by
    simpa [e] using
      (Equiv.prod_comp e.symm (fun j : Fin I.card => f (e j).val))
  rw [hprod]
  exact arithmeticFunctionFinProduct_norm_le_divisorCoefficient I.card
    (fun j => f (e j).val) (by
      intro j m
      exact hf (e j).val m) n

/-- The ordered convolution of any selected set of at most twenty actual
residue-restricted smooth Heath--Brown factors has coefficient modulus at
most `d₂₀(n)`. The residue classes and normalized source coefficients are
retained exactly in the factor functions. -/
theorem smoothHeathBrownResidueGroupCoefficient_norm_le_divisorTwenty
    {X z : ℝ} (hX : 3 ≤ X) {K : ℕ}
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (hI : I.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ) (n : PositiveInteger) :
    ‖(∏ i : I,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val)) n.1‖ ≤
      (divisorCoefficient 20 n.1 : ℝ) := by
  have hsmall := arithmeticFunctionSubsetProduct_norm_le_divisorCoefficient
    I (fun i => smoothHeathBrownResidueFactorArithmeticFunction (z := z)
      q (residue i) (fs i))
    (by
      intro i m
      exact smoothHeathBrownResidueFactor_norm_le_one hX q (residue i) (fs i) m)
    n.1
  have hmono : divisorCoefficient I.card n.1 ≤ divisorCoefficient 20 n.1 :=
    divisorCoefficient_mono n.2 hI
  exact hsmall.trans (by exact_mod_cast hmono)

/-- The coefficient bound in the form consumed by the scalar trilinear mean
theorem. -/
theorem smoothHeathBrownResidueGroupCoefficient_norm_le_divisorSquareTwenty
    {X z : ℝ} (hX : 3 ≤ X) {K : ℕ}
    (fs : Fin K → SmoothHeathBrownFactor X)
    (I : Finset (Fin K)) (hI : I.card ≤ 20)
    (q : ℕ) (residue : Fin K → ℕ) (n : PositiveInteger) :
    ‖(∏ i : I,
        smoothHeathBrownResidueFactorArithmeticFunction (z := z)
          q (residue i.val) (fs i.val)) n.1‖ ≤
      (divisorCoefficient 2 n.1 : ℝ) ^ 20 := by
  exact (smoothHeathBrownResidueGroupCoefficient_norm_le_divisorTwenty
    hX fs I hI q residue n).trans (by
      exact_mod_cast divisorCoefficient_twenty_le_two_pow n.1 n.2)

#print axioms smoothHeathBrownResidueGroupCoefficient_norm_le_divisorTwenty
#print axioms smoothHeathBrownResidueGroupCoefficient_norm_le_divisorSquareTwenty

end FractionalPrimes.Literature.DirichletAdapter

end
