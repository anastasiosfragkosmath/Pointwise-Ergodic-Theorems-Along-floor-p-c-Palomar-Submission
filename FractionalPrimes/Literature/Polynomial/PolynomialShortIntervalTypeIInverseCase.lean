module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLowFrequencyDecay
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalPMAOneWeight
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalVariationAdapter

/-!
# Type-I and Type-I₂ inverse output in the integer short-interval argument

This is the discrete post-inverse step in `lupo:conditional-integer`.
The inverse witness gives a small binomial coefficient norm for `r * P`;
the checked variation adapter then tests the original weight against the
PMA residue-prefix envelope.  The source powers `E = 2*c*D+3` and
`a₀ = A+2E+50a+3` are retained.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators

/-- The Type-I or Type-I₂ inverse alternative contradicts the original
large correlation after conversion to the source residue modulus and
variation budgets.  `hRbudget` and `hNormBudget` are the exact inverse
conclusions with `δ⁻¹ = (log X)^D`; the two PMA bounds are the common-constant
one-weight estimates. -/
theorem typeIOrTypeI2BinomialPMAContradiction
    (d X H K c D E a : ℕ) (A a₀ η δ : ℝ)
    (P : Polynomial ℝ) (r : ℤ) (w : ℤ → ℂ) (C : ℝ)
    (hd : 1 ≤ d) (hX : 3 ≤ X)
    (hη : 0 < η) (_hηmax : η < 3 / 16)
    (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η))
    (hL : 2 ≤ Real.log (X : ℝ))
    (hA : 0 < A)
    (hE : E = 2 * c * D + 3) (hEa : E < a)
    (ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3)
    (hK : 2 ≤ K) (_hc : 1 ≤ c) (_hD : 1 ≤ D)
    (hP : P.natDegree ≤ d)
    (hr : 1 ≤ r)
    (hδinv : δ⁻¹ = (Real.log (X : ℝ)) ^ D)
    (hRbudget : (r : ℝ) ≤ (K : ℝ) * (δ⁻¹) ^ c)
    (hNormBudget :
      binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
        (X : ℤ) (H : ℝ) ≤ (K : ℝ) * (δ⁻¹) ^ c)
    (hL3modulus : (d.factorial : ℝ) * (K : ℝ) ≤
      (Real.log (X : ℝ)) ^ 3)
    (hL3variation : (d.factorial : ℝ) *
      (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ) ≤
        (Real.log (X : ℝ)) ^ 3)
    (hCpos : 0 < C)
    (hCsmall : 2 * C < (Real.log (X : ℝ)) ^ 2)
    (hMuPrefix :
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀))
    (hCramerPrefix :
      residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀))
    (hw : w = (fun n => (paperMu n : ℂ)) ∨
      w = (fun n => (paperLambda n : ℂ) -
        (paperShortBlockCramerWeight (X : ℝ) n : ℂ)))
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    False := by
  let L : ℝ := Real.log (X : ℝ)
  let W : ℝ := (K : ℝ) * L ^ (c * D)
  have hLge1 : (1 : ℝ) ≤ L := by linarith
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hLengthExponent : 0 ≤ (5 / 8 : ℝ) + η := by positivity
  have hHoneReal : (1 : ℝ) ≤ (H : ℝ) := by
    calc
      1 ≤ (X : ℝ) ^ ((5 / 8 : ℝ) + η) := Real.one_le_rpow hXone hLengthExponent
      _ ≤ (H : ℝ) := hHlower
  have hHone : 1 ≤ H := by exact_mod_cast hHoneReal
  have hEtaExponent : 1 - η ≤ 1 := by linarith
  have hUpperPower : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
    calc
      (X : ℝ) ^ (1 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hEtaExponent
      _ = (X : ℝ) := Real.rpow_one _
  have hHleX : H ≤ X := by
    exact_mod_cast (le_trans hHupper hUpperPower)
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hBudgetPower : (δ⁻¹) ^ c = L ^ (c * D) := by
    calc
      (δ⁻¹) ^ c = ((Real.log (X : ℝ)) ^ D) ^ c := by rw [hδinv]
      _ = (Real.log (X : ℝ)) ^ (D * c) := by rw [pow_mul]
      _ = (Real.log (X : ℝ)) ^ (c * D) := by rw [Nat.mul_comm D c]
      _ = L ^ (c * D) := rfl
  have hRbudget' : (r : ℝ) ≤ W := by
    simpa [W, L, hBudgetPower] using hRbudget
  have hNormBudget' :
      binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P)
        (X : ℤ) (H : ℝ) ≤ W := by
    simpa [W, L, hBudgetPower] using hNormBudget
  have hWnonneg : 0 ≤ W := by positivity
  have hFacnonneg : (0 : ℝ) ≤ (d.factorial : ℝ) := by positivity
  have hFacpos : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  have hrCast : (r.toNat : ℝ) = (r : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ r)
  let q : ℕ := r.toNat * d.factorial
  have hqCast : (q : ℝ) = (r : ℝ) * (d.factorial : ℝ) := by
    simp [q, hrCast]
  have hcDleE : c * D + 3 ≤ E := by
    rw [hE]
    have hcDleDouble : c * D ≤ 2 * c * D := by
      calc
        c * D = 1 * (c * D) := by simp
        _ ≤ 2 * (c * D) := Nat.mul_le_mul_right (c * D) (by omega)
        _ = 2 * c * D := by rw [Nat.mul_assoc]
    exact Nat.add_le_add_right hcDleDouble 3
  have hqSmall : (q : ℝ) ≤ L ^ E := by
    calc
      (q : ℝ) ≤ (d.factorial : ℝ) * W := by
        rw [hqCast]
        calc
          (r : ℝ) * (d.factorial : ℝ) ≤ W * (d.factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hRbudget' hFacnonneg
          _ = (d.factorial : ℝ) * W := by ring
      _ = ((d.factorial : ℝ) * (K : ℝ)) * L ^ (c * D) := by
        simp [W]
        ring
      _ ≤ L ^ 3 * L ^ (c * D) :=
        mul_le_mul_of_nonneg_right hL3modulus (by positivity)
      _ = L ^ (c * D + 3) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ L ^ E := pow_le_pow_right₀ hLge1 hcDleE
  have hqSmallA : (q : ℝ) ≤ L ^ a := by
    exact hqSmall.trans (pow_le_pow_right₀ hLge1 (Nat.le_of_lt hEa))
  have hqModulus : ((r.toNat * d.factorial : ℕ) : ℝ) ≤ L ^ a := by
    simpa [q] using hqSmallA
  have hBinomialBound : 0 ≤ W := hWnonneg
  have hTest := polynomialPhase_testByResiduePrefixes_of_smallBinomialNorm
    d X H hd (by omega : 0 < X) (by omega : 0 < H) P hP r hr W (L ^ a)
    hBinomialBound hqModulus hNormBudget' w
  let R : ℝ := residuePrefixEnvelope X H w (L ^ a)
  let V : ℝ := (d.factorial : ℝ) *
    ((r : ℝ) + 2 * Real.pi * binomialVariationConstant d * W)
  have hEnv : 0 ≤ R := by
    dsimp [R]
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  have hBinConst : 0 ≤ 2 * Real.pi * binomialVariationConstant d := by
    positivity [binomialVariationConstant_nonneg d]
  have hInner :
      (r : ℝ) + 2 * Real.pi * binomialVariationConstant d * W ≤
        W * (1 + 2 * Real.pi * binomialVariationConstant d) := by
    nlinarith [hRbudget', hWnonneg, hBinConst]
  have hVsmall : V ≤ L ^ E := by
    calc
      V ≤ (d.factorial : ℝ) *
          (W * (1 + 2 * Real.pi * binomialVariationConstant d)) :=
        mul_le_mul_of_nonneg_left hInner hFacnonneg
      _ = ((d.factorial : ℝ) *
          (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ)) *
            L ^ (c * D) := by
        simp [W]
        ring
      _ ≤ L ^ 3 * L ^ (c * D) :=
        mul_le_mul_of_nonneg_right hL3variation (by positivity)
      _ = L ^ (c * D + 3) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ L ^ E := pow_le_pow_right₀ hLge1 hcDleE
  have hSmallVariation :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          w n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤ R * L ^ E := by
    calc
      _ ≤ R * V := by simpa [R, V] using hTest
      _ ≤ R * L ^ E := mul_le_mul_of_nonneg_left hVsmall hEnv
  have hDecayExponent : E ≤ 2 * E + 50 * a + 1 := by omega
  have hVariation :
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          w n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        R * L ^ (2 * E + 50 * a + 1) := by
    exact hSmallVariation.trans <|
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hLge1 hDecayExponent) hEnv
  have hPrefix :
      R ≤ C * (H : ℝ) * L ^ (-a₀) := by
    rcases hw with hmu | hcr
    · subst w
      dsimp [R, L]
      simpa only [← Real.rpow_natCast] using hMuPrefix
    · subst w
      dsimp [R, L]
      simpa only [← Real.rpow_natCast] using hCramerPrefix
  have hDecay := lowFrequencyTypeII_majorArcDecay
    A a₀ L C (H : ℝ) R
      (‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖)
      E a hA hL hHpos ha₀ hCpos hCsmall hPrefix hVariation
  exact (lt_asymm hLarge (by simpa [L] using hDecay)).elim

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.typeIOrTypeI2BinomialPMAContradiction
