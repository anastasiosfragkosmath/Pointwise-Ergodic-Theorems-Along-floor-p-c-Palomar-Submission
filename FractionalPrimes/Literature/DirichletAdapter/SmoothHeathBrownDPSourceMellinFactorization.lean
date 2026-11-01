module

public import FractionalPrimes.Literature.Polynomial.PolynomialMellinSeparation
public import FractionalPrimes.Literature.Polynomial.PolynomialOuterCutoffPreservesAverages
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorSourceIdentity
public import Mathlib.Tactic

/-! A source-window adapter for the finite Mellin separation identity.  The
finite source sum remains on `(X/2,3X]`; its support is converted exactly to
the positive-integer support sum used by the Fourier/Mellin factorization. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

/-- The normalized smooth Heath--Brown factor as a finite Mellin factor on
positive integers. Its finite support is the checked dyadic source window;
the logarithmic tag already carries the source `4 log X` normalization. -/
noncomputable def smoothHeathBrownNormalizedMellinFactor
    {X z : ℝ} (f : SmoothHeathBrownFactor X) : MellinSeparationFactor := by
  classical
  let g : PositiveInteger → ℂ := fun n =>
    (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n.1 : ℂ)
  have hfinite : (Function.support g).Finite := by
    have hindices :
        ((smoothHeathBrownFactorFiniteSupport f : Finset ℕ) : Set ℕ).Finite :=
      (smoothHeathBrownFactorFiniteSupport f).finite_toSet
    have hpre :
        {n : PositiveInteger | n.1 ∈ smoothHeathBrownFactorFiniteSupport f}.Finite := by
      apply hindices.preimage
      intro n hn m hm hnm
      exact Subtype.ext hnm
    apply hpre.subset
    intro n hn
    change g n ≠ 0 at hn
    have hcoeff :
        smoothHeathBrownNormalizedFactorCoefficient (z := z) f n.1 ≠ 0 := by
      intro hz
      apply hn
      simp [g, hz]
    exact smoothHeathBrownNormalizedFactorCoefficient_support f hcoeff
  exact Finsupp.ofSupportFinite g hfinite

@[simp] theorem smoothHeathBrownNormalizedMellinFactor_apply
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (n : PositiveInteger) :
    smoothHeathBrownNormalizedMellinFactor (z := z) f n =
      (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n.1 : ℂ) := by
  classical
  simp [smoothHeathBrownNormalizedMellinFactor]

private theorem smoothHeathBrownNormalizedMellinFactor_toArithmeticFunction_apply
    {X z : ℝ} (f : SmoothHeathBrownFactor X) (n : ℕ) :
    toComplexArithmeticFunction (smoothHeathBrownNormalizedMellinFactor (z := z) f) n =
      (smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ) := by
  by_cases hn : 0 < n
  · let p : PositiveInteger := ⟨n, hn⟩
    simpa [p] using
      (toComplexArithmeticFunction_apply
        (smoothHeathBrownNormalizedMellinFactor (z := z) f) p)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    cases f <;>
      simp [toComplexArithmeticFunction,
        smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownThetaFactor, smoothHeathBrownLogFactor,
        smoothHeathBrownMobiusFactor]

/-- The original real Heath--Brown convolution coefficient is the source
normalization times the ordered arithmetic convolution of its normalized
finite Mellin factors. The equality is coefficientwise, before any cutoff or
residue restriction. -/
theorem smoothHeathBrownConvolutionFactors_eq_scaledMellinArithmeticProduct
    {X z : ℝ} (hX : 3 ≤ X)
    (fs : List (SmoothHeathBrownFactor X)) (n : ℕ) :
    (smoothHeathBrownConvolutionFactors z fs n : ℂ) =
      (((4 * Real.log X) ^
          fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
        mellinSeparationArithmeticProduct
          (fun i : Fin fs.length =>
            smoothHeathBrownNormalizedMellinFactor (z := z) (fs.get i)) n := by
  classical
  let c : ℝ := 4 * Real.log X
  have hraw := smoothHeathBrownConvolutionFactors_apply_finMulAntidiag
    (z := z) fs n
  have hnorm := arithmeticFunctionFinProduct_apply_finMulAntidiag
    fs.length
    (fun i : Fin fs.length =>
      toComplexArithmeticFunction
        (smoothHeathBrownNormalizedMellinFactor (z := z) (fs.get i))) n
  change (smoothHeathBrownConvolutionFactors z fs n : ℂ) = _
  rw [hraw]
  rw [mellinSeparationArithmeticProduct]
  rw [hnorm]
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hrestore := smoothHeathBrown_normalizedFactorProduct_restore
    (z := z) hX fs v
  have hcomplex := congrArg (fun y : ℝ => (y : ℂ)) hrestore
  have hfactor (i : Fin fs.length) :
      toComplexArithmeticFunction
          (smoothHeathBrownNormalizedMellinFactor (z := z) (fs.get i)) (v i) =
        (smoothHeathBrownNormalizedFactorCoefficient (z := z) (fs.get i)
          (v i) : ℂ) :=
    smoothHeathBrownNormalizedMellinFactor_toArithmeticFunction_apply
      (fs.get i) (v i)
  have hnormprod :
      (∏ i : Fin fs.length,
        (smoothHeathBrownNormalizedFactorCoefficient (z := z) (fs.get i)
          (v i) : ℂ)) =
        ∏ i : Fin fs.length,
          toComplexArithmeticFunction
            (smoothHeathBrownNormalizedMellinFactor (z := z) (fs.get i))
            (v i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (hfactor i).symm
  have hcomplex' :
      ((∏ i : Fin fs.length,
        smoothHeathBrownFactorFunction z (fs.get i) (v i) : ℝ) : ℂ) =
        (((4 * Real.log X) ^
          fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
          ∏ i : Fin fs.length,
            (smoothHeathBrownNormalizedFactorCoefficient (z := z)
              (fs.get i) (v i) : ℂ) := by
    simpa [c, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_prod] using hcomplex.symm
  rw [hnormprod] at hcomplex'
  exact hcomplex'

private theorem smoothHeathBrownSourceWindow_mem_iff {X : ℝ}
    (hX : 3 ≤ X) (n : ℕ) :
    n ∈ mellinWindowSupportIndices X ↔
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
  unfold mellinWindowSupportIndices
  exact mellinIntervalIndices_mem_iff (by positivity) n

private theorem smoothHeathBrownSourceCutoff_support_mem
    {X : ℝ} (hX : 3 ≤ X) (n : ℕ)
    (hcut : polynomialOuterCutoff ((n : ℝ) / X) ≠ 0) :
    n ∈ mellinWindowSupportIndices X := by
  have hXpos : 0 < X := by linarith
  have hsupp : (n : ℝ) / X ∈ Function.support polynomialOuterCutoff := by
    rw [Function.mem_support]
    exact hcut
  have hs := polynomialOuterCutoff_support_subset hsupp
  apply (smoothHeathBrownSourceWindow_mem_iff hX n).2
  constructor
  · have hmul := (le_div_iff₀ hXpos).1 hs.1
    nlinarith
  · have hmul := (div_le_iff₀ hXpos).1 hs.2
    nlinarith

private theorem smoothHeathBrownMellinMonomial_eq
    (p : PositiveInteger) (t : ℝ) :
    mellinDirichletMonomial p.1 t =
      mellinSeparationMonomial p
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
  unfold mellinDirichletMonomial mellinSeparationMonomial
  congr 1
  push_cast
  ring

/-- The exact finite cutoff polynomial of one finitely-supported coefficient
sequence equals the source residue Mellin sum.  It is enough that the
coefficient sequence agrees with the arithmetic-function extension on the
source window. -/
theorem smoothHeathBrownSourceWindowMellin_eq_residueMellinSum
    {X : ℝ} (hX : 3 ≤ X) (q : ℕ) (a : ℤ)
    (f : MellinSeparationFactor) (c : ℕ → ℂ) (t : ℝ)
    (hcoeff : ∀ n ∈ mellinWindowSupportIndices X,
      c n = toComplexArithmeticFunction f n) :
    (∑ n ∈ mellinWindowSupportIndices X,
      c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
        (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
          mellinDirichletMonomial n t) =
      mellinSeparationResidueMellinSum f q a X
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
  classical
  let S := mellinWindowSupportIndices X
  let src : ℕ → ℂ := fun n =>
    c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
      (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
        mellinDirichletMonomial n t
  let dst : PositiveInteger → ℂ := fun p =>
    toComplexArithmeticFunction f p.1 *
      (polynomialOuterCutoff ((p.1 : ℝ) / X) : ℂ) *
        mellinSeparationMonomial p
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hleft :
      (∑ n ∈ S, src n) = ∑ n ∈ S.filter (fun n => src n ≠ 0), src n := by
    rw [Finset.sum_filter_ne_zero]
  have hright :
      mellinSeparationResidueMellinSum f q a X
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
        ∑ p ∈ (f.support.filter
          (fun p => Int.ModEq (q : ℤ) (p.1 : ℤ) a)).filter
            (fun p => dst p ≠ 0), dst p := by
    unfold mellinSeparationResidueMellinSum
    rw [Finset.sum_filter_ne_zero]
    apply Finset.sum_congr rfl
    intro p hp
    have hres : Int.ModEq (q : ℤ) (p.1 : ℤ) a :=
      (Finset.mem_filter.mp hp).2
    simp [dst, hres, mul_assoc]
  have hbij :
      (∑ p ∈ (f.support.filter
          (fun p => Int.ModEq (q : ℤ) (p.1 : ℤ) a)).filter
            (fun p => dst p ≠ 0), dst p) =
        ∑ n ∈ S.filter (fun n => src n ≠ 0), src n := by
    apply Finset.sum_bij (fun p _ => p.1)
    · intro p hp
      have hdst : dst p ≠ 0 := (Finset.mem_filter.mp hp).2
      have hdstFactors :
          toComplexArithmeticFunction f p.1 ≠ 0 ∧
            (polynomialOuterCutoff ((p.1 : ℝ) / X) : ℂ) ≠ 0 ∧
              mellinSeparationMonomial p
                (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
        simpa [dst, mul_assoc] using hdst
      have hcut : polynomialOuterCutoff ((p.1 : ℝ) / X) ≠ 0 := by
        intro hz
        apply hdstFactors.2.1
        simp [hz]
      have hmemS := smoothHeathBrownSourceCutoff_support_mem hX p.1 hcut
      rw [Finset.mem_filter]
      refine ⟨hmemS, ?_⟩
      have hcoeff' := hcoeff p.1 hmemS
      have hres : Int.ModEq (q : ℤ) (p.1 : ℤ) a :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hmono := smoothHeathBrownMellinMonomial_eq p t
      simpa [src, hcoeff', hres, hmono, dst, mul_assoc] using hdst
    · intro p hp p' hp' hval
      exact Subtype.ext hval
    · intro n hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnS, hnterm⟩
      have hnposR : 0 < (n : ℝ) :=
        lt_trans (by linarith [hX])
          ((smoothHeathBrownSourceWindow_mem_iff hX n).1 hnS).1
      have hnpos : 0 < n := by exact_mod_cast hnposR
      let p : PositiveInteger := ⟨n, hnpos⟩
      have hcoeff' := hcoeff n hnS
      have hres : Int.ModEq (q : ℤ) (n : ℤ) a := by
        by_contra hnot
        apply hnterm
        simp [src, hnot]
      have hmono := smoothHeathBrownMellinMonomial_eq p t
      have hsrcFactors :
          Int.ModEq (q : ℤ) (n : ℤ) a ∧
            c n ≠ 0 ∧
              (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) ≠ 0 ∧
                mellinDirichletMonomial n t ≠ 0 := by
        simpa [src, mul_assoc] using hnterm
      have hcoeffne : toComplexArithmeticFunction f n ≠ 0 := by
        simpa [hcoeff'] using hsrcFactors.2.1
      have hmonoNe : mellinSeparationMonomial p
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
        simp [mellinSeparationMonomial]
      have hval : toComplexArithmeticFunction f n = f p := by
        simpa [p] using toComplexArithmeticFunction_apply f p
      have hfn : f p ≠ 0 := by
        intro hz
        apply hcoeffne
        rw [hval]
        exact hz
      have hdst : dst p ≠ 0 := by
        have hprod := mul_ne_zero
          (mul_ne_zero hfn hsrcFactors.2.2.1) hmonoNe
        · simpa [dst, p, hmono, mul_assoc] using hprod
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, hdst⟩
        rw [Finset.mem_filter]
        exact ⟨Finsupp.mem_support_iff.mpr (by
          exact hfn), hres⟩
      · rfl
    · intro p hp
      have hres : Int.ModEq (q : ℤ) (p.1 : ℤ) a := by
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hdst : dst p ≠ 0 := (Finset.mem_filter.mp hp).2
      have hdstFactors :
          toComplexArithmeticFunction f p.1 ≠ 0 ∧
            (polynomialOuterCutoff ((p.1 : ℝ) / X) : ℂ) ≠ 0 ∧
              mellinSeparationMonomial p
                (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
        simpa [dst, mul_assoc] using hdst
      have hmemS := smoothHeathBrownSourceCutoff_support_mem hX p.1
        (by
          intro hz
          apply hdstFactors.2.1
          simp [hz])
      have hcoeff' := hcoeff p.1 hmemS
      have hmono := smoothHeathBrownMellinMonomial_eq p t
      simp [src, dst, hcoeff', hres, hmono, mul_assoc]
  calc
    (∑ n ∈ mellinWindowSupportIndices X,
      c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
        (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
          mellinDirichletMonomial n t) = ∑ n ∈ S, src n := by
            rfl
    _ = ∑ n ∈ S.filter (fun n => src n ≠ 0), src n := hleft
    _ = ∑ p ∈ (f.support.filter
          (fun p => Int.ModEq (q : ℤ) (p.1 : ℤ) a)).filter
            (fun p => dst p ≠ 0), dst p := hbij.symm
    _ = mellinSeparationResidueMellinSum f q a X
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := hright.symm

/-- The source cutoff polynomial of a coefficientwise finite convolution is
exactly the finite residue-tuple Fourier/Mellin integral in
`lup:mellin-separation`. The coefficient matching is explicit, while the
source real window and angular Fourier normalization are unchanged. -/
theorem smoothHeathBrownSourceWindowMellin_eq_separatedConvolution
    {X : ℝ} (hX : 3 ≤ X) {r q : ℕ} (hr : 0 < r) (hq : 0 < q)
    (a : ℤ) (α : Fin r → MellinSeparationFactor) (c : ℕ → ℂ) (t : ℝ)
    (hcoeff : ∀ n ∈ mellinWindowSupportIndices X,
      c n = toComplexArithmeticFunction
        (mellinSeparationConvolutionProduct α) n) :
    (∑ n ∈ mellinWindowSupportIndices X,
      c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
        (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
          mellinDirichletMonomial n t) =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ b ∈ mellinSeparationAllowedResidues a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) := by
  have hsource := smoothHeathBrownSourceWindowMellin_eq_residueMellinSum
    hX q a (mellinSeparationConvolutionProduct α) c t hcoeff
  have hsep := separateSmoothConvolutionMellin hr α hq a X
    (by linarith [hX]) (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hfreq (u : ℝ) :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) -
          Complex.I * (u : ℂ) =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ) := by
    push_cast
    ring
  calc
    _ = mellinSeparationResidueMellinSum
        (mellinSeparationConvolutionProduct α) q a X
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := hsource
    _ = _ := by simpa only [hfreq] using hsep

/-- The same exact factorization with an external component scalar. The scalar
is kept outside the residue sum, which allows the source's binomial
coefficient and unique `4 log X` logarithmic normalization to be restored
without changing the factor polynomials. -/
theorem smoothHeathBrownSourceWindowMellin_eq_scaledSeparatedConvolution
    {X : ℝ} (hX : 3 ≤ X) {r q : ℕ} (hr : 0 < r) (hq : 0 < q)
    (a : ℤ) (α : Fin r → MellinSeparationFactor) (κ : ℂ)
    (c : ℕ → ℂ) (t : ℝ)
    (hcoeff : ∀ n ∈ mellinWindowSupportIndices X,
      c n = κ * toComplexArithmeticFunction
        (mellinSeparationConvolutionProduct α) n) :
    (∑ n ∈ mellinWindowSupportIndices X,
      c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
        (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
          mellinDirichletMonomial n t) =
      κ * ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ b ∈ mellinSeparationAllowedResidues a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ))) := by
  classical
  let d : ℕ → ℂ := fun n =>
    toComplexArithmeticFunction
      (mellinSeparationConvolutionProduct α) n
  have hscale :
      (∑ n ∈ mellinWindowSupportIndices X,
        c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
          (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
            mellinDirichletMonomial n t) =
        κ * (∑ n ∈ mellinWindowSupportIndices X,
          d n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
            (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
              mellinDirichletMonomial n t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcoeff n hn]
    simp [d, mul_assoc]
  have hbase := smoothHeathBrownSourceWindowMellin_eq_separatedConvolution
    hX hr hq a α d t (by intro n hn; rfl)
  calc
    _ = κ * (∑ n ∈ mellinWindowSupportIndices X,
        d n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
          (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
            mellinDirichletMonomial n t) := hscale
    _ = κ * ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ b ∈ mellinSeparationAllowedResidues a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ))) := by
      rw [hbase]

#print axioms smoothHeathBrownSourceWindowMellin_eq_residueMellinSum
#print axioms smoothHeathBrownSourceWindowMellin_eq_separatedConvolution
#print axioms smoothHeathBrownSourceWindowMellin_eq_scaledSeparatedConvolution
#print axioms smoothHeathBrownNormalizedMellinFactor_apply

end FractionalPrimes.Literature.DirichletAdapter

end
