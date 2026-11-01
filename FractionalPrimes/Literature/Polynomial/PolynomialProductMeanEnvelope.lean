module

public import FractionalPrimes.Literature.Polynomial.PolynomialMellinSeparation
public import FractionalPrimes.Literature.Polynomial.PolynomialDirichletMeanEnvelope

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal

set_option maxHeartbeats 500000

/-- The coefficient family `f(n) ζ(n/X) 1_{n ≡ a (q)}` for the finite
convolution represented by the preceding Mellin-separation node. -/
noncomputable def mellinSeparationProductWindowCoefficient
    {r : ℕ} (α : Fin r → MellinSeparationFactor) (q : ℕ)
    (a : ℤ) (X : ℝ) (n : ℕ) : ℂ := by
  classical
  exact if hn : 0 < n then
    if Int.ModEq (q : ℤ) (n : ℤ) a then
      mellinSeparationConvolutionProduct α ⟨n, hn⟩ *
        (polynomialOuterCutoff ((n : ℝ) / X) : ℂ)
    else 0
  else 0

/-- The coefficient ℓ¹ bound used only to package this finite sequence in the
existing Mellin-window data structure. -/
noncomputable def mellinSeparationProductWindowCoefficientBound
    {r : ℕ} (α : Fin r → MellinSeparationFactor) : ℝ :=
  ∑ n ∈ (mellinSeparationConvolutionProduct α).support,
    ‖mellinSeparationConvolutionProduct α n‖

/-- The support of the product-window coefficients lies in the approved
`(X/2,3X]` Dirichlet window. -/
theorem mellinSeparationProductWindowCoefficient_support
    {r q : ℕ} (α : Fin r → MellinSeparationFactor) (a : ℤ) {X : ℝ}
    (hX : 3 ≤ X) (n : ℕ) (hn : 0 < n)
    (hcoeff : mellinSeparationProductWindowCoefficient α q a X n ≠ 0) :
    X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
  classical
  unfold mellinSeparationProductWindowCoefficient at hcoeff
  simp only [dif_pos hn] at hcoeff
  split_ifs at hcoeff with hres
  · have hcut : polynomialOuterCutoff ((n : ℝ) / X) ≠ 0 := by
      intro hz
      apply hcoeff
      simp [hz]
    have hsupport : (n : ℝ) / X ∈ Function.support polynomialOuterCutoff := by
      rw [Function.mem_support]
      exact hcut
    have hbounds := polynomialOuterCutoff_support_subset hsupport
    have hXpos : 0 < X := by linarith
    constructor
    · have hlow : 3 / 4 ≤ (n : ℝ) / X := hbounds.1
      have hmul := (le_div_iff₀ hXpos).1 hlow
      linarith
    · have hupp : (n : ℝ) / X ≤ 5 / 2 := hbounds.2
      have hmul := (div_le_iff₀ hXpos).1 hupp
      linarith
  · exact (hcoeff (by simp [hres])).elim

/-- Every coefficient is bounded by the sum of the norms of the finite
convolution coefficients. -/
theorem mellinSeparationProductWindowCoefficient_bound
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (a : ℤ) (X : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖mellinSeparationProductWindowCoefficient α q a X n‖ ≤
      mellinSeparationProductWindowCoefficientBound α := by
  classical
  unfold mellinSeparationProductWindowCoefficientBound
  unfold mellinSeparationProductWindowCoefficient
  simp only [dif_pos hn]
  split_ifs with hres
  · have hcut0 : 0 ≤ polynomialOuterCutoff ((n : ℝ) / X) :=
      polynomialOuterCutoff_nonneg _
    have hcut1 : polynomialOuterCutoff ((n : ℝ) / X) ≤ 1 :=
      polynomialOuterCutoff_le_one _
    have hnorm : ‖(polynomialOuterCutoff ((n : ℝ) / X) : ℂ)‖ =
        polynomialOuterCutoff ((n : ℝ) / X) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcut0]
    rw [norm_mul, hnorm]
    have hcoef : ‖mellinSeparationConvolutionProduct α ⟨n, hn⟩‖ ≤
        ∑ m ∈ (mellinSeparationConvolutionProduct α).support,
          ‖mellinSeparationConvolutionProduct α m‖ := by
      by_cases hs : ⟨n, hn⟩ ∈ (mellinSeparationConvolutionProduct α).support
      · exact Finset.single_le_sum (fun m hm => norm_nonneg _) hs
      · have hz : mellinSeparationConvolutionProduct α ⟨n, hn⟩ = 0 := by
          by_contra hne
          exact hs (Finsupp.mem_support_iff.mpr hne)
        rw [hz]
        simp only [norm_zero]
        exact Finset.sum_nonneg (s := (mellinSeparationConvolutionProduct α).support)
          (f := fun m : PositiveInteger =>
            ‖mellinSeparationConvolutionProduct α m‖)
          (fun m hm => norm_nonneg _)
    calc
      ‖mellinSeparationConvolutionProduct α ⟨n, hn⟩‖ *
            polynomialOuterCutoff ((n : ℝ) / X)
          ≤ ‖mellinSeparationConvolutionProduct α ⟨n, hn⟩‖ :=
            mul_le_of_le_one_right (norm_nonneg _) hcut1
      _ ≤ mellinSeparationProductWindowCoefficientBound α := hcoef
  · simp only [if_neg hres, norm_zero]
    exact Finset.sum_nonneg (s := (mellinSeparationConvolutionProduct α).support)
      (f := fun m : PositiveInteger =>
        ‖mellinSeparationConvolutionProduct α m‖)
      (fun m hm => norm_nonneg _)

/-- The Mellin-window package for the product coefficients. Its `A_X` field
is overwritten by the source's residue-restricted finite Dirichlet sum, an
equivalent presentation of the constructor's window sum. -/
noncomputable def mellinSeparationProductWindowData
    {r : ℕ} (α : Fin r → MellinSeparationFactor) (q : ℕ)
    (a : ℤ) (X : ℝ) (hX : 3 ≤ X) : MellinWindowData := by
  classical
  let f := mellinSeparationConvolutionProduct α
  let c : ℕ → ℂ := mellinSeparationProductWindowCoefficient α q a X
  let B := mellinSeparationProductWindowCoefficientBound α
  let w := mellinWindowData (fun _ => 0) X 1 B c hX
    (by norm_num) (by linarith) (by
      dsimp [B]
      exact Finset.sum_nonneg fun n hn => norm_nonneg _)
    (by
      intro n hn hne
      exact mellinSeparationProductWindowCoefficient_support (q := q) α a hX n hn hne)
    (by
      intro n hn
      exact mellinSeparationProductWindowCoefficient_bound α a X n hn)
  let A : ℝ → ℂ := fun t =>
    mellinSeparationResidueMellinSum f q a X
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))
  exact { w with A_X := A }

/-- The product of residue-class Dirichlet polynomials evaluated on the
vertical line shifted by `u`. -/
noncomputable def productDirichletPolynomialsAt
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (t u : ℝ) : ℂ :=
  ∏ j, mellinSeparationFactorPolynomial α q j (b j)
    (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ))

/-- The positive tail integrand in the product envelope. -/
noncomputable def productDirichletTailIntegrand
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (t u : ℝ) : ℝ :=
  ‖productDirichletPolynomialsAt α b t u‖

/-- The symmetric tail integral for a fixed residue tuple and Mellin shift. -/
noncomputable def productDirichletTailIntegral
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (W u V : ℝ) : ℝ :=
  ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
    productDirichletTailIntegrand α b t u

/-- The normalized objective whose finite maximum is the product mean
envelope `G_b(u)`. -/
noncomputable def productDirichletMeanObjective
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (T0 W u V : ℝ) : ℝ :=
  (T0 / V) * productDirichletTailIntegral α b W u V

/-- The exact compact-interval maximum `G_b(u)` from `lup:product-envelope`,
defined as a supremum pending the attainment theorem below. -/
noncomputable def productDirichletMeanEnvelope
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (T0 W u : ℝ) : ℝ :=
  sSup (productDirichletMeanObjective α b T0 W u ''
    Set.Icc T0 (T0 * W ^ 4))

/-- Each individual Mellin monomial is continuous in its complex exponent. -/
@[fun_prop]
theorem mellinSeparationMonomial_continuous (n : PositiveInteger) :
    Continuous (mellinSeparationMonomial n) := by
  unfold mellinSeparationMonomial
  fun_prop

/-- The finite residue-restricted Mellin polynomial in the product-window
package is continuous on the vertical line. -/
theorem mellinSeparationProductWindowData_A_X_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor) (a : ℤ)
    (X : ℝ) (hX : 3 ≤ X) :
    Continuous (mellinSeparationProductWindowData α q a X hX).A_X := by
  change Continuous (fun t : ℝ =>
    mellinSeparationResidueMellinSum
      (mellinSeparationConvolutionProduct α) q a X
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)))
  unfold mellinSeparationResidueMellinSum
  fun_prop

/-- Each finite residue-class Dirichlet polynomial is continuous in its
complex argument. -/
@[fun_prop]
theorem mellinSeparationFactorPolynomial_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor) (j : Fin r)
    (b : Fin q) :
    Continuous (mellinSeparationFactorPolynomial α q j b) := by
  unfold mellinSeparationFactorPolynomial
  fun_prop

/-- Continuity in both the vertical parameter and the Mellin shift. -/
theorem productDirichletPolynomialsAt_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) :
    Continuous (fun p : ℝ × ℝ =>
      productDirichletPolynomialsAt α b p.1 p.2) := by
  unfold productDirichletPolynomialsAt mellinSeparationFactorPolynomial
    mellinSeparationMonomial
  fun_prop

/-- The norm-valued product integrand is continuous jointly in its two
parameters. -/
theorem productDirichletTailIntegrand_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) :
    Continuous (fun p : ℝ × ℝ =>
      productDirichletTailIntegrand α b p.1 p.2) := by
  unfold productDirichletTailIntegrand
  exact continuous_norm.comp (productDirichletPolynomialsAt_continuous α b)

/-- Continuity of the product polynomial along any fixed shifted vertical
line. -/
theorem productDirichletPolynomialsAt_continuous_in_t
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (u : ℝ) :
    Continuous (fun t : ℝ => productDirichletPolynomialsAt α b t u) := by
  change Continuous (fun t : ℝ =>
    ∏ j, mellinSeparationFactorPolynomial α q j (b j)
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)))
  apply continuous_finsetProd
  intro j hj
  apply (mellinSeparationFactorPolynomial_continuous α j (b j)).comp
  fun_prop

/-- The unshifted product polynomial. -/
noncomputable def productDirichletBasePolynomial
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (t : ℝ) : ℂ :=
  ∏ j, mellinSeparationFactorPolynomial α q j (b j)
    (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))

theorem productDirichletBasePolynomial_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) :
    Continuous (productDirichletBasePolynomial α b) := by
  change Continuous (fun t : ℝ =>
    ∏ j, mellinSeparationFactorPolynomial α q j (b j)
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)))
  have h := productDirichletPolynomialsAt_continuous_in_t α b 0
  change Continuous (fun t : ℝ =>
    ∏ j, mellinSeparationFactorPolynomial α q j (b j)
      (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - 0 : ℝ) : ℂ))) at h
  simpa only [sub_zero] using h

/-- Primitive of the unshifted absolute product polynomial. -/
noncomputable def productDirichletTailPrimitive
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (x : ℝ) : ℝ :=
  ∫ t in 0..x, ‖productDirichletBasePolynomial α b t‖

theorem productDirichletTailPrimitive_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) :
    Continuous (productDirichletTailPrimitive α b) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((continuous_norm.comp
    (productDirichletBasePolynomial_continuous α b)).integral_hasStrictDerivAt
      0 x).hasDerivAt.continuousAt

/-- A fixed dummy package used to view the product mean as the existing
Mellin-window envelope; only its `A_X` field enters that envelope. -/
noncomputable def productDirichletZeroWindowData : MellinWindowData where
  rho := fun _ => 0
  X := 3
  H := 1
  B := 0
  a := fun _ => 0
  X_lower := by norm_num
  H_pos := by norm_num
  H_upper := by norm_num
  B_nonneg := by norm_num
  coefficient_support := by
    intro n hn hne
    simp at hne
  coefficient_bound := by
    intro n hn
    simp
  A_X := fun _ => 0
  N_H := 0
  h_H := fun _ => 0
  K_H := fun _ => 0
  rho_T := fun _ _ => 0
  S_H_T := fun _ => 0

/-- Mellin-window data whose Dirichlet polynomial is the product polynomial
shifted by `u`. -/
noncomputable def productDirichletShiftedWindowData
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (u : ℝ) : MellinWindowData :=
  {productDirichletZeroWindowData with
    A_X := fun t => productDirichletPolynomialsAt α b t u}

/-- Translate the symmetric product tail to the continuous primitive. -/
theorem productDirichletTailIntegral_eq_primitive
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {W u V : ℝ}
    (hW : 0 < W) (hWV : W ≤ V) :
    productDirichletTailIntegral α b W u V =
      productDirichletTailPrimitive α b (V - u) -
        productDirichletTailPrimitive α b (W - u) +
        productDirichletTailPrimitive α b (-W - u) -
        productDirichletTailPrimitive α b (-V - u) := by
  let w := productDirichletShiftedWindowData α b u
  have hA : Continuous w.A_X := by
    change Continuous (fun t : ℝ => productDirichletPolynomialsAt α b t u)
    exact productDirichletPolynomialsAt_continuous_in_t α b u
  have hshift (x y : ℝ) :
      (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) =
        ∫ t in x - u..y - u, ‖productDirichletBasePolynomial α b t‖ := by
    have hs := intervalIntegral.integral_comp_sub_right (a := x) (b := y)
      (f := fun t : ℝ => ‖productDirichletBasePolynomial α b t‖) u
    simpa [productDirichletPolynomialsAt, productDirichletBasePolynomial] using hs
  have hf : Continuous (fun t : ℝ => ‖productDirichletBasePolynomial α b t‖) :=
    continuous_norm.comp (productDirichletBasePolynomial_continuous α b)
  have h0V :
      (∫ t in 0..V, ‖w.A_X t‖) =
        productDirichletTailPrimitive α b (V - u) -
          productDirichletTailPrimitive α b (-u) := by
    change (∫ t in 0..V, ‖productDirichletPolynomialsAt α b t u‖) = _
    rw [hshift 0 V]
    have hi := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hf.intervalIntegrable 0 (V - u)) (hf.intervalIntegrable 0 (-u))
    simpa [productDirichletTailPrimitive] using hi.symm
  have h0W :
      (∫ t in 0..W, ‖w.A_X t‖) =
        productDirichletTailPrimitive α b (W - u) -
          productDirichletTailPrimitive α b (-u) := by
    change (∫ t in 0..W, ‖productDirichletPolynomialsAt α b t u‖) = _
    rw [hshift 0 W]
    have hi := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hf.intervalIntegrable 0 (W - u)) (hf.intervalIntegrable 0 (-u))
    simpa [productDirichletTailPrimitive] using hi.symm
  have h0negW :
      (∫ t in 0..(-W), ‖w.A_X t‖) =
        productDirichletTailPrimitive α b (-W - u) -
          productDirichletTailPrimitive α b (-u) := by
    change (∫ t in 0..(-W), ‖productDirichletPolynomialsAt α b t u‖) = _
    rw [hshift 0 (-W)]
    have hi := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hf.intervalIntegrable 0 (-W - u)) (hf.intervalIntegrable 0 (-u))
    simpa [productDirichletTailPrimitive] using hi.symm
  have h0negV :
      (∫ t in 0..(-V), ‖w.A_X t‖) =
        productDirichletTailPrimitive α b (-V - u) -
          productDirichletTailPrimitive α b (-u) := by
    change (∫ t in 0..(-V), ‖productDirichletPolynomialsAt α b t u‖) = _
    rw [hshift 0 (-V)]
    have hi := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hf.intervalIntegrable 0 (-V - u)) (hf.intervalIntegrable 0 (-u))
    simpa [productDirichletTailPrimitive] using hi.symm
  calc
    productDirichletTailIntegral α b W u V =
        dirichletAbsoluteTailIntegral w W V := rfl
    _ = (∫ t in 0..V, ‖w.A_X t‖) -
          (∫ t in 0..W, ‖w.A_X t‖) +
          (∫ t in 0..(-W), ‖w.A_X t‖) -
          (∫ t in 0..(-V), ‖w.A_X t‖) :=
      dirichletAbsoluteTailIntegral_eq_primitive w hA hW hWV
    _ = _ := by rw [h0V, h0W, h0negW, h0negV]; ring

/-- A globally continuous extension of the normalized product-tail objective;
on the source's compact endpoint interval it is exactly the displayed
`(T₀/V)` objective. -/
noncomputable def productDirichletMeanObjectiveExtended
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (T0 W u V : ℝ) : ℝ :=
  (T0 / max T0 V) *
    (productDirichletTailPrimitive α b (max W V - u) -
      productDirichletTailPrimitive α b (W - u) +
      productDirichletTailPrimitive α b (-W - u) -
      productDirichletTailPrimitive α b (-max W V - u))

theorem productDirichletMeanObjective_eq_extended
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W u V : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hV : V ∈ Set.Icc T0 (T0 * W ^ 4)) :
    productDirichletMeanObjective α b T0 W u V =
      productDirichletMeanObjectiveExtended α b T0 W u V := by
  have hWpos : 0 < W := by linarith
  have hWV : W ≤ V := le_trans hWT hV.1
  have hmaxW : max W V = V := max_eq_right hWV
  have hmaxT : max T0 V = V := max_eq_right hV.1
  rw [productDirichletMeanObjective, productDirichletTailIntegral_eq_primitive
    α b hWpos hWV]
  simp only [productDirichletMeanObjectiveExtended, hmaxW, hmaxT]

/-- The continuous extension is jointly continuous in the Mellin shift and
the outer endpoint. -/
theorem productDirichletMeanObjectiveExtended_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (T0 W : ℝ) (hT0 : 0 < T0) :
    Continuous (fun p : ℝ × ℝ =>
      productDirichletMeanObjectiveExtended α b T0 W p.1 p.2) := by
  have hden : ∀ p : ℝ × ℝ, max T0 p.2 ≠ 0 := by
    intro p
    exact ne_of_gt (lt_of_lt_of_le hT0 (le_max_left _ _))
  have hratio : Continuous (fun p : ℝ × ℝ => T0 / max T0 p.2) := by
    exact continuous_const.div (continuous_const.max continuous_snd) hden
  have htail : Continuous (fun p : ℝ × ℝ =>
      productDirichletTailPrimitive α b (max W p.2 - p.1) -
        productDirichletTailPrimitive α b (W - p.1) +
        productDirichletTailPrimitive α b (-W - p.1) -
        productDirichletTailPrimitive α b (-max W p.2 - p.1)) := by
    have hp := productDirichletTailPrimitive_continuous α b
    have h1 : Continuous (fun p : ℝ × ℝ =>
        productDirichletTailPrimitive α b (max W p.2 - p.1)) :=
      hp.comp ((continuous_const.max continuous_snd).sub continuous_fst)
    have h2 : Continuous (fun p : ℝ × ℝ =>
        productDirichletTailPrimitive α b (W - p.1)) :=
      hp.comp (continuous_const.sub continuous_fst)
    have h3 : Continuous (fun p : ℝ × ℝ =>
        productDirichletTailPrimitive α b (-W - p.1)) :=
      hp.comp (continuous_const.sub continuous_fst)
    have h4 : Continuous (fun p : ℝ × ℝ =>
        productDirichletTailPrimitive α b (-max W p.2 - p.1)) :=
      hp.comp ((continuous_const.max continuous_snd).neg.sub continuous_fst)
    exact ((h1.sub h2).add h3).sub h4
  unfold productDirichletMeanObjectiveExtended
  exact hratio.mul htail

/-- The exact product mean envelope is continuous as a function of the
Mellin shift, hence measurable. -/
theorem productDirichletMeanEnvelope_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    Continuous (productDirichletMeanEnvelope α b T0 W) := by
  have hT0 : 0 < T0 := lt_of_lt_of_le (by linarith) hWT
  let F : ℝ → ℝ → ℝ := fun u V =>
    productDirichletMeanObjectiveExtended α b T0 W u V
  have hF : Continuous ↿F := by
    change Continuous (fun p : ℝ × ℝ =>
      productDirichletMeanObjectiveExtended α b T0 W p.1 p.2)
    exact productDirichletMeanObjectiveExtended_continuous α b T0 W hT0
  have hImage (u : ℝ) :
      productDirichletMeanObjective α b T0 W u ''
          Set.Icc T0 (T0 * W ^ 4) = F u '' Set.Icc T0 (T0 * W ^ 4) := by
    apply Set.image_congr
    intro V hV
    exact productDirichletMeanObjective_eq_extended α b hW hWT hV
  change Continuous (fun u : ℝ =>
    sSup (productDirichletMeanObjective α b T0 W u ''
      Set.Icc T0 (T0 * W ^ 4)))
  rw [show (fun u : ℝ =>
      sSup (productDirichletMeanObjective α b T0 W u ''
        Set.Icc T0 (T0 * W ^ 4))) =
    fun u => sSup (F u '' Set.Icc T0 (T0 * W ^ 4)) by
      funext u
      rw [hImage u]]
  exact isCompact_Icc.continuous_sSup hF

/-- For each fixed Mellin shift, the compact outer-endpoint supremum defining
`G_b(u)` is attained. -/
theorem productDirichletMeanEnvelope_hasMaximum
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q)
    {T0 W u : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    ∃ V ∈ Set.Icc T0 (T0 * W ^ 4),
      productDirichletMeanObjective α b T0 W u V =
        productDirichletMeanEnvelope α b T0 W u ∧
      ∀ V' ∈ Set.Icc T0 (T0 * W ^ 4),
        productDirichletMeanObjective α b T0 W u V' ≤
          productDirichletMeanEnvelope α b T0 W u := by
  let w := productDirichletShiftedWindowData α b u
  have hA : Continuous w.A_X := by
    change Continuous (fun t : ℝ => productDirichletPolynomialsAt α b t u)
    change Continuous (fun t : ℝ =>
      ∏ j, mellinSeparationFactorPolynomial α q j (b j)
        (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)))
    apply continuous_finsetProd
    intro j hj
    apply (mellinSeparationFactorPolynomial_continuous α j (b j)).comp
    fun_prop
  obtain ⟨V, hV, hEq, hle⟩ := dirichletMeanEnvelope_hasMaximum w hA hW hWT
  dsimp [w, productDirichletShiftedWindowData] at hEq hle
  change productDirichletMeanObjective α b T0 W u V =
    productDirichletMeanEnvelope α b T0 W u at hEq
  change ∀ V' ∈ Set.Icc T0 (T0 * W ^ 4),
    productDirichletMeanObjective α b T0 W u V' ≤
      productDirichletMeanEnvelope α b T0 W u at hle
  refine ⟨V, hV, ?_, ?_⟩
  · exact hEq
  · intro V' hV'
    exact hle V' hV'

/-- The coefficient ℓ1 majorant for one residue-class factor polynomial. -/
noncomputable def mellinSeparationFactorNormSum
    {r : ℕ} (α : Fin r → MellinSeparationFactor) (j : Fin r) : ℝ :=
  ∑ n ∈ (α j).support, ‖α j n‖

/-- Every factor polynomial is bounded on the one-half vertical line by the
sum of its coefficient magnitudes. -/
theorem mellinSeparationFactorPolynomial_norm_le
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (j : Fin r) (b : Fin q) (t : ℝ) :
    ‖mellinSeparationFactorPolynomial α q j b
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤
      mellinSeparationFactorNormSum α j := by
  classical
  have hmono (n : PositiveInteger) :
      ‖mellinSeparationMonomial n
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤ 1 := by
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let L : ℂ := (Real.log (n.1 : ℝ) : ℂ)
    have hre : Complex.re (-s * L) = -Real.log (n.1 : ℝ) / 2 := by
      rw [Complex.mul_re]
      simp only [s, L, Complex.neg_re, Complex.neg_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    change ‖Complex.exp (-s * L)‖ ≤ 1
    rw [Complex.norm_exp, hre]
    apply Real.exp_le_one_iff.mpr
    have hn : (1 : ℝ) ≤ n.1 := by exact_mod_cast n.2
    have hlog : 0 ≤ Real.log (n.1 : ℝ) := Real.log_nonneg hn
    linarith
  let S := (α j).support.filter
    (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) (b.1 : ℤ))
  have hsum :
      ‖∑ n ∈ S, (α j) n * mellinSeparationMonomial n
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤
        ∑ n ∈ S, ‖(α j) n‖ := by
    apply norm_sum_le_of_le
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hmono n)
  have hdecomp :
      (α j).support.sum (fun n => ‖(α j) n‖) =
        S.sum (fun n => ‖(α j) n‖) +
          ((α j).support.filter (fun n =>
            ¬ Int.ModEq (q : ℤ) (n.1 : ℤ) (b.1 : ℤ))).sum
            (fun n => ‖(α j) n‖) := by
    simpa [S] using (Finset.sum_filter_add_sum_filter_not
      ((α j).support)
      (fun n => Int.ModEq (q : ℤ) (n.1 : ℤ) (b.1 : ℤ))
      (fun n => ‖(α j) n‖)).symm
  have hfilter :
      (∑ n ∈ S, ‖(α j) n‖) ≤ mellinSeparationFactorNormSum α j := by
    unfold mellinSeparationFactorNormSum
    calc
      (∑ n ∈ S, ‖(α j) n‖) ≤
          (∑ n ∈ S, ‖(α j) n‖) +
            ((α j).support.filter (fun n =>
              ¬ Int.ModEq (q : ℤ) (n.1 : ℤ) (b.1 : ℤ))).sum
              (fun n => ‖(α j) n‖) :=
        le_add_of_nonneg_right
          (Finset.sum_nonneg fun n hn => norm_nonneg _)
      _ = (α j).support.sum (fun n => ‖(α j) n‖) := hdecomp.symm
  simpa [mellinSeparationFactorPolynomial, S] using hsum.trans hfilter

/-- Every factor coefficient majorant is nonnegative. -/
theorem mellinSeparationFactorNormSum_nonneg
    {r : ℕ} (α : Fin r → MellinSeparationFactor) (j : Fin r) :
    0 ≤ mellinSeparationFactorNormSum α j := by
  unfold mellinSeparationFactorNormSum
  exact Finset.sum_nonneg fun n hn => norm_nonneg _

/-- The product of the coefficient majorants for all factors. -/
noncomputable def productDirichletPolynomialNormBound
    {r : ℕ} (α : Fin r → MellinSeparationFactor) : ℝ :=
  ∏ j, mellinSeparationFactorNormSum α j

/-- The residue product is uniformly bounded in both real variables. -/
theorem productDirichletPolynomialsAt_norm_le
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (t u : ℝ) :
    ‖productDirichletPolynomialsAt α b t u‖ ≤
      productDirichletPolynomialNormBound α := by
  classical
  unfold productDirichletPolynomialsAt productDirichletPolynomialNormBound
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro j hj
    exact norm_nonneg _
  · intro j hj
    simpa using mellinSeparationFactorPolynomial_norm_le α j (b j) (t - u)

/-- The angular Fourier transform of the cutoff kernel is continuous, since it
is a rescaled Schwartz Fourier transform. -/
theorem mellinSeparationLogKernelFourier_continuous :
    Continuous mellinSeparationLogKernelFourier := by
  have hFourier : Continuous
      (𝓕 mellinSeparationLogKernelSchwartz : SchwartzMap ℝ ℂ) :=
    SchwartzMap.continuous _
  have hF : Continuous (fun t : ℝ =>
      (𝓕 mellinSeparationLogKernelSchwartz : SchwartzMap ℝ ℂ)
        (t / (2 * Real.pi))) :=
    hFourier.comp (continuous_id.div_const (2 * Real.pi))
  apply hF.congr
  intro t
  exact (mellinSeparationLogKernelFourier_eq_fourier t).symm

/-- Positive integrand for swapping the product tail and Fourier integrals. -/
private noncomputable def productDirichletFubiniIntegrand
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) (t u : ℝ) : ℝ :=
  ‖mellinSeparationLogKernelFourier u‖ *
    ‖productDirichletPolynomialsAt α b t u‖

private theorem productDirichletFubiniIntegrand_continuous
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) :
    Continuous (fun p : ℝ × ℝ =>
      productDirichletFubiniIntegrand α b p.1 p.2) := by
  exact (continuous_norm.comp
      (mellinSeparationLogKernelFourier_continuous.comp continuous_snd)).mul
    (continuous_norm.comp (productDirichletPolynomialsAt_continuous α b))

/-- Compact vertical support and the uniform factor bound make the Fubini
integrand integrable on a vertical interval times the whole Fourier line. -/
private theorem productDirichletFubiniIntegrand_integrableOn_Icc
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {a c : ℝ} :
    Integrable (fun p : ℝ × ℝ =>
      productDirichletFubiniIntegrand α b p.1 p.2)
      ((volume.restrict (Set.Icc a c)).prod volume) := by
  let C := productDirichletPolynomialNormBound α
  have hC : 0 ≤ C := by
    dsimp [C, productDirichletPolynomialNormBound]
    exact Finset.prod_nonneg fun j hj => mellinSeparationFactorNormSum_nonneg α j
  have hdom : Integrable
      (fun p : ℝ × ℝ => C * ‖mellinSeparationLogKernelFourier p.2‖)
      ((volume.restrict (Set.Icc a c)).prod volume) := by
    have hconst : Integrable (fun _ : ℝ => C)
        (volume.restrict (Set.Icc a c)) := integrable_const C
    exact hconst.mul_prod mellinSeparationLogKernelFourier_integrable.norm
  apply Integrable.mono' hdom
    (productDirichletFubiniIntegrand_continuous α b).aestronglyMeasurable
  filter_upwards with p
  dsimp [productDirichletFubiniIntegrand]
  have hP := productDirichletPolynomialsAt_norm_le α b p.1 p.2
  have hK := norm_nonneg (mellinSeparationLogKernelFourier p.2)
  rw [abs_of_nonneg (mul_nonneg hK (norm_nonneg _))]
  calc
    ‖mellinSeparationLogKernelFourier p.2‖ *
        ‖productDirichletPolynomialsAt α b p.1 p.2‖ ≤
      ‖mellinSeparationLogKernelFourier p.2‖ * C :=
        mul_le_mul_of_nonneg_left hP hK
    _ = C * ‖mellinSeparationLogKernelFourier p.2‖ := by ring

/-- Fubini swaps the product tail integral on a compact vertical interval. -/
private theorem productDirichletFubini_swap_Icc
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {a c : ℝ} :
    (∫ t in Set.Icc a c, ∫ u : ℝ,
      productDirichletFubiniIntegrand α b t u) =
    ∫ u : ℝ, ∫ t in Set.Icc a c,
      productDirichletFubiniIntegrand α b t u := by
  let μ := volume.restrict (Set.Icc a c)
  have h := integral_integral_swap
    (μ := μ) (ν := volume)
    (f := fun t u => productDirichletFubiniIntegrand α b t u)
    (productDirichletFubiniIntegrand_integrableOn_Icc α b)
  simpa [μ, productDirichletFubiniIntegrand] using h

/-- Split the symmetric product tail into its positive and negative interval
integrals, with the exact Lebesgue endpoint convention. -/
private theorem productDirichletTailIntegral_eq_intervalIntegrals
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {W u V : ℝ}
    (hW : 0 < W) (hWV : W ≤ V) :
    productDirichletTailIntegral α b W u V =
      (∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖) +
        (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖) := by
  let w := productDirichletShiftedWindowData α b u
  have hA : Continuous w.A_X := by
    change Continuous (fun t : ℝ => productDirichletPolynomialsAt α b t u)
    exact productDirichletPolynomialsAt_continuous_in_t α b u
  calc
    productDirichletTailIntegral α b W u V =
        dirichletAbsoluteTailIntegral w W V := rfl
    _ = (∫ t in W..V, ‖w.A_X t‖) + (∫ t in -V..-W, ‖w.A_X t‖) :=
      dirichletAbsoluteTailIntegral_eq_intervalIntegrals w hA hW hWV
    _ = _ := by
      simp [w, productDirichletShiftedWindowData]

/-- A crude but uniform length bound for every product tail. -/
private theorem productDirichletTailIntegral_le
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {W u V : ℝ}
    (hW : 0 < W) (hWV : W ≤ V) :
    productDirichletTailIntegral α b W u V ≤
      2 * V * productDirichletPolynomialNormBound α := by
  let C := productDirichletPolynomialNormBound α
  have hC : 0 ≤ C := by
    dsimp [C, productDirichletPolynomialNormBound]
    exact Finset.prod_nonneg fun j hj => mellinSeparationFactorNormSum_nonneg α j
  have hPcont : Continuous (fun t : ℝ =>
      ‖productDirichletPolynomialsAt α b t u‖) :=
    continuous_norm.comp (productDirichletPolynomialsAt_continuous_in_t α b u)
  have hfinitePos : volume (Set.Icc W V) ≠ ∞ :=
    ne_of_lt isCompact_Icc.measure_lt_top
  have hfiniteNeg : volume (Set.Icc (-V) (-W)) ≠ ∞ :=
    ne_of_lt isCompact_Icc.measure_lt_top
  have hPpos : IntegrableOn
      (fun t : ℝ => ‖productDirichletPolynomialsAt α b t u‖) (Set.Icc W V) :=
    hPcont.continuousOn.integrableOn_compact isCompact_Icc
  have hPneg : IntegrableOn
      (fun t : ℝ => ‖productDirichletPolynomialsAt α b t u‖)
      (Set.Icc (-V) (-W)) := hPcont.continuousOn.integrableOn_compact isCompact_Icc
  have hCpos : IntegrableOn (fun _ : ℝ => C) (Set.Icc W V) :=
    integrableOn_const hfinitePos
  have hCneg : IntegrableOn (fun _ : ℝ => C) (Set.Icc (-V) (-W)) :=
    integrableOn_const hfiniteNeg
  have hmonoPos :
      (∫ t in Set.Icc W V, ‖productDirichletPolynomialsAt α b t u‖) ≤
        (∫ t in Set.Icc W V, C) := by
    apply setIntegral_mono_on hPpos hCpos measurableSet_Icc
    intro t ht
    exact productDirichletPolynomialsAt_norm_le α b t u
  have hmonoNeg :
      (∫ t in Set.Icc (-V) (-W), ‖productDirichletPolynomialsAt α b t u‖) ≤
        (∫ t in Set.Icc (-V) (-W), C) := by
    apply setIntegral_mono_on hPneg hCneg measurableSet_Icc
    intro t ht
    exact productDirichletPolynomialsAt_norm_le α b t u
  have hconstPos : (∫ t in Set.Icc W V, C) = (V - W) * C := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hWV)]
  have hconstNeg : (∫ t in Set.Icc (-V) (-W), C) = (V - W) * C := by
    have hneg : -V ≤ -W := by linarith
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hneg)]
    congr 1 <;> ring
  have hposInterval :
      (∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖) ≤
        (V - W) * C := by
    rw [intervalIntegral.integral_of_le hWV,
      ← integral_Icc_eq_integral_Ioc]
    exact hmonoPos.trans hconstPos.le
  have hnegInterval :
      (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖) ≤
        (V - W) * C := by
    have hneg : -V ≤ -W := by linarith
    rw [intervalIntegral.integral_of_le hneg,
      ← integral_Icc_eq_integral_Ioc]
    exact hmonoNeg.trans hconstNeg.le
  rw [productDirichletTailIntegral_eq_intervalIntegrals α b hW hWV]
  calc
    _ ≤ 2 * (V - W) * C := by linarith
    _ ≤ 2 * V * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      linarith

/-- Each compact maximum defining the product envelope is nonnegative and
uniformly bounded by the coefficient majorant. -/
theorem productDirichletMeanEnvelope_nonneg_and_le
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W : ℝ} (u : ℝ)
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    0 ≤ productDirichletMeanEnvelope α b T0 W u ∧
      productDirichletMeanEnvelope α b T0 W u ≤
        2 * T0 * productDirichletPolynomialNormBound α := by
  have hWpos : 0 < W := by linarith
  have hT0pos : 0 < T0 := lt_of_lt_of_le hWpos hWT
  have hcap : T0 ≤ T0 * W ^ 4 := by
    have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ (by linarith : 1 ≤ W)
    nlinarith
  obtain ⟨V, hV, hEq, hmax⟩ :=
    productDirichletMeanEnvelope_hasMaximum α b (u := u) hW hWT
  have hT0mem : T0 ∈ Set.Icc T0 (T0 * W ^ 4) := ⟨le_rfl, hcap⟩
  have hTailMeas : MeasurableSet {t : ℝ | W ≤ |t| ∧ |t| ≤ T0} := by
    change MeasurableSet ((fun t : ℝ => |t|) ⁻¹' Set.Icc W T0)
    exact (isClosed_Icc.preimage continuous_abs).measurableSet
  have hTailNonneg : 0 ≤ productDirichletTailIntegral α b W u T0 :=
    setIntegral_nonneg hTailMeas (by intro t ht; exact norm_nonneg _)
  have hObjT0 : productDirichletMeanObjective α b T0 W u T0 =
      productDirichletTailIntegral α b W u T0 := by
    simp [productDirichletMeanObjective, div_self hT0pos.ne']
  have hnonneg : 0 ≤ productDirichletMeanEnvelope α b T0 W u := by
    calc
      0 ≤ productDirichletTailIntegral α b W u T0 := hTailNonneg
      _ = productDirichletMeanObjective α b T0 W u T0 := hObjT0.symm
      _ ≤ productDirichletMeanEnvelope α b T0 W u := hmax T0 hT0mem
  have hVpos : 0 < V := lt_of_lt_of_le hT0pos hV.1
  have htail := productDirichletTailIntegral_le α b (u := u) hWpos
    (le_trans hWT hV.1)
  have hobj : productDirichletMeanObjective α b T0 W u V ≤
      2 * T0 * productDirichletPolynomialNormBound α := by
    unfold productDirichletMeanObjective
    calc
      T0 / V * productDirichletTailIntegral α b W u V ≤
          T0 / V * (2 * V * productDirichletPolynomialNormBound α) :=
        mul_le_mul_of_nonneg_left htail (div_nonneg hT0pos.le hVpos.le)
      _ = 2 * T0 * productDirichletPolynomialNormBound α := by
        field_simp [hVpos.ne']
  refine ⟨hnonneg, ?_⟩
  rw [← hEq]
  exact hobj

/-- The Fourier-kernel-weighted product envelope is integrable on the whole
real line. -/
theorem productDirichletMeanEnvelope_weighted_integrable
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    Integrable (fun u : ℝ => ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope α b T0 W u) := by
  have hGcont := productDirichletMeanEnvelope_continuous α b hW hWT
  have hGbound (u : ℝ) :
      ‖productDirichletMeanEnvelope α b T0 W u‖ ≤
        2 * T0 * productDirichletPolynomialNormBound α := by
    rw [Real.norm_of_nonneg
      (productDirichletMeanEnvelope_nonneg_and_le α b u hW hWT).1]
    exact (productDirichletMeanEnvelope_nonneg_and_le α b u hW hWT).2
  exact mellinSeparationLogKernelFourier_integrable.norm.mul_bdd
    hGcont.aestronglyMeasurable (Filter.Eventually.of_forall hGbound)

/-- The two-variable nonnegative integrand factors exactly after the
vertical Fubini swap on a compact interval. -/
private theorem productDirichletFubini_Icc_eq
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in Set.Icc x y, ∫ u : ℝ,
      productDirichletFubiniIntegrand α b t u) =
      ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) := by
  rw [productDirichletFubini_swap_Icc α b]
  apply integral_congr_ae
  filter_upwards with u
  have hinterval :
      (∫ t in Set.Icc x y, ‖productDirichletPolynomialsAt α b t u‖) =
        (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
  calc
    (∫ t in Set.Icc x y, productDirichletFubiniIntegrand α b t u) =
        ‖mellinSeparationLogKernelFourier u‖ *
          (∫ t in Set.Icc x y, ‖productDirichletPolynomialsAt α b t u‖) := by
      simp only [productDirichletFubiniIntegrand]
      rw [integral_const_mul]
    _ = _ := by rw [hinterval]

/-- For a fixed shift, the vertical product integral factors its constant
Fourier weight. -/
private theorem productDirichletFubini_t_integral_factor
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {x y : ℝ} (hxy : x ≤ y) (u : ℝ) :
    (∫ t in Set.Icc x y, productDirichletFubiniIntegrand α b t u) =
      ‖mellinSeparationLogKernelFourier u‖ *
        (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) := by
  have hinterval :
      (∫ t in Set.Icc x y, ‖productDirichletPolynomialsAt α b t u‖) =
        (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
  calc
    (∫ t in Set.Icc x y, productDirichletFubiniIntegrand α b t u) =
        ‖mellinSeparationLogKernelFourier u‖ *
          (∫ t in Set.Icc x y, ‖productDirichletPolynomialsAt α b t u‖) := by
      simp only [productDirichletFubiniIntegrand]
      rw [integral_const_mul]
    _ = _ := by rw [hinterval]

/-- The Fourier-weighted product integral on a bounded vertical interval is
integrable in the Mellin shift. -/
private theorem productDirichletKernelInterval_integrable
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {x y : ℝ} (hxy : x ≤ y) :
    Integrable (fun u : ℝ => ‖mellinSeparationLogKernelFourier u‖ *
      (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖)) := by
  have hpair := productDirichletFubiniIntegrand_integrableOn_Icc
    (α := α) b (a := x) (c := y)
  have hswap : Integrable (fun u : ℝ =>
      ∫ t in Set.Icc x y, productDirichletFubiniIntegrand α b t u) :=
    hpair.swap.integral_prod_left
  apply hswap.congr
  filter_upwards with u
  exact productDirichletFubini_t_integral_factor α b hxy u

/-- For every admissible outer endpoint, its product objective is bounded by
the integrated maximum envelope. -/
private theorem productDirichletMeanObjective_kernel_integral_le
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W V : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hV : V ∈ Set.Icc T0 (T0 * W ^ 4)) :
    ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanObjective α b T0 W u V ≤
      ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanEnvelope α b T0 W u := by
  have hWpos : 0 < W := by linarith
  have hT0pos : 0 < T0 := lt_of_lt_of_le hWpos hWT
  have hVpos : 0 < V := lt_of_lt_of_le hT0pos hV.1
  have hTailMeas : MeasurableSet {t : ℝ | W ≤ |t| ∧ |t| ≤ V} := by
    change MeasurableSet ((fun t : ℝ => |t|) ⁻¹' Set.Icc W V)
    exact (isClosed_Icc.preimage continuous_abs).measurableSet
  have hObjNonneg (u : ℝ) :
      0 ≤ productDirichletMeanObjective α b T0 W u V :=
    mul_nonneg (div_nonneg hT0pos.le hVpos.le)
      (setIntegral_nonneg hTailMeas (by intro t ht; exact norm_nonneg _))
  have hObjContExt : Continuous (fun u : ℝ =>
      productDirichletMeanObjectiveExtended α b T0 W u V) := by
    have hpair : Continuous (fun u : ℝ => (u, V)) := by fun_prop
    exact (productDirichletMeanObjectiveExtended_continuous α b T0 W hT0pos).comp hpair
  have hObjCont : Continuous (fun u : ℝ =>
      productDirichletMeanObjective α b T0 W u V) := by
    apply hObjContExt.congr
    intro u
    exact (productDirichletMeanObjective_eq_extended α b hW hWT hV).symm
  have hObjBound (u : ℝ) :
      ‖productDirichletMeanObjective α b T0 W u V‖ ≤
        2 * T0 * productDirichletPolynomialNormBound α := by
    rw [Real.norm_of_nonneg (hObjNonneg u)]
    obtain ⟨_, _, _, hmax⟩ := productDirichletMeanEnvelope_hasMaximum α b
      (u := u) hW hWT
    exact (hmax V hV).trans
      (productDirichletMeanEnvelope_nonneg_and_le α b u hW hWT).2
  have hLeftInt : Integrable (fun u : ℝ =>
      ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanObjective α b T0 W u V) :=
    mellinSeparationLogKernelFourier_integrable.norm.mul_bdd
      hObjCont.aestronglyMeasurable (Filter.Eventually.of_forall hObjBound)
  have hRightInt := productDirichletMeanEnvelope_weighted_integrable α b hW hWT
  apply integral_mono hLeftInt hRightInt
  intro u
  obtain ⟨_, _, _, hmax⟩ := productDirichletMeanEnvelope_hasMaximum α b
    (u := u) hW hWT
  exact mul_le_mul_of_nonneg_left (hmax V hV) (norm_nonneg _)

/-- The constructed Dirichlet-window polynomial is exactly the finite
residue-product Mellin expansion from `lup:mellin-separation`. -/
theorem mellinSeparationProductWindowData_A_X_eq
    {r q : ℕ} (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X) (t : ℝ) :
    (mellinSeparationProductWindowData α q a X hX).A_X t =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              productDirichletPolynomialsAt α b t u := by
  have harg (u : ℝ) :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) -
          Complex.I * (u : ℂ) =
        (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)) := by
    push_cast
    ring
  change mellinSeparationResidueMellinSum
      (mellinSeparationConvolutionProduct α) q a X
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) = _
  have hXpos : 0 < X := by linarith
  rw [separateSmoothConvolutionMellin hr α hq a X hXpos
    (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  apply integral_congr_ae
  filter_upwards with u
  simp only [productDirichletPolynomialsAt]
  rw [harg u]

/-- Pointwise triangle inequality for the exact Mellin separation identity. -/
private theorem mellinSeparationProductWindowData_norm_le
    {r q : ℕ} (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X) (t : ℝ) :
    ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖ ≤
      (2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, productDirichletFubiniIntegrand α b t u := by
  rw [mellinSeparationProductWindowData_A_X_eq hr α hq a X hX t]
  let B : Finset (Fin r → Fin q) :=
    mellinSeparationAllowedResidues (r := r) (q := q) a
  have hc : 0 ≤ (2 * Real.pi : ℝ)⁻¹ := by positivity
  have hnormc : ‖(↑((2 * Real.pi : ℝ)⁻¹) : ℂ)‖ = (2 * Real.pi : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hterm (b : Fin r → Fin q) :
      ‖∫ u : ℝ, mellinSeparationLogKernelFourier u *
          mellinSeparationScaleFactor X u *
            productDirichletPolynomialsAt α b t u‖ ≤
        ∫ u : ℝ, productDirichletFubiniIntegrand α b t u := by
    calc
      _ ≤ ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u *
          mellinSeparationScaleFactor X u *
            productDirichletPolynomialsAt α b t u‖ :=
        norm_integral_le_integral_norm (fun u : ℝ =>
          mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              productDirichletPolynomialsAt α b t u)
      _ = ∫ u : ℝ, productDirichletFubiniIntegrand α b t u := by
        apply integral_congr_ae
        filter_upwards with u
        simp [productDirichletFubiniIntegrand, norm_mul,
          mellinSeparationScaleFactor_norm]
  have hsum := norm_sum_le B (fun b =>
    ∫ u : ℝ, mellinSeparationLogKernelFourier u *
      mellinSeparationScaleFactor X u *
        productDirichletPolynomialsAt α b t u)
  rw [norm_mul, hnormc]
  calc
    (2 * Real.pi : ℝ)⁻¹ *
        ‖∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              productDirichletPolynomialsAt α b t u‖ ≤
      (2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ‖∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              productDirichletPolynomialsAt α b t u‖ := by
        exact mul_le_mul_of_nonneg_left hsum hc
    _ ≤ (2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, productDirichletFubiniIntegrand α b t u := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact Finset.sum_le_sum fun b hb => hterm b

/-- Integrating the pointwise separated Mellin bound over a compact vertical
interval gives a finite sum of product-factor integrals. -/
private theorem mellinSeparationProductWindowData_Icc_integral_le
    {r q : ℕ} (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    {x y : ℝ} :
    (∫ t in Set.Icc x y,
      ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖) ≤
      (2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ t in Set.Icc x y, ∫ u : ℝ,
            productDirichletFubiniIntegrand α b t u := by
  let B : Finset (Fin r → Fin q) :=
    mellinSeparationAllowedResidues (r := r) (q := q) a
  let c : ℝ := (2 * Real.pi : ℝ)⁻¹
  have hA : Continuous (mellinSeparationProductWindowData α q a X hX).A_X :=
    mellinSeparationProductWindowData_A_X_continuous α a X hX
  have hleft : IntegrableOn
      (fun t : ℝ => ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖)
      (Set.Icc x y) :=
    (continuous_norm.comp hA).continuousOn.integrableOn_compact isCompact_Icc
  have hpair (b : Fin r → Fin q) :
      Integrable (fun p : ℝ × ℝ =>
        productDirichletFubiniIntegrand α b p.1 p.2)
        ((volume.restrict (Set.Icc x y)).prod volume) :=
    productDirichletFubiniIntegrand_integrableOn_Icc α b
  have heach (b : Fin r → Fin q) :
      Integrable (fun t : ℝ => ∫ u : ℝ,
        productDirichletFubiniIntegrand α b t u)
        (volume.restrict (Set.Icc x y)) :=
    (hpair b).integral_prod_left
  have hsum : Integrable (fun t : ℝ =>
      ∑ b ∈ B, ∫ u : ℝ, productDirichletFubiniIntegrand α b t u)
      (volume.restrict (Set.Icc x y)) := by
    apply integrable_finsetSum B
    intro b hb
    exact heach b
  have hright : IntegrableOn
      (fun t : ℝ => c *
        ∑ b ∈ B, ∫ u : ℝ, productDirichletFubiniIntegrand α b t u)
      (Set.Icc x y) := by
    change Integrable (fun t : ℝ => c *
      ∑ b ∈ B, ∫ u : ℝ, productDirichletFubiniIntegrand α b t u)
      (volume.restrict (Set.Icc x y))
    simpa only [mul_comm] using hsum.const_mul c
  have hmono :
      (∫ t in Set.Icc x y,
        ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖) ≤
      (∫ t in Set.Icc x y, c *
        ∑ b ∈ B, ∫ u : ℝ,
          productDirichletFubiniIntegrand α b t u) := by
    apply setIntegral_mono_on hleft hright measurableSet_Icc
    intro t ht
    simpa [B, c] using
      mellinSeparationProductWindowData_norm_le hr α hq a X hX t
  calc
    _ ≤ ∫ t in Set.Icc x y, c *
        ∑ b ∈ B, ∫ u : ℝ,
          productDirichletFubiniIntegrand α b t u := hmono
    _ = c * ∑ b ∈ B,
        ∫ t in Set.Icc x y, ∫ u : ℝ,
          productDirichletFubiniIntegrand α b t u := by
      rw [integral_const_mul, integral_finsetSum B (fun b hb => heach b)]

/-- The same separated bound in interval-integral form, with the Fourier
integral outside the vertical factor integral. -/
private theorem mellinSeparationProductWindowData_intervalIntegral_le
    {r q : ℕ} (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in x..y,
      ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖) ≤
      (2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
            (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) := by
  let B : Finset (Fin r → Fin q) :=
    mellinSeparationAllowedResidues (r := r) (q := q) a
  have hsumEq :
      (∑ b ∈ B, ∫ t in Set.Icc x y, ∫ u : ℝ,
        productDirichletFubiniIntegrand α b t u) =
      ∑ b ∈ B, ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        (∫ t in x..y, ‖productDirichletPolynomialsAt α b t u‖) := by
    apply Finset.sum_congr rfl
    intro b hb
    exact productDirichletFubini_Icc_eq α b hxy
  calc
    (∫ t in x..y,
        ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖) =
        (∫ t in Set.Icc x y,
          ‖(mellinSeparationProductWindowData α q a X hX).A_X t‖) := by
      rw [intervalIntegral.integral_of_le hxy,
        ← integral_Icc_eq_integral_Ioc]
    _ ≤ (2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
            ∫ t in Set.Icc x y, ∫ u : ℝ,
              productDirichletFubiniIntegrand α b t u :=
      mellinSeparationProductWindowData_Icc_integral_le hr α hq a X hX
    _ = _ := by
      have h := congrArg (fun z : ℝ => (2 * Real.pi : ℝ)⁻¹ * z) hsumEq
      simpa [B] using h

/-- The Fourier integral of a normalized product tail equals the normalized
sum of its positive and negative vertical interval integrals. -/
private theorem productDirichletMeanObjective_kernel_integral_eq
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W V : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hV : V ∈ Set.Icc T0 (T0 * W ^ 4)) :
    ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanObjective α b T0 W u V =
      (T0 / V) *
        ((∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          (∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖)) +
        (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖))) := by
  have hWpos : 0 < W := by linarith
  have hVpos : 0 < V := lt_of_lt_of_le (lt_of_lt_of_le (by linarith) hWT) hV.1
  have hWV : W ≤ V := le_trans hWT hV.1
  have hneg : -V ≤ -W := by linarith
  have hposInt := productDirichletKernelInterval_integrable α b hWV
  have hnegInt := productDirichletKernelInterval_integrable α b hneg
  have hpoint (u : ℝ) :
      ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanObjective α b T0 W u V =
        (T0 / V) * (‖mellinSeparationLogKernelFourier u‖ *
          ((∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖) +
            (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖))) := by
    rw [productDirichletMeanObjective,
      productDirichletTailIntegral_eq_intervalIntegrals α b
        (u := u) hWpos hWV]
    ring
  calc
    ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanObjective α b T0 W u V =
      ∫ u : ℝ, (T0 / V) * (‖mellinSeparationLogKernelFourier u‖ *
        ((∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖) +
          (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖))) := by
      apply integral_congr_ae
      filter_upwards with u
      exact hpoint u
    _ = _ := by
      rw [integral_const_mul]
      have hsumFun :
          (fun u : ℝ => ‖mellinSeparationLogKernelFourier u‖ *
            ((∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖) +
              (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖))) =
          (fun u : ℝ =>
            (‖mellinSeparationLogKernelFourier u‖ *
              (∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖)) +
            (‖mellinSeparationLogKernelFourier u‖ *
              (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖))) := by
        funext u
        exact mul_add _ _ _
      rw [hsumFun, integral_add hposInt hnegInt]

/-- Each normalized product mean is bounded after Fourier weighting by the
product maximum `G_b`. -/
private theorem productDirichletMeanObjective_integral_le
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (b : Fin r → Fin q) {T0 W V : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0)
    (hV : V ∈ Set.Icc T0 (T0 * W ^ 4)) :
    (T0 / V) *
        ((∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          (∫ t in W..V, ‖productDirichletPolynomialsAt α b t u‖)) +
        (∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          (∫ t in -V..-W, ‖productDirichletPolynomialsAt α b t u‖))) ≤
      ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanEnvelope α b T0 W u := by
  calc
    _ = ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanObjective α b T0 W u V :=
      (productDirichletMeanObjective_kernel_integral_eq α b hW hWT hV).symm
    _ ≤ _ := productDirichletMeanObjective_kernel_integral_le α b hW hWT hV

/-- The Mellin mean envelope of the residue-restricted convolution is bounded
by the finite sum of its product mean envelopes. -/
theorem dirichletEnvelopeOfProductMeans
    {r q : ℕ} (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope
        (mellinSeparationProductWindowData α q a X hX) T0 W ≤
      (2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
            productDirichletMeanEnvelope α b T0 W u := by
  let w := mellinSeparationProductWindowData α q a X hX
  let B : Finset (Fin r → Fin q) :=
    mellinSeparationAllowedResidues (r := r) (q := q) a
  let c : ℝ := (2 * Real.pi : ℝ)⁻¹
  have hWpos : 0 < W := by linarith
  have hT0pos : 0 < T0 := lt_of_lt_of_le hWpos hWT
  have hA : Continuous w.A_X :=
    mellinSeparationProductWindowData_A_X_continuous α a X hX
  obtain ⟨U, hU, hEq, hmax⟩ :=
    dirichletMeanEnvelope_hasMaximum w hA hW hWT
  have hWU : W ≤ U := le_trans hWT hU.1
  have hUpos : 0 < U := lt_of_lt_of_le hT0pos hU.1
  have hneg : -U ≤ -W := by linarith
  let P : (Fin r → Fin q) → ℝ := fun b =>
    ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      (∫ t in W..U, ‖productDirichletPolynomialsAt α b t u‖)
  let N : (Fin r → Fin q) → ℝ := fun b =>
    ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
      (∫ t in -U..-W, ‖productDirichletPolynomialsAt α b t u‖)
  have hsource := dirichletAbsoluteTailIntegral_eq_intervalIntegrals
    w hA hWpos hWU
  have hpos := mellinSeparationProductWindowData_intervalIntegral_le
    hr α hq a X hX hWU
  have hnegBound := mellinSeparationProductWindowData_intervalIntegral_le
    hr α hq a X hX hneg
  have hsumId :
      (T0 / U) *
          (c * ∑ b ∈ B, P b + c * ∑ b ∈ B, N b) =
        c * ∑ b ∈ B, (T0 / U) * (P b + N b) := by
    calc
      _ = c * ((T0 / U) * ∑ b ∈ B, P b +
          (T0 / U) * ∑ b ∈ B, N b) := by ring
      _ = c * (∑ b ∈ B, (T0 / U) * P b +
          ∑ b ∈ B, (T0 / U) * N b) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = c * ∑ b ∈ B, ((T0 / U) * P b + (T0 / U) * N b) := by
        rw [← Finset.sum_add_distrib]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have hsumBound :
      ∑ b ∈ B, (T0 / U) * (P b + N b) ≤
        ∑ b ∈ B, ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanEnvelope α b T0 W u := by
    apply Finset.sum_le_sum
    intro b hb
    exact productDirichletMeanObjective_integral_le α b hW hWT hU
  have hobj : dirichletMeanEnvelopeObjective w T0 W U ≤
      c * ∑ b ∈ B, ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
        productDirichletMeanEnvelope α b T0 W u := by
    rw [dirichletMeanEnvelopeObjective, hsource]
    calc
      T0 / U *
          ((∫ t in W..U, ‖w.A_X t‖) +
            (∫ t in -U..-W, ‖w.A_X t‖)) ≤
        T0 / U * (c * ∑ b ∈ B, P b + c * ∑ b ∈ B, N b) :=
          mul_le_mul_of_nonneg_left (add_le_add hpos hnegBound)
            (div_nonneg hT0pos.le hUpos.le)
      _ = c * ∑ b ∈ B, (T0 / U) * (P b + N b) := hsumId
      _ ≤ c * ∑ b ∈ B,
          ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
            productDirichletMeanEnvelope α b T0 W u :=
        mul_le_mul_of_nonneg_left hsumBound (by dsimp [c]; positivity)
  rw [← hEq]
  simpa [w, B, c, P, N] using hobj

/-- The allowed residue tuples form a subset of the full `q`-ary tuple
space, so their number is at most `q^r`. -/
theorem mellinSeparationAllowedResidues_card_le
    {r q : ℕ} (a : ℤ) :
    (mellinSeparationAllowedResidues (r := r) (q := q) a).card ≤ q ^ r := by
  classical
  rw [mellinSeparationAllowedResidues]
  calc
    ((Finset.univ : Finset (Fin r → Fin q)).filter fun b =>
        Int.ModEq (q : ℤ) ((∏ j, (b j).1 : ℕ) : ℤ) a).card ≤
      (Finset.univ : Finset (Fin r → Fin q)).card := Finset.card_filter_le _ _
    _ = q ^ r := by simp [Fintype.card_fun]

/-- The finite residue sum on the right side of the product-envelope
inequality is integrable in the Mellin shift. -/
theorem dirichletEnvelopeOfProductMeans_rhs_integrable
    {r q : ℕ} (α : Fin r → MellinSeparationFactor)
    (a : ℤ) {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    Integrable (fun u : ℝ =>
      ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
        ‖mellinSeparationLogKernelFourier u‖ *
          productDirichletMeanEnvelope α b T0 W u) := by
  classical
  let B : Finset (Fin r → Fin q) :=
    mellinSeparationAllowedResidues (r := r) (q := q) a
  change Integrable (fun u : ℝ =>
    ∑ b ∈ B, ‖mellinSeparationLogKernelFourier u‖ *
      productDirichletMeanEnvelope α b T0 W u)
  apply integrable_finsetSum B
  intro b hb
  exact productDirichletMeanEnvelope_weighted_integrable α b hW hWT

/-- Under the logarithmic modulus and degree hypotheses, the residue tuple
count is at most the source's polylogarithmic bound. -/
theorem mellinSeparationAllowedResidues_card_le_log_power
    {r q : ℕ} (a : ℤ) (B R X : ℝ)
    (hB : 0 < B) (_hR : 0 < R) (hX : 3 ≤ X)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log X) B)
    (hr : (r : ℝ) ≤ R) :
    ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) ≤
      Real.rpow (Real.log X) (B * R) := by
  have hXpos : 0 < X := by linarith
  have hlogone : 1 < Real.log X :=
    (Real.lt_log_iff_exp_lt hXpos).2
      (lt_of_lt_of_le Real.exp_one_lt_three hX)
  have hlogpos : 0 < Real.log X := lt_trans zero_lt_one hlogone
  have hcard := mellinSeparationAllowedResidues_card_le (r := r) (q := q) a
  have hcardReal :
      ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) ≤
        ((q ^ r : ℕ) : ℝ) := by exact_mod_cast hcard
  have hpow : (q : ℝ) ^ r ≤ (Real.rpow (Real.log X) B) ^ r :=
    pow_le_pow_left₀ (by positivity) hq r
  calc
    ((mellinSeparationAllowedResidues (r := r) (q := q) a).card : ℝ) ≤
        ((q ^ r : ℕ) : ℝ) := hcardReal
    _ = (q : ℝ) ^ r := by rw [Nat.cast_pow]
    _ ≤ (Real.rpow (Real.log X) B) ^ r := hpow
    _ = Real.rpow (Real.log X) (B * (r : ℝ)) := by
      calc
        (Real.rpow (Real.log X) B) ^ r =
            Real.rpow (Real.rpow (Real.log X) B) (r : ℝ) :=
          (Real.rpow_natCast (Real.rpow (Real.log X) B) r).symm
        _ = Real.rpow (Real.log X) (B * (r : ℝ)) :=
          (Real.rpow_mul hlogpos.le B (r : ℝ)).symm
    _ ≤ Real.rpow (Real.log X) (B * R) :=
      Real.rpow_le_rpow_of_exponent_le hlogone.le
        (mul_le_mul_of_nonneg_left hr hB.le)

#print axioms FractionalPrimes.Literature.Polynomial.dirichletEnvelopeOfProductMeans
#print axioms FractionalPrimes.Literature.Polynomial.mellinSeparationAllowedResidues_card_le
#print axioms FractionalPrimes.Literature.Polynomial.dirichletEnvelopeOfProductMeans_rhs_integrable
#print axioms FractionalPrimes.Literature.Polynomial.mellinSeparationAllowedResidues_card_le_log_power

end FractionalPrimes.Literature.Polynomial

end
