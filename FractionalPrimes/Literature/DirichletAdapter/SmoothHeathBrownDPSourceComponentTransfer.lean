module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPComponentAccumulation
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPSourceMellinFactorization
public import FractionalPrimes.Literature.Polynomial.PolynomialProductMeanEnvelope
public import FractionalPrimes.Literature.Polynomial.PolynomialDirichletMeanEnvelopeFiniteSum
public import Mathlib.Tactic

/-! The exact source-component adapter from a normalized Heath--Brown
convolution coefficient to its residue-product Mellin window. The source
cutoff, congruence condition, and `(X/2,3X]` support convention are kept. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open MeasureTheory
open scoped BigOperators

/-- If the uncut coefficient sequence agrees with the scaled normalized
factor convolution, then its exact source outer-cutoff Mellin polynomial is
the same scalar times the product-window Mellin polynomial. -/
theorem smoothHeathBrownSourceComponentMellin_eq_scaledProductWindowData
    {X : ℝ} (hX : 3 ≤ X) {r q : ℕ} (hr : 0 < r) (hq : 0 < q)
    (a : ℤ) (α : Fin r → MellinSeparationFactor) (κ : ℂ)
    (g : ℕ → ℝ) (t : ℝ)
    (hcoeff : ∀ n ∈ mellinWindowSupportIndices X,
      (g n : ℂ) = κ * toComplexArithmeticFunction
        (mellinSeparationConvolutionProduct α) n) :
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a g t =
      κ * (mellinSeparationProductWindowData α q a X hX).A_X t := by
  classical
  let c : ℕ → ℂ := fun n => (g n : ℂ)
  have hfourier := smoothHeathBrownSourceWindowMellin_eq_scaledSeparatedConvolution
    hX hr hq a α κ c t (by
      intro n hn
      exact hcoeff n hn)
  have hpoly :
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a g t =
        ∑ n ∈ mellinWindowSupportIndices X,
          c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
            (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
              mellinDirichletMonomial n t := by
    unfold smoothHeathBrownComponentOuterCutoffMellinPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    simp [c, smoothHeathBrownComponentOuterCutoffCoefficient,
      Complex.ofReal_mul, mul_assoc]
  have hdata := mellinSeparationProductWindowData_A_X_eq
    hr α hq a X hX t
  calc
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a g t =
        ∑ n ∈ mellinWindowSupportIndices X,
          c n * (polynomialOuterCutoff ((n : ℝ) / X) : ℂ) *
            (if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0) *
              mellinDirichletMonomial n t := hpoly
    _ = κ * ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        (∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, mellinSeparationLogKernelFourier u *
            mellinSeparationScaleFactor X u *
              ∏ j, mellinSeparationFactorPolynomial α q j (b j)
                (((1 / 2 : ℝ) : ℂ) + Complex.I * ((t - u : ℝ) : ℂ)))) := by
      exact hfourier
    _ = κ * (mellinSeparationProductWindowData α q a X hX).A_X t := by
      rw [hdata]
      apply congrArg (fun s : ℂ => κ *
        ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) * s))
      apply Finset.sum_congr rfl
      intro b hb
      apply integral_congr_ae
      filter_upwards with u
      simp [productDirichletPolynomialsAt]

/-- Subhomogeneity of the exact compact source mean envelope under scalar
multiplication of its Mellin polynomial. The maximum is taken over the same
closed endpoint range on both sides. -/
theorem dirichletMeanEnvelope_scaledA_X_le
    (w : MellinWindowData) (hA : Continuous w.A_X) (κ : ℂ)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope
      { w with A_X := fun t => κ * w.A_X t } T0 W ≤
        ‖κ‖ * dirichletMeanEnvelope w T0 W := by
  classical
  let wκ : MellinWindowData := { w with A_X := fun t => κ * w.A_X t }
  have hκnonneg : 0 ≤ ‖κ‖ := norm_nonneg _
  have hT0pos : 0 < T0 := lt_of_lt_of_le (by linarith : 0 < W) hWT
  have hW1 : 1 ≤ W := by linarith
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
  have hdomain : (Set.Icc T0 (T0 * W ^ 4)).Nonempty := by
    refine ⟨T0, ?_⟩
    constructor
    · rfl
    · nlinarith [mul_nonneg hT0pos.le (sub_nonneg.mpr hW4)]
  have hImageNe :
      (dirichletMeanEnvelopeObjective wκ T0 W ''
        Set.Icc T0 (T0 * W ^ 4)).Nonempty := by
    rcases hdomain with ⟨V, hV⟩
    exact ⟨dirichletMeanEnvelopeObjective wκ T0 W V, V, hV, rfl⟩
  apply csSup_le hImageNe
  rintro y ⟨V, hV, rfl⟩
  have hWpos : 0 < W := by linarith
  have hVpos : 0 < V := lt_of_lt_of_le (lt_of_lt_of_le hWpos hWT) hV.1
  have htail : dirichletAbsoluteTailIntegral wκ W V =
      ‖κ‖ * dirichletAbsoluteTailIntegral w W V := by
    unfold dirichletAbsoluteTailIntegral
    calc
      (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V}, ‖κ * w.A_X t‖) =
          ∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V},
            ‖κ‖ * ‖w.A_X t‖ := by
              apply integral_congr_ae
              filter_upwards with t
              rw [norm_mul]
      _ = ‖κ‖ *
          (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ V}, ‖w.A_X t‖) := by
            rw [integral_const_mul]
  have hobj : dirichletMeanEnvelopeObjective wκ T0 W V =
      ‖κ‖ * dirichletMeanEnvelopeObjective w T0 W V := by
    rw [dirichletMeanEnvelopeObjective, htail,
      dirichletMeanEnvelopeObjective]
    ring
  obtain ⟨U, hU, hmax, hmaxAll⟩ :=
    dirichletMeanEnvelope_hasMaximum w hA hW hWT
  have hupper := hmaxAll V hV
  rw [hobj]
  exact mul_le_mul_of_nonneg_left hupper hκnonneg

/-- Function-level form of scalar subhomogeneity for the source envelope. -/
theorem dirichletMeanEnvelopeOfA_X_le_scaled
    (A : ℝ → ℂ) (w : MellinWindowData) (hA : Continuous w.A_X)
    (κ : ℂ) (hscale : ∀ t, A t = κ * w.A_X t)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * dirichletMeanEnvelope w T0 W := by
  let wA : MellinWindowData := { w with A_X := A }
  let wκ : MellinWindowData :=
    { w with A_X := fun t => κ * w.A_X t }
  have hAeq : A = (fun t => κ * w.A_X t) := by
    funext t
    exact hscale t
  have henvEq : dirichletMeanEnvelope wA T0 W =
      dirichletMeanEnvelope wκ T0 W := by
    rw [dirichletMeanEnvelope_eq_ofA_X, dirichletMeanEnvelope_eq_ofA_X]
    exact congrArg (fun f => dirichletMeanEnvelopeOfA_X f T0 W) hAeq
  calc
    dirichletMeanEnvelopeOfA_X A T0 W =
        dirichletMeanEnvelope wA T0 W :=
      (dirichletMeanEnvelope_eq_ofA_X wA T0 W).symm
    _ = dirichletMeanEnvelope wκ T0 W := henvEq
    _ ≤ ‖κ‖ * dirichletMeanEnvelope w T0 W := by
      simpa [wκ] using dirichletMeanEnvelope_scaledA_X_le w hA κ hW hWT

/-- Combining scalar normalization with Mellin separation gives the source
component envelope directly in terms of the Fourier-kernel weighted product
mean envelopes.  This is the exact interface for the subsequent finite
group/block accumulation; it retains every residue tuple and Mellin shift. -/
theorem dirichletMeanEnvelopeOfA_X_le_scaledProductMeans
    {r q : ℕ} (hr : 0 < r) (α : Fin r → MellinSeparationFactor)
    (hq : 0 < q) (a : ℤ) (X : ℝ) (hX : 3 ≤ X)
    (κ : ℂ) (A : ℝ → ℂ)
    (hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData α q a X hX).A_X t)
    {T0 W : ℝ} (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X A T0 W ≤
      ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
            productDirichletMeanEnvelope α b T0 W u) := by
  classical
  let w := mellinSeparationProductWindowData α q a X hX
  have hA : Continuous w.A_X := by
    dsimp [w]
    exact mellinSeparationProductWindowData_A_X_continuous α a X hX
  have hscaled := dirichletMeanEnvelopeOfA_X_le_scaled A w hA κ
    (by intro t; exact hscale t) hW hWT
  have hseparate := dirichletEnvelopeOfProductMeans hr α hq a X hX hW hWT
  rw [dirichletMeanEnvelope_eq_ofA_X] at hseparate
  calc
    dirichletMeanEnvelopeOfA_X A T0 W ≤
        ‖κ‖ * dirichletMeanEnvelope w T0 W := by
          simpa [w] using hscaled
    _ ≤ ‖κ‖ * ((2 * Real.pi : ℝ)⁻¹ *
        ∑ b ∈ mellinSeparationAllowedResidues (r := r) (q := q) a,
          ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
            productDirichletMeanEnvelope α b T0 W u) :=
      mul_le_mul_of_nonneg_left hseparate (norm_nonneg κ)

/-- Exact coefficient factorization for one retained Möbius component,
including the binomial coefficient and every normalized logarithmic factor. -/
theorem smoothHeathBrownMobiusComponent_eq_scaledMellinArithmeticProduct
    {X z : ℝ} (hX : 3 ≤ X) (ν : SmoothHeathBrownMobiusLabel X)
    (n : ℕ) :
    (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n : ℂ) =
      ((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownMobiusLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ)) *
        mellinSeparationArithmeticProduct
          (fun i : Fin (smoothHeathBrownMobiusLabelFactors ν).length =>
            smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
              ((smoothHeathBrownMobiusLabelFactors ν).get i)) n := by
  classical
  let fs := smoothHeathBrownMobiusLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X) (fs.get i)
  have hraw := smoothHeathBrownConvolutionFactors_eq_scaledMellinArithmeticProduct
    (z := dyadicMobiusCutoff X) hX fs n
  rw [smoothHeathBrownMobiusComponent_apply]
  have hraw' :
      (smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownMobiusLabelFactors ν) n : ℂ) =
        (((4 * Real.log X) ^
          (smoothHeathBrownMobiusLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
          mellinSeparationArithmeticProduct
            (fun i : Fin (smoothHeathBrownMobiusLabelFactors ν).length =>
              smoothHeathBrownNormalizedMellinFactor
                (z := dyadicMobiusCutoff X)
                ((smoothHeathBrownMobiusLabelFactors ν).get i)) n := by
    simpa [fs, α] using hraw
  rw [show ((dyadicBinomialCoefficient ν.1 *
      smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownMobiusLabelFactors ν) n : ℝ) : ℂ) =
      (dyadicBinomialCoefficient ν.1 : ℂ) *
        (smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
          (smoothHeathBrownMobiusLabelFactors ν) n : ℂ) by
          exact Complex.ofReal_mul _ _]
  rw [hraw']
  ring

/-- Exact coefficient factorization for one retained von Mangoldt component. -/
theorem smoothHeathBrownVonMangoldtComponent_eq_scaledMellinArithmeticProduct
    {X z : ℝ} (hX : 3 ≤ X) (ν : SmoothHeathBrownVonMangoldtLabel X)
    (n : ℕ) :
    (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n : ℂ) =
      ((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownVonMangoldtLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ)) *
        mellinSeparationArithmeticProduct
          (fun i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length =>
            smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
              ((smoothHeathBrownVonMangoldtLabelFactors ν).get i)) n := by
  classical
  let fs := smoothHeathBrownVonMangoldtLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X) (fs.get i)
  have hraw := smoothHeathBrownConvolutionFactors_eq_scaledMellinArithmeticProduct
    (z := dyadicMobiusCutoff X) hX fs n
  rw [smoothHeathBrownVonMangoldtComponent_apply]
  have hraw' :
      (smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownVonMangoldtLabelFactors ν) n : ℂ) =
        (((4 * Real.log X) ^
          (smoothHeathBrownVonMangoldtLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ) *
          mellinSeparationArithmeticProduct
            (fun i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length =>
              smoothHeathBrownNormalizedMellinFactor
                (z := dyadicMobiusCutoff X)
                ((smoothHeathBrownVonMangoldtLabelFactors ν).get i)) n := by
    simpa [fs, α] using hraw
  rw [show ((dyadicBinomialCoefficient ν.1 *
      smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownVonMangoldtLabelFactors ν) n : ℝ) : ℂ) =
      (dyadicBinomialCoefficient ν.1 : ℂ) *
        (smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
          (smoothHeathBrownVonMangoldtLabelFactors ν) n : ℂ) by
          exact Complex.ofReal_mul _ _]
  rw [hraw']
  ring

/-- A retained Möbius component's exact outer-cutoff Dirichlet polynomial is
the source scalar times the product-window polynomial of its normalized
factor list. -/
theorem smoothHeathBrownMobiusComponentMellin_eq_scaledProductWindowData
    {X z : ℝ} (hX : 3 ≤ X) {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ν : SmoothHeathBrownMobiusLabel X) (t : ℝ) :
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) t =
      ((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownMobiusLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ)) *
        (mellinSeparationProductWindowData
          (fun i : Fin (smoothHeathBrownMobiusLabelFactors ν).length =>
            smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
              ((smoothHeathBrownMobiusLabelFactors ν).get i))
          q a X hX).A_X t := by
  classical
  let fs := smoothHeathBrownMobiusLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X) (fs.get i)
  let κ : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  have hr : 0 < fs.length := by
    have hcount := smoothHeathBrownMobiusFactorCount ν
    dsimp [fs]
    omega
  have hcoeff : ∀ n ∈ mellinWindowSupportIndices X,
      (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n : ℂ) =
        κ * toComplexArithmeticFunction
          (mellinSeparationConvolutionProduct α) n := by
    intro n hn
    have h := smoothHeathBrownMobiusComponent_eq_scaledMellinArithmeticProduct
      (z := dyadicMobiusCutoff X) hX ν n
    change _ = _ at h
    simpa [α, κ, fs, mellinSeparationArithmeticProduct_eq_tupleConvolution]
      using h
  have hresult := smoothHeathBrownSourceComponentMellin_eq_scaledProductWindowData
    hX hr hq a α κ
      (fun n => smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n) t
      hcoeff
  have hfun : (fun n => smoothHeathBrownMobiusComponent
      (dyadicMobiusCutoff X) ν n) =
      smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν := by
    funext n
    rfl
  rw [hfun] at hresult
  simpa [α, κ, fs] using hresult

/-- The corresponding exact source-polynomial factorization for a retained
von Mangoldt component. -/
theorem smoothHeathBrownVonMangoldtComponentMellin_eq_scaledProductWindowData
    {X z : ℝ} (hX : 3 ≤ X) {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ν : SmoothHeathBrownVonMangoldtLabel X) (t : ℝ) :
    smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) t =
      ((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownVonMangoldtLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ)) *
        (mellinSeparationProductWindowData
          (fun i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length =>
            smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
              ((smoothHeathBrownVonMangoldtLabelFactors ν).get i))
          q a X hX).A_X t := by
  classical
  let fs := smoothHeathBrownVonMangoldtLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X) (fs.get i)
  let κ : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  have hr : 0 < fs.length := by
    have hcount := smoothHeathBrownVonMangoldtFactorCount ν
    dsimp [fs]
    omega
  have hcoeff : ∀ n ∈ mellinWindowSupportIndices X,
      (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n : ℂ) =
        κ * toComplexArithmeticFunction
          (mellinSeparationConvolutionProduct α) n := by
    intro n hn
    have h := smoothHeathBrownVonMangoldtComponent_eq_scaledMellinArithmeticProduct
      (z := dyadicMobiusCutoff X) hX ν n
    change _ = _ at h
    simpa [α, κ, fs, mellinSeparationArithmeticProduct_eq_tupleConvolution]
      using h
  have hresult := smoothHeathBrownSourceComponentMellin_eq_scaledProductWindowData
    hX hr hq a α κ
      (fun n => smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n) t
      hcoeff
  have hfun : (fun n => smoothHeathBrownVonMangoldtComponent
      (dyadicMobiusCutoff X) ν n) =
      smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν := by
    funext n
    rfl
  rw [hfun] at hresult
  simpa [α, κ, fs] using hresult

/-- The exact source envelope of one retained Möbius component is controlled
by the product-window envelope with its full scalar normalization. -/
theorem smoothHeathBrownMobiusComponentEnvelope_le_scaledProductWindow
    {X z : ℝ} (hX : 3 ≤ X) {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ν : SmoothHeathBrownMobiusLabel X) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)) T0 W ≤
      ‖((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownMobiusLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ))‖ *
        dirichletMeanEnvelope
          (mellinSeparationProductWindowData
            (fun i : Fin (smoothHeathBrownMobiusLabelFactors ν).length =>
              smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
                ((smoothHeathBrownMobiusLabelFactors ν).get i))
            q a X hX) T0 W := by
  classical
  let fs := smoothHeathBrownMobiusLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X) (fs.get i)
  let κ : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  let w := mellinSeparationProductWindowData α q a X hX
  let A := smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
    (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)
  have hA : Continuous w.A_X := by
    dsimp [w, α, fs]
    exact mellinSeparationProductWindowData_A_X_continuous _ a X hX
  have hscale : ∀ t, A t = κ * w.A_X t := by
    intro t
    simpa [A, w, κ, α, fs] using
      smoothHeathBrownMobiusComponentMellin_eq_scaledProductWindowData
        (z := z) hX hq a ν t
  have hbound := dirichletMeanEnvelopeOfA_X_le_scaled A w hA κ hscale hW hWT
  simpa [A, w, κ, α, fs] using hbound

/-- The exact source envelope of one retained von Mangoldt component has the
same product-window reduction. -/
theorem smoothHeathBrownVonMangoldtComponentEnvelope_le_scaledProductWindow
    {X z : ℝ} (hX : 3 ≤ X) {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ν : SmoothHeathBrownVonMangoldtLabel X) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)) T0 W ≤
      ‖((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownVonMangoldtLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ))‖ *
        dirichletMeanEnvelope
          (mellinSeparationProductWindowData
            (fun i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length =>
              smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
                ((smoothHeathBrownVonMangoldtLabelFactors ν).get i))
            q a X hX) T0 W := by
  classical
  let fs := smoothHeathBrownVonMangoldtLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X) (fs.get i)
  let κ : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  let w := mellinSeparationProductWindowData α q a X hX
  let A := smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
    (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)
  have hA : Continuous w.A_X := by
    dsimp [w, α, fs]
    exact mellinSeparationProductWindowData_A_X_continuous _ a X hX
  have hscale : ∀ t, A t = κ * w.A_X t := by
    intro t
    simpa [A, w, κ, α, fs] using
      smoothHeathBrownVonMangoldtComponentMellin_eq_scaledProductWindowData
        (z := z) hX hq a ν t
  have hbound := dirichletMeanEnvelopeOfA_X_le_scaled A w hA κ hscale hW hWT
  simpa [A, w, κ, α, fs] using hbound

/-- A retained Möbius component is bounded by the exact finite sum of
Fourier-kernel weighted product envelopes of its normalized factors. -/
theorem smoothHeathBrownMobiusComponentEnvelope_le_scaledProductMeans
    {X z : ℝ} (hX : 3 ≤ X) {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ν : SmoothHeathBrownMobiusLabel X) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)) T0 W ≤
      ‖((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownMobiusLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ))‖ *
        ((2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ mellinSeparationAllowedResidues
              (r := (smoothHeathBrownMobiusLabelFactors ν).length)
              (q := q) a,
            ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
              productDirichletMeanEnvelope
                (fun i : Fin (smoothHeathBrownMobiusLabelFactors ν).length =>
                  smoothHeathBrownNormalizedMellinFactor
                    (z := dyadicMobiusCutoff X)
                    ((smoothHeathBrownMobiusLabelFactors ν).get i))
                b T0 W u) := by
  classical
  let fs := smoothHeathBrownMobiusLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
      (fs.get i)
  let κ : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  let A := smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
    (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)
  have hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData α q a X hX).A_X t := by
    intro t
    simpa [A, κ, α, fs] using
      smoothHeathBrownMobiusComponentMellin_eq_scaledProductWindowData
        (z := z) hX hq a ν t
  have hlen : 0 < fs.length := by
    have hcount := smoothHeathBrownMobiusFactorCount ν
    dsimp [fs]
    omega
  have hbound := dirichletMeanEnvelopeOfA_X_le_scaledProductMeans
    hlen α hq a X hX κ A hscale hW hWT
  simpa [A, κ, α, fs] using hbound

/-- The corresponding source-facing product-mean bound for one retained
von Mangoldt component. -/
theorem smoothHeathBrownVonMangoldtComponentEnvelope_le_scaledProductMeans
    {X z : ℝ} (hX : 3 ≤ X) {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ν : SmoothHeathBrownVonMangoldtLabel X) {T0 W : ℝ}
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)) T0 W ≤
      ‖((dyadicBinomialCoefficient ν.1 : ℂ) *
        (((4 * Real.log X) ^
          (smoothHeathBrownVonMangoldtLabelFactors ν).countP
            smoothHeathBrownTypeILogFactor : ℝ) : ℂ))‖ *
        ((2 * Real.pi : ℝ)⁻¹ *
          ∑ b ∈ mellinSeparationAllowedResidues
              (r := (smoothHeathBrownVonMangoldtLabelFactors ν).length)
              (q := q) a,
            ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
              productDirichletMeanEnvelope
                (fun i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length =>
                  smoothHeathBrownNormalizedMellinFactor
                    (z := dyadicMobiusCutoff X)
                    ((smoothHeathBrownVonMangoldtLabelFactors ν).get i))
                b T0 W u) := by
  classical
  let fs := smoothHeathBrownVonMangoldtLabelFactors ν
  let α : Fin fs.length → MellinSeparationFactor := fun i =>
    smoothHeathBrownNormalizedMellinFactor (z := dyadicMobiusCutoff X)
      (fs.get i)
  let κ : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ) *
    (((4 * Real.log X) ^ fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)
  let A := smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
    (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)
  have hscale : ∀ t, A t = κ *
      (mellinSeparationProductWindowData α q a X hX).A_X t := by
    intro t
    simpa [A, κ, α, fs] using
      smoothHeathBrownVonMangoldtComponentMellin_eq_scaledProductWindowData
        (z := z) hX hq a ν t
  have hlen : 0 < fs.length := by
    have hcount := smoothHeathBrownVonMangoldtFactorCount ν
    dsimp [fs]
    omega
  have hbound := dirichletMeanEnvelopeOfA_X_le_scaledProductMeans
    hlen α hq a X hX κ A hscale hW hWT
  simpa [A, κ, α, fs] using hbound

/-- The source Möbius mean envelope is accumulated over all retained labels,
with each component already converted to its exact residue-product Fourier
mean. -/
theorem outerCutoffMobiusWindowData_envelope_le_retainedProductMeans
    (rho : ℝ → ℝ) {X H T0 W : ℝ} (hX : 3 ≤ X)
    (hH : 0 < H) (hHX : H ≤ X) (q : ℕ) (hq : 0 < q) (a : ℤ)
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope
        (outerCutoffWindowData rho X H q a
          (fun n => (paperMu n : ℝ)) hX hH hHX hq (Or.inr rfl)) T0 W ≤
      ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
        ‖((dyadicBinomialCoefficient ν.1 : ℂ) *
          (((4 * Real.log X) ^
            (smoothHeathBrownMobiusLabelFactors ν).countP
              smoothHeathBrownTypeILogFactor : ℝ) : ℂ))‖ *
          ((2 * Real.pi : ℝ)⁻¹ *
            ∑ b ∈ mellinSeparationAllowedResidues
                (r := (smoothHeathBrownMobiusLabelFactors ν).length)
                (q := q) a,
              ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
                productDirichletMeanEnvelope
                  (fun i : Fin (smoothHeathBrownMobiusLabelFactors ν).length =>
                    smoothHeathBrownNormalizedMellinFactor
                      (z := dyadicMobiusCutoff X)
                      ((smoothHeathBrownMobiusLabelFactors ν).get i))
                  b T0 W u) := by
  classical
  have haccum := outerCutoffMobiusWindowData_envelope_le_retainedComponentEnvelopes
    rho hX hH hHX q hq a hW hWT
  calc
    _ ≤ ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
          dirichletMeanEnvelopeOfA_X
            (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
              (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν))
            T0 W := haccum
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ν hν
      exact smoothHeathBrownMobiusComponentEnvelope_le_scaledProductMeans
        (z := dyadicMobiusCutoff X) hX hq a ν hW hWT

/-- The source von Mangoldt mean envelope has the parallel finite retained
label accumulation with its exact logarithmic source scalar. -/
theorem outerCutoffVonMangoldtWindowData_envelope_le_retainedProductMeans
    (rho : ℝ → ℝ) {X H T0 W : ℝ} (hX : 3 ≤ X)
    (hH : 0 < H) (hHX : H ≤ X) (q : ℕ) (hq : 0 < q) (a : ℤ)
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope
        (outerCutoffWindowData rho X H q a paperLambda hX hH hHX hq
          (Or.inl rfl)) T0 W ≤
      ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
        ‖((dyadicBinomialCoefficient ν.1 : ℂ) *
          (((4 * Real.log X) ^
            (smoothHeathBrownVonMangoldtLabelFactors ν).countP
              smoothHeathBrownTypeILogFactor : ℝ) : ℂ))‖ *
          ((2 * Real.pi : ℝ)⁻¹ *
            ∑ b ∈ mellinSeparationAllowedResidues
                (r := (smoothHeathBrownVonMangoldtLabelFactors ν).length)
                (q := q) a,
              ∫ u : ℝ, ‖mellinSeparationLogKernelFourier u‖ *
                productDirichletMeanEnvelope
                  (fun i : Fin (smoothHeathBrownVonMangoldtLabelFactors ν).length =>
                    smoothHeathBrownNormalizedMellinFactor
                      (z := dyadicMobiusCutoff X)
                      ((smoothHeathBrownVonMangoldtLabelFactors ν).get i))
                  b T0 W u) := by
  classical
  have haccum := outerCutoffVonMangoldtWindowData_envelope_le_retainedComponentEnvelopes
    rho hX hH hHX q hq a hW hWT
  calc
    _ ≤ ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
          dirichletMeanEnvelopeOfA_X
            (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
              (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν))
            T0 W := haccum
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ν hν
      exact smoothHeathBrownVonMangoldtComponentEnvelope_le_scaledProductMeans
        (z := dyadicMobiusCutoff X) hX hq a ν hW hWT

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.dirichletMeanEnvelopeOfA_X_le_scaledProductMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusComponentEnvelope_le_scaledProductMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownVonMangoldtComponentEnvelope_le_scaledProductMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.outerCutoffMobiusWindowData_envelope_le_retainedProductMeans
#print axioms FractionalPrimes.Literature.DirichletAdapter.outerCutoffVonMangoldtWindowData_envelope_le_retainedProductMeans
