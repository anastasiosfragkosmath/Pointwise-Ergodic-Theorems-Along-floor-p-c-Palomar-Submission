module

public import FractionalPrimes.Literature.Polynomial.PolynomialOuterCutoffPreservesAverages
public import FractionalPrimes.Literature.Polynomial.PolynomialDirichletMeanEnvelopeFiniteSum
public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open MeasureTheory
open scoped BigOperators

/-- The exact cutoff and residue coefficient carried by one retained smooth
Heath--Brown label. -/
noncomputable def smoothHeathBrownComponentOuterCutoffCoefficient
    (X : ℝ) (q : ℕ) (a : ℤ) (g : ℕ → ℝ) (n : ℕ) : ℂ :=
  ((g n * polynomialOuterCutoff ((n : ℝ) / X) : ℝ) : ℂ) *
    if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0

/-- The finite Mellin polynomial of one retained coefficient component with
the source outer cutoff and residue indicator unchanged. -/
noncomputable def smoothHeathBrownComponentOuterCutoffMellinPolynomial
    (X : ℝ) (q : ℕ) (a : ℤ) (g : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ mellinWindowSupportIndices X,
    smoothHeathBrownComponentOuterCutoffCoefficient X q a g n *
      mellinDirichletMonomial n t

theorem smoothHeathBrownComponentOuterCutoffMellinPolynomial_continuous
    (X : ℝ) (q : ℕ) (a : ℤ) (g : ℕ → ℝ) :
    Continuous (smoothHeathBrownComponentOuterCutoffMellinPolynomial
      X q a g) := by
  unfold smoothHeathBrownComponentOuterCutoffMellinPolynomial
  apply continuous_finsetSum
  intro n hn
  apply continuous_const.mul
  unfold mellinDirichletMonomial
  fun_prop

private theorem smoothHeathBrownMobiusComponent_outerCutoffCoefficient_eq_sum
    {X : ℝ} (hX : 3 ≤ X) (q : ℕ) (a : ℤ) (n : ℕ)
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    outerCutoffResidueCoefficient (fun m => (paperMu m : ℝ)) X q a n =
      ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
        smoothHeathBrownComponentOuterCutoffCoefficient X q a
          (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) n := by
  classical
  have hret := smoothHeathBrownMobiusRetainedExpansion hX hn hnX
  have hmu : (paperMu (n : ℤ) : ℝ) =
      (ArithmeticFunction.moebius n : ℝ) := by
    have hnz : 0 < (n : ℤ) := by exact_mod_cast hn
    unfold paperMu
    rw [if_pos hnz]
    simp [mobiusWeight]
  by_cases hres : Int.ModEq (q : ℤ) (n : ℤ) a
  · simp only [outerCutoffResidueCoefficient,
      smoothHeathBrownComponentOuterCutoffCoefficient, hres, if_true, mul_one]
    rw [hmu]
    let ζ := polynomialOuterCutoff ((n : ℝ) / X)
    have hret' :
        (ArithmeticFunction.moebius n : ℝ) * ζ =
          ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
            smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n * ζ := by
      calc
        (ArithmeticFunction.moebius n : ℝ) * ζ =
            ζ * (ArithmeticFunction.moebius n : ℝ) := by ring
        _ = ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
              ζ * smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n := by
          simpa [ζ] using hret
        _ = ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
              smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν n * ζ := by
          apply Finset.sum_congr rfl
          intro ν hν
          ring
    simpa [ζ] using congrArg (fun x : ℝ => (x : ℂ)) hret'
  · simp [outerCutoffResidueCoefficient,
      smoothHeathBrownComponentOuterCutoffCoefficient, hres]

private theorem smoothHeathBrownVonMangoldtComponent_outerCutoffCoefficient_eq_sum
    {X : ℝ} (hX : 3 ≤ X) (q : ℕ) (a : ℤ) (n : ℕ)
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 3 * X) :
    outerCutoffResidueCoefficient (fun m => paperLambda m) X q a n =
      ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
        smoothHeathBrownComponentOuterCutoffCoefficient X q a
          (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) n := by
  classical
  have hret := smoothHeathBrownVonMangoldtRetainedExpansion hX hn hnX
  have hlam : paperLambda (n : ℤ) =
      ArithmeticFunction.vonMangoldt n := by
    have hnz : 0 < (n : ℤ) := by exact_mod_cast hn
    unfold paperLambda
    rw [if_pos hnz]
    simp [vonMangoldtWeight]
  by_cases hres : Int.ModEq (q : ℤ) (n : ℤ) a
  · simp only [outerCutoffResidueCoefficient,
      smoothHeathBrownComponentOuterCutoffCoefficient, hres, if_true, mul_one]
    rw [hlam]
    let ζ := polynomialOuterCutoff ((n : ℝ) / X)
    have hret' :
        ArithmeticFunction.vonMangoldt n * ζ =
          ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
            smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν n * ζ := by
      calc
        ArithmeticFunction.vonMangoldt n * ζ =
            ζ * ArithmeticFunction.vonMangoldt n := by ring
        _ = ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
              ζ * smoothHeathBrownVonMangoldtComponent
                (dyadicMobiusCutoff X) ν n := by
          simpa [ζ] using hret
        _ = ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
              smoothHeathBrownVonMangoldtComponent
                (dyadicMobiusCutoff X) ν n * ζ := by
          apply Finset.sum_congr rfl
          intro ν hν
          ring
    simpa [ζ] using congrArg (fun x : ℝ => (x : ℂ)) hret'
  · simp [outerCutoffResidueCoefficient,
      smoothHeathBrownComponentOuterCutoffCoefficient, hres]

/-- Exact source-frequency expansion of the cutoff Möbius polynomial into
its retained smooth Heath--Brown labels. The residue class, half-open
Dirichlet support, and outer cutoff are kept as in the original task. -/
theorem outerCutoffMobiusWindowData_A_X_eq_retainedComponentSum
    (rho : ℝ → ℝ) {X H : ℝ} (hX : 3 ≤ X) (hH : 0 < H)
    (hHX : H ≤ X) (q : ℕ) (hq : 0 < q) (a : ℤ) (t : ℝ) :
    (outerCutoffWindowData rho X H q a
      (fun n => (paperMu n : ℝ)) hX hH hHX hq
      (Or.inr rfl)).A_X t =
        ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
          smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
            (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) t := by
  classical
  let S := mellinWindowSupportIndices X
  let R := smoothHeathBrownMobiusRetainedLabels X
  have hnsupport (n : ℕ) (hn : n ∈ S) :
      0 < n ∧ (n : ℝ) ≤ 3 * X := by
    have hn' := (mellinIntervalIndices_mem_iff (by linarith [hX]) n).mp hn
    constructor
    · have hnreal : 0 < (n : ℝ) := lt_trans (by linarith [hX]) hn'.1
      exact_mod_cast hnreal
    · exact hn'.2
  have hcoef (n : ℕ) (hn : n ∈ S) :
      outerCutoffResidueCoefficient (fun m => (paperMu m : ℝ)) X q a n =
        ∑ ν ∈ R,
          smoothHeathBrownComponentOuterCutoffCoefficient X q a
            (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) n := by
    have hp := hnsupport n hn
    simpa [S, R] using
      smoothHeathBrownMobiusComponent_outerCutoffCoefficient_eq_sum
        hX q a n hp.1 hp.2
  change (∑ n ∈ S,
      outerCutoffResidueCoefficient (fun n => (paperMu n : ℝ)) X q a n *
        mellinDirichletMonomial n t) = _
  calc
    (∑ n ∈ S,
        outerCutoffResidueCoefficient (fun n => (paperMu n : ℝ)) X q a n *
          mellinDirichletMonomial n t) =
      ∑ n ∈ S, (∑ ν ∈ R,
          smoothHeathBrownComponentOuterCutoffCoefficient X q a
            (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) n) *
          mellinDirichletMonomial n t := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hcoef n hn]
    _ = ∑ ν ∈ R, ∑ n ∈ S,
          smoothHeathBrownComponentOuterCutoffCoefficient X q a
            (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) n *
            mellinDirichletMonomial n t := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
    _ = _ := by
          simp [S, R, smoothHeathBrownComponentOuterCutoffMellinPolynomial]

/-- Exact source-frequency expansion of the cutoff von Mangoldt polynomial
into its retained smooth Heath--Brown labels. -/
theorem outerCutoffVonMangoldtWindowData_A_X_eq_retainedComponentSum
    (rho : ℝ → ℝ) {X H : ℝ} (hX : 3 ≤ X) (hH : 0 < H)
    (hHX : H ≤ X) (q : ℕ) (hq : 0 < q) (a : ℤ) (t : ℝ) :
    (outerCutoffWindowData rho X H q a paperLambda hX hH hHX hq
      (Or.inl rfl)).A_X t =
        ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
          smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
            (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) t := by
  classical
  let S := mellinWindowSupportIndices X
  let R := smoothHeathBrownVonMangoldtRetainedLabels X
  have hnsupport (n : ℕ) (hn : n ∈ S) :
      0 < n ∧ (n : ℝ) ≤ 3 * X := by
    have hn' := (mellinIntervalIndices_mem_iff (by linarith [hX]) n).mp hn
    constructor
    · have hnreal : 0 < (n : ℝ) := lt_trans (by linarith [hX]) hn'.1
      exact_mod_cast hnreal
    · exact hn'.2
  have hcoef (n : ℕ) (hn : n ∈ S) :
      outerCutoffResidueCoefficient (fun m => paperLambda m) X q a n =
        ∑ ν ∈ R,
          smoothHeathBrownComponentOuterCutoffCoefficient X q a
            (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) n := by
    have hp := hnsupport n hn
    simpa [S, R] using
      smoothHeathBrownVonMangoldtComponent_outerCutoffCoefficient_eq_sum
        hX q a n hp.1 hp.2
  change (∑ n ∈ S,
      outerCutoffResidueCoefficient (fun n => paperLambda n) X q a n *
        mellinDirichletMonomial n t) = _
  calc
    (∑ n ∈ S,
        outerCutoffResidueCoefficient (fun n => paperLambda n) X q a n *
          mellinDirichletMonomial n t) =
      ∑ n ∈ S, (∑ ν ∈ R,
          smoothHeathBrownComponentOuterCutoffCoefficient X q a
            (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) n) *
          mellinDirichletMonomial n t := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hcoef n hn]
    _ = ∑ ν ∈ R, ∑ n ∈ S,
          smoothHeathBrownComponentOuterCutoffCoefficient X q a
            (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) n *
            mellinDirichletMonomial n t := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
    _ = _ := by
          simp [S, R, smoothHeathBrownComponentOuterCutoffMellinPolynomial]

/-- The source Möbius mean envelope is bounded by the finite sum of the
retained component envelopes. The analytic estimate on each component is
left explicit for the subsequent Type-I / three-group split. -/
theorem outerCutoffMobiusWindowData_envelope_le_retainedComponentEnvelopes
    (rho : ℝ → ℝ) {X H T0 W : ℝ} (hX : 3 ≤ X)
    (hH : 0 < H) (hHX : H ≤ X) (q : ℕ) (hq : 0 < q) (a : ℤ)
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope
        (outerCutoffWindowData rho X H q a
          (fun n => (paperMu n : ℝ)) hX hH hHX hq (Or.inr rfl)) T0 W ≤
      ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
        dirichletMeanEnvelopeOfA_X
          (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
            (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν))
          T0 W := by
  let w := outerCutoffWindowData rho X H q a
    (fun n => (paperMu n : ℝ)) hX hH hHX hq (Or.inr rfl)
  let R := smoothHeathBrownMobiusRetainedLabels X
  have hA : ∀ t : ℝ, w.A_X t = ∑ ν ∈ R,
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν) t := by
    intro t
    exact outerCutoffMobiusWindowData_A_X_eq_retainedComponentSum
      rho hX hH hHX q hq a t
  have hAcont : Continuous w.A_X := by
    have hlog : 1 ≤ Real.log X := by
      apply (Real.le_log_iff_exp_le (by linarith : 0 < X)).2
      exact Real.exp_one_lt_three.le.trans hX
    have hsupport : ∀ n, 0 < n →
        outerCutoffResidueCoefficient (fun n => (paperMu n : ℝ)) X q a n ≠ 0 →
          X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
      intro n hn hz
      have hs := outerCutoffResidueCoefficient_support
        (fun n => (paperMu n : ℝ)) X q a hX n hn hz
      exact ⟨hs.1, hs.2.le⟩
    simpa [w, outerCutoffWindowData] using
      (mellinWindowData_A_X_continuous rho X H
        (2 * Real.log X)
        (outerCutoffResidueCoefficient (fun n => (paperMu n : ℝ)) X q a)
        hX hH hHX (by linarith [hlog]) hsupport
        (outerCutoffResidueCoefficient_bound
          (fun n => (paperMu n : ℝ)) X q a hX (Or.inr rfl)))
  have hcomponents : ∀ ν : SmoothHeathBrownMobiusLabel X, Continuous
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)) :=
    fun ν => smoothHeathBrownComponentOuterCutoffMellinPolynomial_continuous
      X q a (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν)
  have hsum := dirichletMeanEnvelopeOfA_X_le_sum_of_finite_expansion
    R w
    (fun ν : SmoothHeathBrownMobiusLabel X =>
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
      (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν))
    hA hAcont hcomponents hW hWT
  simpa [w, R, dirichletMeanEnvelope_eq_ofA_X] using hsum

/-- The source von Mangoldt mean envelope is bounded by the finite sum of the
retained component envelopes. -/
theorem outerCutoffVonMangoldtWindowData_envelope_le_retainedComponentEnvelopes
    (rho : ℝ → ℝ) {X H T0 W : ℝ} (hX : 3 ≤ X)
    (hH : 0 < H) (hHX : H ≤ X) (q : ℕ) (hq : 0 < q) (a : ℤ)
    (hW : 2 ≤ W) (hWT : W ≤ T0) :
    dirichletMeanEnvelope
        (outerCutoffWindowData rho X H q a paperLambda hX hH hHX hq (Or.inl rfl)) T0 W ≤
      ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
        dirichletMeanEnvelopeOfA_X
          (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
            (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν))
          T0 W := by
  let w := outerCutoffWindowData rho X H q a paperLambda hX hH hHX hq (Or.inl rfl)
  let R := smoothHeathBrownVonMangoldtRetainedLabels X
  have hA : ∀ t : ℝ, w.A_X t = ∑ ν ∈ R,
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν) t := by
    intro t
    exact outerCutoffVonMangoldtWindowData_A_X_eq_retainedComponentSum
      rho hX hH hHX q hq a t
  have hlog : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < X)).2
    exact Real.exp_one_lt_three.le.trans hX
  have hsupport : ∀ n, 0 < n →
      outerCutoffResidueCoefficient paperLambda X q a n ≠ 0 →
        X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X := by
    intro n hn hz
    have hs := outerCutoffResidueCoefficient_support paperLambda X q a hX n hn hz
    exact ⟨hs.1, hs.2.le⟩
  have hAcont : Continuous w.A_X := by
    simpa [w, outerCutoffWindowData] using
      (mellinWindowData_A_X_continuous rho X H
        (2 * Real.log X) (outerCutoffResidueCoefficient paperLambda X q a)
        hX hH hHX (by linarith [hlog]) hsupport
        (outerCutoffResidueCoefficient_bound paperLambda X q a hX (Or.inl rfl)))
  have hcomponents : ∀ ν : SmoothHeathBrownVonMangoldtLabel X, Continuous
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)) :=
    fun ν => smoothHeathBrownComponentOuterCutoffMellinPolynomial_continuous
      X q a (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν)
  have hsum := dirichletMeanEnvelopeOfA_X_le_sum_of_finite_expansion
    R w
    (fun ν : SmoothHeathBrownVonMangoldtLabel X =>
      smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
        (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν))
    hA hAcont hcomponents hW hWT
  simpa [w, R, dirichletMeanEnvelope_eq_ofA_X] using hsum

#print axioms smoothHeathBrownComponentOuterCutoffMellinPolynomial_continuous
#print axioms outerCutoffMobiusWindowData_A_X_eq_retainedComponentSum
#print axioms outerCutoffMobiusWindowData_envelope_le_retainedComponentEnvelopes
#print axioms outerCutoffVonMangoldtWindowData_A_X_eq_retainedComponentSum
#print axioms outerCutoffVonMangoldtWindowData_envelope_le_retainedComponentEnvelopes

end FractionalPrimes.Literature.DirichletAdapter

end
