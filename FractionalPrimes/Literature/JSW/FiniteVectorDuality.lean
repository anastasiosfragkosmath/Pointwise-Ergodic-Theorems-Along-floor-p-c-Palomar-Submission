module

public import FractionalPrimes.Literature.JSW.VectorDuality
public import FractionalPrimes.Literature.JSW.ComplexMeasureYoung
public import FractionalPrimes.Literature.JSW.CommonNullSet

/-!
# Aggregate finite-vector duality and convolution package

This module collects, without changing their statements, all clauses of
blueprint lemma `lj:vector-duality` under its manifest-facing declaration.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The exact verified clauses of blueprint lemma `lj:vector-duality` for
the finite Euclidean spaces `ℂ^N`. -/
structure FiniteVectorDuality where
  /-- Exact `Lᵖ(ℂ^N)` duality over the full conjugate-exponent unit ball. -/
  duality : ∀ {N : ℕ} {p q : ℝ}, p.HolderConjugate q →
    ∀ {F : ℝ → EuclideanSpace ℂ (Fin N)},
      MemLp F (ENNReal.ofReal p) volume →
      lpNorm F (ENNReal.ofReal p) volume =
        sSup (lpDualPairingValues volume q F)
  /-- The same supremum is obtained from bounded compactly supported tests. -/
  bounded_compact_tests : ∀ {N : ℕ} {p q : ℝ}, p.HolderConjugate q →
    ∀ {F : ℝ → EuclideanSpace ℂ (Fin N)},
      MemLp F (ENNReal.ofReal p) volume →
      lpNorm F (ENNReal.ofReal p) volume =
        sSup (boundedCompactLpDualPairingValues q F)
  /-- Scalar/vector adjoints have equal operator norms at conjugate
  exponents. -/
  adjoint_norm : ∀ {N : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hpq.symm.lt.le⟩
    ∀ (T : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin N)) (ENNReal.ofReal p)
          (volume : Measure ℝ))
      (S : Lp (EuclideanSpace ℂ (Fin N)) (ENNReal.ofReal q)
          (volume : Measure ℝ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)),
      (∀ f g,
        (∫ x, inner ℂ
            ((T f : Lp (EuclideanSpace ℂ (Fin N)) (ENNReal.ofReal p)
              (volume : Measure ℝ)) x)
            ((g : Lp (EuclideanSpace ℂ (Fin N)) (ENNReal.ofReal q)
              (volume : Measure ℝ)) x) ∂volume) =
          ∫ x, inner ℂ
            ((f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) x)
            ((S g : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ)) x)
              ∂volume) →
      ‖T‖ = ‖S‖
  /-- Young's inequality for a finite complex measure at finite exponents. -/
  young_finite : ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ p (volume : Measure ℝ)),
      ‖lpComplexMeasureConvolution p μ F‖ ≤
        μ.variation.real Set.univ * ‖F‖
  /-- Young's inequality, including `L∞` membership, at the endpoint. -/
  young_top : ∀ (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f : ℝ → ℂ) (hf : MemLp f ∞ (volume : Measure ℝ)),
      MemLp (complexMeasureConvolution μ f hf.aestronglyMeasurable) ∞
          (volume : Measure ℝ) ∧
        lpNorm (complexMeasureConvolution μ f hf.aestronglyMeasurable) ∞
            (volume : Measure ℝ) ≤
          μ.variation.real Set.univ * lpNorm f ∞ (volume : Measure ℝ)
  /-- Pointwise Cauchy--Schwarz for convolution by a positive probability
  measure. -/
  probability_square : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℂ) (x : ℝ),
      Integrable (fun y => f (x - y)) μ →
      Integrable (fun y => ‖f (x - y)‖ ^ 2) μ →
      ‖jswConvolution μ f x‖ ^ 2 ≤ ∫ y, ‖f (x - y)‖ ^ 2 ∂μ
  /-- A countable family of representatives can be chosen simultaneously
  outside one exceptional null set. -/
  common_null_set : ∀ {α β ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (f g : ι → α → β),
      (∀ i, f i =ᵐ[μ] g i) →
      ∃ N : Set α, μ N = 0 ∧ ∀ x, x ∉ N → ∀ i, f i x = g i x

/-- Manifest-facing proof of all clauses of `lj:vector-duality`. -/
theorem finiteVectorDuality : FiniteVectorDuality where
  duality := by
    intro N p q hpq F hF
    exact lpNorm_eq_sSup_dualPairingValues hpq hF
  bounded_compact_tests := by
    intro N p q hpq F hF
    exact lpNorm_eq_sSup_boundedCompactLpDualPairingValues hpq hF
  adjoint_norm := by
    intro N p q hpq
    exact lpAdjointOperator_norm_eq hpq
  young_finite := by
    intro p hpFact hp μ hμ F
    exact norm_lpComplexMeasureConvolution_le hp μ F
  young_top := by
    intro μ hμ f hf
    exact complexMeasureConvolution_memLp_top_and_norm_le μ f hf
  probability_square := by
    intro μ hμ f x hf hf_sq
    exact jswProbabilityConvolution_square_le μ f x hf hf_sq
  common_null_set := by
    intro α β ι hα hι μ f g hfg
    exact exists_common_null_set_for_representatives μ f g hfg

end

end FractionalPrimes.Literature.JSW
