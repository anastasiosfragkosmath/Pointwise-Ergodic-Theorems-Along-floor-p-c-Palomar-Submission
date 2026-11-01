module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalBasic
public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalHomogeneity
public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalRestriction
public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalPartition
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Aggregate package for `lu:maximal-basic`

This package collects the exact maximal-sum clauses from the approved
blueprint. Its seminorm is the existing `progressionMaximalSum`; the remaining
fields expose the whole-interval lower and upper bounds, progression
restriction identity, and finite AP-partition subadditivity.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- The verified conclusions of blueprint lemma `lu:maximal-basic` for one
finite integer interval. -/
structure ProgressionMaximalBasic (I : FiniteIntegerInterval) where
  /-- The maximal sum, bundled as a complex seminorm on functions on `I`. -/
  seminorm : Seminorm ℂ ({n : ℤ // n ∈ I.points} → ℂ)
  /-- The bundled seminorm has exactly the blueprint maximal-sum function. -/
  seminorm_apply : ∀ f, seminorm f = progressionMaximalSum I f
  /-- The whole interval is an admissible progression. -/
  interval_lower : ∀ f,
    ‖∑ x ∈ I.points.attach, f x‖ ≤ progressionMaximalSum I f
  /-- Pointwise summation bounds the maximal sum from above. -/
  interval_upper : ∀ f,
    progressionMaximalSum I f ≤ ∑ x ∈ I.points.attach, ‖f x‖
  /-- Restriction to any contained finite arithmetic progression. -/
  restriction : ∀ (P₀ : Finset ℤ) (_hP₀ : isFiniteArithmeticProgression P₀)
    (hP₀I : P₀ ⊆ I.points) (f : {n : ℤ // n ∈ I.points} → ℂ),
      progressionMaximalSum I
          (fun n => if hn : n.1 ∈ P₀ then f ⟨n.1, hP₀I hn⟩ else 0) =
        progressionMaximalSumOnFiniteSet P₀
          (fun n => f ⟨n.1, hP₀I n.2⟩)
  /-- Subadditivity over an explicitly specified finite partition by APs. -/
  partition : ∀ (parts : Finset (Finset ℤ)),
    (∀ P ∈ parts, P ⊆ I.points) →
    (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) →
    parts.biUnion id = I.points →
    (∀ P ∈ parts, isFiniteArithmeticProgression P) → ∀ f,
      progressionMaximalSum I f ≤
        ∑ P ∈ parts,
          progressionMaximalSumOnFiniteSet P
            (fun n => extendByZero I.points f n.1)

/-- The manifest-facing aggregate for blueprint lemma `lu:maximal-basic`. -/
noncomputable def progressionMaximalBasic (I : FiniteIntegerInterval) :
    ProgressionMaximalBasic I where
  seminorm := Seminorm.of (progressionMaximalSum I)
    (fun f g => progressionMaximalSum_add_le I f g)
    (fun c f => by
      have hfun : (c • f) = (fun n => c * f n) := by
        funext n
        simp [Pi.smul_apply, smul_eq_mul]
      rw [hfun]
      exact progressionMaximalSum_smul I c f)
  seminorm_apply := fun f => rfl
  interval_lower := progressionMaximalSum_interval_lower I
  interval_upper := progressionMaximalSum_le_interval_norm_sum I
  restriction := fun P₀ hP₀ hP₀I f =>
    progressionMaximalSum_restrict_to_progression I P₀ hP₀ hP₀I f
  partition := fun parts hsubset hdisjoint hcover hAP f =>
    progressionMaximalSum_le_sum_finiteProgressionPartition
      I parts hsubset hdisjoint hcover hAP f

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalBasic
