module

public import FractionalPrimes.FiniteSupportLpGeneral
public import Mathlib.Topology.DenseEmbedding

@[expose] public section

/-!
# Finite-support density and bounded-operator extension

Mathlib's `lp.hasSum_single` gives the convergence of finite coordinate
truncations.  This module transfers that result through the project's
isometric sequence-`lp`/counting-measure-`Lp` bridge, then records the generic
closed-set argument extending a continuous linear operator estimate from
these exact finite-support inputs.
-/

namespace FractionalPrimes

open MeasureTheory
open Filter
open scoped ENNReal Topology

noncomputable section

variable {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]

/-- The exact finite truncation in sequence `lp` is the finite sum of the
corresponding coordinate vectors. -/
theorem finiteSupportSequenceLpGeneral_eq_sum_single
    (s : Finset ℤ) (f : ℤ → ℂ) :
    finiteSupportSequenceLpGeneral hp0 hpTop Fact.out s f =
      ∑ k ∈ s, lp.single p k (f k) := by
  classical
  apply lp.ext
  funext k
  rw [finiteSupportSequenceLpGeneral_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

/-- Exact finite-support counting-measure `Lp` inputs are dense for every
finite exponent `p ≥ 1`. The truncation is the existing approved
`if k ∈ s then f k else 0` constructor. -/
theorem finiteSupportCountLpGeneral_dense :
    DenseRange (fun q : Finset ℤ × (ℤ → ℂ) =>
      finiteSupportCountLpGeneral hp0 hpTop Fact.out q.1 q.2) := by
  classical
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  let fSeq : lp (fun _ : ℤ => ℂ) p := countLpToGeneralLp hp0 hpTop f
  have hsum : HasSum (fun k : ℤ => lp.single p k (fSeq k)) fSeq :=
    lp.hasSum_single hpTop fSeq
  have htend :
      Tendsto (fun s : Finset ℤ => ∑ k ∈ s, lp.single p k (fSeq k))
        atTop (𝓝 fSeq) := by
    simpa only [HasSum, SummationFilter.unconditional_filter] using hsum
  have hnear : ∀ᶠ s : Finset ℤ in atTop,
      dist (∑ k ∈ s, lp.single p k (fSeq k)) fSeq < ε :=
    (Metric.tendsto_nhds.mp htend) ε hε
  obtain ⟨s, hs⟩ := hnear.exists
  let truncLp : Lp ℂ p (Measure.count : Measure ℤ) :=
    finiteSupportCountLpGeneral hp0 hpTop Fact.out s (fSeq : ℤ → ℂ)
  let truncSeq : lp (fun _ : ℤ => ℂ) p :=
    finiteSupportSequenceLpGeneral hp0 hpTop Fact.out s (fSeq : ℤ → ℂ)
  have htruncBridge :
      truncLp = generalLpToCountLp hp0 hpTop truncSeq := by
    change finiteSupportCountLpGeneral hp0 hpTop Fact.out s (fSeq : ℤ → ℂ) =
      generalLpToCountLp hp0 hpTop
        (finiteSupportSequenceLpGeneral hp0 hpTop Fact.out s (fSeq : ℤ → ℂ))
    apply Lp.ext
    apply ae_count_int_iff_forall.mpr
    intro k
    rw [generalLpToCountLp_apply, finiteSupportSequenceLpGeneral_apply,
      finiteSupportCountLpGeneral_apply]
  have hfBridge : generalLpToCountLp hp0 hpTop fSeq = f := by
    dsimp [fSeq]
    exact generalLpToCountLp_countLpToGeneralLp hp0 hpTop f
  have hdist : dist f truncLp =
      dist (∑ k ∈ s, lp.single p k (fSeq k)) fSeq := by
    calc
      dist f truncLp = ‖f - truncLp‖ := dist_eq_norm _ _
      _ = ‖generalLpToCountLp hp0 hpTop
            (fSeq - ∑ k ∈ s, lp.single p k (fSeq k))‖ := by
        rw [← hfBridge, htruncBridge, ← map_sub]
        change ‖generalLpToCountLp hp0 hpTop
            (fSeq - finiteSupportSequenceLpGeneral hp0 hpTop Fact.out s
              (fSeq : ℤ → ℂ))‖ = _
        rw [finiteSupportSequenceLpGeneral_eq_sum_single hp0 hpTop s
          (fSeq : ℤ → ℂ)]
      _ = ‖fSeq - ∑ k ∈ s, lp.single p k (fSeq k)‖ :=
        generalLpToCountLp_norm hp0 hpTop _
      _ = dist (∑ k ∈ s, lp.single p k (fSeq k)) fSeq := by
        rw [dist_eq_norm]
        exact norm_sub_rev _ _
  refine ⟨truncLp, ⟨(s, (fSeq : ℤ → ℂ)), ?_⟩, ?_⟩
  · rfl
  · rw [hdist]
    exact hs

/-- A continuous linear operator bound proved on the exact finite-support
counting-`Lp` inputs extends to all counting-`Lp` inputs. This isolates the
density step used after the finite-output interpolation estimate. -/
theorem continuousLinearMap_bound_of_finiteSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ] F) (C : ℝ)
    (hfinite : ∀ s : Finset ℤ, ∀ g : ℤ → ℂ,
      ‖T (finiteSupportCountLpGeneral hp0 hpTop Fact.out s g)‖ ≤
        C * ‖finiteSupportCountLpGeneral hp0 hpTop Fact.out s g‖) :
    ∀ f : Lp ℂ p (Measure.count : Measure ℤ), ‖T f‖ ≤ C * ‖f‖ := by
  have hdense : DenseRange (fun q : Finset ℤ × (ℤ → ℂ) =>
      finiteSupportCountLpGeneral hp0 hpTop Fact.out q.1 q.2) :=
    finiteSupportCountLpGeneral_dense hp0 hpTop
  have hclosed : IsClosed {f : Lp ℂ p (Measure.count : Measure ℤ) |
      ‖T f‖ ≤ C * ‖f‖} := by
    exact isClosed_le (continuous_norm.comp T.continuous)
      (continuous_const.mul continuous_norm)
  exact isClosed_property hdense hclosed (fun q => hfinite q.1 q.2)

end

end FractionalPrimes
