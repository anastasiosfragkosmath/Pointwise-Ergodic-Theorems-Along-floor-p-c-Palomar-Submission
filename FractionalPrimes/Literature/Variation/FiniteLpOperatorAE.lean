module

public import FractionalPrimes.Literature.Variation.FiniteSimultaneousAE
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Common almost-everywhere limits for finitely many `L^p` operators

This module connects continuity in scalar `L^p` to the finite simultaneous
almost-everywhere extraction used by blueprint `lv:jump-to-variation`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- If inputs converge in `L^p`, the images under finitely many continuous
linear operators have one common subsequence converging almost everywhere
to the corresponding limiting images. -/
theorem exists_strictMono_tendsto_ae_continuousLinearMap_fintype
    {I X : Type*} [Fintype I] [MeasurableSpace X]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (μ : Measure X)
    (T : I → (Lp ℂ p μ →L[ℂ] Lp ℂ p μ))
    (f : ℕ → Lp ℂ p μ) (g : Lp ℂ p μ)
    (hfg : Tendsto f atTop (𝓝 g)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ i, ∀ᵐ x ∂μ,
        Tendsto (fun n => (T i (f (ns n)) : X → ℂ) x) atTop
          (𝓝 ((T i g : X → ℂ) x)) := by
  let F : ℕ → I → X → ℂ := fun n i => T i (f n)
  let G : I → X → ℂ := fun i => T i g
  have hmeasure : ∀ i,
      TendstoInMeasure μ (fun n => F n i) atTop (G i) := by
    intro i
    exact tendstoInMeasure_of_tendsto_Lp
      (((T i).continuous.tendsto g).comp hfg)
  obtain ⟨ns, hns, hlimit⟩ :=
    exists_strictMono_tendsto_ae_forall_fintype μ F G hmeasure
  exact ⟨ns, hns, hlimit⟩

end

end FractionalPrimes.Literature.Variation

end
