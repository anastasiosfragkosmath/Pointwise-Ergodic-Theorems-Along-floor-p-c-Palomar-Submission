module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Simultaneous almost-everywhere subsequences for finite families

This is the finite-coordinate diagonal step used in the density passage of
blueprint `lv:jump-to-variation`.  Repeated extraction preserves convergence
already obtained for earlier coordinates because every extracted sequence is
strictly monotone and hence tends to infinity.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A finite family of sequences converging in measure admits one common
strictly monotone subsequence converging almost everywhere in every listed
coordinate. -/
theorem exists_strictMono_tendsto_ae_forall_finset
    {I X E : Type*} [MeasurableSpace X] [PseudoMetricSpace E]
    (μ : Measure X) (s : Finset I) (F : ℕ → I → X → E) (G : I → X → E)
    (hconv : ∀ i ∈ s,
      TendstoInMeasure μ (fun n => F n i) atTop (G i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ i ∈ s, ∀ᵐ x ∂μ,
        Tendsto (fun n => F (ns n) i x) atTop (𝓝 (G i x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨id, strictMono_id, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨ns, hns, hprevious⟩ := ih fun i hi =>
        hconv i (Finset.mem_insert_of_mem hi)
      have haMeasure : TendstoInMeasure μ (fun n => F (ns n) a) atTop (G a) :=
        (hconv a (Finset.mem_insert_self a s)).comp hns.tendsto_atTop
      obtain ⟨ms, hms, haAlmostEverywhere⟩ :=
        haMeasure.exists_seq_tendsto_ae
      refine ⟨ns ∘ ms, hns.comp hms, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa [Function.comp_def] using haAlmostEverywhere
      · filter_upwards [hprevious i hi] with x hx
        simpa [Function.comp_def] using hx.comp hms.tendsto_atTop

/-- Fintype form of the common almost-everywhere subsequence lemma. -/
theorem exists_strictMono_tendsto_ae_forall_fintype
    {I X E : Type*} [Fintype I] [MeasurableSpace X] [PseudoMetricSpace E]
    (μ : Measure X) (F : ℕ → I → X → E) (G : I → X → E)
    (hconv : ∀ i, TendstoInMeasure μ (fun n => F n i) atTop (G i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ i, ∀ᵐ x ∂μ,
        Tendsto (fun n => F (ns n) i x) atTop (𝓝 (G i x)) := by
  obtain ⟨ns, hns, hlimit⟩ :=
    exists_strictMono_tendsto_ae_forall_finset μ Finset.univ F G
      (fun i _ => hconv i)
  exact ⟨ns, hns, fun i => hlimit i (Finset.mem_univ i)⟩

end

end FractionalPrimes.Literature.Variation

end
