module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownCoefficientBookkeeping
public import Mathlib.Tactic

/-!
# Label-level packaging for retained smooth Heath--Brown components

This file exposes the generic support-retained scale dichotomy directly for
the Möbius and von Mangoldt label families in `lda:smooth-hb`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The source scale alternatives for a retained list of smooth factors. -/
def smoothHeathBrownScaleAlternativeClaim {X : ℝ}
    (fs : List (SmoothHeathBrownFactor X)) : Prop :=
    (∃ i : Fin fs.length,
      (3 / 8 : ℝ) ≤
        Real.log (smoothHeathBrownFactorScale (fs.get i)) /
          Real.log (smoothHeathBrownScaleProduct fs) ∧
        (∀ j : SmoothHeathBrownScaleIndex X, fs.get i ≠ .mobius j)) ∨
    (∃ I J K : Finset (Fin fs.length),
      Disjoint I J ∧ Disjoint I K ∧ Disjoint J K ∧
      I ∪ J ∪ K = Finset.univ ∧
      ((1 / 4 : ℝ) ≤
          Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
            Real.log (smoothHeathBrownScaleProduct fs) ∧
        Real.log (smoothHeathBrownSubgroupScaleProduct fs I) /
            Real.log (smoothHeathBrownScaleProduct fs) ≤ 1 / 2) ∧
      |Real.log (smoothHeathBrownSubgroupScaleProduct fs J) /
          Real.log (smoothHeathBrownScaleProduct fs) -
        Real.log (smoothHeathBrownSubgroupScaleProduct fs K) /
          Real.log (smoothHeathBrownScaleProduct fs)| ≤ 1 / 4 ∧
      I.Nonempty ∧ J.Nonempty ∧ K.Nonempty)

/-- Test whether a factor is logarithmic. -/
def smoothHeathBrownIsLogarithm {X : ℝ} :
    SmoothHeathBrownFactor X → Bool
  | .theta _ => false
  | .mobius _ => false
  | .logarithm _ => true

private theorem smoothHeathBrown_countP_ofFn_eq_zero {X : ℝ} {n : ℕ}
    (f : Fin n → SmoothHeathBrownFactor X)
    (hf : ∀ i, smoothHeathBrownIsLogarithm (f i) = false) :
    (List.ofFn f).countP smoothHeathBrownIsLogarithm = 0 := by
  apply List.countP_eq_zero.mpr
  intro a ha
  simp only [List.mem_ofFn'] at ha
  simp only [Set.mem_range] at ha
  rcases ha with ⟨i, rfl⟩
  simp [hf i]

/-- The Möbius label factor list has logarithmic multiplicity zero. -/
theorem smoothHeathBrownMobiusLabelFactors_log_count {X : ℝ}
    (ν : SmoothHeathBrownMobiusLabel X) :
    (smoothHeathBrownMobiusLabelFactors ν).countP smoothHeathBrownIsLogarithm = 0 := by
  rw [smoothHeathBrownMobiusLabelFactors, List.countP_append]
  rw [smoothHeathBrown_countP_ofFn_eq_zero
      (fun i : Fin ν.1.val => SmoothHeathBrownFactor.mobius (ν.2.1 i))
      (by intro i; rfl)]
  rw [smoothHeathBrown_countP_ofFn_eq_zero
      (fun i : Fin (ν.1.val - 1) => SmoothHeathBrownFactor.theta (ν.2.2 i))
      (by intro i; rfl)]

/-- A von Mangoldt label has exactly one logarithmic factor. -/
theorem smoothHeathBrownVonMangoldtLabelFactors_log_count {X : ℝ}
    (ν : SmoothHeathBrownVonMangoldtLabel X) :
    (smoothHeathBrownVonMangoldtLabelFactors ν).countP smoothHeathBrownIsLogarithm = 1 := by
  rw [smoothHeathBrownVonMangoldtLabelFactors, List.countP_append,
    List.countP_append]
  rw [smoothHeathBrown_countP_ofFn_eq_zero
      (fun i : Fin ν.1.val => SmoothHeathBrownFactor.mobius (ν.2.1.1 i))
      (by intro i; rfl)]
  rw [smoothHeathBrown_countP_ofFn_eq_zero
      (fun i : Fin (ν.1.val - 1) => SmoothHeathBrownFactor.theta (ν.2.1.2 i))
      (by intro i; rfl)]
  simp [smoothHeathBrownIsLogarithm]

/-- The Möbius label factor list contains no logarithmic factors. -/
theorem smoothHeathBrownMobiusLabelFactors_no_log {X : ℝ}
    (ν : SmoothHeathBrownMobiusLabel X) :
    ∀ f ∈ smoothHeathBrownMobiusLabelFactors ν,
      ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .logarithm j := by
  intro f hf j heq
  have hfparts :
      f ∈ List.ofFn (fun i : Fin ν.1.val =>
        SmoothHeathBrownFactor.mobius (ν.2.1 i)) ∨
      f ∈ List.ofFn (fun i : Fin (ν.1.val - 1) =>
        SmoothHeathBrownFactor.theta (ν.2.2 i)) := by
    simpa [smoothHeathBrownMobiusLabelFactors] using hf
  rcases hfparts with hmob | htheta
  · simp only [List.mem_ofFn'] at hmob
    simp only [Set.mem_range] at hmob
    rcases hmob with ⟨i, rfl⟩
    cases heq
  · simp only [List.mem_ofFn'] at htheta
    simp only [Set.mem_range] at htheta
    rcases htheta with ⟨i, rfl⟩
    cases heq

/-- Any logarithmic factor in a von Mangoldt label list is its unique final
logarithmic factor. -/
theorem smoothHeathBrownVonMangoldtLabelFactors_log_unique {X : ℝ}
    (ν : SmoothHeathBrownVonMangoldtLabel X) :
    ∀ f ∈ smoothHeathBrownVonMangoldtLabelFactors ν,
      (∃ j : SmoothHeathBrownScaleIndex X, f = .logarithm j) →
      f = .logarithm ν.2.2 := by
  intro f hf hflog
  have hfparts :
      f ∈ List.ofFn (fun i : Fin ν.1.val =>
        SmoothHeathBrownFactor.mobius (ν.2.1.1 i)) ∨
      f ∈ List.ofFn (fun i : Fin (ν.1.val - 1) =>
        SmoothHeathBrownFactor.theta (ν.2.1.2 i)) ∨
      f = SmoothHeathBrownFactor.logarithm ν.2.2 := by
    simpa [smoothHeathBrownVonMangoldtLabelFactors] using hf
  rcases hfparts with hmob | hrest
  · simp only [List.mem_ofFn'] at hmob
    simp only [Set.mem_range] at hmob
    rcases hmob with ⟨i, rfl⟩
    rcases hflog with ⟨j, hfj⟩
    cases hfj
  · rcases hrest with htheta | hlast
    · simp only [List.mem_ofFn'] at htheta
      simp only [Set.mem_range] at htheta
      rcases htheta with ⟨i, rfl⟩
      rcases hflog with ⟨j, hfj⟩
      cases hfj
    · exact hlast

/-- Every retained Möbius label has the source scale alternatives. -/
theorem smoothHeathBrownMobiusRetainedLabel_scaleAlternatives
    {X : ℝ} (hX : (2 : ℝ) ^ 35 ≤ X)
    {ν : SmoothHeathBrownMobiusLabel X}
    (hν : ν ∈ smoothHeathBrownMobiusRetainedLabels X) :
    smoothHeathBrownScaleAlternativeClaim
      (smoothHeathBrownMobiusLabelFactors ν) := by
  classical
  have hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownMobiusLabelFactors ν) :=
    (Finset.mem_filter.mp hν).2
  have hfsne : smoothHeathBrownMobiusLabelFactors ν ≠ [] := by
    intro hnil
    have hlen := smoothHeathBrownMobiusFactorCount ν
    rw [hnil] at hlen
    simp at hlen
  change smoothHeathBrownScaleAlternativeClaim
    (smoothHeathBrownMobiusLabelFactors ν)
  exact smoothHeathBrownRetainedScaleAlternatives hX
    (smoothHeathBrownMobiusFactorCount ν).2 hfsne hret

/-- Every retained von Mangoldt label has the source scale alternatives. -/
theorem smoothHeathBrownVonMangoldtRetainedLabel_scaleAlternatives
    {X : ℝ} (hX : (2 : ℝ) ^ 35 ≤ X)
    {ν : SmoothHeathBrownVonMangoldtLabel X}
    (hν : ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X) :
    smoothHeathBrownScaleAlternativeClaim
      (smoothHeathBrownVonMangoldtLabelFactors ν) := by
  classical
  have hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownVonMangoldtLabelFactors ν) :=
    (Finset.mem_filter.mp hν).2
  have hfsne : smoothHeathBrownVonMangoldtLabelFactors ν ≠ [] := by
    intro hnil
    have hlen := smoothHeathBrownVonMangoldtFactorCount ν
    rw [hnil] at hlen
    simp at hlen
  change smoothHeathBrownScaleAlternativeClaim
    (smoothHeathBrownVonMangoldtLabelFactors ν)
  exact smoothHeathBrownRetainedScaleAlternatives hX
    (smoothHeathBrownVonMangoldtFactorCount ν).2 hfsne hret

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusRetainedLabel_scaleAlternatives
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownVonMangoldtRetainedLabel_scaleAlternatives
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusLabelFactors_no_log
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownVonMangoldtLabelFactors_log_unique
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownMobiusLabelFactors_log_count
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownVonMangoldtLabelFactors_log_count
