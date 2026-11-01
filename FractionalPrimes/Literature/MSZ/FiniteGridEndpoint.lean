module

public import FractionalPrimes.FiniteMomentExhaustion

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal

/-- A finite family of contractions has a finite maximal function with the
expected cardinality bound. This is the generic sequence-space endpoint used
for `N_{K,L}` in the approved finite-grid lemma. -/
theorem finiteGridMaximalMomentBound
    {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (s : Finset ι) (hs : s.Nonempty)
    (T : ι → lp (fun _ : ℤ => ℂ) p →
      lp (fun _ : ℤ => ℂ) p)
    (hT : ∀ i ∈ s, ∀ g, ‖T i g‖ ≤ ‖g‖)
    (f : lp (fun _ : ℤ => ℂ) p) (u : Finset ℤ) :
    (∑ x ∈ u,
      (s.sup' hs (fun i => ‖T i f x‖)) ^ p.toReal) ≤
        (s.card : ℝ) * ‖f‖ ^ p.toReal := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  calc
    (∑ x ∈ u,
        (s.sup' hs (fun i => ‖T i f x‖)) ^ p.toReal) ≤
        ∑ x ∈ u, ∑ i ∈ s, ‖T i f x‖ ^ p.toReal := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hs
            (fun i => ‖T i f x‖)
          rw [hsup]
          exact Finset.single_le_sum
            (f := fun j => ‖T j f x‖ ^ p.toReal)
            (fun j hj => Real.rpow_nonneg (norm_nonneg (T j f x)) _)
            hi
    _ = ∑ i ∈ s, ∑ x ∈ u, ‖T i f x‖ ^ p.toReal := by
          rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ s, ‖T i f‖ ^ p.toReal := by
          apply Finset.sum_le_sum
          intro i hi
          exact lp.sum_rpow_le_norm_rpow hp (T i f) u
    _ ≤ ∑ i ∈ s, ‖f‖ ^ p.toReal := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.rpow_le_rpow (norm_nonneg _) (hT i hi f) hp.le
    _ = (s.card : ℝ) * ‖f‖ ^ p.toReal := by simp

theorem finiteGridMaximalValue_nonneg
    {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : Finset ι) (hs : s.Nonempty)
    (T : ι → lp (fun _ : ℤ => ℂ) p → lp (fun _ : ℤ => ℂ) p)
    (f : lp (fun _ : ℤ => ℂ) p) (x : ℤ) :
    0 ≤ s.sup' hs (fun i => ‖T i f x‖) := by
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hs
    (fun i => ‖T i f x‖)
  rw [hsup]
  exact norm_nonneg _

theorem finiteGridMaximalLpMomentBound
    {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (s : Finset ι) (hs : s.Nonempty)
    (T : ι → lp (fun _ : ℤ => ℂ) p → lp (fun _ : ℤ => ℂ) p)
    (hT : ∀ i ∈ s, ∀ g, ‖T i g‖ ≤ ‖g‖)
    (f : lp (fun _ : ℤ => ℂ) p) (u : Finset ℤ) :
    ∑ x ∈ u, ‖s.sup' hs (fun i => ‖T i f x‖)‖ ^ p.toReal ≤
      (s.card : ℝ) * ‖f‖ ^ p.toReal := by
  have h := finiteGridMaximalMomentBound hp0 hpTop s hs T hT f u
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (finiteGridMaximalValue_nonneg s hs T f _)] using h

/-- The `ℓᵖ` sequence associated to the finite maximal function. -/
noncomputable def finiteGridMaximalSequence
    {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (s : Finset ι) (hs : s.Nonempty)
    (T : ι → lp (fun _ : ℤ => ℂ) p →
      lp (fun _ : ℤ => ℂ) p)
    (hT : ∀ i ∈ s, ∀ g, ‖T i g‖ ≤ ‖g‖)
    (f : lp (fun _ : ℤ => ℂ) p) :
    lp (fun _ : ℤ => ℝ) p :=
  lpOfUniformFiniteMomentBound hp0 hpTop
    (fun x : ℤ => s.sup' hs (fun i => ‖T i f x‖))
    (show 0 ≤ (s.card : ℝ) * ‖f‖ ^ p.toReal from by positivity)
    (finiteGridMaximalLpMomentBound hp0 hpTop s hs T hT f)

/-- The finite maximal function of a family of `ℓᵖ` contractions has norm
at most `|s|^(1/p) ‖f‖`. -/
theorem finiteGridMaximalSequence_norm_le
    {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (s : Finset ι) (hs : s.Nonempty)
    (T : ι → lp (fun _ : ℤ => ℂ) p →
      lp (fun _ : ℤ => ℂ) p)
    (hT : ∀ i ∈ s, ∀ g, ‖T i g‖ ≤ ‖g‖)
    (f : lp (fun _ : ℤ => ℂ) p) :
    ‖finiteGridMaximalSequence hp0 hpTop s hs T hT f‖ ≤
      (s.card : ℝ) ^ (1 / p.toReal) * ‖f‖ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hC : 0 ≤ (s.card : ℝ) * ‖f‖ ^ p.toReal := by positivity
  calc
    ‖finiteGridMaximalSequence hp0 hpTop s hs T hT f‖ ≤
        ((s.card : ℝ) * ‖f‖ ^ p.toReal) ^ (1 / p.toReal) := by
          simpa [finiteGridMaximalSequence] using
            (lpOfUniformFiniteMomentBound_norm_le hp0 hpTop
              (fun x : ℤ => s.sup' hs (fun i => ‖T i f x‖)) hC
              (finiteGridMaximalLpMomentBound hp0 hpTop s hs T hT f))
    _ = (s.card : ℝ) ^ (1 / p.toReal) * ‖f‖ := by
          rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg f) _)]
          have hnormCancel :
              (‖f‖ ^ p.toReal) ^ (1 / p.toReal) = ‖f‖ := by
            simpa [one_div] using
              (Real.rpow_rpow_inv (norm_nonneg f) (ne_of_gt hp))
          rw [hnormCancel]

end FractionalPrimes.Literature.MSZ

end
