module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionDensity

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- Reindex one selected residue class of the low-degree phase as the phase
of the affine-substitution polynomial `Q(k)=Plo(c+r*k)`. The returned
interval, degree bound, evaluation identity, and sum lower bound are exactly
the inputs to `scalarWeyl_selectedResidue_inductionApplication`. -/
theorem scalarWeyl_selectedResidue_reindexForInduction
    {d N r N' : ℕ} {A : ℝ}
    (hr : 0 < r) (hN' : N' = N ⌈/⌉ r)
    (lo hi b : ℤ)
    (hb : b ∈ Finset.Icc (1 : ℤ) (r : ℤ))
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (Plo : Polynomial ℝ) (hPlo : Plo.natDegree ≤ d - 1)
    (hselected : A ≤
      ‖∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n ≡ b [ZMOD (r : ℤ)]),
        unitFrequencyPhase (Plo.eval (n : ℝ))‖) :
    let c : ℤ := b - (r : ℤ)
    let K : Finset ℤ := Finset.Ico
      (Int.ceil (((lo - c : ℤ) : ℚ) / (r : ℚ)))
      (Int.ceil (((hi - c : ℤ) : ℚ) / (r : ℚ)))
    let Q : Polynomial ℝ :=
      Plo.comp (Polynomial.C (r : ℝ) * Polynomial.X +
        Polynomial.C (c : ℝ))
    K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ) ∧
      Q.natDegree ≤ d - 1 ∧
      (∀ k : ℤ,
        Q.eval (k : ℝ) =
          Plo.eval ((c : ℝ) + (r : ℝ) * (k : ℝ))) ∧
      (∃ a b : ℤ, K = Finset.Ico a b) ∧
      A ≤ ‖∑ k ∈ K, unitFrequencyPhase (Q.eval (k : ℝ))‖ := by
  classical
  let c : ℤ := b - (r : ℤ)
  let K : Finset ℤ := Finset.Ico
    (Int.ceil (((lo - c : ℤ) : ℚ) / (r : ℚ)))
    (Int.ceil (((hi - c : ℤ) : ℚ) / (r : ℚ)))
  let Q : Polynomial ℝ :=
    Plo.comp (Polynomial.C (r : ℝ) * Polynomial.X +
      Polynomial.C (c : ℝ))
  have hReindex :=
    scalarWeyl_residueFiber_reindex hr hN' hb hJsubset
  have hReindex' : K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ) ∧
      ∀ f : ℤ → ℂ,
        (∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n ≡ b [ZMOD (r : ℤ)]), f n) =
        ∑ k ∈ K, f (c + (r : ℤ) * k) := by
    simpa [K, c] using hReindex
  have hQdegree : Q.natDegree ≤ d - 1 := by
    simpa [Q] using scalarWeyl_affineSubstitution_degree Plo hPlo c r
  have hQeval (k : ℤ) :
      Q.eval (k : ℝ) =
        Plo.eval ((c : ℝ) + (r : ℝ) * (k : ℝ)) := by
    simpa [Q] using scalarWeyl_affineSubstitution_eval Plo c r k
  have hKinterval : ∃ a b : ℤ, K = Finset.Ico a b := by
    dsimp [K, c]
    exact ⟨Int.ceil (((lo - (b - (r : ℤ)) : ℤ) : ℚ) / (r : ℚ)),
      Int.ceil (((hi - (b - (r : ℤ)) : ℤ) : ℚ) / (r : ℚ)), rfl⟩
  have hsum :
      (∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n ≡ b [ZMOD (r : ℤ)]),
        unitFrequencyPhase (Plo.eval (n : ℝ))) =
        ∑ k ∈ K, unitFrequencyPhase (Q.eval (k : ℝ)) := by
    calc
      (∑ n ∈ (Finset.Ico lo hi).filter
          (fun n => n ≡ b [ZMOD (r : ℤ)]),
        unitFrequencyPhase (Plo.eval (n : ℝ))) =
          ∑ k ∈ K,
            unitFrequencyPhase
              (Plo.eval ((c : ℝ) + (r : ℝ) * (k : ℝ))) :=
        by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
            hReindex'.2 (fun n => unitFrequencyPhase (Plo.eval (n : ℝ)))
      _ = ∑ k ∈ K, unitFrequencyPhase (Q.eval (k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact congrArg unitFrequencyPhase (hQeval k).symm
  have hselected' := hselected
  rw [hsum] at hselected'
  exact ⟨hReindex'.1, hQdegree, hQeval, hKinterval, hselected'⟩

end FractionalPrimes.Literature.Polynomial
